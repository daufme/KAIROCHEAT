import tkinter as tk
from tkinter import ttk, simpledialog
import struct
import json
import os
import sys

try:
    import pymem
    import pymem.process
except ImportError:
    print("请安装 pymem: pip install pymem")
    sys.exit(1)

def load_json(path):
    with open(path, 'r', encoding='utf-8') as f:
        return json.load(f)

def save_json(path, data):
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=2, ensure_ascii=False)

def hex_to_int(val):
    if isinstance(val, str):
        if val.lower().startswith('0x'):
            return int(val, 16)
        return int(val)
    return int(val)

TYPE_INFO = {
    "int":   (4, "i"),
    "sbyte": (1, "b"),
    "byte":  (1, "B"),
    "long":  (8, "q"),
    "float": (4, "f"),
    "bool":  (1, "B"),
}

def parse_array_type(ftype):
    if ftype.endswith('[]'):
        dims = 0
        temp = ftype
        while temp.endswith('[]'):
            dims += 1
            temp = temp[:-2]
        if temp in TYPE_INFO:
            return (temp, dims)
    return (ftype, 0)

def get_display_label(fdef):
    display = fdef.get("display")
    if display:
        return display
    name = fdef.get("name")
    if name:
        return name
    off = fdef.get("offset")
    if off is not None:
        return f"0x{hex_to_int(off):02X}"
    return "???"

class MemoryEditor:
    def __init__(self, parent, table_name, table_config_path):
        self.parent = parent
        self.table_name = table_name
        self.table_config_path = table_config_path
        self.table_cfg = load_json(table_config_path)
        base_dir = os.path.dirname(table_config_path)

        self.fields_file = os.path.join(base_dir, "..", "fields", self.table_cfg["fields_file"])
        raw_fields = load_json(self.fields_file)["fields"]
        self.fields_def = []
        for f in raw_fields:
            off = f.get("offset")
            ftype = f.get("type")
            if off is None or ftype is None:
                continue
            name = f.get("name", "")
            display = f.get("display", "")
            hidden = f.get("hidden", False)
            self.fields_def.append({
                "offset": off,
                "type": ftype,
                "name": name,
                "display": display,
                "hidden": hidden
            })

        self.id_field = self.table_cfg.get("id_field")
        if self.id_field:
            nmf = self.table_cfg.get("name_map_file")
            if nmf:
                self.name_file = os.path.join(base_dir, "..", "names", nmf)
            else:
                self.name_file = os.path.join(base_dir, "..", "names", f"{self.table_name}_names.json")
            self.id_name_map = {}
            self.load_names()
        else:
            self.id_name_map = None
            self.name_file = None

        self.pm = None
        self.module_base = 0
        self.obj_list = []
        self.current_category_idx = None
        self.current_item_idx = None
        self.current_edit_addr = None
        self.field_labels = {}

        self.create_widgets()
        self.connect_to_process()

    def load_names(self):
        if not self.name_file or not self.id_field: return
        if os.path.exists(self.name_file):
            raw = load_json(self.name_file)
            self.id_name_map = {int(k) if str(k).isdigit() else k: v for k, v in raw.items()}
        else:
            self.id_name_map = {}

    def save_names(self):
        if not self.name_file or self.id_name_map is None: return
        save_json(self.name_file, {str(k): v for k, v in self.id_name_map.items()})

    def create_widgets(self):
        top = ttk.Frame(self.parent)
        top.pack(fill=tk.X, padx=5, pady=5)
        ttk.Button(top, text="Refresh", command=self.refresh_data).pack(side=tk.LEFT, padx=5)
        ttk.Button(top, text="显示所有隐藏字段", command=self.show_all_hidden_fields).pack(side=tk.LEFT, padx=5)
        self.status = ttk.Label(top, text="未连接", foreground="red")
        self.status.pack(side=tk.RIGHT, padx=5)

        paned = ttk.PanedWindow(self.parent, orient=tk.HORIZONTAL)
        paned.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        left = ttk.LabelFrame(paned, text="Categories", width=120)
        paned.add(left, weight=0)
        self.cat_listbox = tk.Listbox(left, width=20)
        self.cat_listbox.pack(fill=tk.BOTH, expand=True)
        self.cat_listbox.bind('<<ListboxSelect>>', self.on_cat_select)

        mid = ttk.LabelFrame(paned, text="List", width=180)
        paned.add(mid, weight=1)
        self.item_listbox = tk.Listbox(mid, width=30)
        self.item_listbox.pack(fill=tk.BOTH, expand=True)
        self.item_listbox.bind('<<ListboxSelect>>', self.on_item_select)

        right = ttk.LabelFrame(paned, text="Fields")
        paned.add(right, weight=3)
        canvas = tk.Canvas(right, borderwidth=0)
        scroll = ttk.Scrollbar(right, orient=tk.VERTICAL, command=canvas.yview)
        self.edit_frame = ttk.Frame(canvas)
        self.edit_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0,0), window=self.edit_frame, anchor="nw")
        canvas.configure(yscrollcommand=scroll.set)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scroll.pack(side=tk.RIGHT, fill=tk.Y)

    def connect_to_process(self):
        try:
            self.pm = pymem.Pymem(self.table_cfg["process"])
            self.module_base = pymem.process.module_from_name(
                self.pm.process_handle, self.table_cfg["module"]).lpBaseOfDll
            self.status.config(text=f"已连接 Base:0x{self.module_base:08X}", foreground="green")
            self.refresh_data()
        except Exception as e:
            self.status.config(text=f"连接失败: {e}", foreground="red")

    def _read_pointer_chain(self):
        chain = self.table_cfg["pointer_chain"]
        base = self.module_base + hex_to_int(chain[0])
        ptr = self.pm.read_uint(base)
        if ptr == 0: return None
        for off in chain[1:]:
            ptr = self.pm.read_uint(ptr + hex_to_int(off))
            if ptr == 0: return None
        return ptr

    def _traverse_addresses(self):
        mode = self.table_cfg.get("mode", "array")
        final_addr = self._read_pointer_chain()
        if final_addr is None: return []
        if mode == "single":
            return [final_addr] if final_addr != 0 else []
        try:
            count = self.pm.read_int(final_addr + 0x0C)
            if count <= 0 or count > 100000: return []
        except:
            return []
        addrs = []
        for i in range(count):
            try:
                addr = self.pm.read_uint(final_addr + 0x10 + i*4)
                if addr and addr % 4 == 0: addrs.append(addr)
            except:
                break
        return addrs

    def _read_value(self, addr, size, fmt):
        return struct.unpack(fmt, self.pm.read_bytes(addr, size))[0]

    def _write_value(self, addr, size, fmt, value):
        self.pm.write_bytes(addr, struct.pack(fmt, value), size)

    def _read_string(self, str_addr):
        if str_addr == 0: return ""
        try:
            length = self.pm.read_int(str_addr + 8)
            if length < 0 or length > 10000: return "<长度异常>"
            return self.pm.read_bytes(str_addr + 12, length * 2).decode('utf-16-le', errors='replace')
        except Exception as e:
            return f"<string读失败: {e}>"

    def _read_1d_array(self, arr_addr, elem_type, max_preview=50):
        if arr_addr == 0: return []
        try:
            length = self.pm.read_int(arr_addr + 0x0C)
            if length < 0 or length > 10000: return ["<len err>"]
            size, fmt = TYPE_INFO[elem_type]
            actual_count = min(length, max_preview)
            values = []
            for i in range(actual_count):
                raw = self._read_value(arr_addr + 0x10 + i * size, size, fmt)
                if elem_type == "bool":
                    values.append(bool(raw))
                else:
                    values.append(raw)
            if length > max_preview:
                values.append(f"... (共 {length} 个元素)")
            return values
        except Exception as e:
            return [f"<err: {e}>"]

    def _read_2d_array(self, arr_addr, elem_type, max_outer=5, max_inner=5):
        if arr_addr == 0: return []
        try:
            outer_len = self.pm.read_int(arr_addr + 0x0C)
            if outer_len < 0 or outer_len > 1000: return ["<len err>"]
            result = []
            for i in range(min(outer_len, max_outer)):
                inner_ptr = self.pm.read_uint(arr_addr + 0x10 + i * 4)
                if inner_ptr:
                    inner_data = self._read_1d_array(inner_ptr, elem_type, max_inner)
                else:
                    inner_data = []
                result.append(inner_data)
            if outer_len > max_outer:
                result.append(f"... (共 {outer_len} 行)")
            return result
        except Exception as e:
            return [f"<err: {e}>"]

    def _read_field(self, addr, fdef):
        off = hex_to_int(fdef["offset"])
        ftype = fdef["type"]
        if ftype == "string":
            return self._read_string(self.pm.read_uint(addr + off))
        base_type, dims = parse_array_type(ftype)
        if dims == 1:
            arr_addr = self.pm.read_uint(addr + off)
            return self._read_1d_array(arr_addr, base_type)
        elif dims == 2:
            arr_addr = self.pm.read_uint(addr + off)
            return self._read_2d_array(arr_addr, base_type)
        elif base_type in TYPE_INFO:
            size, fmt = TYPE_INFO[base_type]
            raw = self._read_value(addr + off, size, fmt)
            if base_type == "bool":
                return bool(raw)
            return raw
        else:
            raise ValueError(f"未知类型: {ftype}")

    def _write_field_value(self, addr, fdef, value):
        off = hex_to_int(fdef["offset"])
        ftype = fdef["type"]
        base_type, dims = parse_array_type(ftype)
        if dims > 0 or ftype == "string":
            raise ValueError(f"不可写入的类型: {ftype}")
        size, fmt = TYPE_INFO[base_type]
        if base_type == "bool":
            val = 1 if value else 0
        else:
            val = value
        self._write_value(addr + off, size, fmt, val)

    def _get_array_base_addr(self, obj_addr, fdef):
        off = hex_to_int(fdef["offset"])
        return self.pm.read_uint(obj_addr + off)

    def _read_all_fields(self, addr):
        data = {}
        for fdef in self.fields_def:
            try:
                data[fdef["name"]] = self._read_field(addr, fdef)
            except Exception as e:
                data[fdef["name"]] = f"ERR:{e}"
        return data

    def _get_category_field(self):
        cat = self.table_cfg.get("category")
        return cat["field"] if cat else None

    def _get_id_field(self):
        return self.id_field

    def refresh_data(self):
        if not self.pm: return
        try:
            addrs = self._traverse_addresses()
            cat_field = self._get_category_field()
            id_field = self._get_id_field()
            self.obj_list = []
            for addr in addrs:
                cv = None; oid = None
                if cat_field or id_field:
                    for fdef in self.fields_def:
                        try:
                            if fdef["name"] == cat_field: cv = self._read_field(addr, fdef)
                            if fdef["name"] == id_field: oid = self._read_field(addr, fdef)
                        except:
                            pass
                self.obj_list.append({'addr':addr, 'cat':cv, 'id':oid})

            if cat_field:
                self.categories = {}
                for obj in self.obj_list:
                    c = obj['cat'] if obj['cat'] is not None else -1
                    self.categories.setdefault(c, []).append(obj)
            else:
                self.categories = {self.table_name: self.obj_list}

            self._refresh_ui()
            self.status.config(text=f"已刷新 {len(self.obj_list)} 个对象", foreground="green")
        except Exception as e:
            self.status.config(text=f"刷新失败: {e}", foreground="red")

    def _refresh_ui(self):
        self.field_labels.clear()
        self.cat_listbox.delete(0, tk.END)
        cat_keys = sorted(self.categories.keys(), key=lambda x: (isinstance(x,int), x) if isinstance(x,int) else (0,str(x)))
        type_names = self.table_cfg.get("category", {}).get("names", {})
        for c in cat_keys:
            if isinstance(c, int):
                name = type_names.get(str(c), str(c))
            else:
                name = str(c)
            self.cat_listbox.insert(tk.END, f"{name} ({len(self.categories[c])})")

        if self.current_category_idx is not None and self.current_category_idx < len(cat_keys):
            self.cat_listbox.selection_set(self.current_category_idx)
            self._fill_item_list(cat_keys[self.current_category_idx])
        else:
            self.item_listbox.delete(0, tk.END)
            self.clear_edit()
            return

        if self.current_item_idx is not None and hasattr(self, 'current_category_items'):
            if self.current_item_idx < len(self.current_category_items):
                self.item_listbox.selection_set(self.current_item_idx)
                obj = self.current_category_items[self.current_item_idx]
                self.current_edit_addr = obj['addr']
                fields = self._read_all_fields(obj['addr'])
                self.display_fields(obj['addr'], obj['id'], fields)
            else:
                self.clear_edit()
        else:
            self.clear_edit()

    def _fill_item_list(self, cat_key):
        self.current_category_items = self.categories[cat_key]
        self.item_listbox.delete(0, tk.END)
        for obj in self.current_category_items:
            iid = obj.get('id')
            if self.id_field and iid is not None:
                name = self.id_name_map.get(iid, '')
                display = f"{name} (ID:{iid})" if name else f"ID:{iid}"
            else:
                display = f"0x{obj['addr']:08X}"
            self.item_listbox.insert(tk.END, display)

    def on_cat_select(self, event=None):
        sel = self.cat_listbox.curselection()
        if not sel: return
        idx = sel[0]
        cat_keys = sorted(self.categories.keys(), key=lambda x: (isinstance(x,int), x) if isinstance(x,int) else (0,str(x)))
        if idx >= len(cat_keys): return
        self.current_category_idx = idx
        self._fill_item_list(cat_keys[idx])
        self.current_item_idx = None
        self.clear_edit()

    def on_item_select(self, event=None):
        sel = self.item_listbox.curselection()
        if not sel: return
        idx = sel[0]
        if not hasattr(self, 'current_category_items'): return
        if idx >= len(self.current_category_items): return
        self.current_item_idx = idx
        obj = self.current_category_items[idx]
        self.current_edit_addr = obj['addr']
        fields = self._read_all_fields(obj['addr'])
        self.display_fields(obj['addr'], obj['id'], fields)

    def clear_edit(self):
        for w in self.edit_frame.winfo_children():
            w.destroy()
        self.field_labels.clear()

    def display_fields(self, addr, obj_id, fields):
        self.clear_edit()
        row = 0

        info = f"地址: 0x{addr:08X}"
        if self.id_field and obj_id is not None:
            info += f"  ID:{obj_id}"
        ttk.Label(self.edit_frame, text=info, foreground="darkblue",
                  font=("TkDefaultFont",9,"bold")).grid(row=row, column=0, columnspan=4, sticky="w", padx=5, pady=(5,2))
        row += 1

        if self.id_field and obj_id is not None and self.id_name_map is not None:
            ttk.Label(self.edit_frame, text="自定义名称").grid(row=row, column=0, sticky="w", padx=5, pady=2)
            name_var = tk.StringVar(value=self.id_name_map.get(obj_id, ''))
            entry = ttk.Entry(self.edit_frame, textvariable=name_var, width=25)
            entry.grid(row=row, column=1, columnspan=2, sticky="w", padx=5, pady=2)
            entry.bind('<Return>', lambda e, oid=obj_id, v=name_var: self._save_name(oid, v))
            ttk.Button(self.edit_frame, text="Save",
                       command=lambda oid=obj_id, var=name_var: self._save_name(oid, var)
                       ).grid(row=row, column=3, padx=5, pady=2)
            row += 1

        for fdef in self.fields_def:
            if fdef.get("hidden", False): continue
            name = fdef["name"]
            disp = get_display_label(fdef)
            offset = hex_to_int(fdef["offset"])
            label_text = f"{disp} (0x{offset:02X})"

            lbl_frame = ttk.Frame(self.edit_frame)
            lbl_frame.grid(row=row, column=0, sticky="w", padx=5, pady=2)
            lbl = ttk.Label(lbl_frame, text=label_text)
            lbl.pack(side=tk.LEFT)
            ttk.Button(lbl_frame, text="✎", width=3,
                       command=lambda n=name: self._rename_field_display(n)).pack(side=tk.LEFT, padx=2)
            ttk.Button(lbl_frame, text="✕", width=3,
                       command=lambda n=name: self._hide_field(n)).pack(side=tk.LEFT, padx=2)
            self.field_labels[name] = lbl

            val = fields.get(name, "ERR")
            ftype = fdef["type"]
            base_type, dims = parse_array_type(ftype)

            if ftype == "string":
                display_str = str(val) if not isinstance(val, str) or not val.startswith("<") else str(val)
                ttk.Label(self.edit_frame, text=display_str, wraplength=350, relief="sunken", anchor="w",
                          background="white").grid(row=row, column=1, columnspan=3, sticky="ew", padx=5, pady=2)
                row += 1
                continue

            if dims == 1:
                self._create_1d_array_editor(row, addr, fdef, val, base_type)
            elif dims == 2:
                self._create_2d_array_editor(row, addr, fdef, val, base_type)
            else:  # 标量
                is_err = isinstance(val, str) and val.startswith("ERR")
                if base_type == "bool":
                    var = tk.StringVar(value="True" if val else "False")
                    combo = ttk.Combobox(self.edit_frame, textvariable=var, values=("True","False"),
                                         width=10, state='readonly' if is_err else 'normal')
                    combo.grid(row=row, column=1, columnspan=2, sticky="ew", padx=5, pady=2)
                    if not is_err:
                        save_btn = ttk.Button(self.edit_frame, text="Save",
                                              command=lambda a=addr, f=fdef, v=var: self._write_bool_field(a, f, v))
                        save_btn.grid(row=row, column=3, padx=5, pady=2)
                        combo.bind('<<ComboboxSelected>>', lambda e, a=addr, f=fdef, v=var: self._write_bool_field(a, f, v))
                else:
                    var = tk.StringVar(value=str(val) if not is_err else val)
                    entry = ttk.Entry(self.edit_frame, textvariable=var, width=18, state='readonly' if is_err else 'normal')
                    entry.grid(row=row, column=1, columnspan=2, sticky="ew", padx=5, pady=2)
                    if not is_err:
                        save_btn = ttk.Button(self.edit_frame, text="Save",
                                              command=lambda a=addr, f=fdef, v=var: self._write_field(a, f, v))
                        save_btn.grid(row=row, column=3, padx=5, pady=2)
                        entry.bind('<Return>', lambda e, a=addr, f=fdef, v=var: self._write_field(a, f, v))
            row += 1

        self.edit_frame.grid_columnconfigure(1, weight=1)
        self.edit_frame.grid_columnconfigure(2, weight=1)

    def _write_bool_field(self, addr, fdef, var):
        try:
            val_str = var.get()
            bool_val = val_str == "True"
            self._write_field_value(addr, fdef, bool_val)
            verify = self._read_field(addr, fdef)
            var.set("True" if verify else "False")
            self.status.config(text=f"✔ {get_display_label(fdef)}: {bool_val} → {verify}", foreground="green")
        except Exception as e:
            self.status.config(text=f"✘ {fdef['name']}: 写入失败 ({e})", foreground="red")

    def _create_1d_array_editor(self, row, obj_addr, fdef, current_val, elem_type):
        name = fdef["name"]
        if isinstance(current_val, list) and not any(isinstance(x, str) and x.startswith("<") for x in current_val):
            elements = current_val
            preview = str(elements) if len(elements) <= 5 else f"[{len(elements)} elements]"
        else:
            elements = None
            preview = str(current_val)

        container = ttk.Frame(self.edit_frame)
        container.grid(row=row, column=1, columnspan=3, sticky="ew", padx=5, pady=2)
        preview_frame = ttk.Frame(container)
        preview_frame.pack(fill=tk.X)
        ttk.Label(preview_frame, text=preview, wraplength=400).pack(side=tk.LEFT)
        if elements is not None:
            expand_btn = ttk.Button(preview_frame, text="▶ 展开", width=6)
            expand_btn.pack(side=tk.RIGHT, padx=5)
        else:
            ttk.Label(preview_frame, text="(无法编辑)").pack(side=tk.RIGHT)

        editor_frame = ttk.Frame(container)
        container.expanded = False
        container.editor_frame = editor_frame
        container.expand_btn = expand_btn if elements is not None else None

        if elements is not None and elem_type in TYPE_INFO:
            size, fmt = TYPE_INFO[elem_type]
            def toggle():
                if container.expanded:
                    editor_frame.pack_forget()
                    expand_btn.config(text="▶ 展开")
                    container.expanded = False
                else:
                    for w in editor_frame.winfo_children():
                        w.destroy()
                    arr_addr = self._get_array_base_addr(obj_addr, fdef)
                    if arr_addr:
                        try:
                            length = self.pm.read_int(arr_addr + 0x0C)
                            if length < 0 or length > 1000:
                                ttk.Label(editor_frame, text="长度异常").pack()
                            else:
                                for i in range(length):
                                    elem_addr = arr_addr + 0x10 + i * size
                                    try:
                                        cur_raw = self._read_value(elem_addr, size, fmt)
                                        cur_val = bool(cur_raw) if elem_type == "bool" else cur_raw
                                    except:
                                        cur_val = "ERR"
                                    ef = ttk.Frame(editor_frame)
                                    ef.pack(fill=tk.X, pady=1)
                                    ttk.Label(ef, text=f"[{i}]").pack(side=tk.LEFT, padx=5)
                                    if elem_type == "bool":
                                        var = tk.StringVar(value="True" if cur_val else "False")
                                        combo = ttk.Combobox(ef, textvariable=var, values=("True","False"), width=10)
                                        combo.pack(side=tk.LEFT, padx=5)
                                        save_btn = ttk.Button(ef, text="Save",
                                                              command=lambda ea=elem_addr, et=elem_type, v=var: self._write_array_element_bool(ea, et, v))
                                        save_btn.pack(side=tk.LEFT, padx=5)
                                        combo.bind('<<ComboboxSelected>>', lambda e, ea=elem_addr, et=elem_type, v=var: self._write_array_element_bool(ea, et, v))
                                    else:
                                        var = tk.StringVar(value=str(cur_val))
                                        entry = ttk.Entry(ef, textvariable=var, width=14)
                                        entry.pack(side=tk.LEFT, padx=5)
                                        save_btn = ttk.Button(ef, text="Save",
                                                              command=lambda ea=elem_addr, et=elem_type, v=var: self._write_array_element(ea, et, v))
                                        save_btn.pack(side=tk.LEFT, padx=5)
                                        entry.bind('<Return>', lambda e, ea=elem_addr, et=elem_type, v=var: self._write_array_element(ea, et, v))
                        except Exception as e:
                            ttk.Label(editor_frame, text=f"读取失败: {e}").pack()
                    else:
                        ttk.Label(editor_frame, text="数组地址无效").pack()
                    editor_frame.pack(fill=tk.X, pady=2)
                    expand_btn.config(text="▼ 收起")
                    container.expanded = True
            expand_btn.config(command=toggle)

    def _create_2d_array_editor(self, row, obj_addr, fdef, current_val, elem_type):
        if not isinstance(current_val, list) or any(isinstance(x, str) and x.startswith("<") for x in current_val):
            ttk.Label(self.edit_frame, text=str(current_val)).grid(row=row, column=1, columnspan=3, sticky="ew", padx=5, pady=2)
            return

        outer_len = len(current_val)
        preview = f"2D [{outer_len}×?]"

        container = ttk.Frame(self.edit_frame)
        container.grid(row=row, column=1, columnspan=3, sticky="ew", padx=5, pady=2)
        preview_frame = ttk.Frame(container)
        preview_frame.pack(fill=tk.X)
        ttk.Label(preview_frame, text=preview).pack(side=tk.LEFT)
        expand_btn = ttk.Button(preview_frame, text="▶ 展开", width=6)
        expand_btn.pack(side=tk.RIGHT, padx=5)

        editor_frame = ttk.Frame(container)
        container.expanded = False
        container.editor_frame = editor_frame
        container.expand_btn = expand_btn

        def toggle_outer():
            if container.expanded:
                editor_frame.pack_forget()
                expand_btn.config(text="▶ 展开")
                container.expanded = False
            else:
                for w in editor_frame.winfo_children():
                    w.destroy()
                arr_addr = self._get_array_base_addr(obj_addr, fdef)
                if not arr_addr:
                    ttk.Label(editor_frame, text="数组地址无效").pack()
                    editor_frame.pack(fill=tk.X, pady=2)
                    expand_btn.config(text="▼ 收起")
                    container.expanded = True
                    return
                try:
                    outer_len = self.pm.read_int(arr_addr + 0x0C)
                    if outer_len < 0 or outer_len > 1000:
                        ttk.Label(editor_frame, text="长度异常").pack()
                        editor_frame.pack(fill=tk.X, pady=2)
                        expand_btn.config(text="▼ 收起")
                        container.expanded = True
                        return
                    for i in range(outer_len):
                        inner_ptr = self.pm.read_uint(arr_addr + 0x10 + i * 4)
                        if inner_ptr:
                            inner_data = self._read_1d_array(inner_ptr, elem_type)
                        else:
                            inner_data = []
                        sub_frame = ttk.Frame(editor_frame)
                        sub_frame.pack(fill=tk.X, pady=2)
                        sub_container = ttk.Frame(sub_frame)
                        sub_container.pack(fill=tk.X)
                        sub_preview = f"[{i}]: " + (str(inner_data) if len(inner_data) <= 5 else f"{len(inner_data)} elements")
                        sub_expand_btn = ttk.Button(sub_container, text="▶", width=3)
                        sub_expand_btn.pack(side=tk.LEFT)
                        ttk.Label(sub_container, text=sub_preview).pack(side=tk.LEFT, padx=5)
                        sub_editor = ttk.Frame(sub_frame)
                        sub_container.expanded = False
                        sub_container.editor_frame = sub_editor
                        sub_container.expand_btn = sub_expand_btn
                        def make_sub_toggle(inner_ptr_addr=inner_ptr, elem_type=elem_type, parent=sub_container, sub_editor=sub_editor, btn=sub_expand_btn):
                            return lambda: self._toggle_sub_array(inner_ptr_addr, elem_type, parent, sub_editor, btn)
                        sub_expand_btn.config(command=make_sub_toggle())
                except Exception as e:
                    ttk.Label(editor_frame, text=f"错误: {e}").pack()
                editor_frame.pack(fill=tk.X, pady=2)
                expand_btn.config(text="▼ 收起")
                container.expanded = True
        expand_btn.config(command=toggle_outer)

    def _toggle_sub_array(self, inner_ptr, elem_type, parent, sub_editor, btn):
        if parent.expanded:
            sub_editor.pack_forget()
            btn.config(text="▶")
            parent.expanded = False
        else:
            for w in sub_editor.winfo_children():
                w.destroy()
            if inner_ptr and elem_type in TYPE_INFO:
                try:
                    length = self.pm.read_int(inner_ptr + 0x0C)
                    if length < 0 or length > 1000:
                        ttk.Label(sub_editor, text="长度异常").pack()
                    else:
                        size, fmt = TYPE_INFO[elem_type]
                        for i in range(length):
                            elem_addr = inner_ptr + 0x10 + i * size
                            try:
                                cur_raw = self._read_value(elem_addr, size, fmt)
                                cur_val = bool(cur_raw) if elem_type == "bool" else cur_raw
                            except:
                                cur_val = "ERR"
                            ef = ttk.Frame(sub_editor)
                            ef.pack(fill=tk.X, pady=1)
                            ttk.Label(ef, text=f"[{i}]").pack(side=tk.LEFT, padx=5)
                            if elem_type == "bool":
                                var = tk.StringVar(value="True" if cur_val else "False")
                                combo = ttk.Combobox(ef, textvariable=var, values=("True","False"), width=10)
                                combo.pack(side=tk.LEFT, padx=5)
                                save_btn = ttk.Button(ef, text="Save",
                                                      command=lambda ea=elem_addr, et=elem_type, v=var: self._write_array_element_bool(ea, et, v))
                                save_btn.pack(side=tk.LEFT, padx=5)
                                combo.bind('<<ComboboxSelected>>', lambda e, ea=elem_addr, et=elem_type, v=var: self._write_array_element_bool(ea, et, v))
                            else:
                                var = tk.StringVar(value=str(cur_val))
                                entry = ttk.Entry(ef, textvariable=var, width=14)
                                entry.pack(side=tk.LEFT, padx=5)
                                save_btn = ttk.Button(ef, text="Save",
                                                      command=lambda ea=elem_addr, et=elem_type, v=var: self._write_array_element(ea, et, v))
                                save_btn.pack(side=tk.LEFT, padx=5)
                                entry.bind('<Return>', lambda e, ea=elem_addr, et=elem_type, v=var: self._write_array_element(ea, et, v))
                except Exception as e:
                    ttk.Label(sub_editor, text=f"读取失败: {e}").pack()
            else:
                ttk.Label(sub_editor, text="空或未知类型").pack()
            sub_editor.pack(fill=tk.X, pady=2)
            btn.config(text="▼")
            parent.expanded = True

    def _write_array_element(self, elem_addr, elem_type, var):
        try:
            new_str = var.get()
            size, fmt = TYPE_INFO[elem_type]
            if elem_type == "float":
                new_val = float(new_str)
            elif elem_type == "byte":
                new_val = int(new_str) & 0xFF
            else:
                new_val = int(new_str)
            old_val = self._read_value(elem_addr, size, fmt)
            self._write_value(elem_addr, size, fmt, new_val)
            verify = self._read_value(elem_addr, size, fmt)
            var.set(str(verify))
            self.status.config(text=f"✔ 数组元素: {old_val} → {verify}", foreground="green")
        except ValueError:
            self.status.config(text="✘ 无效数字", foreground="red")
        except Exception as e:
            self.status.config(text=f"✘ 写入失败 ({e})", foreground="red")

    def _write_array_element_bool(self, elem_addr, elem_type, var):
        try:
            val_str = var.get()
            bool_val = val_str == "True"
            old_raw = self._read_value(elem_addr, 1, "B")
            old_val = bool(old_raw)
            self._write_value(elem_addr, 1, "B", 1 if bool_val else 0)
            verify_raw = self._read_value(elem_addr, 1, "B")
            verify = bool(verify_raw)
            var.set("True" if verify else "False")
            self.status.config(text=f"✔ 数组元素: {old_val} → {verify}", foreground="green")
        except Exception as e:
            self.status.config(text=f"✘ 写入失败 ({e})", foreground="red")

    def _rename_field_display(self, field_name):
        for f in self.fields_def:
            if f["name"] == field_name:
                cur = f.get("display") or f.get("name") or ""
                break
        else:
            return
        new = simpledialog.askstring("重命名显示名", f"'{field_name}' 的新显示名:", initialvalue=cur)
        if new is None: return
        new = new.strip() if new else ""
        f["display"] = new
        save_json(self.fields_file, {"fields": self.fields_def})
        if field_name in self.field_labels:
            off = hex_to_int(f["offset"])
            new_disp = get_display_label(f)
            self.field_labels[field_name].config(text=f"{new_disp} (0x{off:02X})")
        self.status.config(text=f"✔ 显示名已更新: '{new}'", foreground="green")

    def _hide_field(self, field_name):
        for f in self.fields_def:
            if f["name"] == field_name:
                f["hidden"] = True
                break
        else:
            self.status.config(text=f"✘ 找不到字段: {field_name}", foreground="red")
            return
        save_json(self.fields_file, {"fields": self.fields_def})
        self.status.config(text=f"✔ 已隐藏字段: '{field_name}'", foreground="green")
        if self.current_edit_addr is not None:
            fields = self._read_all_fields(self.current_edit_addr)
            obj_id = None
            if self.id_field and hasattr(self, 'current_category_items'):
                if self.current_item_idx is not None and self.current_item_idx < len(self.current_category_items):
                    obj = self.current_category_items[self.current_item_idx]
                    obj_id = obj.get('id')
            self.display_fields(self.current_edit_addr, obj_id, fields)

    def _write_field(self, addr, fdef, var):
        off = hex_to_int(fdef["offset"])
        ftype = fdef["type"]
        base_type, dims = parse_array_type(ftype)
        if ftype == "string" or dims > 0:
            self.status.config(text="不能写入此类型字段", foreground="red")
            return
        try:
            size, fmt = TYPE_INFO[base_type]
            old_val = self._read_value(addr + off, size, fmt)
            new_str = var.get()
            if base_type == "float":
                new_val = float(new_str)
            elif base_type == "byte":
                new_val = int(new_str) & 0xFF
            else:
                new_val = int(new_str)
            self._write_field_value(addr, fdef, new_val)
            verify = self._read_value(addr + off, size, fmt)
            var.set(str(verify))
            self.status.config(text=f"✔ {get_display_label(fdef)}: {old_val} → {verify}", foreground="green")
        except ValueError:
            self.status.config(text=f"✘ {fdef['name']}: 无效数字", foreground="red")
        except Exception as e:
            self.status.config(text=f"✘ {fdef['name']}: 写入失败 ({e})", foreground="red")

    def _save_name(self, obj_id, var):
        if self.id_name_map is None: return
        name = var.get().strip()
        if name:
            self.id_name_map[obj_id] = name
        else:
            self.id_name_map.pop(obj_id, None)
        self.save_names()
        sel = self.item_listbox.curselection()
        if sel:
            idx = sel[0]
            if hasattr(self, 'current_category_items'):
                obj = self.current_category_items[idx]
                if obj.get('id') == obj_id:
                    d = f"{name} (ID:{obj_id})" if name else f"ID:{obj_id}"
                    self.item_listbox.delete(idx)
                    self.item_listbox.insert(idx, d)
                    self.item_listbox.selection_set(idx)
        self.status.config(text=f"✔ 名称已保存", foreground="green")

    def show_all_hidden_fields(self):
        for f in self.fields_def:
            f["hidden"] = False
        save_json(self.fields_file, {"fields": self.fields_def})
        if self.current_edit_addr is not None:
            fields = self._read_all_fields(self.current_edit_addr)
            obj_id = None
            if self.id_field and hasattr(self, 'current_category_items') and self.current_item_idx is not None:
                if self.current_item_idx < len(self.current_category_items):
                    obj = self.current_category_items[self.current_item_idx]
                    obj_id = obj.get('id')
            self.display_fields(self.current_edit_addr, obj_id, fields)
        self.status.config(text="✔ 所有字段已设为显示", foreground="green")

    def destroy(self):
        self.save_names()
        for w in self.parent.winfo_children():
            w.destroy()

class App:
    def __init__(self, root):
        self.root = root
        self.root.title("通用内存编辑器")
        self.root.geometry("1050x700")
        self.tables_dir = os.path.join(os.path.dirname(__file__), "tables")
        self.table_files = [f for f in os.listdir(self.tables_dir) if f.endswith(".json")]
        if not self.table_files:
            sys.exit("tables 目录下未找到配置文件！")
        self.table_names = [os.path.splitext(f)[0] for f in self.table_files]

        top = ttk.Frame(root)
        top.pack(fill=tk.X, padx=5, pady=5)
        ttk.Label(top, text="数据表:").pack(side=tk.LEFT, padx=5)
        self.table_var = tk.StringVar(value=self.table_names[0])
        ttk.OptionMenu(top, self.table_var, self.table_names[0], *self.table_names,
                       command=self.switch_table).pack(side=tk.LEFT, padx=5)
        self.status = ttk.Label(top, text="", foreground="gray")
        self.status.pack(side=tk.RIGHT, padx=5)
        self.container = ttk.Frame(root)
        self.container.pack(fill=tk.BOTH, expand=True)
        self.current_editor = None
        self.switch_table(self.table_names[0])
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)

    def switch_table(self, name):
        if self.current_editor:
            self.current_editor.destroy()
        config_path = os.path.join(self.tables_dir, name + ".json")
        self.current_editor = MemoryEditor(self.container, name, config_path)
        self.status.config(text=f"当前表: {name}")

    def on_closing(self):
        if self.current_editor:
            self.current_editor.save_names()
        self.root.destroy()

if __name__ == "__main__":
    root = tk.Tk()
    App(root)
    root.mainloop()