import tkinter as tk
from tkinter import ttk, simpledialog
import struct
import json
import os
import sys
import re

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

def is_scalar_type(ftype):
    return ftype in TYPE_INFO or ftype == "string"

def get_scalar_size(ftype):
    if ftype == "string":
        return 4
    return TYPE_INFO[ftype][0]

def get_scalar_fmt(ftype):
    if ftype == "string":
        return "I"
    return TYPE_INFO[ftype][1]

def parse_type(ftype):
    vec_match = re.match(r'^Vector<(.+)>$', ftype)
    if vec_match:
        inner = vec_match.group(1)
        return ('vector', inner)
    if ftype.endswith('[]'):
        inner = ftype[:-2]
        return ('array', inner)
    return ('scalar', ftype)

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

        # ID 字段处理：支持表达式 "字段名[索引]"
        self.id_field = self.table_cfg.get("id_field")
        self.id_parsed = self._parse_id_expression()
        if self.id_parsed:
            field_name, _ = self.id_parsed
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

    # ---------- ID 表达式解析 ----------
    def _parse_id_expression(self):
        if not self.id_field:
            return None
        m = re.match(r'^(\w+)\[(\d+)\]$', self.id_field)
        if m:
            field_name, index_str = m.groups()
            return (field_name, int(index_str))
        else:
            return (self.id_field, None)

    def _read_id_value(self, addr):
        if not self.id_parsed:
            return None
        field_name, index = self.id_parsed
        for fdef in self.fields_def:
            if fdef["name"] == field_name:
                val = self._read_field(addr, fdef)
                if index is not None:
                    if isinstance(val, list) and len(val) > index:
                        return val[index]
                    else:
                        return None
                else:
                    return val
        return None

    # ---------- 名称映射 ----------
    def load_names(self):
        if not self.name_file or not self.id_parsed: return
        if os.path.exists(self.name_file):
            raw = load_json(self.name_file)
            self.id_name_map = {int(k) if str(k).isdigit() else k: v for k, v in raw.items()}
        else:
            self.id_name_map = {}

    def save_names(self):
        if not self.name_file or self.id_name_map is None: return
        save_json(self.name_file, {str(k): v for k, v in self.id_name_map.items()})

    # ---------- UI ----------
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
        self.cat_listbox = tk.Listbox(left, width=15)
        self.cat_listbox.pack(fill=tk.BOTH, expand=True)
        self.cat_listbox.bind('<<ListboxSelect>>', self.on_cat_select)

        mid = ttk.LabelFrame(paned, text="List", width=180)
        paned.add(mid, weight=0)
        self.item_listbox = tk.Listbox(mid, width=20)
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

    # ---------- 核心内存读取 ----------
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

    def _read_scalar(self, addr, ftype):
        if ftype == "string":
            return "<错误: 请使用 _read_string>"
        size, fmt = TYPE_INFO[ftype]
        raw = struct.unpack(fmt, self.pm.read_bytes(addr, size))[0]
        if ftype == "bool":
            return bool(raw)
        return raw

    def _write_scalar(self, addr, ftype, value):
        size, fmt = TYPE_INFO[ftype]
        if ftype == "bool":
            val = 1 if value else 0
        else:
            val = value
        self.pm.write_bytes(addr, struct.pack(fmt, val), size)

    def _read_string(self, str_ptr):
        if str_ptr == 0: return ""
        try:
            length = self.pm.read_int(str_ptr + 8)
            if length < 0 or length > 10000: return "<长度异常>"
            return self.pm.read_bytes(str_ptr + 12, length * 2).decode('utf-16-le', errors='replace')
        except Exception as e:
            return f"<string读失败: {e}>"

    def _write_string_object(self, obj_ptr, new_str):
        if obj_ptr == 0:
            raise ValueError("空字符串对象，无法写入")
        length = self.pm.read_int(obj_ptr + 8)
        encoded = new_str.encode('utf-16-le')
        max_bytes = length * 2
        if len(encoded) > max_bytes:
            encoded = encoded[:max_bytes]
        else:
            encoded += b'\x00\x00' * (length - len(encoded)//2)
        self.pm.write_bytes(obj_ptr + 12, encoded, max_bytes)

    def _read_array_data(self, array_base, inner_type):
        try:
            length = self.pm.read_int(array_base + 0x0C)
            if length < 0 or length > 100000:
                return ["<len err>"]
            inner_is_ref = (inner_type == "string" or parse_type(inner_type)[0] != 'scalar')
            elem_size = 4 if inner_is_ref else get_scalar_size(inner_type)
            result = []
            for i in range(length):
                elem_addr = array_base + 0x10 + i * elem_size
                val = self._read_value_at(elem_addr, inner_type)
                result.append(val)
            return result
        except Exception as e:
            return [f"<err: {e}>"]

    def _read_array(self, addr, inner_type):
        arr_ptr = self.pm.read_uint(addr)
        if arr_ptr == 0:
            return []
        return self._read_array_data(arr_ptr, inner_type)

    def _read_vector(self, addr, inner_type):
        vec_ptr = self.pm.read_uint(addr)
        if vec_ptr == 0:
            return []
        inner_ptr = self.pm.read_uint(vec_ptr + 0x8)
        if inner_ptr == 0:
            return []
        array_ptr = self.pm.read_uint(inner_ptr + 0x8)
        if array_ptr == 0:
            return []
        return self._read_array_data(array_ptr, inner_type)

    def _read_value_at(self, addr, ftype):
        kind, inner = parse_type(ftype)
        if kind == 'scalar':
            if inner == "string":
                str_ptr = self.pm.read_uint(addr)
                return self._read_string(str_ptr)
            else:
                return self._read_scalar(addr, inner)
        elif kind == 'array':
            return self._read_array(addr, inner)
        elif kind == 'vector':
            return self._read_vector(addr, inner)
        else:
            return f"<未知类型: {ftype}>"

    # ---------- 写入 ----------
    def _write_value_at(self, addr, ftype, value):
        kind, inner = parse_type(ftype)
        if kind != 'scalar':
            raise ValueError("只能写入标量类型")
        if inner == "string":
            str_ptr = self.pm.read_uint(addr)
            if str_ptr == 0:
                raise ValueError("字符串对象为空，无法写入")
            self._write_string_object(str_ptr, value)
        else:
            self._write_scalar(addr, inner, value)

    def _get_element_address(self, obj_addr, fdef, path):
        off = hex_to_int(fdef["offset"])
        ftype = fdef["type"]
        current_addr = obj_addr + off
        for idx in path:
            kind, inner = parse_type(ftype)
            if kind == 'scalar':
                raise ValueError("路径超出维度")
            if kind == 'array':
                arr_ptr = self.pm.read_uint(current_addr)
                if arr_ptr == 0:
                    raise ValueError("数组指针为空")
                length = self.pm.read_int(arr_ptr + 0x0C)
                if idx >= length:
                    raise ValueError(f"索引 {idx} 超出长度 {length}")
                inner_is_ref = (inner == "string" or parse_type(inner)[0] != 'scalar')
                elem_size = 4 if inner_is_ref else get_scalar_size(inner)
                elem_addr = arr_ptr + 0x10 + idx * elem_size
                current_addr = elem_addr
                ftype = inner
            elif kind == 'vector':
                vec_ptr = self.pm.read_uint(current_addr)
                if vec_ptr == 0:
                    raise ValueError("Vector 指针为空")
                inner_ptr = self.pm.read_uint(vec_ptr + 0x8)
                if inner_ptr == 0:
                    raise ValueError("Vector 内部指针为空")
                array_ptr = self.pm.read_uint(inner_ptr + 0x8)
                if array_ptr == 0:
                    raise ValueError("数组指针为空")
                length = self.pm.read_int(array_ptr + 0x0C)
                if idx >= length:
                    raise ValueError(f"索引 {idx} 超出长度 {length}")
                inner_is_ref = (inner == "string" or parse_type(inner)[0] != 'scalar')
                elem_size = 4 if inner_is_ref else get_scalar_size(inner)
                elem_addr = array_ptr + 0x10 + idx * elem_size
                current_addr = elem_addr
                ftype = inner
            else:
                raise ValueError(f"未知容器类型: {kind}")
        return current_addr

    # ---------- 字段读写 ----------
    def _read_field(self, addr, fdef):
        off = hex_to_int(fdef["offset"])
        ftype = fdef["type"]
        return self._read_value_at(addr + off, ftype)

    def _write_field_value(self, addr, fdef, value):
        off = hex_to_int(fdef["offset"])
        ftype = fdef["type"]
        self._write_value_at(addr + off, ftype, value)

    def _write_field(self, addr, fdef, var):
        try:
            new_str = var.get()
            ftype = fdef["type"]
            kind, inner = parse_type(ftype)
            if kind != 'scalar':
                self.status.config(text="不能写入复合类型字段", foreground="red")
                return
            if inner in TYPE_INFO:
                if inner == "float":
                    new_val = float(new_str)
                elif inner == "byte":
                    new_val = int(new_str) & 0xFF
                else:
                    new_val = int(new_str)
                off = hex_to_int(fdef["offset"])
                old_val = self._read_value_at(addr + off, ftype)
                self._write_value_at(addr + off, ftype, new_val)
                verify = self._read_value_at(addr + off, ftype)
                var.set(str(verify))
                self.status.config(text=f"✔ {get_display_label(fdef)}: {old_val} → {verify}", foreground="green")
            elif inner == "string":
                off = hex_to_int(fdef["offset"])
                old_val = self._read_value_at(addr + off, ftype)
                self._write_value_at(addr + off, ftype, new_str)
                verify = self._read_value_at(addr + off, ftype)
                var.set(verify)
                self.status.config(text=f"✔ {get_display_label(fdef)}: 已更新字符串", foreground="green")
            else:
                self.status.config(text=f"未知类型 {ftype}", foreground="red")
        except ValueError as e:
            self.status.config(text=f"✘ {fdef['name']}: {e}", foreground="red")
        except Exception as e:
            self.status.config(text=f"✘ {fdef['name']}: 写入失败 ({e})", foreground="red")

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

    def _write_array_element(self, elem_addr, ftype, var):
        try:
            new_str = var.get()
            kind, inner = parse_type(ftype)
            if kind != 'scalar':
                self.status.config(text="只支持标量元素写入", foreground="red")
                return
            if inner in TYPE_INFO:
                if inner == "float":
                    new_val = float(new_str)
                elif inner == "byte":
                    new_val = int(new_str) & 0xFF
                else:
                    new_val = int(new_str)
                old_val = self._read_value_at(elem_addr, ftype)
                self._write_value_at(elem_addr, ftype, new_val)
                verify = self._read_value_at(elem_addr, ftype)
                var.set(str(verify))
                self.status.config(text=f"✔ 元素: {old_val} → {verify}", foreground="green")
            elif inner == "string":
                old_val = self._read_value_at(elem_addr, ftype)
                self._write_value_at(elem_addr, ftype, new_str)
                verify = self._read_value_at(elem_addr, ftype)
                var.set(verify)
                self.status.config(text=f"✔ 字符串元素已更新", foreground="green")
            else:
                self.status.config(text=f"未知元素类型 {ftype}", foreground="red")
        except ValueError as e:
            self.status.config(text=f"✘ 无效输入: {e}", foreground="red")
        except Exception as e:
            self.status.config(text=f"✘ 写入失败 ({e})", foreground="red")

    def _write_array_element_bool(self, elem_addr, ftype, var):
        try:
            val_str = var.get()
            bool_val = val_str == "True"
            self._write_value_at(elem_addr, ftype, bool_val)
            verify = self._read_value_at(elem_addr, ftype)
            var.set("True" if verify else "False")
            self.status.config(text=f"✔ 元素: {bool_val} → {verify}", foreground="green")
        except Exception as e:
            self.status.config(text=f"✘ 写入失败 ({e})", foreground="red")

    # ---------- 递归 UI 显示 ----------
    def _create_editor_for_value(self, parent_frame, obj_addr, fdef, value, ftype, path, row_idx, col_offset=0, index=None):
        if isinstance(value, list):
            return self._create_array_container(parent_frame, obj_addr, fdef, value, ftype, path, row_idx, col_offset, index)
        else:
            return self._create_scalar_editor(parent_frame, obj_addr, fdef, value, ftype, path, row_idx, col_offset, index)

    def _create_scalar_editor(self, parent, obj_addr, fdef, value, ftype, path, row_idx, col_offset=0, index=None):
        is_err = isinstance(value, str) and value.startswith("ERR")
        try:
            elem_addr = self._get_element_address(obj_addr, fdef, path)
        except Exception as e:
            elem_addr = None
            self.status.config(text=f"地址计算失败: {e}", foreground="red")

        col = 0
        if col_offset > 0:
            ttk.Label(parent, text="    " * col_offset).grid(row=row_idx, column=col, sticky="w", padx=2)
            col += 1
        if index is not None:
            ttk.Label(parent, text=f"[{index}]", foreground="gray").grid(row=row_idx, column=col, sticky="w", padx=2)
            col += 1

        if ftype == "bool":
            var = tk.StringVar(value="True" if value else "False")
            combo = ttk.Combobox(parent, textvariable=var, values=("True","False"),
                                 width=10, state='readonly' if is_err else 'normal')
            combo.grid(row=row_idx, column=col, sticky="w", padx=5, pady=1)
            col += 1
            if not is_err and elem_addr is not None:
                save_btn = ttk.Button(parent, text="Save", width=6,
                                      command=lambda a=elem_addr, t=ftype, v=var: self._write_array_element_bool(a, t, v))
                save_btn.grid(row=row_idx, column=col, sticky="w", padx=5, pady=1)
                combo.bind('<<ComboboxSelected>>', lambda e, a=elem_addr, t=ftype, v=var: self._write_array_element_bool(a, t, v))
        else:
            var = tk.StringVar(value=str(value) if not is_err else value)
            entry = ttk.Entry(parent, textvariable=var, width=30, state='readonly' if is_err else 'normal')
            entry.grid(row=row_idx, column=col, sticky="w", padx=5, pady=1)
            col += 1
            if not is_err and elem_addr is not None:
                save_btn = ttk.Button(parent, text="Save", width=6,
                                      command=lambda a=elem_addr, t=ftype, v=var: self._write_array_element(a, t, v))
                save_btn.grid(row=row_idx, column=col, sticky="w", padx=5, pady=1)
                entry.bind('<Return>', lambda e, a=elem_addr, t=ftype, v=var: self._write_array_element(a, t, v))
        return row_idx + 1

    def _create_array_container(self, parent, obj_addr, fdef, value_list, ftype, path, row_idx, col_offset=0, index=None):
        """创建可展开的数组容器，全部使用 pack 布局避免 grid 行冲突"""
        if not isinstance(value_list, list):
            return self._create_scalar_editor(parent, obj_addr, fdef, value_list, ftype, path, row_idx, col_offset, index)

        # 判断内部类型
        inner_type = None
        if len(value_list) > 0 and not isinstance(value_list[0], str):
            kind, inner = parse_type(ftype)
            if kind == 'array':
                inner_type = inner
            elif kind == 'vector':
                inner_type = inner
            else:
                inner_type = ftype
        else:
            inner_type = "string"

        # 外层容器：使用 pack 在父级中占据一行
        container = ttk.Frame(parent)
        container.pack(fill=tk.X, pady=1, anchor='w')

        # 预览行（横向排列）
        preview_frame = ttk.Frame(container)
        preview_frame.pack(fill=tk.X)

        # 缩进和序号
        left_part = ttk.Frame(preview_frame)
        left_part.pack(side=tk.LEFT)

        if col_offset > 0:
            ttk.Label(left_part, text="    " * col_offset).pack(side=tk.LEFT)
        if index is not None:
            ttk.Label(left_part, text=f"[{index}]", foreground="gray").pack(side=tk.LEFT, padx=2)

        # 预览文本
        preview_text = f"元素数量: {len(value_list)}"
        preview_label = ttk.Label(preview_frame, text=preview_text, foreground="blue")
        preview_label.pack(side=tk.LEFT, padx=5)

        # 展开按钮
        expand_btn = ttk.Button(preview_frame, text="▶ 展开", width=6)
        expand_btn.pack(side=tk.LEFT, padx=5)

        # 编辑器框架（默认隐藏）
        editor_frame = ttk.Frame(container)
        # 不 pack，初始隐藏

        # 存储数据
        container.preview_frame = preview_frame
        container.editor_frame = editor_frame
        container.expanded = False
        container.expand_btn = expand_btn
        container.obj_addr = obj_addr
        container.fdef = fdef
        container.value_list = value_list
        container.inner_type = inner_type
        container.path = path
        container.col_offset = col_offset

        def toggle():
            if container.expanded:
                editor_frame.pack_forget()
                expand_btn.config(text="▶ 展开")
                container.expanded = False
            else:
                # 清空并重新创建子项
                for w in editor_frame.winfo_children():
                    w.destroy()
                # 使用 grid 在 editor_frame 内部布局，行号从0开始
                sub_row = 0
                for idx, item in enumerate(value_list):
                    sub_path = path + [idx]
                    sub_ftype = inner_type
                    # 递归创建子项
                    sub_row = self._create_editor_for_value(
                        editor_frame, obj_addr, fdef, item, sub_ftype, sub_path, sub_row, col_offset + 1, idx
                    )
                # 显示 editor_frame
                editor_frame.pack(fill=tk.X, pady=2, padx=20)
                expand_btn.config(text="▼ 收起")
                container.expanded = True
        expand_btn.config(command=toggle)

        return row_idx + 1  

    # ---------- 字段显示（主入口） ----------
    def display_fields(self, addr, obj_id, fields):
        self.clear_edit()
        main_frame = ttk.Frame(self.edit_frame)
        main_frame.pack(fill=tk.X, expand=False)

        info = f"地址: 0x{addr:08X}"
        if self.id_parsed and obj_id is not None:
            info += f"  ID:{obj_id}"
        ttk.Label(main_frame, text=info, foreground="darkblue",
                  font=("TkDefaultFont",9,"bold")).grid(row=0, column=0, columnspan=3, sticky="w", padx=5, pady=(5,2))

        row = 1
        if self.id_parsed and obj_id is not None and self.id_name_map is not None:
            ttk.Label(main_frame, text="自定义名称").grid(row=row, column=0, sticky="w", padx=5, pady=2)
            name_var = tk.StringVar(value=self.id_name_map.get(obj_id, ''))
            entry = ttk.Entry(main_frame, textvariable=name_var, width=25)
            entry.grid(row=row, column=1, sticky="w", padx=5, pady=2)
            entry.bind('<Return>', lambda e, oid=obj_id, v=name_var: self._save_name(oid, v))
            ttk.Button(main_frame, text="Save", width=6,
                       command=lambda oid=obj_id, var=name_var: self._save_name(oid, var)
                       ).grid(row=row, column=2, sticky="w", padx=5, pady=2)
            row += 1

        for fdef in self.fields_def:
            if fdef.get("hidden", False): continue
            name = fdef["name"]
            ftype = fdef["type"]
            disp = get_display_label(fdef)
            offset = hex_to_int(fdef["offset"])
            label_text = f"{disp} ({ftype}) (0x{offset:02X})"

            lbl_frame = ttk.Frame(main_frame)
            lbl_frame.grid(row=row, column=0, sticky="w", padx=5, pady=2)
            lbl = ttk.Label(lbl_frame, text=label_text)
            lbl.pack(side=tk.LEFT)
            ttk.Button(lbl_frame, text="✎", width=3,
                       command=lambda n=name: self._rename_field_display(n)).pack(side=tk.LEFT, padx=2)
            ttk.Button(lbl_frame, text="✕", width=3,
                       command=lambda n=name: self._hide_field(n)).pack(side=tk.LEFT, padx=2)
            self.field_labels[name] = lbl

            val = fields.get(name, "ERR")
            value_frame = ttk.Frame(main_frame)
            value_frame.grid(row=row, column=1, columnspan=2, sticky="w", padx=5, pady=2)

            if isinstance(val, list):
                self._create_array_container(value_frame, addr, fdef, val, ftype, [], 0)
            else:
                self._create_scalar_editor_for_field(value_frame, addr, fdef, val, ftype)

            row += 1

        main_frame.grid_columnconfigure(1, weight=1)

    def _create_scalar_editor_for_field(self, parent, addr, fdef, value, ftype):
        is_err = isinstance(value, str) and value.startswith("ERR")
        if ftype == "bool":
            var = tk.StringVar(value="True" if value else "False")
            combo = ttk.Combobox(parent, textvariable=var, values=("True","False"),
                                 width=10, state='readonly' if is_err else 'normal')
            combo.pack(side=tk.LEFT, padx=5)
            if not is_err:
                save_btn = ttk.Button(parent, text="Save", width=6,
                                      command=lambda a=addr, f=fdef, v=var: self._write_bool_field(a, f, v))
                save_btn.pack(side=tk.LEFT, padx=5)
                combo.bind('<<ComboboxSelected>>', lambda e, a=addr, f=fdef, v=var: self._write_bool_field(a, f, v))
        elif ftype == "string":
            var = tk.StringVar(value=str(value) if not is_err else value)
            entry = ttk.Entry(parent, textvariable=var, width=30, state='readonly' if is_err else 'normal')
            entry.pack(side=tk.LEFT, padx=5)
            if not is_err:
                save_btn = ttk.Button(parent, text="Save", width=6,
                                      command=lambda a=addr, f=fdef, v=var: self._write_field(a, f, v))
                save_btn.pack(side=tk.LEFT, padx=5)
                entry.bind('<Return>', lambda e, a=addr, f=fdef, v=var: self._write_field(a, f, v))
        else:
            var = tk.StringVar(value=str(value) if not is_err else value)
            entry = ttk.Entry(parent, textvariable=var, width=18, state='readonly' if is_err else 'normal')
            entry.pack(side=tk.LEFT, padx=5)
            if not is_err:
                save_btn = ttk.Button(parent, text="Save", width=6,
                                      command=lambda a=addr, f=fdef, v=var: self._write_field(a, f, v))
                save_btn.pack(side=tk.LEFT, padx=5)
                entry.bind('<Return>', lambda e, a=addr, f=fdef, v=var: self._write_field(a, f, v))

    # ---------- 其余方法 ----------
    def clear_edit(self):
        for w in self.edit_frame.winfo_children():
            w.destroy()
        self.field_labels.clear()

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
            self.field_labels[field_name].config(text=f"{new_disp} ({f['type']}) (0x{off:02X})")
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
            if self.id_parsed:
                obj_id = self._read_id_value(self.current_edit_addr)
            self.display_fields(self.current_edit_addr, obj_id, fields)

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
            if self.id_parsed:
                obj_id = self._read_id_value(self.current_edit_addr)
            self.display_fields(self.current_edit_addr, obj_id, fields)
        self.status.config(text="✔ 所有字段已设为显示", foreground="green")

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
        return self.id_parsed[0] if self.id_parsed else None

    # ---------- 数据刷新 ----------
    def refresh_data(self):
        if not self.pm: return
        try:
            addrs = self._traverse_addresses()
            cat_field = self._get_category_field()
            self.obj_list = []
            for addr in addrs:
                cv = None
                oid = None
                if cat_field:
                    for fdef in self.fields_def:
                        try:
                            if fdef["name"] == cat_field:
                                cv = self._read_field(addr, fdef)
                                break
                        except:
                            pass
                if self.id_parsed:
                    oid = self._read_id_value(addr)
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
            if self.id_parsed and iid is not None:
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

    def destroy(self):
        self.save_names()
        for w in self.parent.winfo_children():
            w.destroy()

# ---------- 应用主窗口 ----------
class App:
    def __init__(self, root):
        self.root = root
        self.root.title("通用内存编辑器 v5.8")
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