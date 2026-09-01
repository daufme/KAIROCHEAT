# -*- coding: utf-8 -*-
"""
通用内存编辑器 v5.28
功能：通过 JSON 配置定义数据结构，从目标进程读取/写入内存，支持数组展开、XType、SecureType、ExType 结构、远程函数调用。
修复：替换不存在的 pymem 方法 read_byte/write_byte 为 read_bytes/write_bytes，解决 'Pymem' object has no attribute 'read_byte' 错误。
新增：自定义类型数组（如 List<Player>）自动加载 Player.json 字段定义，支持展开编辑（包括递归编辑）。
依赖：
  - pymem：用于进程内存操作
  - ctypes：用于 Windows API 调用（CreateRemoteThread 等）
说明：
  - 支持字段级函数调用，参数可引用当前对象地址（this）、字段值（field:字段名）、字段地址（addr:字段名）
  - 支持 __cdecl / __stdcall / __thiscall 三种调用约定，__cdecl 调用后自动清理栈
  - 数组/Vector/List 容器可展开编辑，支持为数组元素配置索引含义标签（index_labels）
  - 字段显示名可重命名，字段可隐藏/显示
  - 每个字段可定义一个函数，Call 按钮显示其 description
  - XString 数组按引用（指针）处理，支持读取字符串内容
  - 新增导出功能：将所有对象（未隐藏字段）导出为 JSON 文件
  - 修改写入机制：所有写入操作均基于当前选中对象基址重新计算地址（支持不可变对象模式）
  - 新增 SecureType 和 ExType 全系列支持（32位），暂不支持字符串类型
  - 自定义类型数组自动加载同目录下 Custom.json 字段定义，支持可编辑展开（v5.25），本版修复 pymem 方法兼容性（v5.28）
"""

import tkinter as tk
from tkinter import ttk, simpledialog, messagebox, filedialog
import struct
import json
import os
import sys
import re
import threading
import ctypes

try:
    import pymem
    import pymem.process
except ImportError:
    pymem = None

# ========== 辅助函数 ==========
def load_json(path):
    """加载 JSON 文件，自动尝试多种编码"""
    encodings = ['utf-8-sig', 'utf-8', 'gbk', 'gb18030', 'latin-1']
    for enc in encodings:
        try:
            with open(path, 'r', encoding=enc) as f:
                return json.load(f)
        except (UnicodeDecodeError, json.JSONDecodeError):
            continue
    with open(path, 'rb') as f:
        raw = f.read()
        try:
            text = raw.decode('utf-8', errors='ignore')
            return json.loads(text)
        except:
            raise ValueError(f"无法解析 JSON 文件: {path}")

def save_json(path, data):
    """以 UTF-8 带 BOM 格式保存 JSON 文件"""
    with open(path, 'w', encoding='utf-8-sig') as f:
        json.dump(data, f, indent=2, ensure_ascii=False)

def hex_to_int(val):
    """将十六进制字符串或数字转为整数"""
    if isinstance(val, str):
        if val.lower().startswith('0x'):
            return int(val, 16)
        return int(val)
    return int(val)

def format_offset_display(offset_list):
    """将整数偏移列表格式化为显示字符串（逗号分隔）"""
    if not offset_list:
        return "0"
    return ", ".join(f"0x{off:02X}" for off in offset_list)

def get_display_label(fdef, offset_chain=None):
    """获取字段的显示标签（优先 display，其次 name，最后偏移）"""
    display = fdef.get("display")
    if display:
        return display
    name = fdef.get("name")
    if name:
        return name
    if offset_chain is not None:
        return format_offset_display(offset_chain)
    return "???"

TYPE_INFO = {
    "int":   (4, "i"),
    "sbyte": (1, "b"),
    "byte":  (1, "B"),
    "long":  (8, "q"),
    "float": (4, "f"),
    "bool":  (1, "B"),
}

# ========== XType 偏移（仅保留 bitmask, original, value）==========
X_TYPE_OFFSETS = {
    "XInt":    {"bitmask": 0, "original": 4, "value": 8},
    "XLong":   {"bitmask": 0, "original": 8, "value": 16},
    "XByte":   {"bitmask": 0, "original": 4, "value": 5},
    "XShort":  {"bitmask": 0, "original": 4, "value": 6},
    "XFloat":  {"bitmask": 0, "original": 4, "value": 8},
    "XDouble": {"bitmask": 0, "original": 8, "value": 16},
    "XString": {"bitmask": 8, "original": 12, "value": 16},  # 保留但暂不支持写入
}

X_TYPE_SIZES = {
    "XInt":    16,
    "XLong":   32,
    "XByte":   12,
    "XShort":  12,
    "XFloat":  16,
    "XDouble": 32,
    "XString": 32,
}

# ========== SecureType 定义（值类型结构体，32位对齐）==========
SECURE_TYPE_INFO = {
    "SecureByte":   {"bitmask": 0x08, "original": 0x10, "value": 0x18, "orig_size": 1, "val_size": 1, "fmt": "B"},
    "SecureShort":  {"bitmask": 0x08, "original": 0x10, "value": 0x18, "orig_size": 2, "val_size": 2, "fmt": "H"},
    "SecureInt":    {"bitmask": 0x08, "original": 0x10, "value": 0x18, "orig_size": 4, "val_size": 4, "fmt": "I"},
    "SecureLong":   {"bitmask": 0x08, "original": 0x10, "value": 0x18, "orig_size": 8, "val_size": 8, "fmt": "Q"},
    "SecureFloat":  {"bitmask": 0x08, "original": 0x10, "value": 0x18, "orig_size": 4, "val_size": 4, "fmt": "f"},
    "SecureDouble": {"bitmask": 0x08, "original": 0x10, "value": 0x18, "orig_size": 8, "val_size": 8, "fmt": "d"},
}

# Secure 结构体总大小（用于可能的数组存储结构体，但本实现数组存指针，此值仅作备用）
SECURE_TYPE_SIZES = {
    "SecureByte":   0x1C,
    "SecureShort":  0x1C,
    "SecureInt":    0x20,
    "SecureLong":   0x28,
    "SecureFloat":  0x20,
    "SecureDouble": 0x28,
}

# ========== ExType 定义（引用类型，存储指向 Secure 对象的指针）==========
EXT_TYPE_OFFSETS = {
    "ExByte":   {"secure_ptr_offset": 0x08, "secure_type": "SecureByte"},
    "ExShort":  {"secure_ptr_offset": 0x08, "secure_type": "SecureShort"},
    "ExInt":    {"secure_ptr_offset": 0x08, "secure_type": "SecureInt"},
    "ExLong":   {"secure_ptr_offset": 0x08, "secure_type": "SecureLong"},
    "ExFloat":  {"secure_ptr_offset": 0x08, "secure_type": "SecureFloat"},
    "ExDouble": {"secure_ptr_offset": 0x08, "secure_type": "SecureDouble"},
}

# ================================================================

def get_type_size(ftype):
    if ftype in X_TYPE_SIZES:
        return X_TYPE_SIZES[ftype]
    if ftype in SECURE_TYPE_SIZES:
        return SECURE_TYPE_SIZES[ftype]
    if ftype in TYPE_INFO:
        return TYPE_INFO[ftype][0]
    if ftype == "string":
        return 4
    return 4  # 自定义类型按指针大小

def is_scalar_type(ftype):
    return (ftype in TYPE_INFO or ftype == "string" or ftype.startswith("X") or
            ftype.startswith("Secure") or ftype.startswith("Ex"))

def get_scalar_size(ftype):
    if ftype == "string":
        return 4
    if ftype in TYPE_INFO:
        return TYPE_INFO[ftype][0]
    if ftype in X_TYPE_SIZES:
        return X_TYPE_SIZES[ftype]
    if ftype in SECURE_TYPE_SIZES:
        return SECURE_TYPE_SIZES[ftype]
    return 4  # 自定义类型按指针大小

def get_scalar_fmt(ftype):
    if ftype == "string":
        return "I"
    return TYPE_INFO[ftype][1]

def parse_type(ftype):
    """解析类型，返回 (kind, inner)，kind 可能为 'scalar','array','vector','list','xsecure','secure','ext','custom'"""
    if ftype in X_TYPE_OFFSETS:
        return ('xsecure', ftype)
    if ftype in SECURE_TYPE_INFO:
        return ('secure', ftype)
    if ftype in EXT_TYPE_OFFSETS:
        return ('ext', ftype)
    vec_match = re.match(r'^Vector<(.+)>$', ftype)
    if vec_match:
        return ('vector', vec_match.group(1))
    list_match = re.match(r'^List<(.+)>$', ftype)
    if list_match:
        return ('list', list_match.group(1))
    if ftype.endswith('[]'):
        return ('array', ftype[:-2])
    if ftype in TYPE_INFO or ftype == "string":
        return ('scalar', ftype)
    # 未知类型，视为自定义类型
    return ('custom', ftype)

# ========== 主类 ==========
class MemoryEditor:
    """内存编辑器主类，管理字段、读写内存、UI 交互和远程函数调用"""

    SHOW_EDIT_BUTTONS = True

    def __init__(self, parent, table_name, table_config_path):
        self.parent = parent
        self.table_name = table_name
        self.table_config_path = table_config_path
        self.table_cfg = load_json(table_config_path)
        base_dir = os.path.dirname(table_config_path)

        self.fields_dir = os.path.join(base_dir, "..", "fields")
        self.fields_file = os.path.join(self.fields_dir, self.table_cfg["fields_file"])
        raw_fields = load_json(self.fields_file)["fields"]
        self.fields_def = []
        self.offset_chains = []
        for f in raw_fields:
            raw_off = f.get("offset")
            ftype = f.get("type")
            if raw_off is None or ftype is None:
                continue
            name = f.get("name", "")
            display = f.get("display", "")
            hidden = f.get("hidden", False)
            func_def = f.get("function")
            index_labels = f.get("index_labels", [])

            if isinstance(raw_off, str):
                chain = [hex_to_int(raw_off)]
            elif isinstance(raw_off, list):
                chain = [hex_to_int(x) for x in raw_off]
            else:
                chain = [hex_to_int(raw_off)]

            self.fields_def.append({
                "offset": raw_off,
                "type": ftype,
                "name": name,
                "display": display,
                "hidden": hidden,
                "function": func_def,
                "index_labels": index_labels
            })
            self.offset_chains.append(chain)

        self.id_field = self.table_cfg.get("id_field")
        self.id_parsed = self._parse_id_expression()

        self.pm = None
        self.module_base = 0
        self.obj_list = []
        self.current_category_idx = None
        self.current_item_idx = None
        self.current_edit_addr = None
        self.field_labels = {}
        self.custom_type_cache = {}  # 缓存自定义类型定义

        self.create_widgets()
        self.connect_to_process()

    # ---------- 自定义类型加载 ----------
    def _load_custom_type_def(self, type_name):
        """从 fields 目录加载自定义类型定义，返回解析后的字段列表（每个元素包含 offset_chain, type, name, display, hidden）"""
        if type_name in self.custom_type_cache:
            return self.custom_type_cache[type_name]

        file_path = os.path.join(self.fields_dir, type_name + ".json")
        if not os.path.exists(file_path):
            raise ValueError(f"找不到自定义类型定义文件: {file_path}")
        raw_fields = load_json(file_path).get("fields", [])
        parsed = []
        for f in raw_fields:
            raw_off = f.get("offset")
            ftype = f.get("type")
            if raw_off is None or ftype is None:
                continue
            if isinstance(raw_off, str):
                chain = [hex_to_int(raw_off)]
            elif isinstance(raw_off, list):
                chain = [hex_to_int(x) for x in raw_off]
            else:
                chain = [hex_to_int(raw_off)]
            parsed.append({
                "offset_chain": chain,
                "type": ftype,
                "name": f.get("name", ""),
                "display": f.get("display", ""),
                "hidden": f.get("hidden", False),
                "index_labels": f.get("index_labels", [])
            })
        self.custom_type_cache[type_name] = parsed
        return parsed

    def _read_custom_object(self, addr, type_name):
        """读取自定义对象，返回字典（字段名 -> 值），忽略 hidden 字段"""
        if addr == 0:
            return {}
        fields = self._load_custom_type_def(type_name)  # 可能抛出异常
        data = {}
        for fdef in fields:
            try:
                final_addr = self._resolve_offset_chain(addr, fdef["offset_chain"])
                value = self._read_value_at(final_addr, fdef["type"])
                data[fdef["name"]] = value
            except Exception as e:
                data[fdef["name"]] = f"ERR:{e}"
        return data

    def _get_custom_display_name(self, type_name, data_dict, index):
        """根据自定义对象数据生成显示名（用于数组展开时的标签）"""
        # 尝试常见字段：name, display_name, id
        for key in ("name", "display_name", "id"):
            if key in data_dict and isinstance(data_dict[key], (str, int, float)):
                return str(data_dict[key])
        # 如果第一个字段是字符串类型，使用其值
        try:
            fields = self._load_custom_type_def(type_name)
            for fdef in fields:
                if fdef["type"] == "string" and fdef["name"] in data_dict:
                    return str(data_dict[fdef["name"]])
        except:
            pass
        # 回退到类型名+索引
        return f"{type_name} {index}"

    def _parse_id_expression(self):
        """解析 id_field 表达式，支持 field[index]"""
        if not self.id_field:
            return None
        m = re.match(r'^(\w+)\[(\d+)\]$', self.id_field)
        if m:
            return (m.group(1), int(m.group(2)))
        return (self.id_field, None)

    def _read_id_value(self, addr):
        """读取对象 ID 字段值"""
        if not self.id_parsed:
            return None
        field_name, index = self.id_parsed
        for i, fdef in enumerate(self.fields_def):
            if fdef["name"] == field_name:
                val = self._read_field(addr, i)
                if index is not None:
                    return val[index] if isinstance(val, list) and len(val) > index else None
                return val
        return None

    def create_widgets(self):
        """创建 UI 控件，包含导出 JSON 按钮"""
        top = ttk.Frame(self.parent)
        top.pack(fill=tk.X, padx=5, pady=5)
        ttk.Button(top, text="Refresh", command=self.refresh_data).pack(side=tk.LEFT, padx=5)
        if self.SHOW_EDIT_BUTTONS:
            ttk.Button(top, text="显示所有隐藏字段", command=self.show_all_hidden_fields).pack(side=tk.LEFT, padx=5)
        ttk.Button(top, text="导出JSON", command=self.export_json).pack(side=tk.LEFT, padx=5)
        self.status = ttk.Label(top, text="未连接", foreground="red")
        self.status.pack(side=tk.RIGHT, padx=5)

        paned = ttk.PanedWindow(self.parent, orient=tk.HORIZONTAL)
        paned.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        left = ttk.LabelFrame(paned, text="Categories", width=150)
        paned.add(left, weight=0)
        self.cat_listbox = tk.Listbox(left, width=20)
        self.cat_listbox.pack(fill=tk.BOTH, expand=True, padx=2, pady=2)
        self.cat_listbox.bind('<<ListboxSelect>>', self.on_cat_select)

        mid = ttk.LabelFrame(paned, text="List", width=200)
        paned.add(mid, weight=0)
        self.item_listbox = tk.Listbox(mid, width=30)
        self.item_listbox.pack(fill=tk.BOTH, expand=True, padx=2, pady=2)
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
        """连接到目标进程"""
        try:
            self.pm = pymem.Pymem(self.table_cfg["process"])
            self.module_base = pymem.process.module_from_name(
                self.pm.process_handle, self.table_cfg["module"]).lpBaseOfDll
            self.status.config(text=f"已连接 Base:0x{self.module_base:08X}", foreground="green")
            self.refresh_data()
        except Exception as e:
            self.status.config(text=f"连接失败: {e}", foreground="red")

    def _read_pointer_chain(self):
        """读取指针链，返回最终地址"""
        chain = self.table_cfg["pointer_chain"]
        base = self.module_base + hex_to_int(chain[0])
        ptr = self.pm.read_uint(base)
        if ptr == 0: return None
        for off in chain[1:]:
            ptr = self.pm.read_uint(ptr + hex_to_int(off))
            if ptr == 0: return None
        return ptr

    def _traverse_addresses(self):
        """遍历对象列表，返回地址数组"""
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

    def _resolve_offset_chain(self, base_addr, offset_chain):
        """根据偏移链解引用，返回最终数据地址"""
        if not offset_chain:
            return base_addr
        addr = base_addr
        for i, off in enumerate(offset_chain):
            addr = addr + off
            if i != len(offset_chain) - 1:
                addr = self.pm.read_uint(addr)
                if addr == 0:
                    raise ValueError("指针链中断")
        return addr

    def _get_field_address(self, obj_addr, fdef_idx):
        """获取字段的数据地址"""
        return self._resolve_offset_chain(obj_addr, self.offset_chains[fdef_idx])

    def _read_field(self, addr, fdef_idx):
        """读取字段值"""
        field_addr = self._get_field_address(addr, fdef_idx)
        return self._read_value_at(field_addr, self.fields_def[fdef_idx]["type"])

    def _write_field_value(self, addr, fdef_idx, value):
        """写入字段值"""
        field_addr = self._get_field_address(addr, fdef_idx)
        self._write_value_at(field_addr, self.fields_def[fdef_idx]["type"], value)

    def _read_scalar(self, addr, ftype):
        """读取标量类型（非字符串）"""
        if ftype == "string":
            return "<错误: 请使用 _read_string>"
        size, fmt = TYPE_INFO[ftype]
        raw = struct.unpack(fmt, self.pm.read_bytes(addr, size))[0]
        return bool(raw) if ftype == "bool" else raw

    def _write_scalar(self, addr, ftype, value):
        """写入标量类型（非字符串）"""
        size, fmt = TYPE_INFO[ftype]
        val = 1 if (ftype == "bool" and value) else value
        self.pm.write_bytes(addr, struct.pack(fmt, val), size)

    def _read_string(self, str_ptr):
        """读取字符串对象"""
        if str_ptr == 0: return ""
        try:
            length = self.pm.read_int(str_ptr + 8)
            if length < 0 or length > 10000: return "<长度异常>"
            return self.pm.read_bytes(str_ptr + 12, length * 2).decode('utf-16-le', errors='replace')
        except Exception as e:
            return f"<string读失败: {e}>"

    def _write_string_object(self, obj_ptr, new_str):
        """写入字符串对象（不改变长度）"""
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

    # ---------- XType 读写 ----------
    def _read_xsecure(self, addr, xtype):
        """读取 XType 结构的 original 字段"""
        offsets = X_TYPE_OFFSETS[xtype]
        if xtype == "XInt":
            return self.pm.read_int(addr + offsets["original"])
        elif xtype == "XLong":
            return self.pm.read_longlong(addr + offsets["original"])
        elif xtype == "XByte":
            return self.pm.read_bytes(addr + offsets["original"], 1)[0]  # 修复：使用 read_bytes
        elif xtype == "XShort":
            return self.pm.read_short(addr + offsets["original"])
        elif xtype == "XFloat":
            return struct.unpack('f', self.pm.read_bytes(addr + offsets["original"], 4))[0]
        elif xtype == "XDouble":
            return struct.unpack('d', self.pm.read_bytes(addr + offsets["original"], 8))[0]
        elif xtype == "XString":
            str_ptr = self.pm.read_uint(addr + offsets["original"])
            return self._read_string(str_ptr)
        else:
            raise ValueError(f"未知 XType: {xtype}")

    def _write_xsecure(self, addr, xtype, value):
        """写入 XType 结构，更新 original 和 value（加密）"""
        offsets = X_TYPE_OFFSETS[xtype]
        if xtype == "XInt":
            bitmask = self.pm.read_int(addr + offsets["bitmask"])
            self.pm.write_int(addr + offsets["original"], value)
            self.pm.write_int(addr + offsets["value"], value ^ bitmask)
        elif xtype == "XLong":
            bitmask = self.pm.read_longlong(addr + offsets["bitmask"])
            self.pm.write_longlong(addr + offsets["original"], value)
            self.pm.write_longlong(addr + offsets["value"], value ^ bitmask)
        elif xtype == "XByte":
            bitmask = self.pm.read_bytes(addr + offsets["bitmask"], 1)[0]  # 修复
            val = value & 0xFF
            self.pm.write_bytes(addr + offsets["original"], bytes([val]), 1)  # 修复
            self.pm.write_bytes(addr + offsets["value"], bytes([(val ^ (bitmask & 0xFF)) & 0xFF]), 1)  # 修复
        elif xtype == "XShort":
            bitmask = self.pm.read_short(addr + offsets["bitmask"])
            val = value & 0xFFFF
            self.pm.write_short(addr + offsets["original"], val)
            self.pm.write_short(addr + offsets["value"], (val ^ (bitmask & 0xFFFF)) & 0xFFFF)
        elif xtype == "XFloat":
            bitmask = self.pm.read_int(addr + offsets["bitmask"])
            orig_bytes = struct.pack('f', value)
            self.pm.write_bytes(addr + offsets["original"], orig_bytes, 4)
            orig_int = struct.unpack('i', orig_bytes)[0]
            self.pm.write_int(addr + offsets["value"], orig_int ^ bitmask)
        elif xtype == "XDouble":
            bitmask = self.pm.read_longlong(addr + offsets["bitmask"])
            orig_bytes = struct.pack('d', value)
            self.pm.write_bytes(addr + offsets["original"], orig_bytes, 8)
            orig_int = struct.unpack('q', orig_bytes)[0]
            self.pm.write_longlong(addr + offsets["value"], orig_int ^ bitmask)
        elif xtype == "XString":
            raise NotImplementedError("XString 写入暂不支持")
        else:
            raise ValueError(f"未知 XType: {xtype}")

    # ---------- SecureType 读写 ----------
    def _read_secure(self, addr, stype):
        """读取 SecureType 值类型结构的 original 字段（addr 为 Secure 结构体起始地址）"""
        info = SECURE_TYPE_INFO[stype]
        orig_offset = info["original"]
        orig_size = info["orig_size"]
        if orig_size == 1:
            return self.pm.read_bytes(addr + orig_offset, 1)[0]  # 修复
        elif orig_size == 2:
            return self.pm.read_short(addr + orig_offset)
        elif orig_size == 4:
            if stype == "SecureFloat":
                return struct.unpack('f', self.pm.read_bytes(addr + orig_offset, 4))[0]
            else:
                return self.pm.read_int(addr + orig_offset)
        elif orig_size == 8:
            if stype == "SecureDouble":
                return struct.unpack('d', self.pm.read_bytes(addr + orig_offset, 8))[0]
            else:
                return self.pm.read_longlong(addr + orig_offset)
        else:
            raise ValueError(f"不支持的 original 大小: {orig_size}")

    def _write_secure(self, addr, stype, value):
        """写入 SecureType 结构，更新 original 和 value（加密）（addr 为 Secure 结构体起始地址）"""
        info = SECURE_TYPE_INFO[stype]
        bitmask_offset = info["bitmask"]
        orig_offset = info["original"]
        val_offset = info["value"]
        orig_size = info["orig_size"]
        val_size = info["val_size"]

        # 读取 bitmask（修复 read_byte）
        if stype == "SecureByte":
            bitmask = self.pm.read_bytes(addr + bitmask_offset, 1)[0]
        elif stype == "SecureShort":
            bitmask = self.pm.read_short(addr + bitmask_offset)
        elif stype in ("SecureInt", "SecureFloat"):
            bitmask = self.pm.read_int(addr + bitmask_offset)
        elif stype in ("SecureLong", "SecureDouble"):
            bitmask = self.pm.read_longlong(addr + bitmask_offset)
        else:
            raise ValueError(f"未知 Secure 类型: {stype}")

        # 写入 original
        if orig_size == 1:
            val = value & 0xFF
            self.pm.write_bytes(addr + orig_offset, bytes([val]), 1)  # 修复
        elif orig_size == 2:
            val = value & 0xFFFF
            self.pm.write_short(addr + orig_offset, val)
        elif orig_size == 4:
            if stype == "SecureFloat":
                self.pm.write_bytes(addr + orig_offset, struct.pack('f', value), 4)
            else:
                self.pm.write_int(addr + orig_offset, value)
        elif orig_size == 8:
            if stype == "SecureDouble":
                self.pm.write_bytes(addr + orig_offset, struct.pack('d', value), 8)
            else:
                self.pm.write_longlong(addr + orig_offset, value)
        else:
            raise ValueError(f"不支持的 original 大小: {orig_size}")

        # 计算并写入加密 value
        if stype == "SecureByte":
            encrypted = (value & 0xFF) ^ (bitmask & 0xFF)
            self.pm.write_bytes(addr + val_offset, bytes([encrypted & 0xFF]), 1)  # 修复
        elif stype == "SecureShort":
            encrypted = (value & 0xFFFF) ^ (bitmask & 0xFFFF)
            self.pm.write_short(addr + val_offset, encrypted & 0xFFFF)
        elif stype == "SecureInt":
            encrypted = value ^ bitmask
            self.pm.write_int(addr + val_offset, encrypted)
        elif stype == "SecureFloat":
            orig_int = struct.unpack('I', struct.pack('f', value))[0]
            encrypted = orig_int ^ bitmask
            self.pm.write_int(addr + val_offset, encrypted)
        elif stype == "SecureLong":
            encrypted = value ^ bitmask
            self.pm.write_longlong(addr + val_offset, encrypted)
        elif stype == "SecureDouble":
            orig_int = struct.unpack('Q', struct.pack('d', value))[0]
            encrypted = orig_int ^ bitmask
            self.pm.write_longlong(addr + val_offset, encrypted)
        else:
            raise ValueError(f"未知 Secure 类型: {stype}")

    # ---------- ExType 读写 ----------
    def _read_ext(self, addr, etype):
        """读取 ExType 引用类型，解引用得到 Secure 对象的 original"""
        info = EXT_TYPE_OFFSETS[etype]
        ex_ptr = self.pm.read_uint(addr)
        if ex_ptr == 0:
            return 0
        sec_ptr = self.pm.read_uint(ex_ptr + info["secure_ptr_offset"])
        if sec_ptr == 0:
            return 0
        return self._read_secure(sec_ptr, info["secure_type"])

    def _write_ext(self, addr, etype, value):
        """写入 ExType 引用类型，解引用后写入 Secure 对象"""
        info = EXT_TYPE_OFFSETS[etype]
        ex_ptr = self.pm.read_uint(addr)
        if ex_ptr == 0:
            raise ValueError(f"{etype} 对象指针为空")
        sec_ptr = self.pm.read_uint(ex_ptr + info["secure_ptr_offset"])
        if sec_ptr == 0:
            raise ValueError("Secure 对象指针为空")
        self._write_secure(sec_ptr, info["secure_type"], value)

    # ---------- 容器读写 ----------
    def _read_list(self, addr, inner_type):
        """读取 List<T> 容器"""
        list_ptr = self.pm.read_uint(addr)
        if list_ptr == 0:
            return []
        array_ptr = self.pm.read_uint(list_ptr + 0x8)
        if array_ptr == 0:
            return []
        return self._read_array_data(array_ptr, inner_type)

    def _read_array_data(self, array_base, inner_type):
        """从数组对象读取数据，元素大小根据类型确定（Secure/Ex/自定义为指针，XType 为结构体）"""
        try:
            length = self.pm.read_int(array_base + 0x0C)
            if length < 0 or length > 100000:
                return ["<len err>"]
            kind, _ = parse_type(inner_type)
            if kind in ('secure', 'ext', 'custom') or inner_type == "string" or inner_type == "XString":
                elem_size = 4
            elif kind == 'xsecure':
                elem_size = X_TYPE_SIZES.get(inner_type, 4)
            else:
                elem_size = get_scalar_size(inner_type)
            result = []
            for i in range(length):
                elem_addr = array_base + 0x10 + i * elem_size
                if kind == 'custom':
                    ptr = self.pm.read_uint(elem_addr)
                    result.append(self._read_custom_object(ptr, inner_type))
                else:
                    result.append(self._read_value_at(elem_addr, inner_type))
            return result
        except Exception as e:
            return [f"<err: {e}>"]

    def _read_array(self, addr, inner_type):
        """读取普通数组 Type[]"""
        arr_ptr = self.pm.read_uint(addr)
        if arr_ptr == 0:
            return []
        return self._read_array_data(arr_ptr, inner_type)

    def _read_vector(self, addr, inner_type):
        """读取 Vector<T> 容器"""
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
        """根据类型读取内存值（addr 为字段数据地址，即存储实际数据的位置）"""
        kind, inner = parse_type(ftype)
        if kind == 'scalar':
            if inner == "string":
                return self._read_string(self.pm.read_uint(addr))
            return self._read_scalar(addr, inner)
        elif kind == 'array':
            return self._read_array(addr, inner)
        elif kind == 'vector':
            return self._read_vector(addr, inner)
        elif kind == 'list':
            return self._read_list(addr, inner)
        elif kind == 'xsecure':
            return self._read_xsecure(addr, inner)
        elif kind == 'secure':
            sec_ptr = self.pm.read_uint(addr)
            if sec_ptr == 0:
                return 0
            return self._read_secure(sec_ptr, inner)
        elif kind == 'ext':
            return self._read_ext(addr, inner)
        elif kind == 'custom':
            obj_ptr = self.pm.read_uint(addr)
            if obj_ptr == 0:
                return {}
            return self._read_custom_object(obj_ptr, inner)
        else:
            return f"<未知类型: {ftype}>"

    def _write_value_at(self, addr, ftype, value):
        """根据类型写入值（addr 为字段数据地址）"""
        kind, inner = parse_type(ftype)
        if kind == 'scalar':
            if inner == "string":
                str_ptr = self.pm.read_uint(addr)
                if str_ptr == 0:
                    raise ValueError("字符串对象为空，无法写入")
                self._write_string_object(str_ptr, value)
            else:
                self._write_scalar(addr, inner, value)
        elif kind == 'xsecure':
            self._write_xsecure(addr, inner, value)
        elif kind == 'secure':
            sec_ptr = self.pm.read_uint(addr)
            if sec_ptr == 0:
                raise ValueError("Secure 对象指针为空")
            self._write_secure(sec_ptr, inner, value)
        elif kind == 'ext':
            self._write_ext(addr, inner, value)
        else:
            raise ValueError("只能写入标量、XType、SecureType 或 ExType 类型，自定义类型只读")

    def _get_elem_size(self, inner_type):
        """根据内部类型确定元素在数组中的字节大小（用于地址定位）"""
        kind, _ = parse_type(inner_type)
        if kind in ('secure', 'ext', 'custom') or inner_type == "string" or inner_type == "XString":
            return 4
        elif kind == 'xsecure':
            return X_TYPE_SIZES.get(inner_type, 4)
        else:
            return get_scalar_size(inner_type)

    def _get_element_address(self, obj_addr, fdef_idx, path):
        """获取数组/Vector/List 中元素的地址，针对指针类型特殊处理（用于主表字段的数组编辑）"""
        container_addr = self._get_field_address(obj_addr, fdef_idx)
        ftype = self.fields_def[fdef_idx]["type"]
        current_addr = container_addr
        for idx in path:
            kind, inner = parse_type(ftype)
            if kind in ('scalar', 'xsecure', 'secure', 'ext', 'custom'):
                raise ValueError("路径超出维度")
            if kind == 'array':
                arr_ptr = self.pm.read_uint(current_addr)
                if arr_ptr == 0:
                    raise ValueError("数组指针为空")
                length = self.pm.read_int(arr_ptr + 0x0C)
                if idx >= length:
                    raise ValueError(f"索引 {idx} 超出长度 {length}")
                elem_size = self._get_elem_size(inner)
                current_addr = arr_ptr + 0x10 + idx * elem_size
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
                elem_size = self._get_elem_size(inner)
                current_addr = array_ptr + 0x10 + idx * elem_size
                ftype = inner
            elif kind == 'list':
                list_ptr = self.pm.read_uint(current_addr)
                if list_ptr == 0:
                    raise ValueError("List 指针为空")
                array_ptr = self.pm.read_uint(list_ptr + 0x8)
                if array_ptr == 0:
                    raise ValueError("数组指针为空")
                length = self.pm.read_int(array_ptr + 0x0C)
                if idx >= length:
                    raise ValueError(f"索引 {idx} 超出长度 {length}")
                elem_size = self._get_elem_size(inner)
                current_addr = array_ptr + 0x10 + idx * elem_size
                ftype = inner
            else:
                raise ValueError(f"未知容器类型: {kind}")
        return current_addr

    # ========== UI 写入函数（基于当前选中对象） ==========
    def _write_field(self, fdef_idx, var):
        """UI 调用的字段写入函数（标量/字符串/XType/Secure/Ex）"""
        if self.current_edit_addr is None:
            self.status.config(text="没有选中的对象", foreground="red")
            return
        addr = self.current_edit_addr
        fdef = self.fields_def[fdef_idx]
        try:
            new_str = var.get()
            ftype = fdef["type"]
            kind, inner = parse_type(ftype)
            if kind == 'scalar':
                if inner in TYPE_INFO:
                    if inner == "float":
                        new_val = float(new_str)
                    elif inner == "byte":
                        new_val = int(new_str) & 0xFF
                    else:
                        new_val = int(new_str)
                    old_val = self._read_field(addr, fdef_idx)
                    self._write_field_value(addr, fdef_idx, new_val)
                    verify = self._read_field(addr, fdef_idx)
                    var.set(str(verify))
                    label = get_display_label(fdef, self.offset_chains[fdef_idx])
                    self.status.config(text=f"✔ {label}: {old_val} → {verify}", foreground="green")
                elif inner == "string":
                    old_val = self._read_field(addr, fdef_idx)
                    self._write_field_value(addr, fdef_idx, new_str)
                    verify = self._read_field(addr, fdef_idx)
                    var.set(verify)
                    label = get_display_label(fdef, self.offset_chains[fdef_idx])
                    self.status.config(text=f"✔ {label}: 已更新字符串", foreground="green")
                else:
                    self.status.config(text=f"未知标量类型 {ftype}", foreground="red")
            elif kind == 'xsecure':
                if inner == "XString":
                    self.status.config(text="XString 写入暂不支持", foreground="red")
                else:
                    if inner in ("XFloat",):
                        new_val = float(new_str)
                    else:
                        new_val = int(new_str)
                    old_val = self._read_field(addr, fdef_idx)
                    self._write_field_value(addr, fdef_idx, new_val)
                    verify = self._read_field(addr, fdef_idx)
                    var.set(str(verify))
                    label = get_display_label(fdef, self.offset_chains[fdef_idx])
                    self.status.config(text=f"✔ {label}: {old_val} → {verify}", foreground="green")
            elif kind == 'secure':
                if inner in ("SecureFloat", "SecureDouble"):
                    new_val = float(new_str)
                else:
                    new_val = int(new_str)
                old_val = self._read_field(addr, fdef_idx)
                self._write_field_value(addr, fdef_idx, new_val)
                verify = self._read_field(addr, fdef_idx)
                var.set(str(verify))
                label = get_display_label(fdef, self.offset_chains[fdef_idx])
                self.status.config(text=f"✔ {label}: {old_val} → {verify}", foreground="green")
            elif kind == 'ext':
                secure_type = EXT_TYPE_OFFSETS[inner]["secure_type"]
                if secure_type in ("SecureFloat", "SecureDouble"):
                    new_val = float(new_str)
                else:
                    new_val = int(new_str)
                old_val = self._read_field(addr, fdef_idx)
                self._write_field_value(addr, fdef_idx, new_val)
                verify = self._read_field(addr, fdef_idx)
                var.set(str(verify))
                label = get_display_label(fdef, self.offset_chains[fdef_idx])
                self.status.config(text=f"✔ {label}: {old_val} → {verify}", foreground="green")
            else:
                self.status.config(text="不能写入复合类型字段", foreground="red")
        except ValueError as e:
            self.status.config(text=f"✘ {fdef['name']}: {e}", foreground="red")
        except Exception as e:
            self.status.config(text=f"✘ {fdef['name']}: 写入失败 ({e})", foreground="red")

    def _write_bool_field(self, fdef_idx, var):
        """写入布尔字段（先读旧值，再写新值，显示 old→new）"""
        if self.current_edit_addr is None:
            self.status.config(text="没有选中的对象", foreground="red")
            return
        addr = self.current_edit_addr
        fdef = self.fields_def[fdef_idx]
        try:
            bool_val = var.get() == "True"
            old_val = self._read_field(addr, fdef_idx)
            self._write_field_value(addr, fdef_idx, bool_val)
            verify = self._read_field(addr, fdef_idx)
            var.set("True" if verify else "False")
            label = get_display_label(fdef, self.offset_chains[fdef_idx])
            self.status.config(text=f"✔ {label}: {old_val} → {verify}", foreground="green")
        except Exception as e:
            self.status.config(text=f"✘ {fdef['name']}: 写入失败 ({e})", foreground="red")

    # ---------- 数组元素写入方法 ----------
    def _write_array_element(self, fdef_idx, path, ftype, var):
        """写入数组元素（标量或 XType/Secure/Ex）"""
        if self.current_edit_addr is None:
            self.status.config(text="没有选中的对象", foreground="red")
            return
        obj_addr = self.current_edit_addr
        try:
            elem_addr = self._get_element_address(obj_addr, fdef_idx, path)
        except Exception as e:
            self.status.config(text=f"地址计算失败: {e}", foreground="red")
            return
        try:
            new_str = var.get()
            kind, inner = parse_type(ftype)
            if kind == 'scalar':
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
                    self.status.config(text=f"未知标量类型 {ftype}", foreground="red")
            elif kind == 'xsecure':
                if inner == "XString":
                    self.status.config(text="XString 元素写入暂不支持", foreground="red")
                else:
                    if inner in ("XFloat",):
                        new_val = float(new_str)
                    else:
                        new_val = int(new_str)
                    old_val = self._read_value_at(elem_addr, ftype)
                    self._write_value_at(elem_addr, ftype, new_val)
                    verify = self._read_value_at(elem_addr, ftype)
                    var.set(str(verify))
                    self.status.config(text=f"✔ XType 元素: {old_val} → {verify}", foreground="green")
            elif kind == 'secure':
                if inner in ("SecureFloat", "SecureDouble"):
                    new_val = float(new_str)
                else:
                    new_val = int(new_str)
                old_val = self._read_value_at(elem_addr, ftype)
                self._write_value_at(elem_addr, ftype, new_val)
                verify = self._read_value_at(elem_addr, ftype)
                var.set(str(verify))
                self.status.config(text=f"✔ Secure 元素: {old_val} → {verify}", foreground="green")
            elif kind == 'ext':
                secure_type = EXT_TYPE_OFFSETS[inner]["secure_type"]
                if secure_type in ("SecureFloat", "SecureDouble"):
                    new_val = float(new_str)
                else:
                    new_val = int(new_str)
                old_val = self._read_value_at(elem_addr, ftype)
                self._write_value_at(elem_addr, ftype, new_val)
                verify = self._read_value_at(elem_addr, ftype)
                var.set(str(verify))
                self.status.config(text=f"✔ Ex 元素: {old_val} → {verify}", foreground="green")
            else:
                self.status.config(text=f"未知元素类型 {ftype}", foreground="red")
        except ValueError as e:
            self.status.config(text=f"✘ 无效输入: {e}", foreground="red")
        except Exception as e:
            self.status.config(text=f"✘ 写入失败 ({e})", foreground="red")

    def _write_array_element_bool(self, fdef_idx, path, ftype, var):
        """写入布尔数组元素"""
        if self.current_edit_addr is None:
            self.status.config(text="没有选中的对象", foreground="red")
            return
        obj_addr = self.current_edit_addr
        try:
            elem_addr = self._get_element_address(obj_addr, fdef_idx, path)
        except Exception as e:
            self.status.config(text=f"地址计算失败: {e}", foreground="red")
            return
        try:
            bool_val = var.get() == "True"
            old_val = self._read_value_at(elem_addr, ftype)
            self._write_value_at(elem_addr, ftype, bool_val)
            verify = self._read_value_at(elem_addr, ftype)
            var.set("True" if verify else "False")
            self.status.config(text=f"✔ 元素: {old_val} → {verify}", foreground="green")
        except Exception as e:
            self.status.config(text=f"✘ 写入失败 ({e})", foreground="red")

    # ---------- 自定义对象内部字段编辑辅助 ----------
    def _write_custom_field(self, obj_addr, custom_fdef, new_value):
        """写入自定义对象中的某个字段。custom_fdef 是加载后的字段定义（含 offset_chain, type, name）"""
        try:
            field_addr = self._resolve_offset_chain(obj_addr, custom_fdef["offset_chain"])
            old_val = self._read_value_at(field_addr, custom_fdef["type"])
            ftype = custom_fdef["type"]
            kind, inner = parse_type(ftype)
            if kind == 'scalar':
                if inner in TYPE_INFO:
                    if inner == "float":
                        new_val = float(new_value)
                    elif inner == "byte":
                        new_val = int(new_value) & 0xFF
                    else:
                        new_val = int(new_value)
                elif inner == "string":
                    new_val = new_value
                else:
                    raise ValueError(f"未知标量类型 {ftype}")
            elif kind == 'xsecure':
                if inner == "XString":
                    raise NotImplementedError("XString 写入暂不支持")
                if inner in ("XFloat",):
                    new_val = float(new_value)
                else:
                    new_val = int(new_value)
            elif kind == 'secure':
                if inner in ("SecureFloat", "SecureDouble"):
                    new_val = float(new_value)
                else:
                    new_val = int(new_value)
            elif kind == 'ext':
                secure_type = EXT_TYPE_OFFSETS[inner]["secure_type"]
                if secure_type in ("SecureFloat", "SecureDouble"):
                    new_val = float(new_value)
                else:
                    new_val = int(new_value)
            else:
                raise ValueError("此字段类型不支持编辑")

            self._write_value_at(field_addr, ftype, new_val)
            verify = self._read_value_at(field_addr, ftype)
            return old_val, verify, new_val
        except Exception as e:
            raise e

    # ========== UI 编辑器创建 ==========
    def _get_index_label(self, fdef_idx, index, path):
        """根据路径深度返回索引标签：仅第一层使用 index_labels，否则使用 [index]"""
        if index is None:
            return ""
        # 第一层元素：path 长度为 1
        if len(path) == 1:
            labels = self.fields_def[fdef_idx].get("index_labels", [])
            if index < len(labels) and labels[index]:
                return labels[index]
        return f"[{index}]"

    def _create_editor_for_value(self, parent_frame, obj_addr, fdef_idx, value, ftype, path, row_idx, col_offset=0, index=None):
        """递归创建值编辑器（数组展开）"""
        if isinstance(value, list):
            return self._create_array_container(parent_frame, obj_addr, fdef_idx, value, ftype, path, row_idx, col_offset, index)
        elif isinstance(value, dict):
            try:
                if path:
                    elem_addr = self._get_element_address(obj_addr, fdef_idx, path)
                    obj_ptr = self.pm.read_uint(elem_addr)
                else:
                    field_addr = self._get_field_address(obj_addr, fdef_idx)
                    obj_ptr = self.pm.read_uint(field_addr)
                type_name = ftype if parse_type(ftype)[0] == 'custom' else parse_type(ftype)[1]
                display_name = self._get_custom_display_name(type_name, value, index if index is not None else 0)
                return self._create_custom_object_editor(parent_frame, obj_ptr, value, type_name, display_name, row_idx, col_offset)
            except Exception as e:
                ttk.Label(parent_frame, text=f"<错误: {e}>", foreground="red").grid(row=row_idx, column=0, sticky='w', padx=5)
                return row_idx + 1
        else:
            return self._create_scalar_editor(parent_frame, obj_addr, fdef_idx, value, ftype, path, row_idx, col_offset, index)

    def _create_scalar_editor(self, parent, obj_addr, fdef_idx, value, ftype, path, row_idx=0, col_offset=0, index=None):
        """创建标量编辑器（用于数组/容器内部）"""
        is_err = isinstance(value, str) and value.startswith("ERR")
        col = 0
        if index is not None:
            label_text = self._get_index_label(fdef_idx, index, path)
            ttk.Label(parent, text=label_text, foreground="gray").grid(row=row_idx, column=col, sticky="w", padx=2)
            col += 1

        if ftype == "bool":
            var = tk.StringVar(value="True" if value else "False")
            combo = ttk.Combobox(parent, textvariable=var, values=("True","False"),
                                 width=10, state='readonly' if is_err else 'normal')
            combo.grid(row=row_idx, column=col, sticky="w", padx=5, pady=1)
            col += 1
            if not is_err:
                btn = ttk.Button(parent, text="Save", width=6,
                                 command=lambda f=fdef_idx, p=path, t=ftype, v=var: self._write_array_element_bool(f, p, t, v))
                btn.grid(row=row_idx, column=col, sticky="w", padx=5, pady=1)
                combo.bind('<<ComboboxSelected>>', lambda e, f=fdef_idx, p=path, t=ftype, v=var: self._write_array_element_bool(f, p, t, v))
        elif ftype == "string" or ftype == "XString":
            var = tk.StringVar(value=str(value) if not is_err else value)
            entry = ttk.Entry(parent, textvariable=var, width=30, state='readonly' if is_err else 'normal')
            entry.grid(row=row_idx, column=col, sticky="w", padx=5, pady=1)
            col += 1
            if not is_err:
                btn = ttk.Button(parent, text="Save", width=6,
                                 command=lambda f=fdef_idx, p=path, t=ftype, v=var: self._write_array_element(f, p, t, v))
                btn.grid(row=row_idx, column=col, sticky="w", padx=5, pady=1)
                entry.bind('<Return>', lambda e, f=fdef_idx, p=path, t=ftype, v=var: self._write_array_element(f, p, t, v))
        else:
            var = tk.StringVar(value=str(value) if not is_err else value)
            entry = ttk.Entry(parent, textvariable=var, width=18, state='readonly' if is_err else 'normal')
            entry.grid(row=row_idx, column=col, sticky="w", padx=5, pady=1)
            col += 1
            if not is_err:
                btn = ttk.Button(parent, text="Save", width=6,
                                 command=lambda f=fdef_idx, p=path, t=ftype, v=var: self._write_array_element(f, p, t, v))
                btn.grid(row=row_idx, column=col, sticky="w", padx=5, pady=1)
                entry.bind('<Return>', lambda e, f=fdef_idx, p=path, t=ftype, v=var: self._write_array_element(f, p, t, v))
        return row_idx + 1

    def _create_custom_object_editor(self, parent, obj_ptr, obj_data, type_name, display_name, row_idx=0, col_offset=0):
        """创建自定义对象的可编辑展开控件。obj_ptr 是对象基址（若为0则只读）"""
        container = ttk.Frame(parent)
        container.grid(row=row_idx, column=0, sticky='w', pady=1)

        preview_frame = ttk.Frame(container)
        preview_frame.grid(row=0, column=0, sticky='w')

        ttk.Label(preview_frame, text=display_name, foreground="darkblue").grid(row=0, column=0, sticky='w', padx=2)
        expand_btn = ttk.Button(preview_frame, text="▶ 展开", width=6)
        expand_btn.grid(row=0, column=1, sticky='w', padx=5)

        editor_frame = ttk.Frame(container)
        editor_frame.grid(row=1, column=0, sticky='w', pady=2, padx=20)
        editor_frame.grid_remove()

        container.editor_frame = editor_frame
        container.expanded = False
        container.expand_btn = expand_btn
        container.obj_ptr = obj_ptr
        container.obj_data = obj_data
        container.type_name = type_name

        def toggle():
            if container.expanded:
                editor_frame.grid_remove()
                expand_btn.config(text="▶ 展开")
                container.expanded = False
            else:
                for w in editor_frame.winfo_children():
                    w.destroy()
                sub_row = 0
                try:
                    fields = self._load_custom_type_def(type_name)
                except Exception as e:
                    ttk.Label(editor_frame, text=f"<加载类型定义失败: {e}>", foreground="red").grid(row=0, column=0, sticky='w', padx=5)
                    editor_frame.grid()
                    expand_btn.config(text="▼ 收起")
                    container.expanded = True
                    return

                for fdef in fields:
                    if fdef.get("hidden", False):
                        continue
                    field_name = fdef["name"]
                    val = obj_data.get(field_name, "ERR")
                    disp = fdef.get("display") or field_name
                    ttk.Label(editor_frame, text=f"{disp} ({fdef['type']})").grid(row=sub_row, column=0, sticky='w', padx=5, pady=1)
                    if isinstance(val, list):
                        sub_row = self._create_array_container_for_custom(editor_frame, obj_ptr, fdef, val, sub_row+1)
                    elif isinstance(val, dict):
                        try:
                            field_addr = self._resolve_offset_chain(obj_ptr, fdef["offset_chain"])
                            nested_ptr = self.pm.read_uint(field_addr)
                            nested_type = fdef["type"]
                            nested_display = self._get_custom_display_name(nested_type, val, 0)
                            sub_row = self._create_custom_object_editor(editor_frame, nested_ptr, val, nested_type, nested_display, sub_row+1)
                        except Exception as e:
                            ttk.Label(editor_frame, text=f"<错误: {e}>", foreground="red").grid(row=sub_row+1, column=0, sticky='w', padx=5)
                            sub_row += 2
                    else:
                        is_err = isinstance(val, str) and val.startswith("ERR")
                        var = tk.StringVar(value=str(val) if not is_err else val)
                        entry = ttk.Entry(editor_frame, textvariable=var, width=18, state='readonly' if is_err else 'normal')
                        entry.grid(row=sub_row+1, column=0, sticky='w', padx=5, pady=1)
                        if not is_err and obj_ptr != 0:
                            btn = ttk.Button(editor_frame, text="Save", width=6,
                                             command=lambda f=fdef, v=var, o=obj_ptr: self._write_custom_field_ui(o, f, v))
                            btn.grid(row=sub_row+1, column=1, sticky='w', padx=5, pady=1)
                            entry.bind('<Return>', lambda e, f=fdef, v=var, o=obj_ptr: self._write_custom_field_ui(o, f, v))
                        sub_row += 2
                editor_frame.grid()
                expand_btn.config(text="▼ 收起")
                container.expanded = True
        expand_btn.config(command=toggle)
        return row_idx + 1

    def _write_custom_field_ui(self, obj_ptr, custom_fdef, var):
        """UI 写入自定义对象字段的回调"""
        try:
            new_str = var.get()
            old_val, verify, new_val = self._write_custom_field(obj_ptr, custom_fdef, new_str)
            var.set(str(verify))
            disp = custom_fdef.get("display") or custom_fdef["name"]
            self.status.config(text=f"✔ {disp}: {old_val} → {verify}", foreground="green")
        except Exception as e:
            self.status.config(text=f"✘ 写入失败: {e}", foreground="red")

    def _create_array_container_for_custom(self, parent, obj_ptr, custom_fdef, value_list, row_idx=0):
        """在自定义对象内部创建可编辑的数组容器，返回下一个行索引"""
        ftype = custom_fdef["type"]
        kind, inner_type = parse_type(ftype)
        try:
            field_addr = self._resolve_offset_chain(obj_ptr, custom_fdef["offset_chain"])
            container_ptr = self.pm.read_uint(field_addr)
            if container_ptr == 0:
                raise ValueError("容器指针为空")
            if kind == 'array':
                arr_ptr = container_ptr
            elif kind == 'vector':
                inner_ptr = self.pm.read_uint(container_ptr + 0x8)
                arr_ptr = self.pm.read_uint(inner_ptr + 0x8)
            elif kind == 'list':
                arr_ptr = self.pm.read_uint(container_ptr + 0x8)
            else:
                raise ValueError(f"未知容器类型: {kind}")
            length = self.pm.read_int(arr_ptr + 0x0C)
            elem_size = self._get_elem_size(inner_type)
            container = ttk.Frame(parent)
            container.grid(row=row_idx, column=0, sticky='w', pady=1)
            preview_frame = ttk.Frame(container)
            preview_frame.grid(row=0, column=0, sticky='w')
            ttk.Label(preview_frame, text=f"元素数量: {length}", foreground="blue").grid(row=0, column=0, sticky='w', padx=5)
            expand_btn = ttk.Button(preview_frame, text="▶ 展开", width=6)
            expand_btn.grid(row=0, column=1, sticky='w', padx=5)
            editor_frame = ttk.Frame(container)
            editor_frame.grid(row=1, column=0, sticky='w', pady=2, padx=20)
            editor_frame.grid_remove()
            container.expanded = False
            container.expand_btn = expand_btn
            container.editor_frame = editor_frame
            container.arr_ptr = arr_ptr
            container.length = length
            container.inner_type = inner_type
            container.elem_size = elem_size
            container.kind = kind

            def toggle():
                if container.expanded:
                    editor_frame.grid_remove()
                    expand_btn.config(text="▶ 展开")
                    container.expanded = False
                else:
                    for w in editor_frame.winfo_children():
                        w.destroy()
                    sub_row = 0
                    for i in range(container.length):
                        elem_addr = container.arr_ptr + 0x10 + i * container.elem_size
                        inner_kind, _ = parse_type(container.inner_type)
                        if inner_kind == 'custom':
                            elem_ptr = self.pm.read_uint(elem_addr)
                            item_data = self._read_custom_object(elem_ptr, container.inner_type)
                            display = self._get_custom_display_name(container.inner_type, item_data, i)
                            sub_row = self._create_custom_object_editor(editor_frame, elem_ptr, item_data, container.inner_type, display, sub_row)
                        else:
                            item_val = self._read_value_at(elem_addr, container.inner_type)
                            ttk.Label(editor_frame, text=f"[{i}]").grid(row=sub_row, column=0, sticky='w', padx=2)
                            if isinstance(item_val, str) and item_val.startswith("ERR"):
                                ttk.Label(editor_frame, text=item_val, foreground="red").grid(row=sub_row, column=1, sticky='w', padx=5)
                                sub_row += 1
                            else:
                                var = tk.StringVar(value=str(item_val))
                                entry = ttk.Entry(editor_frame, textvariable=var, width=18)
                                entry.grid(row=sub_row, column=1, sticky='w', padx=5)
                                btn = ttk.Button(editor_frame, text="Save", width=6,
                                                 command=lambda a=elem_addr, t=container.inner_type, v=var: self._write_element_ui(a, t, v))
                                btn.grid(row=sub_row, column=2, sticky='w', padx=5)
                                entry.bind('<Return>', lambda e, a=elem_addr, t=container.inner_type, v=var: self._write_element_ui(a, t, v))
                                sub_row += 1
                    editor_frame.grid()
                    expand_btn.config(text="▼ 收起")
                    container.expanded = True
            expand_btn.config(command=toggle)
            return row_idx + 1
        except Exception as e:
            ttk.Label(parent, text=f"<数组加载失败: {e}>", foreground="red").grid(row=row_idx, column=0, sticky='w', padx=5)
            return row_idx + 1

    def _write_element_ui(self, elem_addr, ftype, var):
        """写入数组元素（直接给定元素地址，用于自定义对象内部）"""
        try:
            new_str = var.get()
            kind, inner = parse_type(ftype)
            if kind == 'scalar':
                if inner in TYPE_INFO:
                    if inner == "float":
                        new_val = float(new_str)
                    elif inner == "byte":
                        new_val = int(new_str) & 0xFF
                    else:
                        new_val = int(new_str)
                elif inner == "string":
                    new_val = new_str
                else:
                    raise ValueError(f"未知标量类型 {ftype}")
            elif kind == 'xsecure':
                if inner == "XString":
                    raise NotImplementedError("XString 写入暂不支持")
                if inner in ("XFloat",):
                    new_val = float(new_str)
                else:
                    new_val = int(new_str)
            elif kind == 'secure':
                if inner in ("SecureFloat", "SecureDouble"):
                    new_val = float(new_str)
                else:
                    new_val = int(new_str)
            elif kind == 'ext':
                secure_type = EXT_TYPE_OFFSETS[inner]["secure_type"]
                if secure_type in ("SecureFloat", "SecureDouble"):
                    new_val = float(new_str)
                else:
                    new_val = int(new_str)
            else:
                raise ValueError("此类型不支持编辑")
            old_val = self._read_value_at(elem_addr, ftype)
            self._write_value_at(elem_addr, ftype, new_val)
            verify = self._read_value_at(elem_addr, ftype)
            var.set(str(verify))
            self.status.config(text=f"✔ 元素: {old_val} → {verify}", foreground="green")
        except Exception as e:
            self.status.config(text=f"✘ 写入失败: {e}", foreground="red")

    def _create_array_container(self, parent, obj_addr, fdef_idx, value_list, ftype, path, row_idx=0, col_offset=0, index=None):
        """创建可展开的数组/容器 UI（主表字段）"""
        if not isinstance(value_list, list):
            return self._create_scalar_editor(parent, obj_addr, fdef_idx, value_list, ftype, path, row_idx, col_offset, index)

        kind, inner_type = parse_type(ftype)
        container = ttk.Frame(parent)
        container.grid(row=row_idx, column=0, sticky='w', pady=1)

        preview_frame = ttk.Frame(container)
        preview_frame.grid(row=0, column=0, sticky='w')

        left_part = ttk.Frame(preview_frame)
        left_part.grid(row=0, column=0, sticky='w')
        if index is not None:
            label_text = self._get_index_label(fdef_idx, index, path)
            ttk.Label(left_part, text=label_text, foreground="gray").grid(row=0, column=0, sticky='w', padx=2)

        preview_label = ttk.Label(preview_frame, text=f"元素数量: {len(value_list)}", foreground="blue")
        preview_label.grid(row=0, column=1, sticky='w', padx=5)

        expand_btn = ttk.Button(preview_frame, text="▶ 展开", width=6)
        expand_btn.grid(row=0, column=2, sticky='w', padx=5)

        editor_frame = ttk.Frame(container)
        editor_frame.grid(row=1, column=0, sticky='w', pady=2, padx=20)
        editor_frame.grid_remove()

        container.preview_frame = preview_frame
        container.editor_frame = editor_frame
        container.expanded = False
        container.expand_btn = expand_btn
        container.obj_addr = obj_addr
        container.fdef_idx = fdef_idx
        container.value_list = value_list
        container.inner_type = inner_type
        container.path = path
        container.col_offset = col_offset

        def toggle():
            if container.expanded:
                editor_frame.grid_remove()
                expand_btn.config(text="▶ 展开")
                container.expanded = False
            else:
                for w in editor_frame.winfo_children():
                    w.destroy()
                sub_row = 0
                for idx, item in enumerate(value_list):
                    sub_path = path + [idx]
                    sub_ftype = inner_type
                    if isinstance(item, dict):
                        try:
                            elem_addr = self._get_element_address(obj_addr, fdef_idx, sub_path)
                            obj_ptr = self.pm.read_uint(elem_addr)
                            display = self._get_custom_display_name(inner_type, item, idx)
                            sub_row = self._create_custom_object_editor(editor_frame, obj_ptr, item, inner_type, display, sub_row)
                        except Exception as e:
                            ttk.Label(editor_frame, text=f"<错误: {e}>", foreground="red").grid(row=sub_row, column=0, sticky='w', padx=5)
                            sub_row += 1
                    else:
                        sub_row = self._create_editor_for_value(
                            editor_frame, obj_addr, fdef_idx, item, sub_ftype, sub_path, sub_row, col_offset, idx
                        )
                editor_frame.grid()
                expand_btn.config(text="▼ 收起")
                container.expanded = True
        expand_btn.config(command=toggle)

        return row_idx + 1

    def display_fields(self, addr, obj_id, fields):
        """显示字段编辑器"""
        self.clear_edit()
        main_frame = ttk.Frame(self.edit_frame)
        main_frame.pack(fill=tk.X, expand=False)
        main_frame.grid_columnconfigure(0, weight=0)
        main_frame.grid_columnconfigure(1, weight=1)

        info = f"地址: 0x{addr:08X}"
        if self.id_parsed and obj_id is not None:
            info += f"  ID:{obj_id}"
        ttk.Label(main_frame, text=info, foreground="darkblue",
                  font=("TkDefaultFont",9,"bold")).grid(row=0, column=0, columnspan=2, sticky="w", padx=5, pady=(5,2))

        row = 1
        for i, fdef in enumerate(self.fields_def):
            if fdef.get("hidden", False):
                continue
            name = fdef["name"]
            ftype = fdef["type"]
            disp = get_display_label(fdef, self.offset_chains[i])
            offset_display = format_offset_display(self.offset_chains[i])
            if self.SHOW_EDIT_BUTTONS:
                label_text = f"{disp} ({ftype}) ({offset_display})"
            else:
                label_text = f"{disp} ({ftype})"

            lbl_frame = ttk.Frame(main_frame)
            lbl_frame.grid(row=row, column=0, sticky="w", padx=5, pady=2)
            lbl = ttk.Label(lbl_frame, text=label_text)
            lbl.pack(side=tk.LEFT)
            if self.SHOW_EDIT_BUTTONS:
                ttk.Button(lbl_frame, text="✎", width=3,
                           command=lambda n=name: self._rename_field_display(n)).pack(side=tk.LEFT, padx=2)
                ttk.Button(lbl_frame, text="✕", width=3,
                           command=lambda n=name: self._hide_field(n)).pack(side=tk.LEFT, padx=2)
            self.field_labels[name] = lbl

            value_frame = ttk.Frame(main_frame)
            value_frame.grid(row=row, column=1, sticky="w", padx=5, pady=2)
            hframe = ttk.Frame(value_frame)
            hframe.grid(row=0, column=0, sticky='w')

            try:
                val = fields.get(name, "ERR")
                if isinstance(val, list):
                    self._create_array_container(hframe, addr, i, val, ftype, [], 0)
                elif isinstance(val, dict):
                    field_addr = self._get_field_address(addr, i)
                    obj_ptr = self.pm.read_uint(field_addr)
                    display = self._get_custom_display_name(ftype, val, 0)
                    self._create_custom_object_editor(hframe, obj_ptr, val, ftype, display, 0)
                else:
                    self._create_scalar_editor_for_field(hframe, i, val, ftype)
            except Exception as e:
                ttk.Label(hframe, text=f"加载失败: {e}", foreground="red").grid(row=0, column=0, sticky='w')
                self.status.config(text=f"字段 {name} 加载失败: {e}", foreground="red")
                row += 1
                continue

            func_info = fdef.get("function")
            if func_info is not None:
                desc = func_info.get("description")
                btn_text = desc if desc else "Call"
                if len(btn_text) > 8:
                    btn_text = btn_text[:8] + "…"
                call_btn = ttk.Button(hframe, text=btn_text, width=len(btn_text)+2,
                                      command=lambda idx=i: self._call_function(idx))
                max_col = 0
                for child in hframe.winfo_children():
                    info = child.grid_info()
                    if 'column' in info:
                        max_col = max(max_col, info['column'] + 1)
                call_btn.grid(row=0, column=max_col, padx=5, sticky='w')

            row += 1

    def _create_scalar_editor_for_field(self, parent, fdef_idx, value, ftype):
        """创建字段的标量编辑器"""
        fdef = self.fields_def[fdef_idx]
        is_err = isinstance(value, str) and value.startswith("ERR")
        if ftype == "bool":
            var = tk.StringVar(value="True" if value else "False")
            combo = ttk.Combobox(parent, textvariable=var, values=("True","False"),
                                 width=10, state='readonly' if is_err else 'normal')
            combo.grid(row=0, column=0, sticky="w", padx=5)
            if not is_err:
                btn = ttk.Button(parent, text="Save", width=6,
                                 command=lambda f=fdef_idx, v=var: self._write_bool_field(f, v))
                btn.grid(row=0, column=1, padx=5)
                combo.bind('<<ComboboxSelected>>', lambda e, f=fdef_idx, v=var: self._write_bool_field(f, v))
        elif ftype == "string" or ftype == "XString":
            var = tk.StringVar(value=str(value) if not is_err else value)
            entry = ttk.Entry(parent, textvariable=var, width=20, state='readonly' if is_err else 'normal')
            entry.grid(row=0, column=0, sticky="w", padx=5)
            if not is_err:
                btn = ttk.Button(parent, text="Save", width=6,
                                 command=lambda f=fdef_idx, v=var: self._write_field(f, v))
                btn.grid(row=0, column=1, padx=5)
                entry.bind('<Return>', lambda e, f=fdef_idx, v=var: self._write_field(f, v))
        else:
            var = tk.StringVar(value=str(value) if not is_err else value)
            entry = ttk.Entry(parent, textvariable=var, width=20, state='readonly' if is_err else 'normal')
            entry.grid(row=0, column=0, sticky="w", padx=5)
            if not is_err:
                btn = ttk.Button(parent, text="Save", width=6,
                                 command=lambda f=fdef_idx, v=var: self._write_field(f, v))
                btn.grid(row=0, column=1, padx=5)
                entry.bind('<Return>', lambda e, f=fdef_idx, v=var: self._write_field(f, v))

    def clear_edit(self):
        """清空字段编辑区"""
        for w in self.edit_frame.winfo_children():
            w.destroy()
        self.field_labels.clear()

    # ========== 字段管理 ==========
    def _rename_field_display(self, field_name):
        """重命名字段的显示名"""
        for f in self.fields_def:
            if f["name"] == field_name:
                cur = f.get("display") or f.get("name") or ""
                break
        else:
            return
        new = simpledialog.askstring("重命名显示名", f"'{field_name}' 的新显示名:", initialvalue=cur)
        if new is None:
            return
        new = new.strip()
        f["display"] = new
        save_json(self.fields_file, {"fields": self.fields_def})
        if field_name in self.field_labels:
            idx = next(i for i, f in enumerate(self.fields_def) if f["name"] == field_name)
            new_disp = get_display_label(f, self.offset_chains[idx])
            if self.SHOW_EDIT_BUTTONS:
                offset_display = format_offset_display(self.offset_chains[idx])
                self.field_labels[field_name].config(text=f"{new_disp} ({f['type']}) ({offset_display})")
            else:
                self.field_labels[field_name].config(text=f"{new_disp} ({f['type']})")
        self.status.config(text=f"✔ 显示名已更新: '{new_disp}'" if new else "✔ 显示名已清空，回退到字段名", foreground="green")

    def _hide_field(self, field_name):
        """隐藏字段"""
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
            obj_id = self._read_id_value(self.current_edit_addr) if self.id_parsed else None
            self.display_fields(self.current_edit_addr, obj_id, fields)

    def show_all_hidden_fields(self):
        """显示所有隐藏字段"""
        for f in self.fields_def:
            f["hidden"] = False
        save_json(self.fields_file, {"fields": self.fields_def})
        if self.current_edit_addr is not None:
            fields = self._read_all_fields(self.current_edit_addr)
            obj_id = self._read_id_value(self.current_edit_addr) if self.id_parsed else None
            self.display_fields(self.current_edit_addr, obj_id, fields)
        self.status.config(text="✔ 所有字段已设为显示", foreground="green")

    def _read_all_fields(self, addr):
        """读取对象所有字段值"""
        data = {}
        for i, fdef in enumerate(self.fields_def):
            try:
                data[fdef["name"]] = self._read_field(addr, i)
            except Exception as e:
                data[fdef["name"]] = f"ERR:{e}"
        return data

    def _get_category_field(self):
        """获取分类字段名"""
        cat = self.table_cfg.get("category")
        return cat["field"] if cat else None

    def _get_id_field(self):
        """获取 ID 字段名"""
        return self.id_parsed[0] if self.id_parsed else None

    def refresh_data(self):
        """刷新数据列表"""
        if not self.pm: return
        try:
            addrs = self._traverse_addresses()
            cat_field = self._get_category_field()
            self.obj_list = []
            for addr in addrs:
                cv = None
                oid = None
                if cat_field:
                    for i, fdef in enumerate(self.fields_def):
                        try:
                            if fdef["name"] == cat_field:
                                cv = self._read_field(addr, i)
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
        """刷新 UI 列表"""
        self.field_labels.clear()
        self.cat_listbox.delete(0, tk.END)
        cat_keys = sorted(self.categories.keys(), key=lambda x: (isinstance(x,int), x) if isinstance(x,int) else (0,str(x)))
        type_names = self.table_cfg.get("category", {}).get("names", {})
        for c in cat_keys:
            name = type_names.get(str(c), str(c)) if isinstance(c, int) else str(c)
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
        """填充条目列表"""
        self.current_category_items = self.categories[cat_key]
        self.item_listbox.delete(0, tk.END)
        for obj in self.current_category_items:
            iid = obj.get('id')
            if self.id_parsed and iid is not None:
                display = f"ID:{iid}"
            else:
                display = f"0x{obj['addr']:08X}"
            self.item_listbox.insert(tk.END, display)

    def on_cat_select(self, event=None):
        """分类选择事件"""
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
        """条目选择事件"""
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

    # ========== 函数调用 ==========
    def _parse_parameter(self, param):
        """解析单个参数，返回整数列表（每个4字节）"""
        if isinstance(param, int):
            return [param]
        if isinstance(param, str):
            if param.lower().startswith('0x'):
                return [int(param, 16)]
            try:
                return [int(param)]
            except ValueError:
                pass
            if param.lower() == "this":
                if self.current_edit_addr is None:
                    raise ValueError("当前没有选中的对象")
                return [self.current_edit_addr]
            if param.startswith("field:"):
                field_name = param[6:]
                return self._get_field_value_as_int_list(field_name)
            if param.startswith("addr:"):
                field_name = param[5:]
                return self._get_field_address_as_int(field_name)
            raise ValueError(f"无法解析参数: {param}")
        raise ValueError(f"不支持的参数类型: {type(param)}")

    def _get_field_address_as_int(self, field_name):
        """返回字段地址（4字节）"""
        for idx, fdef in enumerate(self.fields_def):
            if fdef["name"] == field_name:
                addr = self._get_field_address(self.current_edit_addr, idx)
                return [addr]
        raise ValueError(f"找不到字段: {field_name}")

    def _get_field_value_as_int_list(self, field_name):
        """读取字段值，返回一个或多个4字节整数（用于参数）"""
        fdef_idx = None
        for idx, fdef in enumerate(self.fields_def):
            if fdef["name"] == field_name:
                fdef_idx = idx
                break
        if fdef_idx is None:
            raise ValueError(f"找不到字段: {field_name}")

        fdef = self.fields_def[fdef_idx]
        ftype = fdef["type"]
        addr = self._get_field_address(self.current_edit_addr, fdef_idx)
        kind, inner = parse_type(ftype)

        if kind in ('array', 'vector', 'list'):
            ptr = self.pm.read_uint(addr)
            return [ptr]
        if kind == 'scalar' and inner == "string":
            ptr = self.pm.read_uint(addr)
            return [ptr]
        if kind == 'xsecure' and inner == "XString":
            offsets = X_TYPE_OFFSETS["XString"]
            str_ptr = self.pm.read_uint(addr + offsets["original"])
            return [str_ptr]

        if kind == 'secure':
            sec_ptr = self.pm.read_uint(addr)
            if sec_ptr == 0:
                return [0, 0]
            val = self._read_secure(sec_ptr, inner)
            low = val & 0xFFFFFFFF
            high = (val >> 32) & 0xFFFFFFFF
            return [low, high]
        if kind == 'ext':
            val = self._read_ext(addr, inner)
            low = val & 0xFFFFFFFF
            high = (val >> 32) & 0xFFFFFFFF
            return [low, high]

        if kind == 'scalar' and inner in TYPE_INFO:
            size, fmt = TYPE_INFO[inner]
            raw = self.pm.read_bytes(addr, size)
            if size == 1:
                val = struct.unpack('B', raw)[0]
                return [val]
            elif size == 2:
                val = struct.unpack('<H', raw)[0]
                return [val]
            elif size == 4:
                if inner == "float":
                    int_val = struct.unpack('<I', raw)[0]
                    return [int_val]
                else:
                    val = struct.unpack('<I', raw)[0]
                    return [val]
            elif size == 8:
                if inner == "double":
                    int64 = struct.unpack('<Q', raw)[0]
                else:
                    int64 = struct.unpack('<q', raw)[0] & 0xFFFFFFFFFFFFFFFF
                low = int64 & 0xFFFFFFFF
                high = (int64 >> 32) & 0xFFFFFFFF
                return [low, high]
            else:
                raise ValueError(f"不支持的标量大小: {size}")

        if kind == 'xsecure':
            offsets = X_TYPE_OFFSETS[inner]
            orig_addr = addr + offsets["original"]
            if inner in ("XInt", "XFloat"):
                if inner == "XFloat":
                    raw = self.pm.read_bytes(orig_addr, 4)
                    int_val = struct.unpack('<I', raw)[0]
                    return [int_val]
                else:
                    val = self.pm.read_int(orig_addr)
                    return [val]
            elif inner in ("XByte", "XShort"):
                val = self.pm.read_bytes(orig_addr, 1)[0] if inner == "XByte" else self.pm.read_short(orig_addr)
                return [val]
            elif inner in ("XLong", "XDouble"):
                if inner == "XDouble":
                    raw = self.pm.read_bytes(orig_addr, 8)
                    int64 = struct.unpack('<Q', raw)[0]
                else:
                    int64 = self.pm.read_longlong(orig_addr) & 0xFFFFFFFFFFFFFFFF
                low = int64 & 0xFFFFFFFF
                high = (int64 >> 32) & 0xFFFFFFFF
                return [low, high]
            elif inner == "XString":
                str_ptr = self.pm.read_uint(orig_addr)
                return [str_ptr]
            else:
                raise ValueError(f"不支持的 XType: {inner}")

        # 默认尝试读指针
        try:
            ptr = self.pm.read_uint(addr)
            return [ptr]
        except:
            raise ValueError(f"无法读取字段 {field_name} 的值")

    def _call_function(self, fdef_idx):
        """UI 回调：启动远程调用线程"""
        fdef = self.fields_def[fdef_idx]
        func_def = fdef.get("function")
        if not func_def:
            return
        if self.current_edit_addr is None:
            self.status.config(text="没有选中的对象", foreground="red")
            return
        threading.Thread(target=self._execute_call, args=(fdef_idx,), daemon=True).start()

    def _execute_call(self, fdef_idx):
        """执行远程函数调用"""
        fdef = self.fields_def[fdef_idx]
        func_def = fdef["function"]
        func_offset = hex_to_int(func_def.get("offset", 0))
        if func_offset == 0:
            self._update_status("函数偏移无效", "red")
            return
        target_addr = self.module_base + func_offset

        calling_convention = func_def.get("calling_convention", "__cdecl").lower()
        param_list = func_def.get("parameters", [])

        all_args = []
        try:
            for p in param_list:
                vals = self._parse_parameter(p)
                all_args.extend(vals)
        except Exception as e:
            self._update_status(f"参数解析失败: {e}", "red")
            return

        shellcode = bytearray()
        if calling_convention == "__thiscall":
            if not all_args:
                self._update_status("__thiscall 需要至少一个参数 (this)", "red")
                return
            this_val = all_args[0]
            shellcode += b'\xB9' + struct.pack('<I', this_val)
            rest_args = all_args[1:]
        else:
            rest_args = all_args

        for arg in reversed(rest_args):
            shellcode += b'\x68' + struct.pack('<I', arg)

        shellcode += b'\xB8' + struct.pack('<I', target_addr)
        shellcode += b'\xFF\xD0'

        if calling_convention == "__cdecl":
            total_arg_bytes = len(rest_args) * 4
            if total_arg_bytes > 0:
                shellcode += b'\x83\xC4' + struct.pack('<B', total_arg_bytes)

        shellcode += b'\xC3'

        try:
            shellcode_addr = self.pm.allocate(len(shellcode))
            self.pm.write_bytes(shellcode_addr, bytes(shellcode), len(shellcode))
            old_protect = ctypes.c_ulong()
            ctypes.windll.kernel32.VirtualProtectEx(
                self.pm.process_handle,
                shellcode_addr,
                len(shellcode),
                0x40,
                ctypes.byref(old_protect)
            )
        except Exception as e:
            self._update_status(f"分配内存失败: {e}", "red")
            return

        try:
            thread_handle = ctypes.windll.kernel32.CreateRemoteThread(
                self.pm.process_handle,
                None,
                0,
                shellcode_addr,
                0,
                0,
                None
            )
            if not thread_handle:
                raise ctypes.WinError()
            ctypes.windll.kernel32.WaitForSingleObject(thread_handle, -1)
            ctypes.windll.kernel32.CloseHandle(thread_handle)
            self._update_status("调用成功 (void)", "green")
        except Exception as e:
            self._update_status(f"远程调用失败: {e}", "red")
        finally:
            try:
                self.pm.free(shellcode_addr)
            except:
                pass

    def _update_status(self, text, color="green"):
        """在主线程更新状态栏"""
        def callback():
            self.status.config(text=text, foreground=color)
        if threading.current_thread() is threading.main_thread():
            callback()
        else:
            self.parent.after(0, callback)

    def export_json(self):
        """导出所有对象的未隐藏字段到 JSON 文件"""
        if not self.pm:
            messagebox.showerror("错误", "未连接到进程")
            return
        if not hasattr(self, 'obj_list') or not self.obj_list:
            messagebox.showwarning("警告", "没有数据可导出")
            return
        file_path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
        )
        if not file_path:
            return
        data = []
        active_fields = [(i, fdef["name"]) for i, fdef in enumerate(self.fields_def) if not fdef.get("hidden", False)]
        for obj in self.obj_list:
            addr = obj['addr']
            entry = {}
            for idx, name in active_fields:
                try:
                    val = self._read_field(addr, idx)
                    entry[name] = val
                except Exception as e:
                    entry[name] = f"ERR:{e}"
            data.append(entry)
        try:
            save_json(file_path, data)
            self.status.config(text=f"导出成功: {os.path.basename(file_path)}", foreground="green")
        except Exception as e:
            messagebox.showerror("导出失败", str(e))

    def destroy(self):
        """销毁编辑器"""
        for w in self.parent.winfo_children():
            w.destroy()


# ========== 主应用程序 ==========
class App:
    """应用程序主窗口，负责切换数据表"""

    def __init__(self, root):
        self.root = root
        self.root.title("通用内存编辑器 v5.28")
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
        """切换数据表"""
        if self.current_editor:
            self.current_editor.destroy()
        config_path = os.path.join(self.tables_dir, name + ".json")
        self.current_editor = MemoryEditor(self.container, name, config_path)
        self.status.config(text=f"当前表: {name}")

    def on_closing(self):
        """窗口关闭处理"""
        if self.current_editor:
            self.current_editor.destroy()
        self.root.destroy()


if __name__ == "__main__":
    if pymem is None:
        root = tk.Tk()
        root.withdraw()
        messagebox.showerror("依赖缺失", "未找到 pymem 库，请安装：pip install pymem")
        root.destroy()
        sys.exit(1)
    root = tk.Tk()
    App(root)
    root.mainloop()