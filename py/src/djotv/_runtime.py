# ai-disclosure: ai-generated
"""Runs the djot program, compiled from OCaml to WebAssembly, in Wasmtime.

The program is a WASI command: one request per run, the command and its options
as arguments, the input on stdin, the result on stdout.  Its values are WasmGC
references, which a host cannot build, so text is all that crosses.

The nine WASI functions the program imports are defined here rather than taken
from Wasmtime's WASI, which reads stdin from a file only.  Nothing else is
given to the program: no files, no environment, no clock.
"""

from __future__ import annotations

import os
import struct
import threading
from importlib import resources

from wasmtime import (
    Config,
    Engine,
    Func,
    FuncType,
    Instance,
    Memory,
    Module,
    Store,
    Trap,
    TrapCode,
    ValType,
)

_ESPIPE = 70
_STDOUT = 1


class DjotError(Exception):
    """A request the djot program refused, with its message."""


class _Exit(Exception):
    def __init__(self, code: int) -> None:
        self.code = code


class _Call:
    """The WASI functions of one run, over its arguments and its input."""

    def __init__(self, store: Store, args: list[str], stdin: bytes) -> None:
        self.store = store
        self.args = [arg.encode() + b"\0" for arg in args]
        self.stdin = stdin
        self.read = 0
        self.stdout = bytearray()
        self.stderr = bytearray()
        # Set once the module is instantiated, before any function is called.
        self.memory: Memory | None = None

    def _get(self, ptr: int, size: int) -> bytearray:
        assert self.memory is not None
        return self.memory.read(self.store, ptr, ptr + size)

    def _put(self, ptr: int, data: bytes) -> None:
        assert self.memory is not None
        self.memory.write(self.store, data, ptr)

    def _put_u32(self, ptr: int, *values: int) -> None:
        self._put(ptr, struct.pack(f"<{len(values)}I", *values))

    def _iovecs(self, iovs: int, count: int) -> list[tuple[int, int]]:
        return list(struct.iter_unpack("<II", self._get(iovs, 8 * count)))

    def fd_write(self, fd: int, iovs: int, count: int, written: int) -> int:
        out = self.stdout if fd == _STDOUT else self.stderr
        total = 0
        for ptr, size in self._iovecs(iovs, count):
            out += self._get(ptr, size)
            total += size
        self._put_u32(written, total)
        return 0

    def fd_read(self, fd: int, iovs: int, count: int, nread: int) -> int:
        total = 0
        for ptr, size in self._iovecs(iovs, count):
            chunk = self.stdin[self.read : self.read + size]
            self._put(ptr, chunk)
            self.read += len(chunk)
            total += len(chunk)
        self._put_u32(nread, total)
        return 0

    def fd_seek(self, fd: int, offset: int, whence: int, result: int) -> int:
        return _ESPIPE

    def random_get(self, ptr: int, size: int) -> int:
        self._put(ptr, os.urandom(size))
        return 0

    def environ_sizes_get(self, count: int, size: int) -> int:
        self._put_u32(count, 0)
        self._put_u32(size, 0)
        return 0

    def environ_get(self, environ: int, buf: int) -> int:
        return 0

    def args_sizes_get(self, count: int, size: int) -> int:
        self._put_u32(count, len(self.args))
        self._put_u32(size, sum(map(len, self.args)))
        return 0

    def args_get(self, argv: int, buf: int) -> int:
        for i, arg in enumerate(self.args):
            self._put_u32(argv + 4 * i, buf)
            self._put(buf, arg)
            buf += len(arg)
        return 0

    def proc_exit(self, code: int) -> None:
        raise _Exit(code)


_I32, _I64 = ValType.i32(), ValType.i64()
_SIGNATURES: dict[str, tuple[list[ValType], list[ValType]]] = {
    "fd_write": ([_I32] * 4, [_I32]),
    "fd_read": ([_I32] * 4, [_I32]),
    "fd_seek": ([_I32, _I64, _I32, _I32], [_I32]),
    "random_get": ([_I32] * 2, [_I32]),
    "environ_sizes_get": ([_I32] * 2, [_I32]),
    "environ_get": ([_I32] * 2, [_I32]),
    "args_sizes_get": ([_I32] * 2, [_I32]),
    "args_get": ([_I32] * 2, [_I32]),
    "proc_exit": ([_I32], []),
}

_Loaded = tuple[Engine, Module, list[tuple[str, FuncType]]]

_lock = threading.Lock()
_loaded: _Loaded | None = None


def _load() -> _Loaded:
    """The compiled module, with its imports in the order it declares them.

    Compiling takes a few hundred milliseconds; Wasmtime's cache keeps the
    result on disk for the next process.
    """
    global _loaded
    with _lock:
        if _loaded is None:
            config = Config()
            config.cache = True
            engine = Engine(config)
            wasm = resources.files(__package__).joinpath("djot.wasm").read_bytes()
            module = Module(engine, wasm)
            imports = [
                (name, FuncType(*_SIGNATURES[name]))
                for name in (i.name or "" for i in module.imports)
            ]
            _loaded = engine, module, imports
        return _loaded


def run(command: str, options: list[str], text: str) -> str:
    """One run of the program: its stdout, or `DjotError` with its stderr."""
    engine, module, imports = _load()
    store = Store(engine)
    call = _Call(store, ["djot", command, *options], text.encode())
    funcs = [Func(store, ty, getattr(call, name)) for name, ty in imports]
    code = 0
    try:
        exports = Instance(store, module, funcs).exports(store)
        memory, start = exports["memory"], exports["_start"]
        assert isinstance(memory, Memory) and isinstance(start, Func)
        call.memory = memory
        start(store)
    except _Exit as exit:
        code = exit.code
    except Trap as trap:
        if trap.trap_code == TrapCode.STACK_OVERFLOW:
            raise DjotError("the document is nested too deeply") from None
        raise DjotError(f"the djot program crashed: {trap.message}") from None
    if code != 0:
        raise DjotError(call.stderr.decode(errors="replace"))
    return call.stdout.decode()
