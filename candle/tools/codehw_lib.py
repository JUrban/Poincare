"""codehw_lib: high_waters(pid) -> (code bytes, data bytes) written in Candle's code and data buffers (they start
zeroed, so the last non-zero byte bounds what the dynamic compiler wrote).  Reading /proc/PID/mem needs the caller
to be an ancestor of PID (kernel.yama.ptrace_scope = 1)."""
import subprocess
_SYMS = {}
def _syms(exe):
    if exe not in _SYMS:
        _SYMS[exe] = syms = {}
        out = subprocess.run(["nm", exe], capture_output=True, text=True).stdout
        for l in out.split("\n"):
            p = l.split()
            if len(p) == 3 and p[2] in ("cake_codebuffer_begin", "cake_codebuffer_end", "cake_bitmaps_buffer_begin",
                                        "cake_bitmaps_buffer_end"):
                syms[p[2]] = int(p[0], 16)
    return _SYMS[exe]
def high_waters(pid):
    base = None
    for l in open("/proc/%s/maps" % pid):
        f = l.split()
        if l.rstrip().endswith("/cake") and int(f[2], 16) == 0:
            base = int(f[0].split("-")[0], 16); exe = f[-1]; break
    if base is None:
        raise RuntimeError("no mapping of the cake binary")
    s = _syms(exe)
    with open("/proc/%s/mem" % pid, "rb") as mem:
        def nonzero(off, n):
            mem.seek(base + off); return bool(mem.read(n).strip(b"\0"))
        def hw(lo, hi):
            # the dynamic compiler fills the buffer from its start; find the end of the non-zero prefix by
            # binary search over 64 KB blocks (the last bytes before hi may be the linker's alignment padding)
            blk = 1 << 16
            n = (hi - lo) // blk - 1
            a, b = 0, n          # block a is non-zero or a == 0; blocks >= b are zero
            if not nonzero(lo, blk):
                return 0
            while b - a > 1:
                m = (a + b) // 2
                if nonzero(lo + m * blk, blk): a = m
                else: b = m
            mem.seek(base + lo + a * blk); data = mem.read(blk)
            return a * blk + len(data.rstrip(b"\0"))
        return (hw(s["cake_codebuffer_begin"], s["cake_codebuffer_end"]),
                hw(s["cake_bitmaps_buffer_begin"], s["cake_bitmaps_buffer_end"]))
