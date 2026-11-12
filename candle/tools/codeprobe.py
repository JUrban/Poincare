#!/usr/bin/env python3
"""codeprobe.py HEAP_MB PHRASE...: a fresh Candle (no DMTCP) in the pc-master worktree; after each phrase,
print the time and how much of the code and data buffers is written (codewatch.py)."""
import subprocess, sys, time, pexpect
root = "/project/work/wt/pc-master"
p = pexpect.spawn(root + "/candle.sh", cwd=root, env={"CML_HEAP_SIZE": sys.argv[1], "PATH": "/usr/bin:/bin"},
                  encoding="utf-8", timeout=86400, maxread=1 << 20, searchwindowsize=None)
p.expect(r"\n# ", timeout=180)
t0 = time.time()
for ph in sys.argv[2:]:
    p.sendline(ph)
    while True:  # nested loads print prompts too; wait for our marker
        p.sendline('print_string "PHRASE_DONE\\n";;')
        p.expect("PHRASE_DONE\r?\n"); p.expect(r"\n# ")
        break
    print("%8.1fs %s" % (time.time() - t0, ph[:80]), flush=True)
    kids = subprocess.run(["pgrep", "-P", str(p.pid)], capture_output=True, text=True).stdout.split()
    for k in kids:  # candle.sh runs cake as a child
        print(subprocess.run(["python3", "/project/work/pc/tools/codewatch.py", k], capture_output=True, text=True).stdout
              or "(no smaps?)", flush=True)
p.sendline("exit 0;;"); p.close(force=True)
