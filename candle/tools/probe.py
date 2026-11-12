#!/usr/bin/env python3
"""probe.py CKPT PROBEFILE [CANDLE_ROOT]: restore a small Candle checkpoint and send each toplevel phrase of
PROBEFILE (phrases separated by lines '----'), printing Candle's reply to each, continuing after errors."""
import glob, os, re, socket, subprocess, sys, time
import pexpect
DM = "/project/opt/dmtcp/bin"
ck = os.path.join("/project/work/ckpt", sys.argv[1])
root = sys.argv[3] if len(sys.argv) > 3 else "/project/work/wt/pc-master"
s = socket.socket(); s.bind(("", 0)); port = str(s.getsockname()[1]); s.close()
coord = subprocess.Popen([DM + "/dmtcp_coordinator", "--port", port, "--exit-on-last", "-q", "-q"],
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
time.sleep(0.5)
sess = "/project/work/ckpt/sess_" + port; os.makedirs(sess, exist_ok=True)
p = pexpect.spawn(DM + "/dmtcp_restart", ["--coord-port", port, "--ckptdir", sess] + sorted(glob.glob(ck + "/ckpt_*.dmtcp")),
                  cwd=root, encoding="utf-8", timeout=600, maxread=1 << 20, searchwindowsize=None)
time.sleep(2)
p.sendline('print_string "RESTORED\\n";;'); p.expect("RESTORED\r?\n"); p.expect(r"\n# ")
try:
    for i, ph in enumerate(x.strip() for x in open(sys.argv[2]).read().split("\n----\n")):
        if not ph: continue
        p.sendline(ph)
        p.expect(r"\n# ", timeout=600)
        out = re.sub(r"\x1b\[[0-9;]*m", "", p.before).replace("\r", "")
        out = out.split("\n", ph.count("\n") + 1)[-1] if out.startswith(ph.split("\n")[0][:20]) else out
        print("=== %d: %s\n%s" % (i, ph.replace("\n", " ")[:150], out.strip()[:1500]), flush=True)
finally:
    p.terminate(force=True); coord.terminate()
    subprocess.run("rmdir %s 2>/dev/null" % sess, shell=True)
