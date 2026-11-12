#!/usr/bin/env python3
"""pc_lane.py [--restore CK --from N] [--dry] [--tail ITEM...]: the main lane on Candle master (pc-master
worktree), from the pc_base checkpoint (hol.ml, prelude, cauchy, lpspaces, green): compat.ml, then every src/
file of candle/make.ml as its own driver item, checkpointing (alternately pc_m_a and pc_m_b) after about
1800 s of HOL Light time, then the checks and the audit.  Items are numbered; --from N resumes at item N."""
import os, re, subprocess, sys
PC = "/project/repos/Poincare/"
needs = re.findall(r'^needs "([^"]+)";;', open(PC + "candle/make.ml").read(), re.M)
src = [f for f in needs if f.startswith("src/")]
t = {}
for l in open(PC + "doc/timing.tsv").read().split("\n")[1:]:
    p = l.split("\t")
    if len(p) >= 2:
        try: t[p[0]] = float(p[1])
        except ValueError: pass
items, acc, k = ['cmd:loads "pc/candle/compat.ml"'], 0.0, 0
for f in src:
    items.append(f)
    acc += t.get(f, 0)
    if acc >= 1800:
        items.append("ckpt:pc_m_%s" % "ab"[k % 2]); k += 1; acc = 0.0
items += ["ckpt:pc_m_src", 'cmd:loads "pc/candle/check_results.ml"', 'cmd:loads "pc/candle/audit.ml"', "ckpt:pc_m_done"]
args = sys.argv[1:]
restore = args[args.index("--restore") + 1] if "--restore" in args else "pc_base"
start = int(args[args.index("--from") + 1]) if "--from" in args else 0
with open("/project/work/logs/pc/lane_items.txt", "w") as f:
    for i, it in enumerate(items):
        f.write("%5d %s\n" % (i, it))
if "--dry" in args:
    print(len(items), "items;", sum(i.startswith("ckpt:") for i in items), "checkpoints"); sys.exit(0)
os.chdir("/project/work")
env = dict(os.environ, CANDLE_ROOT="/project/work/wt/pc-master")
tag = "lane_from%d" % start
with open("logs/pc/%s.out" % tag, "w") as out:
    sys.exit(subprocess.run(["python3", "pc/tools/cdriver.py", "--restore", restore, "--heap", "46000",
                             "--log", "logs/pc/%s.log" % tag] + items[start:],
                            stdout=out, stderr=subprocess.STDOUT, env=env).returncode)
