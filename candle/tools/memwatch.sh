#!/bin/bash
# memwatch.sh LOG: every 60 s, the RSS of each cake process and, from smaps, how much of the binary's code
# buffer (the dirty r-xp mapping) and data buffer (rw-p) is written
while true; do
  for p in $(ps -eo pid,args --no-headers | awk '/cake --candle|DMTCP:cake/ && !/awk/ {print $1}'); do
    r=$(ps -o rss= -p $p 2>/dev/null); [ -z "$r" ] && continue
    c=$(python3 /project/work/pc/tools/codewatch.py $p 2>/dev/null | awk '$1=="r-xp" {s+=$(NF-1)} $1=="rw-p" {d+=$(NF-1)} END {printf "code %.0f MB data %.0f MB", s, d}')
    echo "$(date +%H:%M:%S) pid $p rss $(awk -v r=$r 'BEGIN{printf "%.1f", r/1048576}') GB $c" >> $1
  done
  sleep 60
done
