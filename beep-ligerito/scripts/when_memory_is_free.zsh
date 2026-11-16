#!/bin/zsh
# Wait until the machine has unused memory, then run a command (research, unaudited).
# [AI-drafted (claude-fable-5-2), 2026-11-14, at the author's request ("run experiments for 100 bits of security"),
# after the run 20261114h, which started on a machine with 2.7 GB of unused memory; please review]
# [AI-revised (claude-opus-5-5), 2026-11-16: copied into the repository BEEP; the gate is now scripts/bench_gate.py, a copy of
# ../5-implementation/scripts/bench_gate.py of the repository random-domain-ligerito; please review]
#
#   zsh scripts/when_memory_is_free.zsh <GB> <max wait in seconds> -- command...
#
# The gate of scripts/bench_gate.py waits for an idle CPU, not for memory. A campaign that
# starts on a machine with little unused memory has its large processes compressed or swapped, and its proofs
# take bursts of page faults. This script reads the unused memory from `top` every 60 s and runs the command once
# it has been at least <GB> GB in 3 consecutive samples and no campaign holds the lock /tmp/bitz-bench.lock.
# Exit code: the command's, or 3 if the memory did not become free within <max wait in seconds>.
set -u
NEED=${1:?usage: zsh when_memory_is_free.zsh <GB> <max wait in seconds> -- command...}
MAXWAIT=${2:?usage: zsh when_memory_is_free.zsh <GB> <max wait in seconds> -- command...}
shift 2
[[ ${1:-} == "--" ]] && shift
(( $# )) || { echo "no command"; exit 2 }
# "PhysMem: 23G used (3982M wired, 3480M compressor), 591M unused." -> 591
unused_mb() {
  top -l 1 -n 0 2>/dev/null | awk '/^PhysMem/ {
    for (i = 2; i <= NF; i++) if ($i ~ /^unused/) {
      v = $(i - 1)
      if (v ~ /G$/) { sub(/G$/, "", v); print int(v * 1024) } else { sub(/M$/, "", v); print int(v) }
    }
  }'
}
waited=0; streak=0
while true; do
  mb=$(unused_mb)
  if [[ -n $mb && $mb -ge $(( NEED * 1024 )) && ! -e /tmp/bitz-bench.lock ]]; then (( streak += 1 )); else streak=0; fi
  echo "[when_memory_is_free] $(date '+%Y-%m-%d %H:%M:%S') unused ${mb:-?} MB (need $(( NEED * 1024 ))), streak $streak/3"
  (( streak >= 3 )) && break
  (( waited >= MAXWAIT )) && { echo "[when_memory_is_free] no $NEED GB of unused memory after $waited s"; exit 3 }
  sleep 60; (( waited += 60 ))
done
exec "$@"
