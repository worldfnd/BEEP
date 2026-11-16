#!/bin/zsh
# Timing driver of the three-way Ligerito comparison (research, unaudited).
# [AI-drafted (claude-fable-5-2), 2026-11-13, at the author's request; please review]
# [AI-revised (claude-opus-5-5), 2026-11-16: copied into the repository BEEP; the gate is now scripts/bench_gate.py, a copy of
# ../5-implementation/scripts/bench_gate.py of the repository random-domain-ligerito; please review]
#
#   python3 scripts/bench_gate.py run --label beep-three-way-<label> --min-idle 80 --hold-seconds 60 -- \
#     zsh scripts/run_cells.zsh <label> [cells file]      (from 7-beep-ligerito, outside any sandbox, on AC power)
#
# The guards of 5-implementation/scripts/run_campaign.zsh of the repository random-domain-ligerito: one cell per process, a cool-down before each cell,
# /usr/bin/time -l per cell, the power source, the load and the swap logged per cell. No cell runs on battery: before
# every cell the driver waits for AC power (at most CAMPAIGN_AC_WAIT seconds), then for a sustained idle CPU again
# (bench_gate.py wait-idle), and a run that ends on battery is set aside and done again on AC. The bench binary is
# built first, with this folder's own target directory (the shell's CARGO_TARGET_DIR belongs to another project).
#
# Results go to bench_results/three-way-<label>/: machine.txt, binaries.txt, campaign.log, cells.tsv,
# cells/<name>.{out,err,meta}. Then: python3 scripts/collect.py bench_results/three-way-<label>.
# Environment: CAMPAIGN_COOLDOWN (s, default 45), CAMPAIGN_REPS (default 9), CAMPAIGN_REQUIRE_AC (default 1),
# CAMPAIGN_AC_WAIT (s, default 14400), CAMPAIGN_IDLE_MIN (default 80), CAMPAIGN_IDLE_HOLD (s, default 60),
# CAMPAIGN_IDLE_EACH (default 0; 1: that idle condition before every cell),
# CAMPAIGN_TIME (default "/usr/bin/time -l"; "none"), CAMPAIGN_DRY_RUN, CAMPAIGN_OUT, CAMPAIGN_OVERWRITE,
# CAMPAIGN_BIN (a bench binary to run in place of the one that the driver builds; for diagnostic runs).
# [AI-revised (claude-fable-5-2), 2026-11-13: CAMPAIGN_BIN]
# [AI-revised (claude-fable-5-2), 2026-11-14: binaries.txt also has the hashes of affine_fast.rs and affine.rs (after the
# run 20261114g, whose binaries.txt has the three hashes of before)]
# [AI-revised (claude-fable-5-2), 2026-11-14: CAMPAIGN_IDLE_EACH=1 waits for the idle condition of the gate before every
# cell, and not only before the first one (for a run while the machine is in use: the run 20261114g-add2)]
set -u
HERE=${0:A:h}; ROOT=${HERE:h}
LABEL=${1:?usage: zsh run_cells.zsh <label> [cells file]}
CELLS=${2:-$HERE/cells.txt}
COOLDOWN=${CAMPAIGN_COOLDOWN:-45}; REPS=${CAMPAIGN_REPS:-9}; REQUIRE_AC=${CAMPAIGN_REQUIRE_AC:-1}; DRY=${CAMPAIGN_DRY_RUN:-0}
TIMECMD=${CAMPAIGN_TIME:-/usr/bin/time -l}
AC_WAIT=${CAMPAIGN_AC_WAIT:-14400}; IDLE_MIN=${CAMPAIGN_IDLE_MIN:-80}; IDLE_HOLD=${CAMPAIGN_IDLE_HOLD:-60}
IDLE_EACH=${CAMPAIGN_IDLE_EACH:-0}
GATE=$HERE/bench_gate.py
OUT=${CAMPAIGN_OUT:-$ROOT/bench_results/three-way-$LABEL}
[[ -f $CELLS ]] || { echo "no cells file $CELLS"; exit 1 }
if [[ -e $OUT && ${CAMPAIGN_OVERWRITE:-0} != 1 ]]; then echo "$OUT exists: take a new label"; exit 1; fi
mkdir -p $OUT/cells
LOG=$OUT/campaign.log
log() { echo "$*" | tee -a $LOG }
power() { pmset -g batt 2>/dev/null | head -1 | sed "s/^Now drawing from //; s/'//g" }
loadavg() { uptime | sed 's/.*load averages*: //' }
swap() { sysctl -n vm.swapusage 2>/dev/null | sed 's/  */ /g' }
cpuline() { top -l 1 -n 0 2>/dev/null | grep -E '^(CPU usage|PhysMem)' | tr '\n' ' ' }

export CARGO_TARGET_DIR=$ROOT/target RUSTFLAGS="-C target-cpu=native"
if [[ -n ${CAMPAIGN_BIN:-} ]]; then
  # A diagnostic run on a given binary (e.g. the bench of an earlier run, rebuilt elsewhere): nothing is built.
  BIN=$CAMPAIGN_BIN
  log "using the bench binary $BIN (CAMPAIGN_BIN): not built here"
else
  log "building the bench binary (target directory $CARGO_TARGET_DIR)"
  (cd $ROOT/flock && cargo bench --offline -p flock-core --bench ligerito_three_way --no-run) >> $LOG 2>&1 || { log "build failed"; exit 1 }
  BIN=$(ls -t $ROOT/target/release/deps/ligerito_three_way-* | grep -v '\.d$' | head -1)
fi
[[ -x $BIN ]] || { log "no bench binary"; exit 1 }
{
  echo "label: $LABEL"; echo "date: $(date '+%Y-%m-%d %H:%M:%S %Z')"; echo "cells: $CELLS"
  echo "cooldown: $COOLDOWN s, reps: $REPS"
  echo "os: $(sw_vers -productVersion 2>/dev/null) $(uname -m)"
  for k in machdep.cpu.brand_string hw.ncpu hw.perflevel0.physicalcpu hw.perflevel1.physicalcpu hw.memsize; do echo "$k: $(sysctl -n $k 2>/dev/null)"; done
  echo "power: $(power)"; echo "load: $(loadavg)"; echo "swap: $(swap)"; echo "top: $(cpuline)"
  echo "rustc: $(rustc --version)"
  echo "flock: succinctlabs/flock 14b78c09b182fdbf0c88fbbf999adbc0ea394fe0 (branch affine-fold-f128) + the local changes of VENDORED.md"
  echo "repository: $(git -C $ROOT rev-parse HEAD 2>/dev/null) $(git -C $ROOT status --porcelain 2>/dev/null | wc -l | tr -d ' ') changed or untracked paths"
} > $OUT/machine.txt
echo "ligerito_three_way $(shasum -a 256 $BIN | cut -c1-16) $BIN" > $OUT/binaries.txt
shasum -a 256 $ROOT/flock/crates/flock-core/src/pcs/ligerito/beep.rs $ROOT/flock/crates/flock-core/benches/ligerito_three_way.rs $CELLS \
  $ROOT/flock/crates/flock-core/src/pcs/ligerito/affine_fast.rs $ROOT/flock/crates/flock-core/src/pcs/ligerito/affine.rs >> $OUT/binaries.txt
cp $CELLS $OUT/cells.txt
# Wait for AC power before a cell; after a wait, wait for an idle machine again. Returns 1 on a timeout.
wait_for_ac() {
  [[ $REQUIRE_AC == 1 && $(power) != AC* ]] || return 0
  log "on battery ($(power)) before $1: waiting for AC power (at most $AC_WAIT s)"
  local waited=0
  while [[ $(power) != AC* ]]; do
    (( waited >= AC_WAIT )) && { log "no AC power after $waited s; stopping"; return 1 }
    sleep 60; (( waited += 60 ))
  done
  log "AC power back after $waited s; waiting for $IDLE_HOLD s of at least $IDLE_MIN % idle CPU"
  python3 $GATE wait-idle --label "three-way-$LABEL-after-ac-wait" --min-idle $IDLE_MIN --hold-seconds $IDLE_HOLD >> $LOG 2>&1
  return 0
}
print -r -- $'name\tstatus\tstart\tend\tpower\tpower_after\tload_before\tcell' > $OUT/cells.tsv
fail=0
while IFS= read -r line || [[ -n $line ]]; do
  line=${line%%\#*}; words=(${=line}); (( ${#words} )) || continue
  name=${words[1]}; shift words
  envs=(); args=()
  for w in $words; do if [[ $w == [A-Z]*=* ]]; then envs+=$w; else args+=$w; fi; done
  cmd=($BIN $args reps=$REPS)
  if [[ $DRY == 1 ]]; then log "DRY $name: env $envs $cmd"; continue; fi
  for attempt in 1 2 3; do
    wait_for_ac $name || exit 2
    sleep $COOLDOWN
    wait_for_ac $name || exit 2
    # On a machine that is in use (CAMPAIGN_IDLE_EACH=1): the idle condition of the gate again, right before the cell.
    if [[ $IDLE_EACH == 1 ]]; then
      python3 $GATE wait-idle --label "three-way-$LABEL-$name" --min-idle $IDLE_MIN --hold-seconds $IDLE_HOLD >> $LOG 2>&1 \
        || { log "no idle machine before $name; stopping"; exit 2 }
    fi
    start=$(date '+%H:%M:%S'); p0=$(power); l0=$(loadavg)
    { echo "name: $name"; echo "attempt: $attempt"; echo "env: $envs"; echo "args: $args reps=$REPS"; echo "start: $(date '+%Y-%m-%d %H:%M:%S')"
      echo "power_before: $p0"; echo "load_before: $l0"; echo "swap_before: $(swap)"; echo "top_before: $(cpuline)" } > $OUT/cells/$name.meta
    if [[ $TIMECMD == none ]]; then
      env $envs $cmd > $OUT/cells/$name.out 2> $OUT/cells/$name.err; rc=$?
    else
      env $envs ${=TIMECMD} $cmd > $OUT/cells/$name.out 2> $OUT/cells/$name.err; rc=$?
    fi
    p1=$(power)
    { echo "end: $(date '+%Y-%m-%d %H:%M:%S')"; echo "exit: $rc"; echo "power_after: $p1"; echo "load_after: $(loadavg)"; echo "swap_after: $(swap)" } >> $OUT/cells/$name.meta
    cell_status=ok; (( rc == 0 )) || cell_status="exit$rc"
    if [[ $REQUIRE_AC == 1 && $p1 != AC* ]]; then
      cell_status="battery"
      for ext in out err meta; do mv $OUT/cells/$name.$ext $OUT/cells/$name.$ext.battery-$attempt; done
    fi
    print -r -- "$name"$'\t'"$cell_status"$'\t'"$start"$'\t'"$(date '+%H:%M:%S')"$'\t'"$p0"$'\t'"$p1"$'\t'"$l0"$'\t'"$envs $args" >> $OUT/cells.tsv
    log "$name (attempt $attempt): $cell_status"
    [[ $cell_status == battery ]] || break
  done
  [[ $cell_status == ok ]] || fail=1
done < $CELLS
log "done: $(date '+%Y-%m-%d %H:%M:%S'), failures: $fail"
exit $fail
