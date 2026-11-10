#!/bin/bash
# p2d build wrapper: detached, TERM-immune (load >= 90 protocol)
#
# R2125609450 -- TERM-immunity is now BOUNDED, and the build tree is now OWNED.
#
# An unconditional `trap "" TERM` is INHERITED ACROSS EXEC: `lean` ignored TERM as
# well as this wrapper. Combined with "kill the pid you can see", that produced a
# permanent ~8 GB / ~80% CPU orphan per abandoned round (ppid=1, log unattributable,
# nobody reading it). Five were live at once: 29.81 GB RSS, ~5 cores, swap 94%.
#
# THE EXACT CHAIN, observed on p2e_r8 (2026-11-10T17:14Z), which is why rule 4 exists:
#   `lake env lean X`  ->  lake forks `lean` (the 8 GB holder) and waits for it.
#   Someone SIGKILLs lake -- a reaper's obvious target, and TERM is inert here.
#   `wait` returns 137, so THIS wrapper printed `exit=137` and exited cleanly,
#   releasing its lock and reporting a finished run WHILE `lean` kept running,
#   reparented to pid 1. The exit status was a lie about whether the build was still
#   alive, and a `kill -KILL -$child` group kill misses it: `set -m` was measured NOT
#   to put the job in its own process group under this bash.
#
# Four rules now hold:
#   1. HARD CAP enforced by SIGKILL. TERM is ignored by design, so TERM can never be
#      the reaper here.
#   2. THE WATCHDOG OUTLIVES THE WRAPPER: reparented if this script is SIGKILLed, it
#      reaps the build within one 5 s poll instead of waiting for the cap.
#   3. ONE WRITER PER LOG: a liveness-based lock refuses a second writer, and the log
#      is APPEND only, so a relaunch can never truncate under a live writer's fd
#      (round 4 once had three writers on one file: truncate-then-interleave).
#   4. THE WRAPPER OWNS THE WHOLE TREE, NOT JUST ITS CHILD. The watchdog records every
#      descendant pid it ever sees; on ANY exit path the wrapper SIGKILLs the survivors.
#      A killed middle process can no longer leave its build running.
#
# Liveness is asked of `ps`, NEVER of `kill -0`: kill -0 returns nonzero for EPERM as
# well as ESRCH, so it calls a LIVE but unsignalable holder "dead" and tears down a
# lock still being written (measured: a lock held by pid 1 was broken and a second
# writer ran).
#
# Env: LEAN_MAX_SECONDS (default 1800) is the hard wall-clock cap.
set -u
cd /Volumes/Substrate-1/bigo/sssp-nlogn-lane || exit 66
LOG=${1:-p2d_r1.log}
MAX=${LEAN_MAX_SECONDS:-1800}
TREE=$(mktemp -t p2d_tree.XXXXXX) || exit 66
trap "" TERM

alive() { case "${1:-}" in ''|*[!0-9]*) return 1;; esac; ps -p "$1" -o pid= >/dev/null 2>&1; }
snap() {  # record $1 and all its descendants into $TREE
  local p=$1 k
  printf '%s\n' "$p" >> "$TREE"
  for k in $(pgrep -P "$p" 2>/dev/null); do snap "$k"; done
}
reap_tree() {  # SIGKILL every recorded survivor that is still alive
  local p
  [ -s "$TREE" ] || return 0
  sort -u -o "$TREE" "$TREE" 2>/dev/null
  for p in $(cat "$TREE"); do
    if alive "$p"; then kill -KILL "$p" 2>/dev/null; echo "$p" >> "$TREE.reaped"; fi
  done
}

# ---- one writer per log; stale locks are broken by LIVENESS, not by age ----
LOCK="$LOG.lockd"
if ! mkdir "$LOCK" 2>/dev/null; then
  holder=$(cat "$LOCK/pid" 2>/dev/null || true)
  if alive "${holder:-}"; then
    echo "refusing: pid $holder is already writing $LOG" >&2
    exit 75
  fi
  rm -rf "$LOCK"
  mkdir "$LOCK" 2>/dev/null || { echo "refusing: $LOG lock contested" >&2; exit 75; }
fi
echo $$ > "$LOCK/pid"
cleanup() { rm -rf "$LOCK"; }   # NOTE: never rm "$TREE" here -- the watchdog is
# reparented and still needs it after this script is gone (that bug made REAP a no-op).
trap cleanup EXIT

# ---- the run ----
lake env lean Submission/FibHeapProg.lean >> "$LOG" 2>&1 &
child=$!
printf '%s\n' "$child" > "$TREE"

# ---- watchdog: survives this script, reaps on wrapper death OR on the hard cap ----
(
  waited=0
  while [ "$waited" -lt "$MAX" ]; do
    snap "$child"
    if ! alive "$$"; then
      printf '\nR2125609450 REAP: wrapper %s died; SIGKILLing build tree of %s after %ss\n' "$$" "$child" "$waited" >> "$LOG"
      reap_tree; rm -f "$TREE" "$TREE.reaped"; exit 0
    fi
    alive "$child" || { snap "$child"; [ -s "$TREE.reaped" ] || true; }
    sleep 1; waited=$((waited + 1))
  done
  printf '\nR2125609450 TIMEOUT: SIGKILL to build tree of %s after %ss (TERM is ignored by design)\n' "$child" "$MAX" >> "$LOG"
  reap_tree; rm -f "$TREE" "$TREE.reaped"
) &
wd=$!

wait "$child"; rc=$?

# RULE 4: the child may have died while its own children kept running.
reap_tree
if [ -s "$TREE.reaped" ]; then
  printf 'R2125609450 ORPHAN-GUARD: child %s exited rc=%s but its descendants were still alive; SIGKILLed: %s\n' \
    "$child" "$rc" "$(tr '\n' ' ' < "$TREE.reaped")" >> "$LOG"
fi
kill "$wd" 2>/dev/null
rm -f "$TREE" "$TREE.reaped"
printf 'exit=%s cap=%ss child=%s log=%s\n' "$rc" "$MAX" "$child" "$LOG" >> "$LOG"
exit "$rc"
