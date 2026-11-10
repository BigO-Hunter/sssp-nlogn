#!/bin/bash
# p2e build wrapper -- p2d_build.sh's rules, with the KILL TARGET removed.
#
# MEASURED 2026-11-10T06:39 (p2e_r11.log): `lake env lean X` forks `lean` and
# waits. A reaper SIGKILLed **lake** (child rc=137) while `lean` (2.8 GB, the
# real elaboration) kept running; the wrapper's rule-4 orphan guard reaped the
# survivor, so no orphan was left -- but the round was lost at 60 s.
# The five storm rounds before it (r9/r9b/r9c/r9d/r10) died the other way
# (the WRAPPER was killed). Both shapes are recorded in p2e_receipts.md.
#
# Since `lake` is the observed target and contributes nothing after the env is
# resolved, the wrapper resolves LEAN_PATH once (lake exits immediately there)
# and then runs `lean` DIRECTLY. The watchdog then owns a `lean` child, there is
# no waiting `lake` parent to be culled, and rc is the compiler's own.
#
# Everything else is p2d_build.sh: bounded TERM-immunity, one writer per log
# (liveness, never kill -0), hard SIGKILL cap, watchdog that outlives the
# wrapper, and rule 4 (the wrapper owns the whole tree).
set -u
# launchd-submitted runs get a minimal env: resolve the toolchain explicitly.
export PATH="$HOME/.elan/bin:/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin"
cd /Volumes/Substrate-1/bigo/sssp-nlogn-lane || exit 66
LOG=${1:-p2e_r11.log}
TARGET=${2:-Submission/FibHeapProg.lean}
MAX=${LEAN_MAX_SECONDS:-5400}
TREE=$(mktemp -t p2e_tree.XXXXXX) || exit 66
trap "" TERM

alive() { case "${1:-}" in ''|*[!0-9]*) return 1;; esac; ps -p "$1" -o pid= >/dev/null 2>&1; }
snap() {
  local p=$1 k
  printf '%s\n' "$p" >> "$TREE"
  for k in $(pgrep -P "$p" 2>/dev/null); do snap "$k"; done
}
reap_tree() {
  local p
  [ -s "$TREE" ] || return 0
  sort -u -o "$TREE" "$TREE" 2>/dev/null
  for p in $(cat "$TREE"); do
    if alive "$p"; then kill -KILL "$p" 2>/dev/null; echo "$p" >> "$TREE.reaped"; fi
  done
}

# ---- one writer per log; stale locks broken by LIVENESS ----
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
cleanup() { rm -rf "$LOCK"; }
trap cleanup EXIT

# ---- resolve the lake env ONCE (no elaboration, sub-second), then drop lake ----
LEAN_PATH_RESOLVED=$(lake env printenv LEAN_PATH 2>/dev/null)
if [ -z "${LEAN_PATH_RESOLVED:-}" ]; then
  printf 'FATAL: could not resolve LEAN_PATH from lake\n' >> "$LOG"
  printf 'exit=66\n' >> "$LOG"
  exit 66
fi
printf 'p2e wrapper: lean invoked directly (no lake in the tree); target=%s max=%ss\n' \
  "$TARGET" "$MAX" >> "$LOG"

LEAN_BIN=$(command -v lean)
# -M is OPT-IN. An 1800 MB cap was MEASURED to abort this module (exit 134,
# `lean::memory_exception ... at 'interpreter'`), so the module's floor is
# above 1.8 GB while the cull line behaves as ~2 GB: there is no usable cap.
# Pass LEAN_MEM_MB=<mb> only when a specific ceiling demands one.
MEM_FLAG=()
if [ -n "${LEAN_MEM_MB:-}" ]; then MEM_FLAG=(-M "$LEAN_MEM_MB"); fi
LEAN_PATH="$LEAN_PATH_RESOLVED" "$LEAN_BIN" -j1 "${MEM_FLAG[@]+"${MEM_FLAG[@]}"}" "${TARGET}" -o "${OLEAN_OUT:-/tmp/fhp_check.olean}" >> "$LOG" 2>&1 &
child=$!
printf '%s\n' "$child" > "$TREE"

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

reap_tree
if [ -s "$TREE.reaped" ]; then
  printf 'R2125609450 ORPHAN-GUARD: child %s exited rc=%s but its descendants were still alive; SIGKILLed: %s\n' \
    "$child" "$rc" "$(tr '\n' ' ' < "$TREE.reaped")" >> "$LOG"
fi
kill "$wd" 2>/dev/null
rm -f "$TREE" "$TREE.reaped"
printf 'exit=%s cap=%ss child=%s log=%s\n' "$rc" "$MAX" "$child" "$LOG" >> "$LOG"
exit "$rc"
