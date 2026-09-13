#!/usr/bin/env bash
# One project build/batch command, at most THREE shared slots in total.
# All real jobs use the same absolute SLOT_ROOT. The default remains two.
# Change a coordinated limit only after pausing/draining old callers.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SLOT_ROOT="${BUILD_SLOT_DIR:-$ROOT/.build-slots}"
MAX="${BUILD_SLOT_MAX:-2}"
POLL="${BUILD_SLOT_POLL:-1}"
OWNER_GRACE="${BUILD_SLOT_OWNER_GRACE:-10}"

if [ "$#" -eq 0 ]; then
  echo "usage: $0 command [arg ...]" >&2
  exit 2
fi
case "$MAX" in ''|*[!0-9]*) echo "BUILD_SLOT_MAX must be a positive integer" >&2; exit 2;; esac
if [ "$MAX" -lt 1 ] || [ "$MAX" -gt 3 ]; then
  echo "BUILD_SLOT_MAX must be 1, 2 or 3 (project-wide hard limit is 3)" >&2
  exit 2
fi

mkdir -p "$SLOT_ROOT"
SLOT_ROOT="$(cd "$SLOT_ROOT" && pwd -P)"
token="$$.$(date +%s).$RANDOM"
held=""
child=""
waiting=""
alloc_held=0
snapshot=""

# A successful whole-process query distinguishes an absent PID from a
# failed query. Empty/malformed success is also rejected by finding self.
# Always refresh INSIDE the allocation lock before examining owner slots.
refresh_processes() {
  if ! snapshot="$(LC_ALL=C ps -axo pid=,pgid=,lstart= 2>/dev/null)"; then
    return 1
  fi
  [ -n "$(pid_started "$$")" ]
}

pid_started() {
  printf '%s\n' "$snapshot" | awk -v wanted="$1" '
    $1 == wanted && NF >= 7 {
      sub(/^[[:space:]]*[0-9]+[[:space:]]+[0-9]+[[:space:]]+/, "")
      sub(/[[:space:]]+$/, "")
      gsub(/[[:space:]]+/, " ")
      print
    }'
}

group_present() {
  printf '%s\n' "$snapshot" | awk -v wanted="$1" '
    $2 == wanted { found=1 } END { exit !found }'
}

release_allocator() {
  [ "$alloc_held" -eq 1 ] || return 0
  if [ "$(sed -n '1p' "$SLOT_ROOT/.allocation/token" 2>/dev/null || true)" = "$token" ]; then
    rm -f "$SLOT_ROOT/.allocation/token" "$SLOT_ROOT/.allocation/pid"
    rmdir "$SLOT_ROOT/.allocation" 2>/dev/null || true
  fi
  alloc_held=0
}

release_slot() {
  [ -n "$held" ] || return 0
  if [ "$(sed -n '1p' "$held/token" 2>/dev/null || true)" = "$token" ]; then
    local pgid phase
    pgid="$(sed -n '1p' "$held/child" 2>/dev/null || true)"
    phase="$(sed -n '1p' "$held/phase" 2>/dev/null || true)"
    if [ -z "$pgid" ] && { [ "$phase" = launching ] || [ "$phase" = running ]; }; then
      echo "build-slot: retaining slot; unresolved child launch" >&2
      held=""
      return 0
    fi
    # Preserve capacity if descendants are alive or cannot be checked.
    if [ -n "$pgid" ]; then
      if ! refresh_processes || group_present "$pgid"; then
        echo "build-slot: retaining slot; descendant group status live/unknown" >&2
        held=""
        return 0
      fi
    fi
    rm -f "$held/pid" "$held/started" "$held/token" "$held/child" "$held/phase"
    rmdir "$held" 2>/dev/null || true
  fi
  held=""
}

cleanup() {
  release_slot
  release_allocator
  if [ -n "$waiting" ]; then rm -f "$waiting"; waiting=""; fi
}

forward_signal() {
  local sig="$1" code="$2"
  trap - INT TERM HUP
  # Recover a registered job if the signal arrived before assignment of $!.
  if [ -z "$child" ]; then child="$(jobs -pr | head -n 1)"; fi
  if [ -n "$child" ]; then
    if [ -n "$held" ] && [ "$(sed -n '1p' "$held/token" 2>/dev/null || true)" = "$token" ]; then
      printf '%s\n' "$child" > "$held/child"
    fi
    kill -"$sig" -- "-$child" 2>/dev/null || kill -"$sig" "$child" 2>/dev/null || true
    wait "$child" 2>/dev/null || true
  fi
  cleanup
  exit "$code"
}

trap 'forward_signal INT 130' INT
trap 'forward_signal TERM 143' TERM
trap 'forward_signal HUP 129' HUP
trap cleanup EXIT

path_mtime() {
  local mtime_path="$1" mtime_value
  if mtime_value="$(stat -f %m "$mtime_path" 2>/dev/null)"; then
    case "$mtime_value" in
      ''|*[!0-9]*) ;;
      *) printf '%s\n' "$mtime_value"; return 0 ;;
    esac
  fi
  if mtime_value="$(stat -c %Y -- "$mtime_path" 2>/dev/null)"; then
    case "$mtime_value" in
      ''|*[!0-9]*) ;;
      *) printf '%s\n' "$mtime_value"; return 0 ;;
    esac
  fi
  return 1
}

slot_is_stale() {
  local slot="$1" owner recorded current phase pgid now mtime
  owner="$(sed -n '1p' "$slot/pid" 2>/dev/null || true)"
  case "$owner" in ''|*[!0-9]*) return 1;; esac
  current="$(pid_started "$owner")"
  recorded="$(awk 'NR == 1 { $1=$1; print }' "$slot/started" 2>/dev/null || true)"
  if [ -z "$recorded" ]; then
    # Age alone cannot establish that an unidentified/live owner is dead.
    [ -z "$current" ] || return 1
    now="$(date +%s)"
    mtime="$(path_mtime "$slot" || true)"
    [ -n "$mtime" ] || return 1
    [ $((now - mtime)) -ge "$OWNER_GRACE" ] || return 1
  elif [ -n "$current" ] && [ "$current" = "$recorded" ]; then
    return 1
  fi
  phase="$(sed -n '1p' "$slot/phase" 2>/dev/null || true)"
  pgid="$(sed -n '1p' "$slot/child" 2>/dev/null || true)"
  # A killed wrapper in an unrecorded launch window requires manual recovery.
  if [ -z "$pgid" ] && { [ "$phase" = launching ] || [ "$phase" = running ]; }; then return 1; fi
  if [ -n "$pgid" ]; then
    case "$pgid" in *[!0-9]*) return 1;; esac
    group_present "$pgid" && return 1
  fi
  return 0
}

reclaim_stale() {
  local slot="$1" stale
  slot_is_stale "$slot" || return 1
  # Serialized with allocation: a stale reader cannot rename a replacement
  # already acquired by a new live owner.
  stale="$SLOT_ROOT/.stale.$(basename "$slot").$token"
  if mv "$slot" "$stale" 2>/dev/null; then
    rm -f "$stale/pid" "$stale/started" "$stale/token" "$stale/child" "$stale/phase"
    rmdir "$stale" 2>/dev/null || true
  fi
}

if ! refresh_processes; then
  echo "build-slot: process status unavailable; refusing to start or reclaim" >&2
  exit 75
fi
waiting="$SLOT_ROOT/.waiting.$token"
printf '%s\n' "$$" > "$waiting"

while [ -z "$held" ]; do
  if [ -e "$SLOT_ROOT/.paused" ]; then sleep "$POLL"; continue; fi
  # Crashed allocation locks are fail-closed; recover only at known quiescence.
  if ! mkdir "$SLOT_ROOT/.allocation" 2>/dev/null; then sleep "$POLL"; continue; fi
  alloc_held=1
  printf '%s\n' "$token" > "$SLOT_ROOT/.allocation/token"
  printf '%s\n' "$$" > "$SLOT_ROOT/.allocation/pid"
  if [ -e "$SLOT_ROOT/.paused" ]; then release_allocator; sleep "$POLL"; continue; fi
  if ! refresh_processes; then
    echo "build-slot: process status unavailable inside allocation; refusing to reclaim" >&2
    exit 75
  fi
  i=1
  while [ "$i" -le "$MAX" ]; do
    slot="$SLOT_ROOT/slot-$i"
    if [ -d "$slot" ]; then reclaim_stale "$slot" || true; fi
    if mkdir "$slot" 2>/dev/null; then
      held="$slot"
      printf '%s\n' "$token" > "$held/token"
      printf '%s\n' "$$" > "$held/pid"
      pid_started "$$" > "$held/started"
      printf '%s\n' held > "$held/phase"
      break
    fi
    i=$((i + 1))
  done
  release_allocator
  [ -n "$held" ] || sleep "$POLL"
done

rm -f "$waiting"
waiting=""
set -m
printf '%s\n' launching > "$held/phase"
"$@" &
child=$!
printf '%s\n' "$child" > "$held/child"
printf '%s\n' running > "$held/phase"
set +e
wait "$child"
status=$?
set -e
set +m
child=""
release_slot
exit "$status"
