#!/usr/bin/env bash
set -euo pipefail

ROOT="$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)"
cd "$ROOT"

readonly TIMEOUT_SECONDS=600
readonly MEMORY_LIMIT_BYTES=17179869184
readonly HEAVY_LOCK=/run/lock/overlap-heavy.lock

RUN_ID="${OVERLAP_RUN_ID:-$(date -u +%Y%m%dT%H%M%SZ)}"
RESULT_ROOT="${OVERLAP_RESULTS:-benchmarks/results}"
SIZES=(128 256 512 1024 2048)
OFFSET=3136
RUN_KERNEL=1
RUN_SCALING=1
PACKED_ONLY=0
WITNESS_ONLY=0

usage() {
  cat <<'EOF'
usage: benchmarks/linux/run.sh [options]

Options:
  --kernel-only          Run only the clean project build and module replays.
  --scaling-only         Run only the paired direct/packed benchmarks.
  --packed-only          With scaling, skip the Direct path and measure Packed only.
  --witness-only         Reproduce the older eight-module macOS command sequence.
  --sizes "LIST"         Space-separated cell counts (default: 128 256 512 1024 2048).
  --offset N             Start of the contiguous certificate slice (default: 3136).
  --run-id ID            Use a fixed result identifier instead of the current UTC time.
  -h, --help             Show this help.

Every child process is serialized by a host-wide lock, capped at 600 seconds,
and charged to a 16 GiB cgroup with swap disabled. Launch this script from a
remote tmux session. It never writes a host address, account, or credential.
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --kernel-only)
      RUN_KERNEL=1
      RUN_SCALING=0
      shift
      ;;
    --scaling-only)
      RUN_KERNEL=0
      RUN_SCALING=1
      shift
      ;;
    --packed-only)
      PACKED_ONLY=1
      shift
      ;;
    --witness-only)
      WITNESS_ONLY=1
      RUN_KERNEL=1
      RUN_SCALING=0
      shift
      ;;
    --sizes)
      [[ $# -ge 2 ]] || { printf '%s requires a value\n' "$1" >&2; exit 2; }
      read -r -a SIZES <<< "$2"
      shift 2
      ;;
    --offset)
      [[ $# -ge 2 ]] || { printf '%s requires a value\n' "$1" >&2; exit 2; }
      OFFSET="$2"
      shift 2
      ;;
    --run-id)
      [[ $# -ge 2 ]] || { printf '%s requires a value\n' "$1" >&2; exit 2; }
      RUN_ID="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      printf 'unknown option: %s\n' "$1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if [[ ! "$RUN_ID" =~ ^[A-Za-z0-9._-]+$ ]]; then
  printf 'invalid run id: %s\n' "$RUN_ID" >&2
  exit 2
fi
if [[ ! "$OFFSET" =~ ^[0-9]+$ ]]; then
  printf 'offset must be a non-negative integer\n' >&2
  exit 2
fi
for cells in "${SIZES[@]}"; do
  if [[ ! "$cells" =~ ^[0-9]+$ ]] || (( cells < 2 )); then
    printf 'invalid size: %s\n' "$cells" >&2
    exit 2
  fi
done

RUN_DIR="$RESULT_ROOT/linux-$RUN_ID"
if [[ -e "$RUN_DIR" ]]; then
  printf 'result directory already exists: %s\n' "$RUN_DIR" >&2
  exit 2
fi
mkdir -p "$RUN_DIR"/{logs,time,cgroups,generated/BenchmarksLinux}

unset GIT_CONFIG_COUNT
export LC_ALL=C
export TZ=UTC
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
ulimit -s unlimited 2>/dev/null || ulimit -s 131072
if [[ -n "${HOME:-}" && -d "$HOME/.elan/bin" ]]; then
  export PATH="$HOME/.elan/bin:${PATH:-/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin}"
else
  export PATH="${PATH:-/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin}"
fi

for tool in lake lean jq flock timeout systemd-run; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf 'missing required command: %s\n' "$tool" >&2
    exit 69
  fi
done
if [[ ! -x /usr/bin/time ]]; then
  printf 'missing required command: /usr/bin/time\n' >&2
  exit 69
fi

exec 9>"$HEAVY_LOCK"
if ! flock -n 9; then
  printf 'another overlap benchmark holds %s\n' "$HEAVY_LOCK" >&2
  exit 75
fi

cgroup_path="$(awk -F: '$1 == "0" {print $3}' /proc/self/cgroup)"
host_id="$(hostname)"
nearest_cgroup_value() {
  local name="$1"
  local current="$cgroup_path"
  while [[ -n "$current" ]]; do
    if [[ -r "/sys/fs/cgroup${current}/${name}" ]]; then
      tr ' ' ',' < "/sys/fs/cgroup${current}/${name}"
      return 0
    fi
    current="${current%/*}"
  done
  printf 'unavailable'
}

memory_kib="$(awk '/^MemTotal:/ {print $2}' /proc/meminfo)"
disk_bytes="$(df -B1 --output=size / | awk 'NR == 2 {print $1}')"
disk_available_bytes="$(df -B1 --output=avail / | awk 'NR == 2 {print $1}')"
cpu_model="$(lscpu | awk -F: '/^Model name:/ {sub(/^[[:space:]]+/, "", $2); print $2; exit}')"
pretty_name="$(. /etc/os-release; printf '%s' "$PRETTY_NAME")"

cat > "$RUN_DIR/environment.tsv" <<EOF
field	value	unit_or_note
run_id	$RUN_ID	UTC
os	$pretty_name	-
kernel	$(uname -r)	-
architecture	$(uname -m)	-
cpu_model	$cpu_model	-
logical_cpus	$(nproc)	online CPUs
cpu_cores	$(lscpu | awk -F: '/^Core\(s\) per socket:/ {gsub(/ /, "", $2); print $2}')	per socket
threads_per_core	$(lscpu | awk -F: '/^Thread\(s\) per core:/ {gsub(/ /, "", $2); print $2}')	-
hardware_memory_bytes	$((memory_kib * 1024))	/proc/meminfo MemTotal
cgroup_cpu_max	$(nearest_cgroup_value cpu.max)	quota period
cgroup_cpuset_effective	$(cat /sys/fs/cgroup/cpuset.cpus.effective)	hardware cpuset
cgroup_memory_max	$(nearest_cgroup_value memory.max)	bytes or max
cgroup_memory_high	$(nearest_cgroup_value memory.high)	bytes or max
disk_filesystem_bytes	$disk_bytes	/
disk_available_bytes	$disk_available_bytes	/
lean_version	$(lean --version)	-
lake_version	$(lake --version)	-
python_version	$(python3 --version 2>&1)	-
timeout_seconds	$TIMEOUT_SECONDS	hard per process
memory_limit_bytes	$MEMORY_LIMIT_BYTES	hard per process, swap disabled
lean_num_threads	$LEAN_NUM_THREADS	environment
soft_stack_kib	$(ulimit -s)	inherited by every capped child
slice_offset	$OFFSET	zero-based construction index
EOF

printf 'run_id\tphase\tsize_cells\tmode\tstatus\texit_status\twall_seconds\tuser_seconds\tsystem_seconds\tcpu_percent\tmax_rss_kib\traw_log\ttime_log\tcgroup_log\tcgroup_memory_peak_bytes\tcgroup_cpu_usage_usec\tcgroup_pids_peak\n' \
  > "$RUN_DIR/measurements.tsv"
printf 'size_cells\tdirect_status\tpacked_status\tdirect_phase\tpacked_phase\tdetail\n' \
  > "$RUN_DIR/pair_summary.tsv"

sequence=0
critical_failure=0
LAST_STATUS=failed
LAST_PHASE=unknown

time_to_seconds() {
  local raw="$1"
  awk -F '[:.]' '
    NF == 3 {printf "%.6f", $1 * 60 + $2 "." $3; exit}
    NF == 4 {printf "%.6f", $1 * 3600 + $2 * 60 + $3 "." $4; exit}
    {print ""}
  ' <<< "$raw"
}

capped_run() {
  local phase="$1"
  local size="$2"
  local mode="$3"
  shift 3

  LAST_STATUS=failed
  LAST_PHASE="$phase"
  sequence=$((sequence + 1))
  local stem
  stem="$(printf '%03d-%s-%s%s' "$sequence" "$phase" "$mode" "$size")"
  local body="$RUN_DIR/logs/.${stem}.body"
  local systemd_log="$RUN_DIR/logs/.${stem}.systemd"
  local status_file="$RUN_DIR/logs/.${stem}.status"
  local raw_rel="logs/${stem}.log"
  local time_rel="time/${stem}.time"
  local cgroup_rel="cgroups/${stem}.events"
  local raw_path="$RUN_DIR/$raw_rel"
  local time_path="$RUN_DIR/$time_rel"
  local cgroup_log_path="$RUN_DIR/$cgroup_rel"
  local unit="overlap-${RUN_ID,,}-$(printf '%03d' "$sequence")"
  local command_text
  printf -v command_text '%q ' "$@"
  command_text="${command_text% }"

  local wrapper
  read -r -d '' wrapper <<'WRAPPER' || true
set +e
ulimit -s unlimited 2>/dev/null || ulimit -s 131072
cgroup="$(awk -F: '$1 == "0" {print $3}' /proc/self/cgroup)"
/usr/bin/time -v -o "$2" \
  timeout --verbose --signal=TERM --kill-after=30s "$1" bash -c "$6" \
  > "$3" 2>&1
child_status=$?
{
  for counter in memory.events memory.peak cpu.stat pids.peak; do
    if [[ -r "/sys/fs/cgroup${cgroup}/${counter}" ]]; then
      case "$counter" in
        memory.events|cpu.stat)
          printf '%s\n' "$counter"
          cat "/sys/fs/cgroup${cgroup}/${counter}"
          ;;
        *)
          printf '%s ' "$counter"
          cat "/sys/fs/cgroup${cgroup}/${counter}"
          printf '\n'
          ;;
      esac
    else
      printf '%s unavailable\n' "$counter"
    fi
  done
} > "$4"
printf '%s\n' "$child_status" > "$5"
exit "$child_status"
WRAPPER

  local outer_status=0
  set +e
  systemd-run \
    --quiet \
    --collect \
    --scope \
    --unit="$unit" \
    -p "MemoryMax=$MEMORY_LIMIT_BYTES" \
    -p MemorySwapMax=0 \
    -- bash -c "$wrapper" _ \
      "$TIMEOUT_SECONDS" "$time_path" "$body" "$cgroup_log_path" "$status_file" \
      "$command_text" > "$systemd_log" 2>&1
  outer_status=$?
  set -e

  local child_status="missing"
  if [[ -r "$status_file" ]]; then
    child_status="$(< "$status_file")"
  fi

  {
    printf '# command: %s\n' "$command_text"
    printf '# caps: timeout_seconds=%s memory_limit_bytes=%s swap=0\n' \
      "$TIMEOUT_SECONDS" "$MEMORY_LIMIT_BYTES"
    printf '# systemd_scope_exit=%s child_exit=%s\n\n' "$outer_status" "$child_status"
    if [[ -f "$body" ]]; then cat "$body"; fi
    printf '\n--- /usr/bin/time -v ---\n'
    if [[ -f "$time_path" ]]; then cat "$time_path"; fi
    printf '\n--- cgroup counters ---\n'
    if [[ -f "$cgroup_log_path" ]]; then cat "$cgroup_log_path"; fi
    printf '\n--- systemd-run ---\n'
    if [[ -f "$systemd_log" ]]; then cat "$systemd_log"; fi
  } > "$raw_path"

  sed -i \
    -e "s#${ROOT}#<REPO>#g" \
    -e "s#${HOME}#<HOME>#g" \
    -e "s#${host_id}#<HOST>#g" \
    "$raw_path" "$time_path" "$cgroup_log_path" "$systemd_log" 2>/dev/null || true

  local status="failed"
  local oom_kills=""
  if [[ -f "$cgroup_log_path" ]]; then
    oom_kills="$(awk '
      /^memory.events$/ {inEvents=1; next}
      /^memory.peak / {inEvents=0}
      inEvents && $1 == "oom_kill" {print $2; exit}
    ' "$cgroup_log_path")"
  fi
  if [[ "$outer_status" -eq 0 && "$child_status" == "0" ]]; then
    status="pass"
  elif [[ "${oom_kills:-0}" =~ ^[1-9][0-9]*$ ]]; then
    status="oom"
  elif grep -Eqi \
    'maximum recursion depth|deep recursion|stack overflow|recursion limit' \
    "$raw_path" 2>/dev/null; then
    status="recursion"
  elif [[ "$child_status" == "124" || "$child_status" == "137" ]] &&
    grep -Eqi 'timeout:|sending signal|killing command' "$raw_path"; then
    status="timeout"
  elif [[ "$outer_status" -ne 0 ]]; then
    status="tool_error"
  elif grep -Eqi 'error:|failed|exception' "$raw_path"; then
    status="lean_error"
  fi

  local elapsed_text="" wall_seconds="" user_seconds="" system_seconds=""
  local cpu_percent="" max_rss_kib=""
  local cgroup_memory_peak_bytes="" cgroup_cpu_usage_usec="" cgroup_pids_peak=""
  if [[ -f "$time_path" ]]; then
    elapsed_text="$(awk -F': ' '/Elapsed \(wall clock\)/ {print $NF; exit}' "$time_path")"
    wall_seconds="$(time_to_seconds "$elapsed_text")"
    user_seconds="$(awk -F': ' '/User time/ {print $NF; exit}' "$time_path")"
    system_seconds="$(awk -F': ' '/System time/ {print $NF; exit}' "$time_path")"
    cpu_percent="$(awk -F': ' '/Percent of CPU/ {gsub(/%/, "", $NF); print $NF; exit}' "$time_path")"
    max_rss_kib="$(awk -F': ' '/Maximum resident set size/ {print $NF; exit}' "$time_path")"
  fi
  if [[ -f "$cgroup_log_path" ]]; then
    cgroup_memory_peak_bytes="$(awk '
      $1 == "memory.peak" {print $2; exit}
    ' "$cgroup_log_path")"
    cgroup_cpu_usage_usec="$(awk '
      /^cpu.stat$/ {inCPU=1; next}
      /^pids.peak / {inCPU=0}
      inCPU && $1 == "usage_usec" {print $2; exit}
    ' "$cgroup_log_path")"
    cgroup_pids_peak="$(awk '
      $1 == "pids.peak" {print $2; exit}
    ' "$cgroup_log_path")"
  fi
  if [[ "$status" == "timeout" && -z "$wall_seconds" ]]; then
    wall_seconds="$TIMEOUT_SECONDS"
  fi
  if [[ "$status" == "timeout" || "$status" == "oom" ]]; then
    max_rss_kib=""
    cpu_percent=""
    user_seconds=""
    system_seconds=""
  fi

  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$RUN_ID" "$phase" "$size" "$mode" "$status" "${child_status}" \
    "${wall_seconds:-}" "${user_seconds:-}" "${system_seconds:-}" \
    "${cpu_percent:-}" "${max_rss_kib:-}" "$raw_rel" "$time_rel" "$cgroup_rel" \
    "${cgroup_memory_peak_bytes:-}" "${cgroup_cpu_usage_usec:-}" \
    "${cgroup_pids_peak:-}" \
    >> "$RUN_DIR/measurements.tsv"

  rm -f "$body" "$systemd_log" "$status_file"
  LAST_STATUS="$status"
  printf '%-12s %5s %-8s %-10s %s s %s KiB\n' \
    "$phase" "$size" "$mode" "$status" "${wall_seconds:-?}" "${max_rss_kib:-?}" >&2
  [[ "$status" == "pass" ]]
}

run_kernel_suite() {
  if (( WITNESS_ONLY )); then
    local witness_modules=(
      Tree Data Numerical Algebra AffineBridge Profile Spec Main Bench
    )
    printf '\n[kernel] legacy eight-module witness-only command sequence\n' >&2
    capped_run clean 9408 all lake clean overlap ||
      { critical_failure=1; return; }
    for module in "${witness_modules[@]}"; do
      capped_run build 9408 "$module" lake build "Overlap.$module" ||
        { critical_failure=1; return; }
    done
    capped_run clean 9408 before-default lake clean overlap ||
      { critical_failure=1; return; }
    capped_run default_build 9408 Overlap lake build ||
      { critical_failure=1; return; }
    capped_run build 9408 Bench lake build Overlap.Bench ||
      { critical_failure=1; return; }
    for module in "${witness_modules[@]}"; do
      capped_run leanchecker 9408 "$module" \
        lake env leanchecker "Overlap.$module" ||
        { critical_failure=1; return; }
    done
    capped_run leanchecker 9408 overlap_prefix lake env leanchecker Overlap || true
    printf 'aggregate_prefix\t%s\n' "$LAST_STATUS" \
      > "$RUN_DIR/aggregate_prefix_status.tsv"
    return
  fi

  local modules=(
    Tree PackedConvolution ConvolutionExample Data Numerical Algebra
    AffineBridge Profile Spec Main QuarticRounding CellApprox GridLower
    LagRounding DiscreteUpper Bench
  )
  local file module found
  while IFS= read -r file; do
    module="${file##*/}"
    module="${module%.lean}"
    found=0
    for existing in "${modules[@]}"; do
      if [[ "$existing" == "$module" ]]; then
        found=1
        break
      fi
    done
    if (( ! found )); then
      modules+=("$module")
    fi
  done < <(find Overlap -maxdepth 1 -type f -name '*.lean' -print | sort)

  printf '\n[kernel] clean project build and fresh-process replay\n' >&2
  capped_run clean 9408 all lake clean overlap ||
    { critical_failure=1; return; }
  capped_run default_build 9408 Overlap lake build ||
    { critical_failure=1; return; }
  for module in "${modules[@]}"; do
    capped_run supplemental_build 9408 "$module" \
      lake build "Overlap.$module" ||
      { critical_failure=1; return; }
  done
  for module in "${modules[@]}"; do
    capped_run leanchecker 9408 "$module" \
      lake env leanchecker "Overlap.$module" ||
      { critical_failure=1; return; }
  done
  capped_run leanchecker 9408 overlap_prefix lake env leanchecker Overlap || true
  printf 'aggregate_prefix\t%s\n' "$LAST_STATUS" \
    > "$RUN_DIR/aggregate_prefix_status.tsv"
  capped_run axioms 9408 paper_axioms lake env lean scripts/paper_axioms.lean ||
    { critical_failure=1; return; }
}

pair_status_for() {
  local size="$1"
  local mode="$2"
  awk -F '\t' -v size="$size" -v mode="$mode" '
    $3 == size && $4 == mode && $2 == "leanchecker" {print $5; found=1; exit}
    END {if (!found) print "not_run"}
  ' "$RUN_DIR/measurements.tsv"
}

run_scaling_suite() {
  printf '\n[scaling] paired direct and packed certificate checks\n' >&2
  rm -rf .lake/build/lib/lean/BenchmarksLinux
  mkdir -p .lake/build/lib/lean/BenchmarksLinux
  local direct_stopped=0
  local direct_stop_size=""
  local direct_stop_status=""
  for cells in "${SIZES[@]}"; do
    local direct_status="not_run"
    local packed_status="not_run"
    local direct_phase="not_run"
    local packed_phase="not_run"

    for mode in direct packed; do
      if [[ "$mode" == "direct" ]] &&
        (( PACKED_ONLY || direct_stopped )); then
        direct_status="not_attempted"
        direct_phase="not_attempted"
        continue
      fi
      local source="$RUN_DIR/generated/BenchmarksLinux/${mode}${cells}.lean"
      local olean=".lake/build/lib/lean/BenchmarksLinux/${mode}${cells}.olean"
      local mode_status="not_run"
      local mode_phase="not_run"
      if capped_run generation "$cells" "$mode" \
        benchmarks/linux/generate_pair.sh "$mode" "$cells" "$OFFSET" "$source"; then
        if capped_run elaboration "$cells" "$mode" \
          lake env lean --root "$RUN_DIR/generated" -o "$olean" "$source"; then
          if capped_run leanchecker "$cells" "$mode" \
            lake env leanchecker "BenchmarksLinux.${mode}${cells}"; then
            mode_status="pass"
            mode_phase="leanchecker"
          else
            mode_status="$LAST_STATUS"
            mode_phase="$LAST_PHASE"
          fi
        else
          mode_status="$LAST_STATUS"
          mode_phase="$LAST_PHASE"
        fi
      else
        mode_status="$LAST_STATUS"
        mode_phase="$LAST_PHASE"
      fi

      if [[ "$mode" == "direct" ]]; then
        direct_status="$mode_status"
        direct_phase="$mode_phase"
        if [[ "$mode_status" == "timeout" || "$mode_status" == "oom" ]]; then
          direct_stopped=1
          direct_stop_size="$cells"
          direct_stop_status="$mode_status"
        fi
      else
        packed_status="$mode_status"
        packed_phase="$mode_phase"
      fi
    done

    local detail="three fresh capped processes per mode"
    if [[ "$packed_status" != "pass" ]]; then
      critical_failure=1
      detail="packed path stopped at $packed_phase/$packed_status"
    elif [[ "$direct_status" == "not_attempted" ]]; then
      if (( PACKED_ONLY )); then
        detail="Direct disabled by --packed-only"
      else
        detail="not attempted after Direct ${direct_stop_size} reached ${direct_stop_status}"
      fi
    elif [[ "$direct_status" != "pass" ]]; then
      detail="direct path stopped at $direct_phase/$direct_status"
    fi
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$cells" "$direct_status" "$packed_status" "$direct_phase" "$packed_phase" "$detail" \
      >> "$RUN_DIR/pair_summary.tsv"
  done
}

if (( RUN_KERNEL )); then
  run_kernel_suite
fi
if (( RUN_SCALING )); then
  run_scaling_suite
fi

overall="pass"
if (( critical_failure )); then
  overall="fail"
fi
printf 'overall_status\t%s\n' "$overall" > "$RUN_DIR/overall_status.tsv"

{
  sha256sum construction.json certificate.json lean-toolchain lake-manifest.json
  sha256sum Overlap.lean
  find Overlap -maxdepth 1 -type f -name '*.lean' -print | sort | xargs sha256sum
  sha256sum scripts/paper_axioms.lean
} > "$RUN_DIR/input.sha256"

printf '\nresults: %s\noverall: %s\n' "$RUN_DIR" "$overall" >&2
exit "$critical_failure"
