#!/usr/bin/env bash
# Run the unchanged official setup command with research resource telemetry.
# Preserve its exit code; resource samples never establish proof acceptance.
set -euo pipefail

mkdir -p research-results
official_setup_pid=""
telemetry_pid=""

stop_telemetry() {
  if [[ -n "${telemetry_pid}" ]]; then
    kill "${telemetry_pid}" 2>/dev/null || true
    wait "${telemetry_pid}" 2>/dev/null || true
  fi
}
trap stop_telemetry EXIT

emit_sample() {
  date -u
  free -h || true
  df -h . "${RUNNER_TEMP:?}" || true
  ps -eo pid,ppid,stat,%cpu,%mem,rss,etime,comm --sort=-rss | head -n12 || true
}

telemetry_loop() {
  local pause_pid=""
  stop_pause() {
    if [[ -n "${pause_pid}" ]]; then
      kill "${pause_pid}" 2>/dev/null || true
      wait "${pause_pid}" 2>/dev/null || true
    fi
  }
  stop_loop() {
    stop_pause
    exit 0
  }
  trap stop_loop TERM INT
  while kill -0 "${official_setup_pid}" 2>/dev/null; do
    emit_sample
    sleep 60 &
    pause_pid=$!
    wait "${pause_pid}" || true
    pause_pid=""
  done
}

( ./setup.sh modexp 2>&1 | tee research-results/setup.log ) &
official_setup_pid=$!
telemetry_loop > >(tee research-results/resources.log) 2>&1 &
telemetry_pid=$!

set +e
wait "${official_setup_pid}"
setup_status=$?
set -e
printf 'official_setup_exit=%s\n' "${setup_status}" | tee -a research-results/resources.log
exit "${setup_status}"
