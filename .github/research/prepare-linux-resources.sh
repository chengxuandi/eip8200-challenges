#!/usr/bin/env bash
# Applied research preflight for a disposable GitHub-hosted Ubuntu runner.
# The earlier runner-loss cause is UNCONFIRMED. This is resource protection,
# not a diagnosis, correctness proof, or change to the official harness.
set -euo pipefail

[[ "${GITHUB_ACTIONS:-}" == true && "${RUNNER_OS:-}" == Linux ]] || {
  echo 'Refusing resource cleanup outside a GitHub Actions Linux runner' >&2
  exit 64
}
[[ "${RUNNER_ENVIRONMENT:-}" == github-hosted ]] || {
  echo 'Refusing resource cleanup on a non-GitHub-hosted runner' >&2
  exit 64
}

date -u
free -h
df -h . "${RUNNER_TEMP:?}"
sudo swapon --show

for sdk_target in /usr/local/lib/android /usr/share/dotnet /opt/ghc /opt/hostedtoolcache/ghc; do
  [[ -e "${sdk_target}" || -L "${sdk_target}" ]] || continue
  if [[ -L "${sdk_target}" && ! -e "${sdk_target}" ]]; then
    echo "Skipping dangling SDK symlink: ${sdk_target}"
    continue
  fi
  resolved_sdk="$(realpath -e -- "${sdk_target}")"
  case "${sdk_target}:${resolved_sdk}" in
    /usr/local/lib/android:/usr/local/lib/android|\
    /usr/share/dotnet:/usr/share/dotnet|\
    /opt/ghc:/opt/ghc|\
    /opt/ghc:/opt/hostedtoolcache/ghc|\
    /opt/ghc:/opt/hostedtoolcache/ghc/*|\
    /opt/hostedtoolcache/ghc:/opt/hostedtoolcache/ghc)
      ;;
    *)
      echo "Refusing unreviewed SDK path: ${sdk_target} resolves to ${resolved_sdk}" >&2
      exit 64
      ;;
  esac
  sudo du -sh -- "${sdk_target}"
  # Constant allowlisted target, no trailing slash: remove a top-level symlink
  # without traversing it. Do not cross a mounted SDK subtree.
  sudo rm -rf --one-file-system -- "${sdk_target}"
done

runner_temp_root="$(realpath -e -- "${RUNNER_TEMP}")"
case "${runner_temp_root}" in
  /home/runner/work/_temp|/home/runner/work/_temp/*) ;;
  *)
    echo "Refusing unreviewed RUNNER_TEMP: ${runner_temp_root}" >&2
    exit 64
    ;;
esac
research_swap_file="$(realpath -m -- "${runner_temp_root}/precompile-research.swap")"
[[ "${research_swap_file}" == "${runner_temp_root}/precompile-research.swap" ]] || exit 64
[[ ! -e "${research_swap_file}" && ! -L "${research_swap_file}" ]] || {
  echo 'Refusing to overwrite an existing research swap file' >&2
  exit 64
}
free_bytes="$(df -PB1 -- "${runner_temp_root}" | awk 'NR == 2 {print $4}')"
[[ "${free_bytes}" =~ ^[0-9]+$ ]] || exit 64
required_free_bytes=$((30 * 1024 * 1024 * 1024))
if ((free_bytes >= required_free_bytes)); then
  sudo fallocate -l 8G -- "${research_swap_file}"
  sudo chmod 600 -- "${research_swap_file}"
  sudo mkswap -- "${research_swap_file}"
  if ! sudo swapon -- "${research_swap_file}"; then
    # Only the exact new file created above is removed. Other swap is untouched.
    sudo rm -f -- "${research_swap_file}"
    echo '::warning::Swap activation unavailable; no research swap was added'
  fi
else
  echo "::warning::Less than30GiB free after cleanup (${free_bytes} bytes); skipping8GiB swap"
fi

date -u
free -h
df -h . "${runner_temp_root}"
sudo swapon --show
