#!/usr/bin/env bash
# Run the pinned official comparator against an independent statement model.
set -euo pipefail
cd "$(dirname "$0")/.."

mode="sandboxed"
if [[ "${1:-}" == "--unsandboxed" ]]; then
  mode="unsandboxed"
  shift
fi
if [[ $# -ne 0 ]]; then
  echo 'Usage: scripts/compare.sh [--unsandboxed]' >&2
  exit 2
fi
if [[ "$mode" == sandboxed ]] && ! command -v landrun >/dev/null; then
  echo 'Install landrun on Linux, or explicitly use --unsandboxed for local development.' >&2
  exit 2
fi

python3 scripts/check_project.py
comparator_rev="97ef939c9fe3f8abf93e4adb654517476da7a66f"
comparator_dir="${COMPARATOR_HOME:-$PWD/.lake/comparator-tools/comparator}"
if [[ ! -d "$comparator_dir/.git" ]]; then
  mkdir -p "$(dirname "$comparator_dir")"
  git clone --no-checkout https://github.com/leanprover/comparator.git "$comparator_dir"
  git -C "$comparator_dir" checkout --detach "$comparator_rev"
fi
if [[ "$(git -C "$comparator_dir" rev-parse HEAD)" != "$comparator_rev" ]]; then
  echo 'Comparator checkout does not match the pinned revision.' >&2
  exit 1
fi
git -C "$comparator_dir" diff --quiet HEAD --
(cd "$comparator_dir" && lake build comparator lean4export)
export PATH="$comparator_dir/.lake/build/bin:$comparator_dir/.lake/packages/lean4export/.lake/build/bin:$PATH"

if [[ "$mode" == unsandboxed ]]; then
  echo 'UNSANDBOXED: statement comparison, axiom checks and kernel replay remain enabled; process isolation is absent.' >&2
  shim_dir="$PWD/.lake/comparator-tools/unsandboxed"
  mkdir -p "$shim_dir"
  cat > "$shim_dir/landrun" <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail
# Development adapter for comparator's landrun arguments. No isolation.
while [[ $# -gt 0 ]]; do
  case "$1" in
    --ro|--rox|--rw|--rwx|--env) shift 2 ;;
    --best-effort|-ldd|-add-exec) shift ;;
    --) shift; break ;;
    -*) echo "Unsupported landrun option: $1" >&2; exit 2 ;;
    *) break ;;
  esac
done
[[ $# -gt 0 ]] || exit 2
exec "$@"
SHIM
  chmod +x "$shim_dir/landrun"
  export PATH="$shim_dir:$PATH"
fi

if [[ "$mode" == sandboxed ]]; then
  export LANDRUN_EXECUTABLE="$(command -v landrun)"
  runner_dir="$PWD/.lake/comparator-tools/sandbox-bin"
  mkdir -p "$runner_dir"
  ln -sf "$PWD/scripts/landrun-runner.sh" "$runner_dir/landrun"
  export PATH="$runner_dir:$PATH"
fi

lake env "$comparator_dir/.lake/build/bin/comparator" Verification/config.json
