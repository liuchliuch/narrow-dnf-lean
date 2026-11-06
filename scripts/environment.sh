#!/usr/bin/env bash
# Check Git before Lake can interpret a failed remote lookup as a URL change.
if [[ "$(uname -s)" == Darwin && -z "${DEVELOPER_DIR:-}" && -d /Library/Developer/CommandLineTools ]]; then
  export DEVELOPER_DIR=/Library/Developer/CommandLineTools
fi
if ! git --version >/dev/null; then
  return 1 2>/dev/null || exit 1
fi
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
