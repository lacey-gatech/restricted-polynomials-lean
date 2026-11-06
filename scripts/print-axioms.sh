#!/usr/bin/env bash
# Print the axioms of the main theorems and fail unless each is exactly
# [propext, Classical.choice, Quot.sound]. Run from the repository root after `lake build`.
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

probe_dir=$(mktemp -d "${TMPDIR:-/tmp}/axiom-probe.XXXXXX")
trap 'rm -rf "$probe_dir"' EXIT
probe="$probe_dir/Axioms.lean"
theorems=(
  RestrictedPolynomials.main_theorem
  RestrictedPolynomials.inverse_theorem_bklm
  RestrictedPolynomials.dimitrov
)
{
  echo "import RestrictedPolynomials"
  for theorem in "${theorems[@]}"; do
    echo "#print axioms $theorem"
  done
} > "$probe"

output=$(lake env lean "$probe")
printf '%s\n' "$output"

status=0
for theorem in "${theorems[@]}"; do
  expected="'$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]"
  if ! grep -qxF "$expected" <<< "$output"; then
    echo "error: unexpected axioms for $theorem" >&2
    status=1
  fi
done
exit "$status"
