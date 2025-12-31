#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

apply_patch() {
  local pkg_dir="$1"
  local patch_file="$2"

  if [[ ! -d "$pkg_dir" ]]; then
    return 0
  fi

  if git -C "$pkg_dir" apply --reverse --check "$root/patches/$patch_file" >/dev/null 2>&1; then
    return 0
  fi

  git -C "$pkg_dir" apply "$root/patches/$patch_file"
}

for ws in "$root/analysis" "$root/book"; do
  apply_patch "$ws/.lake/packages/batteries" "batteries-iterators.patch"
  apply_patch "$ws/.lake/packages/aesop" "aesop-transparency-none.patch"
  apply_patch "$ws/.lake/packages/mathlib" "mathlib-assert-exists.patch"
done
