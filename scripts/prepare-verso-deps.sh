#!/bin/bash

set -euo pipefail

root_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
book_dir="${root_dir}/book"

patch_lakefile() {
  local kind="$1"
  local file="$2"
  if [[ ! -f "$file" ]]; then
    echo "missing dependency lakefile: ${file}" >&2
    exit 1
  fi

  python3 - "$kind" "$file" <<'PY'
from __future__ import annotations

import pathlib
import re
import sys

kind = sys.argv[1]
path = pathlib.Path(sys.argv[2])
text = path.read_text()

text = re.sub(r"#\[[^\]]*experimental\.module[^\]]*\]", "#[]", text)

if kind in {"verso", "subverso"}:
    text = text.replace("precompileModules := false", "precompileModules := true")

if kind == "verso":
    if "roots := #[`Verso, `Verso.Instances.Deriving]" not in text:
        text = text.replace("roots := #[`Verso]", "roots := #[`Verso, `Verso.Instances.Deriving]")
elif kind == "subverso":
    if "roots := #[`SubVerso, `SubVerso.Highlighting.Messages]" not in text:
        text = text.replace(
            "roots := #[`SubVerso]",
            "roots := #[`SubVerso, `SubVerso.Highlighting.Messages]",
        )

path.write_text(text)
PY

  if rg -q --no-ignore --hidden "leanOptions := .*experimental\\.module" "$file"; then
    echo "failed to patch experimental.module in ${file}" >&2
    exit 1
  fi
  if [[ "$kind" == "verso" ]] && ! rg -q --no-ignore --hidden 'roots := #\[`Verso, `Verso\.Instances\.Deriving\]' "$file"; then
    echo "failed to patch Verso roots in ${file}" >&2
    exit 1
  fi
  if [[ "$kind" == "subverso" ]] && ! rg -q --no-ignore --hidden 'roots := #\[`SubVerso, `SubVerso\.Highlighting\.Messages\]' "$file"; then
    echo "failed to patch SubVerso roots in ${file}" >&2
    exit 1
  fi
}

precompile() {
  local src="$1"
  local out="$2"
  local outi="$3"

  mkdir -p "$(dirname "$out")" "$(dirname "$outi")"
  (cd "$book_dir" && lake env lean "$src" -o "$out" -i "$outi")
}

patch_lakefile "verso" "${book_dir}/.lake/packages/verso/lakefile.lean"
patch_lakefile "subverso" "${book_dir}/.lake/packages/subverso/lakefile.lean"
patch_lakefile "md4lean" "${book_dir}/.lake/packages/MD4Lean/lakefile.lean"

precompile ".lake/packages/verso/src/verso/Verso/Instances/Deriving.lean" \
  ".lake/packages/verso/.lake/build/lib/lean/Verso/Instances/Deriving.olean" \
  ".lake/packages/verso/.lake/build/lib/lean/Verso/Instances/Deriving.ilean"

precompile ".lake/packages/subverso/src/SubVerso/Compat.lean" \
  ".lake/packages/subverso/.lake/build/lib/lean/SubVerso/Compat.olean" \
  ".lake/packages/subverso/.lake/build/lib/lean/SubVerso/Compat.ilean"

precompile ".lake/packages/subverso/src/SubVerso/Highlighting/Messages.lean" \
  ".lake/packages/subverso/.lake/build/lib/lean/SubVerso/Highlighting/Messages.olean" \
  ".lake/packages/subverso/.lake/build/lib/lean/SubVerso/Highlighting/Messages.ilean"
