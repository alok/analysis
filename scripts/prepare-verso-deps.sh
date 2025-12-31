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
    text = text.replace("precompileModules := true", "precompileModules := false")

if kind == "verso":
    if "roots := #[`Verso, `Verso.Instances.Deriving, `Verso.BEq]" not in text:
        text = text.replace(
            "roots := #[`Verso, `Verso.Instances.Deriving]",
            "roots := #[`Verso, `Verso.Instances.Deriving, `Verso.BEq]",
        )
        text = text.replace("roots := #[`Verso]", "roots := #[`Verso, `Verso.Instances.Deriving, `Verso.BEq]")
    text = text.replace(
        "@[default_target]\nlean_lib VersoLiterate where",
        "lean_lib VersoLiterate where",
    )
    text = text.replace(
        "@[default_target]\nlean_exe «verso-literate» where",
        "lean_exe «verso-literate» where",
    )
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
  if [[ "$kind" == "verso" ]] && ! rg -q --no-ignore --hidden 'roots := #\[`Verso, `Verso\.Instances\.Deriving, `Verso\.BEq\]' "$file"; then
    echo "failed to patch Verso roots in ${file}" >&2
    exit 1
  fi
  if [[ "$kind" == "subverso" ]] && ! rg -q --no-ignore --hidden 'roots := #\[`SubVerso, `SubVerso\.Highlighting\.Messages\]' "$file"; then
    echo "failed to patch SubVerso roots in ${file}" >&2
    exit 1
  fi
}

patch_verso_code() {
  local file="$1"
  if [[ ! -f "$file" ]]; then
    echo "missing verso code file: ${file}" >&2
    exit 1
  fi

  python3 - "$file" <<'PY'
from __future__ import annotations

import pathlib
import sys

path = pathlib.Path(sys.argv[1])
text = path.read_text()

# Drop external code support to avoid Lean segfaults when compiling Verso.Code.External.Files.
text = text.replace("public import Verso.Code.External\n", "")

path.write_text(text)
PY

  if rg -q --no-ignore --hidden "Verso\\.Code\\.External" "$file"; then
    echo "failed to remove Verso.Code.External import in ${file}" >&2
    exit 1
  fi
}

patch_verso_literate_exported() {
  local file="$1"
  if [[ ! -f "$file" ]]; then
    echo "missing verso literate exported file: ${file}" >&2
    exit 1
  fi

  python3 - "$file" <<'PY'
from __future__ import annotations

import pathlib
import sys

path = pathlib.Path(sys.argv[1])
text = path.read_text()

if "import MD4Lean\n" not in text:
    marker = "import Lean.DocString.Extension\n"
    if marker in text:
        text = text.replace(marker, marker + "import MD4Lean\n")
    else:
        text = text.replace("import Lean.Data.Json\n", "import Lean.Data.Json\nimport MD4Lean\n")

path.write_text(text)
PY

  if ! rg -q --no-ignore --hidden "import MD4Lean" "$file"; then
    echo "failed to add MD4Lean import in ${file}" >&2
    exit 1
  fi
}

patch_verso_blog_root() {
  local file="$1"
  if [[ ! -f "$file" ]]; then
    echo "missing verso blog root file: ${file}" >&2
    exit 1
  fi

  python3 - "$file" <<'PY'
from __future__ import annotations

import pathlib
import re
import sys

path = pathlib.Path(sys.argv[1])
text = path.read_text()

text = re.sub(r"^import VersoBlog\\.Generate\\n", "", text, flags=re.M)
text = re.sub(r"^import VersoBlog\\.LiterateModuleDocs\\n", "", text, flags=re.M)
text = re.sub(r"^import VersoBlog\\.Theme\\n", "", text, flags=re.M)

marker = "\nopen Template in\n"
if marker in text:
    text = text.split(marker, 1)[0].rstrip() + "\n"

path.write_text(text)
PY
}

patch_verso_blog_theme() {
  local file="$1"
  if [[ ! -f "$file" ]]; then
    echo "missing verso blog theme file: ${file}" >&2
    exit 1
  fi

  python3 - "$file" <<'PY'
from __future__ import annotations

import pathlib
import sys

path = pathlib.Path(sys.argv[1])

path.write_text("""/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoBlog.Site
import VersoBlog.Template

open Verso.Genre.Blog Template
open Verso Doc Output Html

namespace Verso.Genre.Blog

structure Template.Override where
  template : Template
  params : Params → Params

/--
A specification of how to render a site.
-/
structure Theme where
  primaryTemplate : Template
  pageTemplate : Template
  postTemplate : Template
  archiveEntryTemplate : Template
  categoryTemplate : Template
  adHocTemplates : Array String → Option Template.Override := fun _ => none

namespace Theme

def dirLinks : Site → TemplateM (Array Html)
  | _ => pure #[]

end Theme
""")
PY
}

patch_verso_expander_attribute() {
  local file="$1"
  if [[ ! -f "$file" ]]; then
    echo "missing expander attribute file: ${file}" >&2
    exit 1
  fi

  python3 - "$file" <<'PY'
from __future__ import annotations

import pathlib
import sys

path = pathlib.Path(sys.argv[1])

path.write_text("""/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Lean.Elab.InfoTree.Main
public import Lean.KeyedDeclsAttribute

namespace Verso.Doc.Elab

open Lean

unsafe def mkDocExpanderAttrUnsafe (attrName typeName : Name) (descr : String) (attrDeclName : Name) : IO (KeyedDeclsAttribute α) :=
  KeyedDeclsAttribute.init {
    name := attrName,
    descr := descr,
    valueTypeName := typeName,
    evalKey := fun _ stx => do
      Elab.realizeGlobalConstNoOverloadWithInfo (← Attribute.Builtin.getIdent stx)
  } attrDeclName

@[implemented_by mkDocExpanderAttrUnsafe]
opaque mkDocExpanderAttributeSafe (attrName typeName : Name) (desc : String) (attrDeclName : Name) : IO (KeyedDeclsAttribute α)

public def mkDocExpanderAttribute (attrName typeName : Name) (desc : String) (attrDeclName : Name := by exact decl_name%) : IO (KeyedDeclsAttribute α) :=
  mkDocExpanderAttributeSafe attrName typeName desc attrDeclName

unsafe def mkUncheckedDocExpanderAttrUnsafe (attrName typeName : Name) (descr : String) (attrDeclName : Name) : IO (KeyedDeclsAttribute α) :=
  KeyedDeclsAttribute.init {
    name := attrName,
    descr := descr,
    valueTypeName := typeName,
    evalKey := fun _ stx => do
      return (← Attribute.Builtin.getIdent stx).getId
  } attrDeclName

@[implemented_by mkUncheckedDocExpanderAttrUnsafe]
opaque mkUncheckedDocExpanderAttributeSafe (attrName typeName : Name) (desc : String) (attrDeclName : Name) : IO (KeyedDeclsAttribute α)

public def mkUncheckedDocExpanderAttribute (attrName typeName : Name) (desc : String) (attrDeclName : Name := by exact decl_name%) : IO (KeyedDeclsAttribute α) :=
  mkUncheckedDocExpanderAttributeSafe attrName typeName desc attrDeclName
""")
PY
}

precompile() {
  local src="$1"
  local out="$2"
  local outi="$3"

  (
    cd "$book_dir"
    mkdir -p "$(dirname "$out")" "$(dirname "$outi")"
    lake env lean "$src" -o "$out" -i "$outi"
  )
}

patch_lakefile "verso" "${book_dir}/.lake/packages/verso/lakefile.lean"
patch_lakefile "subverso" "${book_dir}/.lake/packages/subverso/lakefile.lean"
patch_lakefile "md4lean" "${book_dir}/.lake/packages/MD4Lean/lakefile.lean"
patch_verso_code "${book_dir}/.lake/packages/verso/src/verso/Verso/Code.lean"
patch_verso_literate_exported "${book_dir}/.lake/packages/verso/src/verso-literate/VersoLiterate/Exported.lean"
patch_verso_blog_root "${book_dir}/.lake/packages/verso/src/verso-blog/VersoBlog.lean"
patch_verso_blog_theme "${book_dir}/.lake/packages/verso/src/verso-blog/VersoBlog/Theme.lean"
patch_verso_expander_attribute "${book_dir}/.lake/packages/verso/src/verso/Verso/Doc/Elab/ExpanderAttribute.lean"

precompile ".lake/packages/verso/src/verso/Verso/Instances/Deriving.lean" \
  ".lake/packages/verso/.lake/build/lib/lean/Verso/Instances/Deriving.olean" \
  ".lake/packages/verso/.lake/build/lib/lean/Verso/Instances/Deriving.ilean"

precompile ".lake/packages/verso/src/verso/Verso/Instances.lean" \
  ".lake/packages/verso/.lake/build/lib/lean/Verso/Instances.olean" \
  ".lake/packages/verso/.lake/build/lib/lean/Verso/Instances.ilean"

precompile ".lake/packages/verso/src/verso/Verso/Method.lean" \
  ".lake/packages/verso/.lake/build/lib/lean/Verso/Method.olean" \
  ".lake/packages/verso/.lake/build/lib/lean/Verso/Method.ilean"

precompile ".lake/packages/verso/src/verso/Verso/SyntaxUtils.lean" \
  ".lake/packages/verso/.lake/build/lib/lean/Verso/SyntaxUtils.olean" \
  ".lake/packages/verso/.lake/build/lib/lean/Verso/SyntaxUtils.ilean"

precompile ".lake/packages/verso/src/verso/Verso/Parser/Lean.lean" \
  ".lake/packages/verso/.lake/build/lib/lean/Verso/Parser/Lean.olean" \
  ".lake/packages/verso/.lake/build/lib/lean/Verso/Parser/Lean.ilean"

precompile ".lake/packages/verso/src/verso/Verso/Parser.lean" \
  ".lake/packages/verso/.lake/build/lib/lean/Verso/Parser.olean" \
  ".lake/packages/verso/.lake/build/lib/lean/Verso/Parser.ilean"

precompile ".lake/packages/verso/src/verso/Verso/Doc/Elab/ExpanderAttribute.lean" \
  ".lake/packages/verso/.lake/build/lib/lean/Verso/Doc/Elab/ExpanderAttribute.olean" \
  ".lake/packages/verso/.lake/build/lib/lean/Verso/Doc/Elab/ExpanderAttribute.ilean"

precompile ".lake/packages/subverso/src/SubVerso/Compat.lean" \
  ".lake/packages/subverso/.lake/build/lib/lean/SubVerso/Compat.olean" \
  ".lake/packages/subverso/.lake/build/lib/lean/SubVerso/Compat.ilean"

precompile ".lake/packages/subverso/src/SubVerso/Highlighting/Messages.lean" \
  ".lake/packages/subverso/.lake/build/lib/lean/SubVerso/Highlighting/Messages.olean" \
  ".lake/packages/subverso/.lake/build/lib/lean/SubVerso/Highlighting/Messages.ilean"
