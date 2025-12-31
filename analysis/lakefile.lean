import Lake
open Lake DSL

package «Analysis» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
    -- ⟨`doc.verso, true⟩  -- Temporarily disabled to verify code compiles
  ]
  -- Settings applied only to command line builds
  moreLeanArgs := #[]

-- Require Mathlib (the comprehensive library of mathematics in Lean)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

-- This library is needed to build the online version.
-- If ../book/lakefile.lean requires verso @ "v4.X.Y", then this line should require
-- subverso @ "verso-v4.X.Y".
-- Pinned to match book's verso (795bc01) which uses this subverso version.
require subverso from git "https://github.com/leanprover/subverso" @ "519b262cfc93634f904c9fb0992a45377ee49a9d"

-- This library is needed to build the online version.
require MD4Lean from git "https://github.com/acmepjz/md4lean" @ "main"

@[default_target]
lean_lib «Analysis» where
  -- add any library configuration options here

lean_exe "literate-extract" where
  root := `LiterateExtract
  supportInterpreter := true

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"


module_facet literate mod : System.FilePath := do
  let ws ← getWorkspace

  let exeJob ← «literate-extract».fetch
  let modJob ← mod.olean.fetch

  let buildDir := ws.root.buildDir
  let hlFile := mod.filePath (buildDir / "literate") "json"

  exeJob.bindM fun exeFile =>
    modJob.mapM fun _oleanPath => do
      buildFileUnlessUpToDate' (text := true) hlFile <|
        proc {
          cmd := exeFile.toString
          args :=  #[mod.name.toString, hlFile.toString]
          env := ← getAugmentedEnv
        }
      pure hlFile

library_facet literate lib : Array System.FilePath := do
  let mods ← (← lib.modules.fetch).await
  let modJobs ← mods.mapM (·.facet `literate |>.fetch)
  let out ← modJobs.mapM (·.await)
  pure (.pure out)
