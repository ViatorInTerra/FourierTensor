import Lake
import Lean.Data.Json
open Lake DSL

package FourierTensor where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

lean_lib FourierTensorSupport where
  srcDir := "support"
  roots := #[`FourierSchur, `MyProject, `vendor, `work_in_progress]
  globs := #[`FourierSchur.+, `MyProject.+, `vendor.+, `work_in_progress.+]

@[default_target]
lean_lib FourierTensor where
  globs := #[`FourierTensor, `FourierTensor.+]
  -- The center-cache assembly proof needs a larger worker stack.
  moreLeanArgs := #["--tstack", "32768"]

/-- Check module ownership and source availability without compiling proofs. -/
script checkTargets do
  let workspace ← getWorkspace
  let root := workspace.root.dir
  let source ← IO.FS.readFile (root / "provenance/local_source_manifest.json")
  let manifest ← IO.ofExcept (Lean.Json.parse source)
  let authored ← IO.ofExcept (manifest.getObjValAs? (Array Lean.Json) "authored_modules")
  let copied ← IO.ofExcept (manifest.getObjValAs? (Array Lean.Json) "copied_modules")
  for entry in authored ++ copied do
    let name := (← IO.ofExcept (entry.getObjValAs? String "module")).toName
    let path := root / (← IO.ofExcept (entry.getObjValAs? String "path"))
    let some resolvedModule := workspace.findModule? name
      | throw <| IO.userError s!"No Lake library owns module {name}"
    unless ← resolvedModule.leanFile.pathExists do
      throw <| IO.userError s!"Missing source for module {name}: {resolvedModule.leanFile}"
    unless (← IO.FS.realPath resolvedModule.leanFile) == (← IO.FS.realPath path) do
      throw <| IO.userError s!"Lake resolves {name} to {resolvedModule.leanFile}, expected {path}"
  IO.println s!"Resolved {authored.size + copied.size} local module targets in the pinned Lake workspace."
  return 0
