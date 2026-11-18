import Lean

/-! Iterative form of Lean.Util.CollectAxioms. It visits the checked kernel
environment and the same declaration type/value/constructor dependencies,
without recursive retention of earlier visited sets. This command creates
no theorem or axiom and is used only to bound the audit process memory. -/
open Lean Elab Command

private def boundedKernelAxioms (root : Name) (excluded : NameSet := {}) :
    CommandElabM Unit := do
  let env ← getEnv
  unless (env.checked.get.find? root).isSome do
    throwError "unknown checked kernel constant {root}"
  let mut todo : Array Name := #[root]
  let mut visited : NameSet := {}
  let mut axioms : Array Name := #[]
  let mut cutpoints : Array Name := #[]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if !visited.contains name then
      visited := visited.insert name
      if excluded.contains name then
        cutpoints := cutpoints.push name
      else
        match env.checked.get.find? name with
        | none => pure ()
        | some (.quotInfo _) => pure ()
        | some info =>
          todo := todo ++ info.type.getUsedConstants
          if let some value := info.value? then
            todo := todo ++ value.getUsedConstants
          match info with
          | .axiomInfo _ => axioms := axioms.push name
          | .inductInfo i => todo := todo ++ i.ctors.toArray
          | _ => pure ()
  if cutpoints.isEmpty then
    logInfo m!"'{root}' depends on axioms: {axioms.qsort Name.lt |>.map MessageData.ofConstName |>.toList}"
  else
    logInfo m!"residual checked dependencies of '{root}' use axioms: {axioms.qsort Name.lt |>.map MessageData.ofConstName |>.toList}"
    logInfo m!"separately audited cutpoints: {cutpoints.qsort Name.lt |>.map MessageData.ofConstName |>.toList}"
  logInfo m!"checked kernel declarations visited: {visited.size}"

elab "#bounded_kernel_axioms " c:ident : command =>
  boundedKernelAxioms c.getId

elab "#bounded_kernel_axioms_excluding " c:ident " [" stops:ident,* "]" : command => do
  let excluded := stops.getElems.foldl (fun s n => s.insert n.getId) ({} : NameSet)
  boundedKernelAxioms c.getId excluded
