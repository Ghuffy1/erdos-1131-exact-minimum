import Lean.CoreM
import Lean.Replay
import Lean.Util.FoldConsts

open Lean

def dependencyClosure (constants : Std.HashMap Name ConstantInfo)
    (roots : List Name) : IO (Std.HashMap Name ConstantInfo) := do
  let mut pending := roots
  let mut selected : Std.HashMap Name ConstantInfo := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if selected.contains name then
      continue
    let some declaration := constants[name]?
      | throw (IO.userError s!"Missing dependency {name}")
    if declaration.isUnsafe || declaration.isPartial then
      throw (IO.userError s!"Unsafe or partial proof dependency {name}")
    selected := selected.insert name declaration
    for dependency in declaration.getUsedConstantsAsSet do
      pending := dependency :: pending
    match declaration with
    | .inductInfo info => pending := info.all ++ info.ctors ++ pending
    | .recInfo info => pending := info.all ++ pending
    | .quotInfo _ =>
      pending := [`Eq, `Quot, `Quot.mk, `Quot.lift, `Quot.ind] ++ pending
    | _ => pure ()
  return selected

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let roots := [`OriginalProblem1131.full_original_problem,
    `Erdos1131Submission.complete_problem,
    `Erdos1131.algebraicMinimum_eq_minimum,
    `Erdos1131.minimum_attained,
    `Erdos1131.boundaryPolynomial_degree]
  withImportModules #[{ module := `Challenge }] {} fun environment => do
    let selected ← dependencyClosure environment.constants.map₁ roots
    let output ← IO.getStdout
    output.putStrLn s!"Selected {selected.size} declarations in the complete proof dependency closure."
    output.flush
    let mut axioms : List Name := []
    for (name, declaration) in selected.toList do
      if declaration matches .axiomInfo _ then
        axioms := name :: axioms
        if name != `propext && name != `Classical.choice && name != `Quot.sound then
          throw (IO.userError s!"Unapproved axiom {name}")
    output.putStrLn s!"Axioms {axioms}"
    output.flush
    let checked ← (← mkEmptyEnvironment).toKernelEnv.replay selected
    for name in roots do
      if (checked.find? name).isNone then
        throw (IO.userError s!"Target missing after replay {name}")
    output.putStrLn "PASS. All selected declarations replayed into an initially empty kernel environment."
    output.flush
