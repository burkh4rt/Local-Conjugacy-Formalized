module

public import Lean

@[expose] public section

open Lean

instance : MonadEnv (StateM Environment) where
  getEnv := get
  modifyEnv := modify

def sameExpr (c s : ConstantInfo) (ce se : Expr) : Bool :=
  c.levelParams == s.levelParams && ce == se

/-- A local consistency check, not a substitute for Palomar's sandboxed
Comparator and NanoDa replay. Loads the two modules in separate environments. -/
unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let challenge ← importModules #[{ module := `Challenge }] {}
  let visibleSolution ← importModules #[{ module := `Solution }] {}
  -- Include the private proof declarations of every local module as well.
  let localImports : Array Import := visibleSolution.header.moduleNames.filterMap fun name =>
    if name.toString.startsWith "LocalConjugacy" then
      some { module := name, importAll := true }
    else none
  enableInitializersExecution
  let solution ← importModules (localImports.push { module := `Solution, importAll := true })
    {} (loadExts := true)
  let names := [
    `LocalConjugacy.theorem_1_1, `LocalConjugacy.lemma_1_2,
    `LocalConjugacy.corollary_1_3, `LocalConjugacy.corollary_1_4,
    `LocalConjugacy.proposition_2_1, `LocalConjugacy.proposition_2_2,
    `LocalConjugacy.proposition_2_3, `LocalConjugacy.proposition_3_1,
    `LocalConjugacy.proposition_3_2, `LocalConjugacy.proposition_4_1,
    `LocalConjugacy.proposition_4_2, `LocalConjugacy.counterexample_quaternion,
    `LocalConjugacy.counterexample_heisenberg]
  for name in names do
    let c := challenge.find? name
    let s := solution.find? name
    let same := match c, s with
      | some c, some s =>
        sameExpr c s c.type s.type
      | _, _ => false
    let axs := (collectAxioms name : StateM Environment (Array Name)).run' solution
    IO.println (Json.mkObj [
      ("name", toJson name.toString), ("challenge_present", toJson c.isSome),
      ("solution_present", toJson s.isSome), ("same_type", toJson same),
      ("axioms", toJson (axs.map Name.toString))]).compress
  for (name, c) in challenge.constants.toList do
    if name.toString.startsWith "LocalConjugacy." && !c.isTheorem then
      let s := solution.find? name
      let same := match s with
        | some s => sameExpr c s c.type s.type && match c.value?, s.value? with
          | some cv, some sv => sameExpr c s cv sv
          | none, none => true
          | _, _ => false
        | none => false
      IO.println (Json.mkObj [
        ("definition", toJson name.toString), ("same_definition", toJson same)]).compress
  for (name, c) in challenge.constants.toList do
    if name.toString.startsWith "LocalConjugacy." && c.isTheorem && !names.contains name then
      let s := solution.find? name
      let same := match s with
        | some s => c.toConstantVal == s.toConstantVal && c.value? true == s.value? true
        | none => false
      IO.println (Json.mkObj [
        ("shared_theorem", toJson name.toString), ("same_proof", toJson same)]).compress
  for (name, info) in solution.constants.toList do
    if (name.toString.startsWith "LocalConjugacy." ||
        name.toString.startsWith "_private.LocalConjugacy.") && info.isTheorem then
      let axs := (collectAxioms name : StateM Environment (Array Name)).run' solution
      IO.println (Json.mkObj [
        ("supporting_theorem", toJson name.toString),
        ("axioms", toJson (axs.map Name.toString))]).compress
