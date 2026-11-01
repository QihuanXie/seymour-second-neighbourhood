import Seymour
open Lean

/-!
Proof-term traversal for the final results of the library `Seymour`.
Run from the repository root: `lake env lean scripts/DepCheck.lean`.
It lists, for each result, the number of constants reachable from it and the number of those
that come from Mathlib's linear algebra (matrices, linear maps, submodules, ranks, polynomial
rings, fraction fields, bases, linear independence).
-/

/-- All constants reachable from `root` through types and values. -/
def reach (env : Environment) (root : Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[root]
  while stack.size > 0 do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    if let some ci := env.find? n then
      for c in ci.getUsedConstantsAsSet do
        if !visited.contains c then stack := stack.push c
  return visited

def linAlgPrefixes : List String :=
  ["Matrix.", "LinearMap.", "LinearEquiv.", "Module.finrank", "Module.rank", "Submodule.",
   "FractionRing", "MvPolynomial.", "Polynomial.", "Basis.", "LinearIndependent"]

#eval show CoreM Unit from do
  let env ← getEnv
  for root in [`Seymour.seymour, `Seymour.seymour_second_neighbourhood, `Seymour.set_version,
      `Seymour.Deletion.deletion, `Seymour.Deletion.rank_lemma, `Seymour.weighted_real,
      `Seymour.triangle_free_degree_bound, `Seymour.directed_triangle_of_semidegree] do
    let s := reach env root
    let hits := s.toList.filter fun n => linAlgPrefixes.any fun p => p.isPrefixOf n.toString
    IO.println s!"{root}: {s.size} constants; linear-algebra constants: {hits.length} {hits.take 3}"
