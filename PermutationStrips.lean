import PermutationStrips.Conjecture
import PermutationStrips.Schedule
import PermutationStrips.Sampling
import Lean.Util.CollectAxioms

/-!
# Certification of Kaczynski's finite strip conjecture

`PermutationStrips.Conjecture.kaczynski_second_conjecture` gives the order of
both attained minima. `PermutationStrips.Conjecture.lower_leading_constants`
gives their liminf bounds. The sampling and schedule modules verify additional
estimates in the angular construction.

The default build checks the transitive dependencies of every public declaration
in the project namespace against Lean's three standard axioms.
-/

run_cmd
  let env ← Lean.getEnv
  let check : Lean.CollectAxioms.M Unit := do
    for (name, _) in env.constants.toList do
      if `PermutationStrips |>.isPrefixOf name then
        Lean.CollectAxioms.collect name
  let (_, result) := (check.run env).run {}
  for ax in result.axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom in the strip proofs: {ax}"
