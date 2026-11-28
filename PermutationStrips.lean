import PermutationStrips.Conjecture
import PermutationStrips.TheoremTwo
import PermutationStrips.Schedule
import PermutationStrips.Sampling
import Lean.Util.CollectAxioms

/-!
# Certification of the strip conjecture and the sharp angular profile

`PermutationStrips.Conjecture.kaczynski_second_conjecture` gives the order of
both attained minima. `PermutationStrips.Conjecture.lower_leading_constants`
gives their liminf bounds. `PermutationStrips.Angular.sharp_angular_profile`
constructs the Euclidean length-one compact witness and gives both extremal laws.
`PermutationStrips.Angular.critical_grid_rate` gives the critical log-log loss.
`PermutationStrips.AngularBlock.exists_linear_ensemble` gives 128k paths of
exactly k shuffles and the weighted section bound 199/k at every interior height.

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
