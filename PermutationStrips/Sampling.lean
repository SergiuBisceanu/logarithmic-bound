import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-! Simultaneous approximation of mean section lengths on a finite mesh. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace PermutationStrips.Sampling

/-- The empirical mean minus its expectation at a given height. -/
noncomputable def deviation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {M : ℕ}
    (X : Fin M → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (∑ i, (X i t ω - ∫ u, X i t u ∂μ)) / M

/-- A single realization of independent bounded samples approximates the mean from above
at all mesh points. The failure probability bound is the mesh size times exp(-2 M ε²). -/
theorem exists_on_mesh {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {M : ℕ} (hM : 0 < M) (X : Fin M → ℝ → Ω → ℝ) (mesh : Finset ℝ)
    (hind : ∀ t ∈ mesh, iIndepFun (fun i => X i t) μ)
    (hmeas : ∀ i t, AEMeasurable (X i t) μ)
    (hb : ∀ i t, ∀ᵐ ω ∂μ, X i t ω ∈ Icc 0 1)
    {ε : ℝ} (he : 0 ≤ ε) (hc : (mesh.card : ℝ) * Real.exp (-2*M*ε^2) < 1) :
    ∃ ω, ∀ t ∈ mesh, deviation μ X t ω < ε := by
  classical
  let bad := fun t => {ω | ε ≤ deviation μ X t ω}
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  have tail (t : ℝ) (ht : t ∈ mesh) :
      μ.real (bad t) ≤ Real.exp (-2*M*ε^2) := by
    let Z := fun i ω => X i t ω - ∫ u, X i t u ∂μ
    have hi : iIndepFun Z μ := (hind t ht).comp
      (fun i x => x - ∫ u, X i t u ∂μ) (fun _ => measurable_id.sub_const _)
    have sg (i : Fin M) : HasSubgaussianMGF (Z i) (1/4) μ := by
      convert hasSubgaussianMGF_of_mem_Icc (hmeas i t) (hb i t) using 1; norm_num
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (s := Finset.univ) hi
      (fun i _ => sg i) (mul_nonneg he hm.le)
    change μ.real {ω | ε ≤ (∑ i, Z i ω)/(M:ℝ)} ≤ _
    simp only [le_div_iff₀ hm] at *
    convert h using 2
    simp
    field_simp
    ring
  have bound := (measureReal_biUnion_finset_le (μ := μ) mesh bad).trans
    (Finset.sum_le_sum tail)
  have small : μ.real (⋃ t ∈ mesh, bad t) < 1 := by
    exact bound.trans_lt (by simpa using hc)
  by_contra! hn
  have allbad : (⋃ t ∈ mesh, bad t) = univ := by
    apply eq_univ_of_forall
    intro ω
    obtain ⟨t,ht,hω⟩ := hn ω
    exact mem_iUnion₂.mpr ⟨t,ht,hω⟩
  simp [allbad] at small

/-- A one-sided approximation on a mesh extends to the entire interval by a modulus
of continuity for the empirical error. -/
theorem extend_mesh {mesh : Finset ℝ} {f : ℝ → ℝ} {ε L h : ℝ} (hL : 0 ≤ L)
    (hmesh : ∀ t ∈ Icc (0:ℝ) 1, ∃ s ∈ mesh, |t-s| ≤ h)
    (hlip : ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ mesh, f t - f s ≤ L * |t-s|)
    (hnet : ∀ s ∈ mesh, f s ≤ ε) :
    ∀ t ∈ Icc (0:ℝ) 1, f t ≤ ε + L*h := by
  intro t ht
  obtain ⟨s,hs,hd⟩ := hmesh t ht
  linarith [hlip t ht s hs, hnet s hs, mul_le_mul_of_nonneg_left hd hL]

end PermutationStrips.Sampling
