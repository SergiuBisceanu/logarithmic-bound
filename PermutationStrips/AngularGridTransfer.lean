import PermutationStrips.Angular
import PermutationStrips.Matching

/-!
# Simultaneous angular transfer from an arbitrary uniform coupling

Hall matching is performed on the cells carrying positive mass. Thus one
permutation works for every projection direction as well as for Favard length.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PermutationStrips.Angular
noncomputable section

/-- Every positive grid size admits a permutation whose closed physical cells
are contained in the square neighbourhood of a full-measure set. -/
theorem exists_grid_subset_thick {K : Set (ℝ × ℝ)}
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (hK : μ Kᶜ = 0)
    (hx : μ.map Prod.fst = volume.restrict (Icc (0:ℝ) 1))
    (hy : μ.map Prod.snd = volume.restrict (Icc (0:ℝ) 1)) {n : ℕ} (hn : 0 < n) :
    ∃ σ : Equiv.Perm (Fin n), (Pattern.equalGrid hn σ).carrier ⊆ thick (1/n) K := by
  classical
  let G := Pattern.equalGrid hn (Equiv.refl (Fin n))
  let B (i : Fin n) := Ioc (G.x i) (G.x i+G.w i)
  let w := 1/(n:ℝ)
  have mB (i : Fin n) : MeasurableSet (B i) := measurableSet_Ioc
  have cover : (⋃ i, B i) = Ioc (0:ℝ) 1 := G.x_cover
  have disj : Pairwise (fun i j => Disjoint (B i) (B j)) := G.x_disjoint
  have wpos : 0 < w := G.wpos ⟨0,hn⟩
  have marg (g : ℝ × ℝ → ℝ) (mg : Measurable g)
      (hg : μ.map g = volume.restrict (Icc (0:ℝ) 1)) (i : Fin n) :
      μ.real (g ⁻¹' B i) = w := by
    have sub : B i ⊆ Icc (0:ℝ) 1 := (Pattern.axis_subset G.x G.w G.x_cover i).trans Ioc_subset_Icc_self
    calc
      _ = (μ.map g).real (B i) := by simp [measureReal_def,Measure.map_apply mg (mB i)]
      _ = volume.real (B i) := by
        rw [hg,measureReal_restrict_apply (mB i),inter_eq_left.mpr sub]
      _ = w := by
        change volume.real (Ioc (G.x i) (G.x i+G.w i)) = _
        rw [Real.volume_real_Ioc_of_le (by linarith [G.wpos i])]
        change G.x i+w-G.x i=w
        ring
  have full (g : ℝ × ℝ → ℝ) (mg : Measurable g)
      (hg : μ.map g = volume.restrict (Icc (0:ℝ) 1)) :
      ∀ᵐ p ∂μ, g p ∈ ⋃ j, B j := by
    rw [cover,← ae_map_iff mg.aemeasurable (p:=fun x => x ∈ Ioc (0:ℝ) 1) measurableSet_Ioc,hg,
      ← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ:=volume) (a:=(0:ℝ)) (b:=1))]
    exact ae_restrict_mem measurableSet_Ioc
  have slice (s : Set (ℝ × ℝ)) (ms : MeasurableSet s) (g : ℝ × ℝ → ℝ) (mg : Measurable g)
      (hg : μ.map g = volume.restrict (Icc (0:ℝ) 1)) :
      (∑ j, μ.real (s ∩ g ⁻¹' B j)) = μ.real s := by
    rw [← measureReal_iUnion_fintype (μ:=μ)
      (fun i j h => ((disj h).preimage g).mono inter_subset_right inter_subset_right)
      (fun j => ms.inter ((mB j).preimage mg))]
    apply measureReal_congr
    filter_upwards [full g mg hg] with p hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨i,hi⟩ := hp
    apply propext
    constructor
    · intro hh; obtain ⟨_,hs,_⟩ := mem_iUnion.mp hh; exact hs
    · intro hs; exact mem_iUnion.mpr ⟨i,hs,hi⟩
  let a (i j : Fin n) := μ.real ((Prod.fst ⁻¹' B i) ∩ (Prod.snd ⁻¹' B j))
  have row (i : Fin n) : (∑ j, a i j) = w :=
    (slice _ ((mB _).preimage measurable_fst) _ measurable_snd hy).trans (marg _ measurable_fst hx i)
  have col (j : Fin n) : (∑ i, a i j) = w := by
    simp only [a,inter_comm (Prod.fst ⁻¹' _) (Prod.snd ⁻¹' _)]
    exact (slice _ ((mB _).preimage measurable_snd) _ measurable_fst hx).trans (marg _ measurable_snd hy j)
  obtain ⟨σ,positive⟩ := exists_perm_positive_of_balanced a wpos (fun _ _ => measureReal_nonneg) row col
  refine ⟨σ,?_⟩
  intro p hp
  obtain ⟨i,hp₁,hp₂⟩ := mem_iUnion.mp hp
  have hit : ∃ q ∈ K, q.1 ∈ B i ∧ q.2 ∈ B (σ i) := by
    by_contra! H
    have sub : (Prod.fst ⁻¹' B i) ∩ (Prod.snd ⁻¹' B (σ i)) ⊆ Kᶜ :=
      fun q hq hq' => H q hq' hq.1 hq.2
    have hz := measure_mono_null sub hK
    simpa [a, measureReal_def,hz] using positive i
  obtain ⟨q,hq,hq₁,hq₂⟩ := hit
  have box (j : Fin n) {x y : ℝ} (h₁ : x ∈ Icc (G.x j) (G.x j+w)) (h₂ : y ∈ B j) :
      x-y ∈ Icc (-w) w := by
    change G.x j < y ∧ y ≤ G.x j+w at h₂
    constructor <;> linarith [h₁.1,h₁.2,h₂.1,h₂.2]
  exact mem_image2.mpr ⟨q,hq,(p.1-q.1,p.2-q.2),⟨box i hp₁ hq₁,box (σ i) hp₂ hq₂⟩,by ext <;> simp⟩

end
end PermutationStrips.Angular
