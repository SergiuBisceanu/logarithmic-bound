import PermutationStrips.Pattern

/-!
# Transfer from an unequal permutation pattern to the equal grid

The mass assigned to a pair of grid intervals is the sum, over the original
squares, of the product of its two one-dimensional overlaps divided by the side
length. Summing along either grid axis recovers the grid width exactly.
-/

open Set MeasureTheory
open scoped Interval BigOperators

namespace PermutationStrips.Pattern

noncomputable section

/-- Every selected equal-grid square actually meets the original closed pattern. -/
theorem exists_grid_meets {ι : Type*} [Fintype ι] (P : Pattern ι) {n : ℕ} (hn : 0 < n) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n,
      ((Icc (gridStart i) (gridStart i + 1/n) ×ˢ
        Icc (gridStart (σ i)) (gridStart (σ i) + 1/n)) ∩ P.carrier).Nonempty := by
  classical
  let G := equalGrid hn (Equiv.refl (Fin n))
  let L (i : Fin n) (k : ι) := volume.real
    (Ioc (G.x i) (G.x i + G.w i) ∩ Ioc (P.x k) (P.x k + P.w k))
  let R (j : Fin n) (k : ι) := volume.real
    (Ioc (G.x j) (G.x j + G.w j) ∩ Ioc (P.y k) (P.y k + P.w k))
  have length {l d : ℝ} (hd : 0 ≤ d) : volume.real (Ioc l (l+d)) = d := by
    rw [Real.volume_real_Ioc_of_le (by linarith)]; ring
  have Lrow i : ∑ k, L i k = G.w i :=
    (sum_overlap P.x P.w P.x_cover P.x_disjoint (axis_subset G.x G.w G.x_cover i)).trans
      (length (G.wpos i).le)
  have Rrow j : ∑ k, R j k = G.w j :=
    (sum_overlap P.y P.w P.y_cover P.y_disjoint (axis_subset G.x G.w G.x_cover j)).trans
      (length (G.wpos j).le)
  have Lcol k : ∑ i, L i k = P.w k := by
    simpa only [L, inter_comm] using
      (sum_overlap G.x G.w G.x_cover G.x_disjoint (axis_subset P.x P.w P.x_cover k)).trans
        (length (P.wpos k).le)
  have Rcol k : ∑ j, R j k = P.w k := by
    simpa only [R, inter_comm] using
      (sum_overlap G.x G.w G.x_cover G.x_disjoint (axis_subset P.y P.w P.y_cover k)).trans
        (length (P.wpos k).le)
  let A (i j : Fin n) := ∑ k, L i k * R j k / P.w k
  have row i : ∑ j, A i j = 1 / (n : ℝ) := by
    unfold A
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_div, ← Finset.mul_sum, Rcol, mul_div_cancel_right₀ _ (P.wpos _).ne']
    exact Lrow i
  have col j : ∑ i, A i j = 1 / (n : ℝ) := by
    unfold A
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_div, ← Finset.sum_mul, Lcol, mul_div_cancel_left₀ _ (P.wpos _).ne']
    exact Rrow j
  obtain ⟨σ,hσ⟩ := exists_perm_positive_of_balanced A (w := 1/(n:ℝ)) (by positivity)
    (fun i j => Finset.sum_nonneg (fun k _ =>
      div_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg) (P.wpos k).le)) row col
  refine ⟨σ, fun i => ?_⟩
  have hex : ∃ k, 0 < L i k ∧ 0 < R (σ i) k := by
    by_contra! h
    have hz : A i (σ i) ≤ 0 := Finset.sum_nonpos fun k _ => by
      by_cases hl : 0 < L i k
      · have hr := h k hl
        exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hl.le hr) (P.wpos k).le
      · exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hl) measureReal_nonneg) (P.wpos k).le
    exact (not_lt_of_ge hz) (hσ i)
  obtain ⟨k,hl,hr⟩ := hex
  have hit {B : Set ℝ} (h : 0 < volume.real B) : B.Nonempty :=
    nonempty_iff_ne_empty.mpr fun he => by simp [he] at h
  obtain ⟨x,hx,hx'⟩ := hit hl
  obtain ⟨y,hy,hy'⟩ := hit hr
  refine ⟨(x,y), ⟨⟨hx.1.le,hx.2⟩,hy.1.le,hy.2⟩, mem_iUnion.mpr ⟨k,?_,?_⟩⟩
  · exact ⟨hx'.1.le,hx'.2⟩
  · exact ⟨hy'.1.le,hy'.2⟩


/-- Inflating each of a finite family of intervals by `δ` on both ends adds
at most `2 N δ` to the length of their union, with no separation assumption. -/
theorem length_inflate_intervals {ι : Type*} [Fintype ι] (l r : ι → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    volume.real (⋃ i, Icc (l i-δ) (r i+δ)) ≤
      volume.real (⋃ i, Icc (l i) (r i)) + 2 * Fintype.card ι * δ := by
  let E := ⋃ i, Icc (l i) (r i)
  let B i := Icc (l i-δ) (l i) ∪ Icc (r i) (r i+δ)
  have hs : (⋃ i, Icc (l i-δ) (r i+δ)) ⊆ E ∪ ⋃ i, B i := by
    intro x hx
    obtain ⟨i,hl,hr⟩ := mem_iUnion.mp hx
    by_cases hlo : l i ≤ x
    · by_cases hhi : x ≤ r i
      · exact Or.inl (mem_iUnion.mpr ⟨i,hlo,hhi⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨i, Or.inr ⟨le_of_not_ge hhi,hr⟩⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨i, Or.inl ⟨hl,le_of_not_ge hlo⟩⟩)
  have compact : IsCompact (E ∪ ⋃ i, B i) :=
    (isCompact_iUnion (fun _ => isCompact_Icc)).union
      (isCompact_iUnion (fun _ => isCompact_Icc.union isCompact_Icc))
  have each (i : ι) : volume.real (B i) ≤ 2*δ := by
    apply (measureReal_union_le _ _).trans
    rw [Real.volume_real_Icc_of_le (by linarith), Real.volume_real_Icc_of_le (by linarith)]
    linarith
  calc
    _ ≤ volume.real (E ∪ ⋃ i, B i) := measureReal_mono hs compact.measure_lt_top.ne
    _ ≤ volume.real E + volume.real (⋃ i, B i) := measureReal_union_le _ _
    _ ≤ volume.real E + ∑ i, 2*δ := by
      exact add_le_add_left ((measureReal_iUnion_fintype_le _).trans
        (Finset.sum_le_sum fun i _ => each i)) _
    _ = _ := by simp; ring

/-- One permutation approximates all projected lengths of the finite pattern
simultaneously, with error `2 N/n` for `N` original components. -/
theorem exists_grid_length_le {ι : Type*} [Fintype ι] (P : Pattern ι) {n : ℕ} (hn : 0 < n) :
    ∃ σ : Equiv.Perm (Fin n), ∀ t ∈ Icc (0 : ℝ) 1,
      volume.real ((equalGrid hn σ).sectionAt t) ≤
        volume.real (P.sectionAt t) + 2 * Fintype.card ι / n := by
  obtain ⟨σ, hσ⟩ := P.exists_grid_meets hn
  let G := equalGrid hn σ
  let δ := 1 / (n : ℝ)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  refine ⟨σ, fun t ht => ?_⟩
  have hsub : G.sectionAt t ⊆ ⋃ k, Icc (P.start t k - δ) (P.start t k + P.w k + δ) := by
    rw [G.sectionAt_eq ht]
    intro z hz
    obtain ⟨i, hl,hr⟩ := mem_iUnion.mp hz
    obtain ⟨p, hgrid, hp⟩ := hσ i
    have hpP : projection t p ∈ P.sectionAt t := ⟨p, hp, rfl⟩
    rw [P.sectionAt_eq ht] at hpP
    obtain ⟨k,hk,hk'⟩ := mem_iUnion.mp hpP
    have hpLo : G.start t i ≤ projection t p :=
      add_le_add (mul_le_mul_of_nonneg_left hgrid.1.1 (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left hgrid.2.1 ht.1)
    have hpHi : projection t p ≤ G.start t i + δ := by
      have hh := add_le_add (mul_le_mul_of_nonneg_left hgrid.1.2 (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left hgrid.2.2 ht.1)
      change (1-t)*p.1 + t*p.2 ≤ (1-t)*(gridStart i) + t*(gridStart (σ i)) + δ
      change (1-t)*p.1 + t*p.2 ≤ (1-t)*(gridStart i+δ) + t*(gridStart (σ i)+δ) at hh
      linarith
    change z ≤ G.start t i + δ at hr
    exact mem_iUnion.mpr ⟨k,by constructor <;> linarith⟩
  have hc : IsCompact (⋃ k, Icc (P.start t k - δ) (P.start t k + P.w k + δ)) :=
    isCompact_iUnion fun _ => isCompact_Icc
  calc
    _ ≤ _ := measureReal_mono hsub hc.measure_lt_top.ne
    _ ≤ volume.real (⋃ k, Icc (P.start t k) (P.start t k + P.w k)) + 2 * Fintype.card ι * δ :=
      length_inflate_intervals _ _ hδ
    _ = _ := by rw [← P.sectionAt_eq ht]; dsimp [δ]; ring

/-- Transfer of the actual strip union area by Cavalieri's principle. -/
theorem exists_grid_area_le {ι : Type*} [Fintype ι] (P : Pattern ι) {n : ℕ} (hn : 0 < n) :
    ∃ σ : Equiv.Perm (Fin n), (equalGrid hn σ).area ≤ P.area + 2 * Fintype.card ι / n := by
  obtain ⟨σ,hs⟩ := P.exists_grid_length_le hn
  refine ⟨σ, ?_⟩
  have hi := P.intervalIntegrable_length
  have hc : IntervalIntegrable (fun _ : ℝ => 2 * (Fintype.card ι : ℝ) / n) volume 0 1 :=
    intervalIntegrable_const
  calc
    _ ≤ ∫ t in (0:ℝ)..1, (volume.real (P.sectionAt t) + 2 * Fintype.card ι / n) :=
      intervalIntegral.integral_mono_on zero_le_one (equalGrid hn σ).intervalIntegrable_length
        (hi.add hc) hs
    _ = _ := by rw [intervalIntegral.integral_add hi hc, intervalIntegral.integral_const]; simp [area]


/-- Cavalieri's area of the equal-grid endpoint pattern equals the planar
Lebesgue measure of the corresponding union of parallelograms. -/
theorem equalGrid_area {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    (equalGrid hn σ).area = Crossings.permutationArea σ := by
  let G := equalGrid hn σ
  let S := ⋃ i : Fin n, Crossings.strip (n : ℝ)⁻¹ i.val (σ i).val
  have hm : MeasurableSet S := MeasurableSet.iUnion fun i => Crossings.measurable_strip ..
  change G.area = Crossings.squareMeasure.real S
  rw [area, intervalIntegral.integral_of_le zero_le_one, Crossings.area_sections hm]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2⟩
  have fiber : (Prod.mk t) ⁻¹' S = G.sectionAt t := by
    rw [G.sectionAt_eq ht']
    ext x
    change ((t,x) ∈ ⋃ i : Fin n, Crossings.strip (n : ℝ)⁻¹ i.val (σ i).val) ↔ _
    simp only [mem_iUnion]
    apply exists_congr; intro i
    have left : (n:ℝ)⁻¹ * Crossings.path i.val (σ i).val t = G.start t i := by
      dsimp [Crossings.path, G, equalGrid, start, projection, gridStart]
      ring
    have right : (n:ℝ)⁻¹ * (Crossings.path i.val (σ i).val t+1) = G.start t i + G.w i := by
      rw [mul_add, left]
      simp [G, equalGrid]
    change (_ ≤ x ∧ x ≤ _) ↔ (_ ≤ x ∧ x ≤ _)
    rw [left,right]
  change volume.real (G.sectionAt t) = Crossings.spaceMeasure.real ((Prod.mk t) ⁻¹' S)
  rw [fiber, Crossings.spaceMeasure, measureReal_restrict_apply (G.measurableSet_sectionAt ht'),
    inter_eq_left.mpr (G.sectionAt_subset_unit ht')]

/-- A finite unequal pattern directly bounds the optimum of the physical
equal-grid strip problem, at every positive grid size. -/
theorem exists_permutationArea_le {ι : Type*} [Fintype ι] (P : Pattern ι) {n : ℕ} (hn : 0 < n) :
    ∃ σ : Equiv.Perm (Fin n), Crossings.permutationArea σ ≤ P.area + 2 * Fintype.card ι / n := by
  simpa only [equalGrid_area] using P.exists_grid_area_le hn

end
end PermutationStrips.Pattern
