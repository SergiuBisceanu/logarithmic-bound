import Mathlib.Combinatorics.Hall.Finite
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Interval.Set.Union
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic

/-!
# Equal-grid matching from uniform coordinate marginals

Hall's condition follows by counting the mass in any collection of rows twice.
We apply this to genuine rectangular cell masses for a coupling of two copies
of Lebesgue measure on the unit interval. The partition uses right-closed cells,
with the point zero included in the first cell. The selected endpoint squares
are closed and lie within a grid width of the given full-measure set.
-/

open Finset Set MeasureTheory
open scoped BigOperators

namespace PermutationStrips

noncomputable section

/-- Hall's matching for a nonnegative matrix with a common positive row and
column mass. Entries along the selected permutation are strictly positive. -/
theorem exists_perm_positive_of_balanced {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) {w : ℝ} (hw : 0 < w) (hn : ∀ i j, 0 ≤ a i j)
    (hr : ∀ i, ∑ j, a i j = w) (hc : ∀ j, ∑ i, a i j = w) :
    ∃ σ : Equiv.Perm ι, ∀ i, 0 < a i (σ i) := by
  classical
  let f (i : ι) := Finset.univ.filter fun j => a i j ≠ 0
  have hall (s : Finset ι) : s.card ≤ (s.biUnion f).card := by
    have row (i : ι) : ∑ j ∈ f i, a i j = w := by
      rw [← hr i]
      exact Finset.sum_subset (Finset.filter_subset _ _) fun j _ hj => by
        simpa [f] using hj
    have hs : ∑ i ∈ s, ∑ j ∈ f i, a i j = (s.card : ℝ) * w := by simp [row]
    have ht : ∑ i, ∑ j ∈ s.biUnion f, a i j = ((s.biUnion f).card : ℝ) * w := by
      rw [Finset.sum_comm]; simp [hc]
    suffices (s.card : ℝ) * w ≤ ((s.biUnion f).card : ℝ) * w by
      exact_mod_cast (le_of_mul_le_mul_right this hw)
    rw [← hs, ← ht]
    trans ∑ i ∈ s, ∑ j ∈ s.biUnion f, a i j
    · exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_biUnion_of_mem f hi) (fun j _ _ => hn i j)
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ =>
        Finset.sum_nonneg fun j _ => hn i j
  obtain ⟨g, hg, hpos⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' f).1 hall
  refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg), fun i => ?_⟩
  exact lt_of_le_of_ne (hn i (g i)) (Ne.symm (Finset.mem_filter.mp (hpos i)).2)

private def gridEdge (n k : ℕ) (hk : k ≤ n) : unitInterval :=
  ⟨(k : ℝ) / n, by positivity, by
    by_cases hn : n = 0
    · simp [hn]
    · have hp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      exact (div_le_one hp).2 (by exact_mod_cast hk)⟩

/-- The closed interval `[i/n, (i+1)/n]` in the unit interval. -/
def closedGridInterval {n : ℕ} (i : Fin n) : Set unitInterval :=
  Icc (gridEdge n i.val i.isLt.le) (gridEdge n (i.val + 1) i.isLt)

theorem mem_closedGridInterval {n : ℕ} {i : Fin n} {x : unitInterval} :
    x ∈ closedGridInterval i ↔ (i.val : ℝ) / n ≤ x ∧ (x : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) / n :=
  Iff.rfl

private def bin {n : ℕ} (i : Fin n) : Set unitInterval :=
  if i.val = 0 then closedGridInterval i
  else Ioc (gridEdge n i.val i.isLt.le) (gridEdge n (i.val + 1) i.isLt)

private theorem bin_measurable {n : ℕ} (i : Fin n) : MeasurableSet (bin i) := by
  unfold bin closedGridInterval
  split <;> first | exact measurableSet_Icc | exact measurableSet_Ioc

private theorem bin_subset_closed {n : ℕ} (i : Fin n) : bin i ⊆ closedGridInterval i := by
  unfold bin
  split
  · exact Subset.rfl
  · exact Ioc_subset_Icc_self

private theorem bin_cover {n : ℕ} (hn : 0 < n) (x : unitInterval) : ∃ i : Fin n, x ∈ bin i := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  by_cases hx : (x : ℝ) = 0
  · refine ⟨⟨0, hn⟩, ?_⟩
    simp only [bin, ↓reduceIte, closedGridInterval, Set.mem_Icc]
    change ((0 : ℕ) : ℝ) / n ≤ (x : ℝ) ∧ (x : ℝ) ≤ ((0 + 1 : ℕ) : ℝ) / n
    rw [hx]
    norm_num
  · have hx' : (x : ℝ) ∈ Ioc (((0 : ℕ) : ℝ) / n) ((n : ℝ) / n) := by
      simpa [hn'] using And.intro (lt_of_le_of_ne x.property.1 (Ne.symm hx)) x.property.2
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp
      (Ioc_subset_biUnion_Ioc n (fun k : ℕ => (k : ℝ) / n) hx')
    obtain ⟨hk, mem⟩ := Set.mem_iUnion.mp hk
    let i : Fin n := ⟨k, Finset.mem_range.mp hk⟩
    refine ⟨i, ?_⟩
    unfold bin
    split
    · exact ⟨mem.1.le, mem.2⟩
    · exact mem

private theorem bins_disjoint {n : ℕ} : Pairwise (fun i j : Fin n => Disjoint (bin i) (bin j)) := by
  suffices h : ∀ i j : Fin n, i < j → Disjoint (bin i) (bin j) by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact h i j hlt
    · exact (h j i hgt).symm
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hj' : j.val ≠ 0 := by change i.val < j.val at hij; omega
  have hix := (bin_subset_closed i hi).2
  rw [bin, if_neg hj'] at hj
  have hsep : (gridEdge n (i.val + 1) i.isLt : ℝ) ≤ (gridEdge n j.val j.isLt.le : ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Nat.succ_le_of_lt hij
  change (x : ℝ) ≤ (gridEdge n (i.val + 1) i.isLt : ℝ) at hix
  exact (not_lt_of_ge (hix.trans hsep)) hj.1

private theorem bin_volume_real {n : ℕ} (i : Fin n) : volume.real (bin i) = 1 / (n : ℝ) := by
  have hwidth : (gridEdge n (i.val + 1) i.isLt : ℝ) - (gridEdge n i.val i.isLt.le : ℝ) =
      1 / (n : ℝ) := by simp [gridEdge, add_div]
  unfold bin closedGridInterval
  split <;> simp [measureReal_def, hwidth]

private theorem sum_mass_inter_partition {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Set Ω) (hs : MeasurableSet s)
    (f : ι → Set Ω) (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (fun i j => Disjoint (f i) (f j))) (hu : ∀ x, ∃ i, x ∈ f i) :
    ∑ i, μ.real (s ∩ f i) = μ.real s := by
  have hdis : Pairwise (fun i j => Disjoint (s ∩ f i) (s ∩ f j)) :=
    fun i j hij => (hd hij).mono inter_subset_right inter_subset_right
  rw [← measureReal_iUnion_fintype hdis (fun i => hs.inter (hf i))]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hi.1
  · intro hx
    obtain ⟨i, hi⟩ := hu x
    exact Set.mem_iUnion.mpr ⟨i, hx, hi⟩

private theorem closedGridInterval_dist {n : ℕ} {i : Fin n} {x y : unitInterval}
    (hx : x ∈ closedGridInterval i) (hy : y ∈ closedGridInterval i) : dist x y ≤ 1 / (n : ℝ) := by
  change |(x : ℝ) - (y : ℝ)| ≤ _
  have hwidth : (gridEdge n (i.val + 1) i.isLt : ℝ) - (gridEdge n i.val i.isLt.le : ℝ) =
      1 / (n : ℝ) := by simp [gridEdge, add_div]
  apply abs_le.mpr
  obtain ⟨hx₁, hx₂⟩ := hx
  obtain ⟨hy₁, hy₂⟩ := hy
  change (gridEdge n i.val _ : ℝ) ≤ (x : ℝ) at hx₁
  change (x : ℝ) ≤ (gridEdge n (i.val + 1) _ : ℝ) at hx₂
  change (gridEdge n i.val _ : ℝ) ≤ (y : ℝ) at hy₁
  change (y : ℝ) ≤ (gridEdge n (i.val + 1) _ : ℝ) at hy₂
  constructor <;> linarith

/-- If a coupling of two uniform marginals gives full measure to `K`, some
permutation of the equal grid has every closed selected square within sup-distance
`1/n` of `K`. The witness is a point of `K` in the very same grid cell. -/
theorem uniform_marginals_grid_matching {n : ℕ} (hn : 0 < n)
    (μ : Measure (unitInterval × unitInterval)) [IsProbabilityMeasure μ]
    (hx : μ.map Prod.fst = volume) (hy : μ.map Prod.snd = volume)
    (K : Set (unitInterval × unitInterval)) (hK : μ Kᶜ = 0) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, ∃ z ∈ K,
      z ∈ (closedGridInterval i ×ˢ closedGridInterval (σ i)) ∧
      ∀ p ∈ (closedGridInterval i ×ˢ closedGridInterval (σ i)), dist p z ≤ 1 / (n : ℝ) := by
  classical
  let r (i : Fin n) : Set (unitInterval × unitInterval) := Prod.fst ⁻¹' bin i
  let c (i : Fin n) : Set (unitInterval × unitInterval) := Prod.snd ⁻¹' bin i
  have mr i : MeasurableSet (r i) := (bin_measurable i).preimage measurable_fst
  have mc i : MeasurableSet (c i) := (bin_measurable i).preimage measurable_snd
  have dr : Pairwise (fun i j => Disjoint (r i) (r j)) :=
    fun _ _ h => (bins_disjoint h).preimage _
  have dc : Pairwise (fun i j => Disjoint (c i) (c j)) :=
    fun _ _ h => (bins_disjoint h).preimage _
  let a (i j : Fin n) := μ.real (r i ∩ c j)
  have row (i : Fin n) : ∑ j, a i j = 1 / (n : ℝ) := by
    change ∑ j, μ.real (r i ∩ c j) = _
    rw [sum_mass_inter_partition μ (r i) (mr i) c mc dc (fun p => bin_cover hn p.2)]
    calc μ.real (r i) = (μ.map Prod.fst).real (bin i) := by
           simp [r, measureReal_def, Measure.map_apply measurable_fst (bin_measurable i)]
         _ = _ := by rw [hx, bin_volume_real]
  have col (j : Fin n) : ∑ i, a i j = 1 / (n : ℝ) := by
    change ∑ i, μ.real (r i ∩ c j) = _
    simp_rw [inter_comm (r _) (c j)]
    rw [sum_mass_inter_partition μ (c j) (mc j) r mr dr (fun p => bin_cover hn p.1)]
    calc μ.real (c j) = (μ.map Prod.snd).real (bin j) := by
           simp [c, measureReal_def, Measure.map_apply measurable_snd (bin_measurable j)]
         _ = _ := by rw [hy, bin_volume_real]
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨σ, hσ⟩ := exists_perm_positive_of_balanced a (w := 1 / (n : ℝ)) (by positivity)
    (fun _ _ => ENNReal.toReal_nonneg) row col
  refine ⟨σ, fun i => ?_⟩
  have hit : ∃ z ∈ K, z ∈ r i ∩ c (σ i) := by
    by_contra h
    have hsub : r i ∩ c (σ i) ⊆ Kᶜ := fun z hz hmem => h ⟨z, hmem, hz⟩
    have hz := measure_mono_null hsub hK
    simpa [a, measureReal_def, hz] using hσ i
  obtain ⟨z, hz, hr, hc⟩ := hit
  have hcell : z ∈ (closedGridInterval i ×ˢ closedGridInterval (σ i)) :=
    ⟨bin_subset_closed i hr, bin_subset_closed (σ i) hc⟩
  refine ⟨z, hz, hcell, fun p hp => ?_⟩
  rw [Prod.dist_eq]
  exact max_le (closedGridInterval_dist hp.1 hcell.1) (closedGridInterval_dist hp.2 hcell.2)

/-- The endpoint set of an equal-grid permutation: one closed square in each
row and column of the unit square. -/
def permutationGrid {n : ℕ} (σ : Equiv.Perm (Fin n)) : Set (unitInterval × unitInterval) :=
  ⋃ i, closedGridInterval i ×ˢ closedGridInterval (σ i)

/-- The equal-grid transfer in set-inclusion form, with the sup metric on the square. -/
theorem exists_permutationGrid_subset_cthickening {n : ℕ} (hn : 0 < n)
    (μ : Measure (unitInterval × unitInterval)) [IsProbabilityMeasure μ]
    (hx : μ.map Prod.fst = volume) (hy : μ.map Prod.snd = volume)
    (K : Set (unitInterval × unitInterval)) (hK : μ Kᶜ = 0) :
    ∃ σ : Equiv.Perm (Fin n), permutationGrid σ ⊆ Metric.cthickening (1 / (n : ℝ)) K := by
  obtain ⟨σ, hσ⟩ := uniform_marginals_grid_matching hn μ hx hy K hK
  refine ⟨σ, fun p hp => ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
  obtain ⟨z, hz, _, hd⟩ := hσ i
  exact Metric.mem_cthickening_of_dist_le p z _ K hz (hd p hi)

end

end PermutationStrips
