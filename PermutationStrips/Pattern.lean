import PermutationStrips.Matching
import PermutationStrips.Crossings

/-!
# Finite permutation patterns

Each component matches two intervals of the same positive width. Right-closed
intervals encode exact partitions of `(0,1]`, while the planar carrier includes
all edges of its squares.
-/

open Set MeasureTheory
open scoped Interval BigOperators

namespace PermutationStrips

structure Pattern (ι : Type*) where
  x : ι → ℝ
  y : ι → ℝ
  w : ι → ℝ
  wpos : ∀ i, 0 < w i
  x_cover : (⋃ i, Ioc (x i) (x i + w i)) = Ioc 0 1
  y_cover : (⋃ i, Ioc (y i) (y i + w i)) = Ioc 0 1
  x_disjoint : Pairwise fun i j => Disjoint (Ioc (x i) (x i + w i)) (Ioc (x j) (x j + w j))
  y_disjoint : Pairwise fun i j => Disjoint (Ioc (y i) (y i + w i)) (Ioc (y j) (y j + w j))

/-- Horizontal position of the segment with endpoint pair `p` at height `t`. -/
def projection (t : ℝ) (p : ℝ × ℝ) : ℝ := (1-t)*p.1 + t*p.2

namespace Pattern

def carrier {ι : Type*} (P : Pattern ι) : Set (ℝ × ℝ) :=
  ⋃ i, Icc (P.x i) (P.x i + P.w i) ×ˢ Icc (P.y i) (P.y i + P.w i)

def sectionAt {ι : Type*} (P : Pattern ι) (t : ℝ) : Set ℝ := projection t '' P.carrier

/-- Area computed by the horizontal sections of the strip union. -/
noncomputable def area {ι : Type*} (P : Pattern ι) : ℝ :=
  ∫ t in (0 : ℝ)..1, volume.real (P.sectionAt t)

def start {ι : Type*} (P : Pattern ι) (t : ℝ) (i : ι) := projection t (P.x i,P.y i)

theorem sectionAt_eq {ι : Type*} (P : Pattern ι) {t : ℝ} (ht : t ∈ Icc 0 1) :
    P.sectionAt t = ⋃ i, Icc (P.start t i) (P.start t i + P.w i) := by
  ext z
  constructor
  · rintro ⟨⟨a,b⟩, hp, rfl⟩
    obtain ⟨i, ⟨⟨ha,ha'⟩, hb,hb'⟩⟩ := Set.mem_iUnion.mp hp
    refine Set.mem_iUnion.mpr ⟨i, ?_, ?_⟩ <;> unfold start projection
    · exact add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left hb ht.1)
    · have h := add_le_add (mul_le_mul_of_nonneg_left ha' (sub_nonneg.mpr ht.2))
          (mul_le_mul_of_nonneg_left hb' ht.1)
      dsimp at *
      linarith
  · intro hz
    obtain ⟨i, hl,hr⟩ := Set.mem_iUnion.mp hz
    let e := z - P.start t i
    have h₁ : 0 ≤ e := sub_nonneg.mpr hl
    have h₂ : e ≤ P.w i := by dsimp [e]; linarith
    refine ⟨(P.x i+e, P.y i+e), Set.mem_iUnion.mpr ⟨i, ⟨by constructor <;> linarith,
      by constructor <;> linarith⟩⟩, ?_⟩
    dsimp [e, start, projection]
    ring

/-- Finite union of closed intervals for the section, hence measurability. -/
theorem measurableSet_sectionAt {ι : Type*} [Finite ι] (P : Pattern ι) {t : ℝ}
    (ht : t ∈ Icc 0 1) : MeasurableSet (P.sectionAt t) := by
  classical
  rw [P.sectionAt_eq ht]
  exact MeasurableSet.iUnion fun _ => measurableSet_Icc

/-- Equal-grid intervals start at these coordinates. -/
noncomputable def gridStart {n : ℕ} (i : Fin n) : ℝ := i.val / (n : ℝ)

private theorem grid_cover {n : ℕ} (hn : 0 < n) :
    (⋃ i : Fin n, Ioc (gridStart i) (gridStart i + 1 / n)) = Ioc 0 1 := by
  have npos : 0 < (n : ℝ) := by exact_mod_cast hn
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have h : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
    exact ⟨lt_of_le_of_lt (by unfold gridStart; positivity) hi.1, hi.2.trans (by
      rw [gridStart, ← add_div]; exact (div_le_one npos).2 h)⟩
  · intro hx
    have hx' : x ∈ Ioc (((0 : ℕ) : ℝ)/n) ((n : ℝ)/n) := by simpa [npos.ne'] using hx
    obtain ⟨k, h⟩ := Set.mem_iUnion.mp (Ioc_subset_biUnion_Ioc n (fun k : ℕ => (k : ℝ)/n) hx')
    obtain ⟨hk, hi⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨⟨k,Finset.mem_range.mp hk⟩, by simpa [gridStart, add_div] using hi⟩

private theorem grid_disjoint {n : ℕ} :
    Pairwise fun i j : Fin n => Disjoint (Ioc (gridStart i) (gridStart i + 1/n))
      (Ioc (gridStart j) (gridStart j + 1/n)) := by
  have h {i j : Fin n} (hij : i < j) : gridStart i + 1/n ≤ gridStart j := by
    rw [gridStart, gridStart, ← add_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast hij
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  rcases lt_or_gt_of_ne hij with hlt|hgt
  · exact (not_lt_of_ge (hi.2.trans (h hlt))) hj.1
  · exact (not_lt_of_ge (hj.2.trans (h hgt))) hi.1

/-- The pattern selected by an equal-grid permutation. -/
noncomputable def equalGrid {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n)) : Pattern (Fin n) where
  x := gridStart
  y := fun i => gridStart (σ i)
  w := fun _ => 1 / (n : ℝ)
  wpos := fun _ => by positivity
  x_cover := grid_cover hn
  y_cover := (σ.surjective.iUnion_comp (fun i => Ioc (gridStart i) (gridStart i + 1/n))).trans (grid_cover hn)
  x_disjoint := grid_disjoint
  y_disjoint := fun _ _ h => grid_disjoint (σ.injective.ne h)

theorem axis_subset {ι : Type*} (a w : ι → ℝ)
    (cover : (⋃ i, Ioc (a i) (a i + w i)) = Ioc 0 1) (i : ι) :
    Ioc (a i) (a i + w i) ⊆ Ioc 0 1 := by
  rw [← cover]
  exact subset_iUnion (fun j => Ioc (a j) (a j + w j)) i

theorem axis_bounds {ι : Type*} (a w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (cover : (⋃ i, Ioc (a i) (a i + w i)) = Ioc 0 1) (i : ι) :
    0 ≤ a i ∧ a i + w i ≤ 1 :=
  ((Ioc_subset_Ioc_iff (by linarith [hw i] : a i < a i + w i)).mp
    (axis_subset a w cover i)).symm

theorem sum_overlap {ι : Type*} [Fintype ι] (a w : ι → ℝ)
    (cover : (⋃ i, Ioc (a i) (a i + w i)) = Ioc 0 1)
    (disj : Pairwise (fun i j => Disjoint (Ioc (a i) (a i + w i)) (Ioc (a j) (a j + w j))))
    {l r : ℝ} (hB : Ioc l r ⊆ Ioc 0 1) :
    ∑ i, volume.real (Ioc l r ∩ Ioc (a i) (a i + w i)) = volume.real (Ioc l r) := by
  have hd : Pairwise fun i j => Disjoint (Ioc l r ∩ Ioc (a i) (a i + w i))
      (Ioc l r ∩ Ioc (a j) (a j + w j)) :=
    fun _ _ h => (disj h).mono inter_subset_right inter_subset_right
  rw [← measureReal_iUnion_fintype hd (fun _ => measurableSet_Ioc.inter measurableSet_Ioc)
      (fun _ => ne_top_of_le_ne_top measure_Ioc_lt_top.ne (measure_mono inter_subset_right)),
    ← inter_iUnion, cover, inter_eq_left.mpr hB]

/-- At every height the projected pattern is contained in the unit interval. -/
theorem sectionAt_subset_unit {ι : Type*} (P : Pattern ι) {t : ℝ} (ht : t ∈ Icc 0 1) :
    P.sectionAt t ⊆ Icc 0 1 := by
  rintro z ⟨⟨a,b⟩, hp, rfl⟩
  obtain ⟨i, ⟨ha, hb⟩⟩ := mem_iUnion.mp hp
  have x := axis_bounds P.x P.w P.wpos P.x_cover i
  have y := axis_bounds P.y P.w P.wpos P.y_cover i
  have ba : a ∈ Icc (0 : ℝ) 1 := ⟨x.1.trans ha.1,ha.2.trans x.2⟩
  have bb : b ∈ Icc (0 : ℝ) 1 := ⟨y.1.trans hb.1,hb.2.trans y.2⟩
  unfold projection
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) ba.1) (mul_nonneg ht.1 bb.1)
  · dsimp
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ba.2),
      mul_nonneg ht.1 (sub_nonneg.mpr bb.2)]

theorem section_length_le_one {ι : Type*} (P : Pattern ι) {t : ℝ} (ht : t ∈ Icc 0 1) :
    volume.real (P.sectionAt t) ≤ 1 := by
  calc
    _ ≤ volume.real (Icc (0:ℝ) 1) := measureReal_mono (P.sectionAt_subset_unit ht) measure_Icc_lt_top.ne
    _ = _ := by simp

theorem isCompact_sectionAt {ι : Type*} [Finite ι] (P : Pattern ι) {t : ℝ}
    (ht : t ∈ Icc 0 1) : IsCompact (P.sectionAt t) := by
  rw [P.sectionAt_eq ht]
  exact isCompact_iUnion fun _ => isCompact_Icc

theorem sum_width {ι : Type*} [Fintype ι] (P : Pattern ι) : ∑ i, P.w i = 1 := by
  have len i : volume.real (Ioc (P.x i) (P.x i + P.w i)) = P.w i := by
    rw [Real.volume_real_Ioc_of_le (by linarith [P.wpos i])]; ring
  rw [← (by simp : volume.real (Ioc (0:ℝ) 1) = 1), ← P.x_cover,
    measureReal_iUnion_fintype P.x_disjoint (fun _ => measurableSet_Ioc) (fun _ => measure_Ioc_lt_top.ne)]
  simp [len]

theorem measurable_length_Icc_indicator {ι : Type*} [Finite ι] (P : Pattern ι) :
    Measurable ((Icc (0:ℝ) 1).indicator (fun t => volume.real (P.sectionAt t))) := by
  let V (t : ℝ) := ⋃ i, Icc (P.start t i) (P.start t i + P.w i)
  have hB : MeasurableSet {z : ℝ × ℝ | z.2 ∈ V z.1} := by
    have he : {z : ℝ × ℝ | z.2 ∈ V z.1} =
        ⋃ i, {z : ℝ × ℝ | P.start z.1 i ≤ z.2 ∧ z.2 ≤ P.start z.1 i + P.w i} := by
      ext z; simp [V]
    rw [he]; apply MeasurableSet.iUnion; intro i
    exact (measurableSet_le (by unfold start projection; fun_prop) measurable_snd).inter
      (measurableSet_le measurable_snd (by unfold start projection; fun_prop))
  have hm : Measurable (fun t => volume.real (V t)) :=
    (measurable_measure_prodMk_left hB).ennreal_toReal
  have he : (Icc (0:ℝ) 1).indicator (fun t => volume.real (P.sectionAt t)) =
      (Icc (0:ℝ) 1).indicator (fun t => volume.real (V t)) := by
    ext t
    by_cases ht : t ∈ Icc (0:ℝ) 1 <;> simp [ht, V, P.sectionAt_eq]
  rw [he]
  exact hm.indicator measurableSet_Icc

theorem intervalIntegrable_length {ι : Type*} [Finite ι] (P : Pattern ι) :
    IntervalIntegrable (fun t => volume.real (P.sectionAt t)) volume 0 1 := by
  let f := (Icc (0:ℝ) 1).indicator (fun t => volume.real (P.sectionAt t))
  have he (t : ℝ) (ht : t ∈ Ioc 0 1) : f t = volume.real (P.sectionAt t) :=
    indicator_of_mem (Ioc_subset_Icc_self ht) _
  have hi : IntegrableOn f (Ioc (0:ℝ) 1) := by
    apply IntegrableOn.of_bound measure_Ioc_lt_top P.measurable_length_Icc_indicator.aestronglyMeasurable 1
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    change ‖f t‖ ≤ 1
    rw [he t ht, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact P.section_length_le_one ⟨ht.1.le,ht.2⟩
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact hi.congr_fun he measurableSet_Ioc

end Pattern
end PermutationStrips
