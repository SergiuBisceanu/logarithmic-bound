import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Int.Interval
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Tactic

/-!
# The moving overlaps in the red–blue shuffle

Coordinates below are in units of a paired square's side.  The offset `h` pairs
red square `i` with blue square `i+h`.  The shell lemmas count parameter windows
*and* control the mass of the pairs in each window.  The overlap estimate is for
arbitrary measurable sections of the unit interval.
-/

open Set MeasureTheory
open scoped ENNReal

namespace PermutationStrips.Shuffle

/-- Signed separation of the blue and red sections at height `t`. -/
def displacement (t u h : ℝ) : ℝ := (2 - t) * h + 1 - (u + 1) * t

/-- The parameter giving the displacement `-s` for offset `h`. -/
noncomputable def sweep (t h s : ℝ) : ℝ := ((2 - t) * h + 1 + s) / t - 1

theorem displacement_sweep {t : ℝ} (ht : t ≠ 0) (h s : ℝ) :
    displacement t (sweep t h s) h = -s := by
  unfold displacement sweep
  field_simp
  ring

/-- Integer offsets for which the full shift window `0 ≤ s ≤ 1` fits in the shell. -/
noncomputable def offsets (U t : ℝ) : Finset ℤ :=
  Finset.Icc ⌈((U + 1) * t - 1) / (2 - t)⌉ ⌊((2 * U + 1) * t - 2) / (2 - t)⌋

theorem mem_offsets {U t : ℝ} {h : ℤ} (ht : 0 < t) (ht' : t ≤ 1/2) :
    h ∈ offsets U t ↔ U ≤ sweep t h 0 ∧ sweep t h 1 ≤ 2 * U := by
  have hden : 0 < 2 - t := by linarith
  rw [offsets, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
  unfold sweep
  constructor
  · rintro ⟨h₁, h₂⟩
    have h₁' := (div_le_iff₀ hden).mp h₁
    have h₂' := (le_div_iff₀ hden).mp h₂
    constructor
    · apply le_sub_iff_add_le.mpr
      apply (le_div_iff₀ ht).mpr
      nlinarith
    · apply sub_le_iff_le_add.mpr
      apply (div_le_iff₀ ht).mpr
      nlinarith
  · rintro ⟨h₁, h₂⟩
    have h₁' := (le_div_iff₀ ht).mp (le_sub_iff_add_le.mp h₁)
    have h₂' := (div_le_iff₀ ht).mp (sub_le_iff_le_add.mp h₂)
    exact ⟨(div_le_iff₀ hden).mpr (by nlinarith),
      (le_div_iff₀ hden).mpr (by nlinarith)⟩

theorem sweep_mem_shell {U t : ℝ} {h : ℤ} (ht : 0 < t) (ht' : t ≤ 1/2)
    (hh : h ∈ offsets U t) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    sweep t h s ∈ Icc U (2*U) := by
  obtain ⟨hl, hr⟩ := (mem_offsets ht ht').mp hh
  have mono : Monotone (sweep t (h : ℝ)) := by
    intro x y hxy
    unfold sweep
    gcongr
  exact ⟨hl.trans (mono hs.1), (mono hs.2).trans hr⟩

theorem sweep_windows_separated {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/2)
    {h j : ℤ} (hh : h < j) : sweep t h 1 < sweep t j 0 := by
  have hj : (h : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (show h + 1 ≤ j by omega)
  unfold sweep
  apply sub_lt_sub_right
  apply (div_lt_div_iff_of_pos_right ht).mpr
  nlinarith [mul_nonneg (show 0 ≤ 2 - t by linarith) (sub_nonneg.mpr hj)]

/-- At least `Ut/4` entire, mutually separated windows are available. -/
theorem offsets_card {U t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/2) (hUt : 8 ≤ U*t) :
    U*t/4 ≤ ((offsets U t).card : ℝ) := by
  let a := ((U+1)*t-1)/(2-t)
  let b := ((2*U+1)*t-2)/(2-t)
  have hden : 0 < 2-t := by linarith
  have hspan : U*t/4 ≤ b-a-1 := by
    dsimp [a,b]
    rw [div_sub_div_same]
    apply le_sub_iff_add_le.mpr
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_nonneg (show 0 ≤ U*t by linarith) ht.le]
  have hceil : (⌈a⌉ : ℝ) < a+1 := Int.ceil_lt_add_one a
  have hfloor : b < (⌊b⌋ : ℝ)+1 := Int.lt_floor_add_one b
  have hn : (0 : ℤ) ≤ ⌊b⌋+1-⌈a⌉ := by
    have : (0 : ℝ) ≤ (⌊b⌋ : ℝ)+1-(⌈a⌉ : ℝ) := by linarith
    exact_mod_cast this
  change U*t/4 ≤ ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ)
  rw [Int.card_Icc]
  have hc : (((⌊b⌋+1-⌈a⌉).toNat : ℕ) : ℝ) = (⌊b⌋ : ℝ)+1-(⌈a⌉ : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  rw [hc]
  linarith

/-- The total rescaled red width participating at a given integer offset. -/
noncomputable def pairedWidth (u : ℝ) (h : ℤ) : ℝ := ((⌊u⌋ : ℝ)-h-1)/(2*u)

theorem pairedWidth_sweep {t U : ℝ} {h : ℤ} (ht : 0 < t) (ht' : t ≤ 1/2)
    (hU : 16 ≤ U) (hUt : 8 ≤ U*t) (hh : h ∈ offsets U t) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    1 ≤ h ∧ 1/8 ≤ pairedWidth (sweep t h s) h := by
  have hu := (sweep_mem_shell ht ht' hh hs).1
  have hl := ((mem_offsets ht ht').mp hh).1
  have hbase : (U+1)*t ≤ (2-t)*(h:ℝ)+1+0 := by
    exact (le_div_iff₀ ht).mp (le_sub_iff_add_le.mp hl)
  have hpos : 0 < (h : ℝ) := by
    by_contra! hneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2-t by linarith) hneg]
  have hi : (0:ℤ) < h := by exact_mod_cast hpos
  have hthree : 3*(h:ℝ) ≤ sweep t h s := by
    unfold sweep
    apply le_sub_iff_add_le.mpr
    apply (le_div_iff₀ ht).mpr
    nlinarith [mul_nonneg (show 0 ≤ 2-4*t by linarith) hpos.le, hs.1]
  refine ⟨by omega, ?_⟩
  unfold pairedWidth
  apply (le_div_iff₀ (show 0 < 2 * sweep t h s by linarith)).mpr
  linarith [Int.lt_floor_add_one (sweep t h s)]


/-- The overlap of a section with its translate by `-s`. -/
noncomputable def overlap (F : Set ℝ) (s : ℝ) : ℝ≥0∞ :=
  volume {x : ℝ | x ∈ F ∧ x+s ∈ F}

/-- The area under the positive-shift overlap curve counts the upper triangle
of pairs of section points. Lebesgue measure is unchanged by the shear
`(s,x) ↦ (x,x+s)`. -/
theorem overlap_pairs {F : Set ℝ} (hF : MeasurableSet F) (hunit : F ⊆ Icc 0 1) :
    (volume F)^2 ≤ 2 * ∫⁻ s in Icc (0 : ℝ) 1, overlap F s := by
  classical
  let μ : Measure ℝ := volume
  let A : Set (ℝ × ℝ) := {p | p.1 ∈ F ∧ p.2 ∈ F ∧ p.1 ≤ p.2}
  have hA : MeasurableSet A :=
    (hF.preimage measurable_fst).inter ((hF.preimage measurable_snd).inter
      (measurableSet_le measurable_fst measurable_snd))
  let T := fun z : ℝ × ℝ => (z.2, z.2+z.1)
  have hT := measurePreserving_prod_add_swap μ μ
  have hpre : MeasurableSet (T ⁻¹' A) := hA.preimage hT.measurable
  have heq : μ.prod μ A = ∫⁻ s in Icc (0 : ℝ) 1, overlap F s := by
    calc
      μ.prod μ A = μ.prod μ (T ⁻¹' A) :=
        (hT.measure_preimage hA.nullMeasurableSet).symm
      _ = ∫⁻ s, μ (Prod.mk s ⁻¹' (T ⁻¹' A)) := Measure.prod_apply hpre
      _ = ∫⁻ s, (Icc (0 : ℝ) 1).indicator (overlap F) s := by
        apply lintegral_congr
        intro s
        by_cases hs : s ∈ Icc (0 : ℝ) 1
        · rw [indicator_of_mem hs]
          apply congrArg μ
          ext x
          change (x ∈ F ∧ x+s ∈ F ∧ x ≤ x+s) ↔ x ∈ F ∧ x+s ∈ F
          constructor
          · rintro ⟨hx,hy,-⟩
            exact ⟨hx,hy⟩
          · rintro ⟨hx,hy⟩
            exact ⟨hx,hy,by linarith [hs.1]⟩
        · rw [indicator_of_notMem hs]
          have he : Prod.mk s ⁻¹' (T ⁻¹' A) = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro x hx
            change x ∈ F ∧ x+s ∈ F ∧ x ≤ x+s at hx
            exact hs ⟨by linarith [hx.2.2], by linarith [(hunit hx.1).1, (hunit hx.2.1).2]⟩
          rw [he, measure_empty]
      _ = _ := lintegral_indicator measurableSet_Icc _
  have hcover : F ×ˢ F ⊆ A ∪ Prod.swap ⁻¹' A := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    rcases le_total x y with h|h
    · exact Or.inl ⟨hx,hy,h⟩
    · exact Or.inr ⟨hy,hx,h⟩
  calc
    (volume F)^2 = μ.prod μ (F ×ˢ F) := by simp [μ, pow_two]
    _ ≤ μ.prod μ (A ∪ Prod.swap ⁻¹' A) := measure_mono hcover
    _ ≤ μ.prod μ A + μ.prod μ (Prod.swap ⁻¹' A) := measure_union_le _ _
    _ = 2 * ∫⁻ s in Icc (0 : ℝ) 1, overlap F s := by
      rw [Measure.measurePreserving_swap.measure_preimage hA.nullMeasurableSet, heq, two_mul]


theorem measurable_overlap {F : Set ℝ} (hF : MeasurableSet F) : Measurable (overlap F) := by
  let A : Set (ℝ × ℝ) := {p | p.2 ∈ F ∧ p.2+p.1 ∈ F}
  have hA : MeasurableSet A :=
    (hF.preimage measurable_snd).inter (hF.preimage (measurable_snd.add measurable_fst))
  exact measurable_measure_prodMk_left hA

theorem overlap_interval {F : Set ℝ} (hF : MeasurableSet F) (hunit : F ⊆ Icc 0 1) :
    (volume F).toReal^2 ≤ 2 * ∫ s in (0 : ℝ)..1, (overlap F s).toReal := by
  have hbound (s : ℝ) : overlap F s ≤ 1 := by
    calc
      overlap F s ≤ volume F := measure_mono (fun x hx => hx.1)
      _ ≤ volume (Icc (0:ℝ) 1) := measure_mono hunit
      _ = 1 := by simp
  have hint : (∫⁻ s in Icc (0:ℝ) 1, overlap F s) ≤ 1 := by
    calc
      _ ≤ ∫⁻ s in Icc (0:ℝ) 1, (1 : ℝ≥0∞) := lintegral_mono hbound
      _ = 1 := by simp
  have hp := ENNReal.toReal_mono (show 2 * (∫⁻ s in Icc (0:ℝ) 1, overlap F s) ≠ ∞ by
    exact ENNReal.mul_ne_top (by norm_num) (ne_top_of_le_ne_top (by norm_num) hint))
      (overlap_pairs hF hunit)
  rw [intervalIntegral.integral_of_le (by norm_num), restrict_Ioc_eq_restrict_Icc,
    integral_toReal (measurable_overlap hF).aemeasurable
      (Filter.Eventually.of_forall fun s => lt_of_le_of_lt (hbound s) (by norm_num))]
  simpa using hp

/-- Exact integral of translated overlap in one full scale sweep. -/
theorem sweep_integral (F : Set ℝ) {t : ℝ} (ht : 0 < t) (h : ℤ) :
    t * (∫ u in sweep t h 0..sweep t h 1, (overlap F (-displacement t u h)).toReal) =
      ∫ s in (0:ℝ)..1, (overlap F s).toReal := by
  let c := t-(2-t)*(h:ℝ)-1
  have harg (u : ℝ) : -displacement t u h = t*u+c := by
    dsimp [displacement, c]; ring
  have hlim (s : ℝ) : t*sweep t h s+c=s := by
    dsimp [sweep,c]
    field_simp
    ring
  simp_rw [harg]
  simpa only [hlim] using intervalIntegral.mul_integral_comp_mul_add
    (a := sweep t h 0) (b := sweep t h 1) (f := fun s => (overlap F s).toReal) t c

/-- The average overlap certified by the disjoint windows.  The factor `1/8`
is a lower bound on the total red width in each of these windows. The factor
`1/U` is the density of the uniform distribution on `[U,2U]`. -/
noncomputable def certifiedSaving (F : Set ℝ) (U t : ℝ) : ℝ :=
  (∑ h ∈ offsets U t, ∫ u in sweep t h 0..sweep t h 1,
    (overlap F (-displacement t u h)).toReal) / (8*U)

/-- The paper's quadratic scale-averaging estimate for the certified pairs.
Only measurability and containment in the unit interval are required of `F`. -/
theorem certifiedSaving_lower {F : Set ℝ} (hF : MeasurableSet F) (hunit : F ⊆ Icc 0 1)
    {U t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/2) (hU : 16 ≤ U) (hUt : 8 ≤ U*t) :
    (volume F).toReal^2 / 64 ≤ certifiedSaving F U t := by
  let I := ∫ s in (0:ℝ)..1, (overlap F s).toReal
  have hI : (volume F).toReal^2 ≤ 2*I := overlap_interval hF hunit
  have hIn : 0 ≤ I := by nlinarith [sq_nonneg (volume F).toReal]
  have hn := offsets_card ht ht' hUt
  have hs (h : ℤ) : (∫ u in sweep t h 0..sweep t h 1,
      (overlap F (-displacement t u h)).toReal) = I/t := by
    apply (eq_div_iff ht.ne').mpr
    rw [mul_comm]
    exact sweep_integral F ht h
  unfold certifiedSaving
  simp_rw [hs]
  rw [Finset.sum_const, nsmul_eq_mul]
  apply (le_div_iff₀ (by positivity : 0 < 8*U)).mpr
  rw [← mul_div_assoc]
  apply (le_div_iff₀ ht).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hn) hIn,
    mul_nonneg (sub_nonneg.mpr hI) (show 0 ≤ U*t by linarith)]

/-- Positions of the unit-width children before rescaling the outer square.
Only the final, possibly longer, red and blue children are excluded. -/
def redStart (t u i : ℝ) : ℝ := (1-t)*(2*i)+t*(u+i)
def blueStart (t i : ℝ) : ℝ := (1-t)*(2*i+1)+t*i

def translated (F : Set ℝ) (a : ℝ) : Set ℝ := {x | x-a ∈ F}

theorem blue_sub_red (t u i h : ℝ) :
    blueStart t (i+h) - redStart t u i = displacement t u h := by
  unfold blueStart redStart displacement; ring

/-- The full red/blue intersection of the unit-width children. The omitted
last child in each color can only enlarge the geometric saving. -/
noncomputable def regularIntersection (F : Set ℝ) (t u : ℝ) : Set ℝ :=
  (⋃ i ∈ Finset.Icc (0:ℤ) (⌊u⌋-2), translated F (redStart t u i)) ∩
  (⋃ i ∈ Finset.Icc (0:ℤ) (⌊u⌋-2), translated F (blueStart t i))

private theorem translated_pair (F : Set ℝ) (t u : ℝ) (i h : ℤ) :
    volume (translated F (redStart t u i) ∩ translated F (blueStart t (i+h))) =
      overlap F (-displacement t u h) := by
  let r := redStart t u i
  have he : translated F (redStart t u i) ∩ translated F (blueStart t (i+h)) =
      (fun x : ℝ => x + (-r)) ⁻¹' {x : ℝ | x ∈ F ∧ x+(-displacement t u h) ∈ F} := by
    ext x
    have hb := blue_sub_red t u i h
    have hdiff : x - blueStart t (↑i+↑h) = x + (-r) + -displacement t u h := by dsimp [r]; linarith
    simp only [translated, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, sub_eq_add_neg] at *
    rw [← hdiff]
  rw [he,measure_preimage_add_right]
  rfl

private theorem red_disjoint {F : Set ℝ} (hunit : F ⊆ Icc 0 1) {t : ℝ}
    (ht' : t ≤ 1/2) (u : ℝ) {i j : ℤ} (hij : i < j) :
    Disjoint (translated F (redStart t u i)) (translated F (redStart t u j)) := by
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hx := (hunit hi).2
  have hy := (hunit hj).1
  have hgap : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast (show i+1≤j by omega)
  dsimp [redStart] at hx hy
  nlinarith [mul_nonneg (show 0 ≤ 2-t by linarith) (sub_nonneg.mpr hgap)]

/-- Disjoint matched pairs give a lower bound for the actual red/blue
intersection, not only for the overlap function of a single pair. -/
theorem regular_intersection_lower {F : Set ℝ} (hF : MeasurableSet F)
    (hunit : F ⊆ Icc 0 1) {t u : ℝ} (ht' : t ≤ 1/2) {h : ℤ} (hh : 1 ≤ h) :
    (((⌊u⌋-h-1).toNat : ℕ) : ℝ≥0∞) * overlap F (-displacement t u h) ≤
      volume (regularIntersection F t u) := by
  classical
  let inds := Finset.Icc (0:ℤ) (⌊u⌋-h-2)
  let pair := fun i : ℤ => translated F (redStart t u i) ∩ translated F (blueStart t (i+h))
  have hd : (inds : Set ℤ).PairwiseDisjoint pair := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (red_disjoint hunit ht' u hlt).mono inter_subset_left inter_subset_left
    · exact (red_disjoint hunit ht' u hgt).symm.mono inter_subset_left inter_subset_left
  have hm : ∀ i ∈ inds, MeasurableSet (pair i) := by
    intro i _
    exact (hF.preimage (measurable_id.sub_const _)).inter (hF.preimage (measurable_id.sub_const _))
  have hsub : (⋃ i ∈ inds, pair i) ⊆ regularIntersection F t u := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨i,hi,hr,hb⟩
    have hi' := Finset.mem_Icc.mp hi
    refine ⟨Set.mem_iUnion₂.mpr ⟨i,Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩,hr⟩,
      Set.mem_iUnion₂.mpr ⟨i+h,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩⟩
    simpa using hb
  have hc : inds.card = (⌊u⌋-h-1).toNat := by
    dsimp [inds]
    rw [Int.card_Icc]
    congr 1
    omega
  calc
    _ = (∑ i ∈ inds, volume (pair i)) := by
      simp [pair, translated_pair, hc, nsmul_eq_mul]
    _ = volume (⋃ i ∈ inds, pair i) := (measure_biUnion_finset hd hm).symm
    _ ≤ _ := measure_mono hsub

/-- Length of the common regular red and blue sections after rescaling by
the side factor `1/(2u)`. -/
noncomputable def regularSaving (F : Set ℝ) (t u : ℝ) : ℝ :=
  (volume (regularIntersection F t u)).toReal / (2*u)

/-- Joint measurability when the inner section, height and scale all vary. -/
theorem measurable_regularSaving_family {α : Type*} [MeasurableSpace α]
    {F : α → Set ℝ} (hF : MeasurableSet {p : α × ℝ | p.2 ∈ F p.1})
    {T U : α → ℝ} (hT : Measurable T) (hU : Measurable U) :
    Measurable (fun a => regularSaving (F a) (T a) (U a)) := by
  have hc (f : ℤ → α × ℝ → ℝ) (hf : ∀ i, Measurable (f i)) :
      MeasurableSet {z : α × ℝ | z.2 ∈
        ⋃ i ∈ Finset.Icc (0:ℤ) (⌊U z.1⌋-2), translated (F z.1) (f i z)} := by
    have he : {z : α × ℝ | z.2 ∈ ⋃ i ∈ Finset.Icc (0:ℤ) (⌊U z.1⌋-2),
        translated (F z.1) (f i z)} =
        ⋃ i : ℤ, {z : α × ℝ | 0 ≤ i ∧ (i+2 : ℤ) ≤ ⌊U z.1⌋ ∧ z.2-f i z ∈ F z.1} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_Icc, translated]
      constructor
      · rintro ⟨i,⟨hi,hi'⟩,hx⟩
        exact ⟨i,hi,by omega,hx⟩
      · rintro ⟨i,hi,hi',hx⟩
        exact ⟨i,⟨hi,by omega⟩,hx⟩
    rw [he]
    apply MeasurableSet.iUnion
    intro i
    exact (MeasurableSet.const _).inter ((measurableSet_le measurable_const
      (Int.measurable_floor.comp (hU.comp measurable_fst))).inter
        (hF.preimage (measurable_fst.prodMk (measurable_snd.sub (hf i)))))
  have hreg : MeasurableSet {z : α × ℝ | z.2 ∈ regularIntersection (F z.1) (T z.1) (U z.1)} :=
    (hc (fun i z => redStart (T z.1) (U z.1) i) (by intro i; unfold redStart; fun_prop)).inter
      (hc (fun i z => blueStart (T z.1) i) (by intro i; unfold blueStart; fun_prop))
  have hm : Measurable (fun a => volume (regularIntersection (F a) (T a) (U a))) :=
    measurable_measure_prodMk_left hreg
  exact hm.ennreal_toReal.div (measurable_const.mul hU)

private theorem measurable_regularSaving {F : Set ℝ} (hF : MeasurableSet F) (t : ℝ) :
    Measurable (regularSaving F t) :=
  measurable_regularSaving_family (F := fun _ : ℝ => F) (T := fun _ => t) (U := id)
    (hF.preimage measurable_snd) measurable_const measurable_id

private theorem regular_measure_bound {F : Set ℝ} (hunit : F ⊆ Icc 0 1) (t u : ℝ) :
    volume (regularIntersection F t u) ≤ ((Finset.Icc (0:ℤ) (⌊u⌋-2)).card : ℝ≥0∞) := by
  let K := Finset.Icc (0:ℤ) (⌊u⌋-2)
  calc
    _ ≤ volume (⋃ i ∈ K, translated F (redStart t u i)) := measure_mono inter_subset_left
    _ ≤ ∑ i ∈ K, volume (translated F (redStart t u i)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ K, (1:ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro i _
      have he : translated F (redStart t u i) = (fun x : ℝ => x + -redStart t u i) ⁻¹' F := by
        ext x
        simp only [translated, sub_eq_add_neg, Set.mem_preimage, Set.mem_setOf_eq]
      rw [he, measure_preimage_add_right]
      exact (measure_mono hunit).trans (by simp)
    _ = _ := by simp [K]

private theorem integrableOn_regularSaving {F : Set ℝ} (hF : MeasurableSet F)
    (hunit : F ⊆ Icc 0 1) (t : ℝ) {U : ℝ} (hU : 16 ≤ U) :
    IntegrableOn (regularSaving F t) (Icc U (2*U)) := by
  let N := (Finset.Icc (0:ℤ) (⌊2*U⌋-2)).card
  refine IntegrableOn.of_bound (measure_Icc_lt_top) (measurable_regularSaving hF t).aestronglyMeasurable
    (N:ℝ) ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with u hu
  have hc : (Finset.Icc (0:ℤ) (⌊u⌋-2)).card ≤ N :=
    Finset.card_le_card (Finset.Icc_subset_Icc_right (sub_le_sub_right (Int.floor_mono hu.2) 2))
  have hm : (volume (regularIntersection F t u)).toReal ≤ N := by
    simpa using ENNReal.toReal_mono (by simp : (N:ℝ≥0∞) ≠ ∞)
      ((regular_measure_bound hunit t u).trans (by exact_mod_cast hc))
  have hu' : 1 ≤ 2*u := by linarith [hu.1]
  simp only [regularSaving, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ENNReal.toReal_nonneg (by linarith : 0 ≤ 2*u))]
  exact (div_le_self ENNReal.toReal_nonneg hu').trans hm

theorem saving_on_window {F : Set ℝ} (hF : MeasurableSet F) (hunit : F ⊆ Icc 0 1)
    {U t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/2) (hU : 16 ≤ U) (hUt : 8 ≤ U*t)
    {h : ℤ} (hh : h ∈ offsets U t) {u : ℝ} (hu : u ∈ Icc (sweep t h 0) (sweep t h 1)) :
    (overlap F (-displacement t u h)).toReal / 8 ≤ regularSaving F t u := by
  let s := -displacement t u h
  have hs : s ∈ Icc (0:ℝ) 1 := by
    have h₀ := (div_le_iff₀ ht).mp (sub_le_iff_le_add.mp hu.1)
    have h₁ := (le_div_iff₀ ht).mp (le_sub_iff_add_le.mp hu.2)
    dsimp [s,displacement]
    constructor <;> nlinarith
  have he : sweep t h s = u := by dsimp [s, sweep, displacement]; field_simp; ring
  have hp := pairedWidth_sweep ht ht' hU hUt hh hs
  rw [he] at hp
  have hu' : 0 < u := by
    have hz := (sweep_mem_shell ht ht' hh hs).1
    rw [he] at hz
    linarith
  have hgeom := regular_intersection_lower hF hunit ht' hp.1 (u := u)
  have hreal := ENNReal.toReal_mono (ne_top_of_le_ne_top (by simp) (regular_measure_bound hunit t u)) hgeom
  have hfloor : (0:ℤ) ≤ ⌊u⌋-h-1 := by
    have hx := (le_div_iff₀ (by linarith : 0 < 2*u)).mp hp.2
    exact_mod_cast (show (0:ℝ) ≤ (⌊u⌋:ℝ)-(h:ℝ)-1 by linarith)
  have hcast : ((((⌊u⌋-h-1).toNat):ℕ):ℝ) = (⌊u⌋:ℝ)-(h:ℝ)-1 := by
    exact_mod_cast Int.toNat_of_nonneg hfloor
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, hcast] at hreal
  have hx := (le_div_iff₀ (by linarith : 0 < 2*u)).mp hp.2
  unfold regularSaving
  apply (le_div_iff₀ (by linarith : 0 < 2*u)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (ENNReal.toReal_nonneg (a:=overlap F s))]

/-- The actual mean red/blue intersection in the complete parameter shell.
This counts only the regular children, so it already gives the required saving
before including the two possibly longer final children. -/
theorem shell_average {F : Set ℝ} (hF : MeasurableSet F) (hunit : F ⊆ Icc 0 1)
    {U t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/2) (hU : 16 ≤ U) (hUt : 8 ≤ U*t) :
    (volume F).toReal^2 / 64 ≤
      (∫ u in Icc U (2*U), regularSaving F t u) / U := by
  classical
  let W := fun h : ℤ => Icc (sweep t h 0) (sweep t h 1)
  have hw (h : ℤ) (hh : h ∈ offsets U t) : W h ⊆ Icc U (2*U) := by
    obtain ⟨hl,hr⟩ := (mem_offsets ht ht').mp hh
    exact fun _ hx => ⟨hl.trans hx.1,hx.2.trans hr⟩
  have hi := integrableOn_regularSaving hF hunit t hU
  have hwi (h : ℤ) (hh : h ∈ offsets U t) := hi.mono_set (hw h hh)
  have hd : ((offsets U t):Set ℤ).PairwiseDisjoint W := by
    intro h _ j _ hne
    apply Set.disjoint_left.mpr
    intro u hu hv
    rcases lt_or_gt_of_ne hne with hlt|hgt
    · linarith [(sweep_windows_separated ht ht' hlt), hu.2, hv.1]
    · linarith [(sweep_windows_separated ht ht' hgt), hv.2, hu.1]
  have hsum : (∑ h ∈ offsets U t, ∫ u in W h,
      (overlap F (-displacement t u h)).toReal / 8) ≤
      ∫ u in Icc U (2*U), regularSaving F t u := by
    calc
      _ ≤ ∑ h ∈ offsets U t, ∫ u in W h, regularSaving F t u := by
        apply Finset.sum_le_sum
        intro h hh
        refine setIntegral_mono_on ?_ (hwi h hh) measurableSet_Icc ?_
        · refine IntegrableOn.of_bound measure_Icc_lt_top ?_ 1 ?_
          · have hm : Measurable (fun u : ℝ => -displacement t u h) := by unfold displacement; fun_prop
            exact ((measurable_overlap hF).ennreal_toReal.comp hm).div_const 8 |>.aestronglyMeasurable
          · filter_upwards with u
            have hm : overlap F (-displacement t u h) ≤ 1 :=
              (measure_mono (show {x:ℝ | x∈F ∧ x+-displacement t u h ∈ F} ⊆ Icc 0 1 from
                fun _ hx => hunit hx.1)).trans (by simp)
            have hx := ENNReal.toReal_mono (by simp) hm
            simp only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg ENNReal.toReal_nonneg (by norm_num : (0:ℝ)≤8))]
            simpa using (show (overlap F (-displacement t u h)).toReal/8 ≤ (1:ℝ) by
              simp at hx; linarith)
        · exact fun u hu => saving_on_window hF hunit ht ht' hU hUt hh hu
      _ = ∫ u in ⋃ h ∈ offsets U t, W h, regularSaving F t u :=
        (integral_biUnion_finset _ (fun _ _ => measurableSet_Icc) hd hwi).symm
      _ ≤ _ := setIntegral_mono_set hi (by
        filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Icc] with u hu
        exact div_nonneg ENNReal.toReal_nonneg (by linarith [hu.1] : 0≤2*u))
        (Filter.Eventually.of_forall (by
          intro u hu
          obtain ⟨h,hh,hz⟩ := Set.mem_iUnion₂.mp hu
          exact hw h hh hz))
  have he (h : ℤ) : (∫ u in W h, (overlap F (-displacement t u h)).toReal / 8) =
      (∫ u in sweep t h 0..sweep t h 1, (overlap F (-displacement t u h)).toReal)/8 := by
    have horder : sweep t h 0 ≤ sweep t h 1 := by unfold sweep; gcongr; norm_num
    rw [intervalIntegral.integral_of_le horder, restrict_Ioc_eq_restrict_Icc, ← integral_div]
  simp_rw [he] at hsum
  rw [← Finset.sum_div] at hsum
  have H := certifiedSaving_lower hF hunit ht ht' hU hUt
  unfold certifiedSaving at H
  apply (le_div_iff₀ (by linarith : 0 < U)).mpr
  have H' := (le_div_iff₀ (by linarith : 0 < 8*U)).mp H
  linarith

end PermutationStrips.Shuffle
