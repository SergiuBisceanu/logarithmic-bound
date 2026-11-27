import PermutationStrips.FiniteUpper
import PermutationStrips.Sliding
import PermutationStrips.TwoStrips
import PermutationStrips.Weighted

/-!
# The two least areas in Kaczynski's strip problem

The admissible free top starts are expressed in grid units. All areas in the
definitions below are planar Lebesgue measures in the physical unit square.
-/

open Set MeasureTheory Filter Asymptotics
open scoped BigOperators Topology Asymptotics

namespace PermutationStrips.Conjecture

open Crossings

noncomputable section

/-- Top starts in grid units. The actual top intervals are `[bᵢ/n,(bᵢ+1)/n]`. -/
def topBox (n : ℕ) : Set (Fin n → ℝ) := Icc (fun _ => 0) (fun _ => (n:ℝ)-1)

def slidingArea {n : ℕ} (b : Fin n → ℝ) : ℝ :=
  squareMeasure.real (⋃ i : Fin n, strip (1/n) i.val (b i))

/-- The infimum for freely sliding top intervals. -/
def beta (n : ℕ) : ℝ := sInf (slidingArea '' topBox n)

/-- The infimum for permutations of the top grid. -/
def alpha (n : ℕ) : ℝ := sInf (range (permutationArea (n := n)))

theorem perm_topBox {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (fun i => ((σ i).val : ℝ)) ∈ topBox n := by
  refine ⟨fun i => Nat.cast_nonneg _, fun i => ?_⟩
  have h : ((σ i).val : ℝ) + 1 ≤ n := by exact_mod_cast (σ i).isLt
  change ((σ i).val : ℝ) ≤ (n:ℝ)-1
  linarith

theorem slidingArea_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    slidingArea (fun i => ((σ i).val : ℝ)) = permutationArea σ := by
  simp [slidingArea, permutationArea, one_div]

private theorem box_nonempty (n : ℕ) : (topBox n).Nonempty :=
  ⟨_, perm_topBox (Equiv.refl _)⟩

private theorem area_bounded_below (n : ℕ) : BddBelow (slidingArea '' topBox n) :=
  ⟨0, by rintro _ ⟨b, _, rfl⟩; exact measureReal_nonneg⟩

theorem alpha_attained (n : ℕ) : ∃ σ : Equiv.Perm (Fin n), permutationArea σ = alpha n :=
  (range_nonempty (permutationArea (n := n))).csInf_mem (finite_range _)

theorem alpha_le {n : ℕ} (σ : Equiv.Perm (Fin n)) : alpha n ≤ permutationArea σ :=
  csInf_le (finite_range _).bddBelow (mem_range_self σ)

theorem beta_le {n : ℕ} {b : Fin n → ℝ} (hb : b ∈ topBox n) : beta n ≤ slidingArea b :=
  csInf_le (area_bounded_below n) ⟨b,hb,rfl⟩

theorem beta_le_alpha (n : ℕ) : beta n ≤ alpha n := by
  obtain ⟨σ,hσ⟩ := alpha_attained n
  rw [← hσ, ← slidingArea_perm]
  exact beta_le (perm_topBox σ)

theorem beta_nonneg (n : ℕ) : 0 ≤ beta n :=
  le_csInf ((box_nonempty n).image slidingArea) (by rintro _ ⟨b, _, rfl⟩; exact measureReal_nonneg)

private def region {n : ℕ} (b : Fin n → ℝ) :=
  ⋃ i : Fin n, strip (1/n) i.val (b i)

private def left {n : ℕ} (b : Fin n → ℝ) (t : ℝ) (i : Fin n) :=
  (1/n) * path i.val (b i) t

private theorem fiber_eq {n : ℕ} (b : Fin n → ℝ) (t : ℝ) :
    (Prod.mk t) ⁻¹' region b = ⋃ i : Fin n, Icc (left b t i) (left b t i + 1/n) := by
  ext x
  change ((t,x) ∈ ⋃ i : Fin n, strip (1/n) i.val (b i)) ↔ _
  simp only [mem_iUnion]
  apply exists_congr; intro i
  change (_ ≤ x ∧ x ≤ 1 / (n : ℝ) * (path i.val (b i) t + 1)) ↔ (_ ≤ x ∧ x ≤ _)
  rw [mul_add, mul_one]; rfl

private theorem measurable_region {n : ℕ} (b : Fin n → ℝ) : MeasurableSet (region b) :=
  MeasurableSet.iUnion fun _ => measurable_strip ..

private theorem int_fiber {n : ℕ} (b : Fin n → ℝ) :
    Integrable (fun t => spaceMeasure.real (Prod.mk t ⁻¹' region b)) timeMeasure := by
  have hm : Measurable (fun t => spaceMeasure (Prod.mk t ⁻¹' region b)) :=
    measurable_measure_prodMk_left (measurable_region b)
  apply (integrable_const (1 : ℝ)).mono' hm.ennreal_toReal.aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact (measureReal_mono (μ := spaceMeasure) (subset_univ _)).trans (by simp [spaceMeasure,measureReal_def])

private theorem fiber_subset_unit {n : ℕ} (hn : 0 < n) (c : Fin n → ℝ) (hc : c ∈ topBox n)
    {t : ℝ} (ht : t ∈ Ioc 0 1) : (Prod.mk t ⁻¹' region c) ⊆ Icc (0:ℝ) 1 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hw : 0 ≤ 1/(n:ℝ) := by positivity
  rw [fiber_eq]
  intro x hx
  obtain ⟨i,h₁,h₂⟩ := mem_iUnion.mp hx
  have lo : 0 ≤ path i.val (c i) t :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (Nat.cast_nonneg _)) (mul_nonneg ht.1.le (hc.1 i))
  have hi : path i.val (c i) t + 1 ≤ n := by
    have hci := hc.2 i
    change c i ≤ (n:ℝ)-1 at hci
    have hni : (i.val:ℝ)+1 ≤ n := by exact_mod_cast i.isLt
    unfold path
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hni),
      mul_nonneg ht.1.le (sub_nonneg.mpr hci)]
  refine ⟨(mul_nonneg hw lo).trans h₁,h₂.trans ?_⟩
  unfold left
  rw [show 1/(n:ℝ) * path i.val (c i) t + 1/n = (path i.val (c i) t + 1) / n by ring]
  exact (div_le_one hn').2 hi

private theorem measure_fiber_le {n : ℕ} (hn : 0 < n) (b c : Fin n → ℝ) (hc : c ∈ topBox n)
    {t : ℝ} (ht : t ∈ Ioc 0 1) :
    spaceMeasure.real (Prod.mk t ⁻¹' region b) ≤
      spaceMeasure.real (Prod.mk t ⁻¹' region c) + 2*dist b c := by
  let w := 1 / (n:ℝ)
  let δ := w * dist b c
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hδ : 0 ≤ δ := mul_nonneg hw dist_nonneg
  have hI (i : Fin n) : |left b t i - left c t i| ≤ δ := by
    have hi : dist (b i) (c i) ≤ dist b c := (dist_pi_le_iff dist_nonneg).mp le_rfl i
    rw [Real.dist_eq] at hi
    have he : left b t i - left c t i = w*t*(b i - c i) := by dsimp [left,path,w]; ring
    rw [he, abs_mul, abs_of_nonneg (mul_nonneg hw ht.1.le)]
    exact (mul_le_mul_of_nonneg_left hi (mul_nonneg hw ht.1.le)).trans
      (by dsimp [δ]; nlinarith [mul_nonneg (mul_nonneg hw (sub_nonneg.mpr ht.2)) (dist_nonneg (x:=b) (y:=c))])
  have sub : (Prod.mk t ⁻¹' region b) ⊆ ⋃ i, Icc (left c t i-δ) (left c t i+w+δ) := by
    rw [fiber_eq]
    intro x hx
    obtain ⟨i, hx₁,hx₂⟩ := mem_iUnion.mp hx
    obtain ⟨h₁,h₂⟩ := abs_le.mp (hI i)
    change x ≤ left b t i + w at hx₂
    exact mem_iUnion.mpr ⟨i, by constructor <;> linarith⟩
  have size : 2 * Fintype.card (Fin n) * δ = 2*dist b c := by
    simp only [Fintype.card_fin]; dsimp [δ,w]; field_simp
  have finiteInfl : volume (⋃ i, Icc (left c t i-δ) (left c t i+w+δ)) ≠ ⊤ :=
    (isCompact_iUnion (fun _ => isCompact_Icc)).measure_lt_top.ne
  rw [spaceMeasure, measureReal_restrict_apply (measurable_prodMk_left (measurable_region b)),
    measureReal_restrict_apply (measurable_prodMk_left (measurable_region c)), inter_eq_left.mpr (fiber_subset_unit hn c hc ht)]
  calc
    _ ≤ _ := measureReal_mono (inter_subset_left.trans sub) finiteInfl
    _ ≤ volume.real (⋃ i, Icc (left c t i) (left c t i + w)) + 2 * Fintype.card (Fin n) * δ :=
      Pattern.length_inflate_intervals _ _ hδ
    _ = _ := by rw [fiber_eq, size]

/-- Moving admissible top starts by sup-distance `d` in grid units changes
the physical covered area by at most `2d`. -/
theorem slidingArea_dist_le {n : ℕ} (hn : 0 < n) {b c : Fin n → ℝ}
    (hb : b ∈ topBox n) (hc : c ∈ topBox n) : dist (slidingArea b) (slidingArea c) ≤ 2*dist b c := by
  have bound (b c : Fin n → ℝ) (hc : c ∈ topBox n) : slidingArea b ≤ slidingArea c + 2*dist b c := by
    change squareMeasure.real (region b) ≤ squareMeasure.real (region c) + _
    rw [area_sections (measurable_region b), area_sections (measurable_region c)]
    have h := integral_mono_ae (int_fiber b) ((int_fiber c).add (integrable_const (2*dist b c)))
      (show ∀ᵐ t ∂timeMeasure, spaceMeasure.real (Prod.mk t ⁻¹' region b) ≤
          spaceMeasure.real (Prod.mk t ⁻¹' region c) + 2*dist b c from by
        filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioc (a:=(0:ℝ)) (b:=1))] with t ht
        exact measure_fiber_le hn b c hc ht)
    calc
      _ ≤ ∫ t, (spaceMeasure.real (Prod.mk t ⁻¹' region c) + 2*dist b c) ∂timeMeasure := h
      _ = _ := by
        rw [integral_add (int_fiber c) (integrable_const (2*dist b c)), integral_const]
        simp [timeMeasure, measureReal_def]
  rw [Real.dist_eq, abs_le]
  have hbc := bound b c hc
  have hcb := bound c b hb
  rw [dist_comm c b] at hcb
  constructor <;> linarith

theorem beta_attained {n : ℕ} (hn : 0 < n) : ∃ b ∈ topBox n, slidingArea b = beta n := by
  have hLip : LipschitzOnWith 2 (slidingArea (n := n)) (topBox n) :=
    LipschitzOnWith.of_dist_le_mul fun _ hb _ hc => slidingArea_dist_le hn hb hc
  have hcompact : IsCompact (topBox n) := isCompact_Icc
  obtain ⟨b,hb,hmin⟩ := hcompact.exists_isMinOn (box_nonempty n) hLip.continuousOn
  refine ⟨b,hb,le_antisymm ?_ (beta_le hb)⟩
  apply le_csInf ((box_nonempty n).image slidingArea)
  rintro _ ⟨c,hc,rfl⟩
  exact hmin hc

theorem beta_log_lower {n : ℕ} (hn : 0 < n) : (1 + 2*Real.log n)⁻¹ ≤ beta n := by
  apply le_csInf ((box_nonempty n).image slidingArea)
  rintro _ ⟨b,hb,rfl⟩
  exact Sliding.sliding_log_lower hn b hb.1 (fun i => by have h := hb.2 i; dsimp at h; linarith)

theorem alpha_log_lower {n : ℕ} (hn : 0 < n) : 1 / (1 + Real.log n) ≤ alpha n := by
  obtain ⟨σ,hσ⟩ := alpha_attained n
  rw [← hσ]
  exact Crossings.logarithmic_lower hn σ

/-- The two-strip computation uses physical top starts, half the starts in grid units. -/
theorem slidingArea_two {b : Fin 2 → ℝ} (hb : b ∈ topBox 2) :
    slidingArea b = TwoStrips.area (b 0/2, b 1/2) := by
  change squareMeasure.real (region b) = _
  rw [area_sections (measurable_region b), TwoStrips.area, intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  change spaceMeasure.real (Prod.mk t ⁻¹' region b) = volume.real (TwoStrips.sectionAt (b 0/2) (b 1/2) t)
  rw [spaceMeasure, measureReal_restrict_apply (measurable_prodMk_left (measurable_region b)),
    inter_eq_left.mpr (fiber_subset_unit (by decide) b hb ht), fiber_eq]
  congr 1
  have hu (f : Fin 2 → Set ℝ) : (⋃ i, f i) = f 0 ∪ f 1 := by
    ext x; constructor
    · intro h; obtain ⟨i,hi⟩ := mem_iUnion.mp h; fin_cases i <;> simp_all
    · rintro (h|h)
      · exact mem_iUnion.mpr ⟨0,h⟩
      · exact mem_iUnion.mpr ⟨1,h⟩
  rw [hu]
  norm_num [left, path, TwoStrips.sectionAt]
  congr 2 <;> ring

/-- Exact least area for two freely sliding strips. -/
theorem beta_two : beta 2 = Real.sqrt 2 / 2 := by
  have image_eq : slidingArea '' topBox 2 = TwoStrips.area '' TwoStrips.sliding := by
    ext v
    constructor
    · rintro ⟨b,hb,rfl⟩
      have b₀ := hb.1 0
      have b₁ := hb.1 1
      have b₀' := hb.2 0
      have b₁' := hb.2 1
      refine ⟨(b 0/2,b 1/2), ?_, (slidingArea_two hb).symm⟩
      change (0 ≤ b 0/2 ∧ b 0/2 ≤ 1/2) ∧ 0 ≤ b 1/2 ∧ b 1/2 ≤ 1/2
      norm_num at b₀ b₁ b₀' b₁'
      constructor <;> constructor <;> linarith
    · rintro ⟨⟨a,b⟩, ⟨⟨ha,ha'⟩,hb,hb'⟩,rfl⟩
      let f : Fin 2 → ℝ := ![2*a,2*b]
      have hf : f ∈ topBox 2 := by
        constructor <;> intro i <;> fin_cases i <;> norm_num [f] <;> linarith
      refine ⟨f,hf,?_⟩
      rw [slidingArea_two hf]
      simp [f]
  rw [beta, image_eq, TwoStrips.sliding_minimum.csInf_eq]

/-- Exact least area for the two permutations of the two-strip grid. -/
theorem alpha_two : alpha 2 = 3 / 4 := by
  let q (σ : Equiv.Perm (Fin 2)) : ℝ × ℝ := (((σ 0).val:ℝ)/2,((σ 1).val:ℝ)/2)
  have eqA (σ : Equiv.Perm (Fin 2)) : permutationArea σ = TwoStrips.area (q σ) :=
    (slidingArea_perm σ).symm.trans (slidingArea_two (perm_topBox σ))
  have image_eq : range (permutationArea (n := 2)) = TwoStrips.area '' TwoStrips.permuted := by
    ext v
    constructor
    · rintro ⟨σ,rfl⟩
      refine ⟨q σ,?_, (eqA σ).symm⟩
      have hn : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
      have cases₂ (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      rcases cases₂ (σ 0) with h₀|h₀ <;> rcases cases₂ (σ 1) with h₁|h₁ <;> simp_all [q, TwoStrips.permuted]
    · rintro ⟨z,hz,rfl⟩
      rcases (show z = (0,1/2) ∨ z = (1/2,0) from hz) with rfl|rfl
      · refine ⟨Equiv.refl _,?_⟩; rw [eqA]; norm_num [q]
      · refine ⟨Equiv.swap 0 1,?_⟩; rw [eqA]; norm_num [q]
  rw [alpha, image_eq, TwoStrips.permutation_minimum.csInf_eq]

/-- Every number below two eventually bounds the normalized freely sliding minimum. -/
theorem eventually_beta_lower {a : ℝ} (ha : a < 2) :
    ∀ᶠ n : ℕ in atTop, a ≤ Real.log n * beta n := by
  filter_upwards [Weighted.eventually_sliding_lower ha, eventually_ge_atTop (1 : ℕ)] with n hn hpos
  obtain ⟨b, hb, he⟩ := beta_attained (show 0 < n by omega)
  rw [← he]
  simpa only [slidingArea, one_div] using hn b hb.1
    (fun i => by have hi := hb.2 i; change b i ≤ (n:ℝ)-1 at hi; linarith)

/-- The corresponding eventual lower constant for permutation minima is `π²/4`. -/
theorem eventually_alpha_lower {a : ℝ} (ha : a < Real.pi^2/4) :
    ∀ᶠ n : ℕ in atTop, a ≤ Real.log n * alpha n := by
  filter_upwards [Weighted.eventually_permutation_lower ha] with n hn
  obtain ⟨σ,hσ⟩ := alpha_attained n
  rw [← hσ]; exact hn σ

private theorem liminf_of_upper {f : ℕ → ℝ} {a C : ℝ} (h : ∀ b < a, ∀ᶠ n in atTop, b ≤ f n)
    (hC : ∀ᶠ n in atTop, f n ≤ C) : a ≤ liminf f atTop := by
  exact (le_liminf_iff' (isCoboundedUnder_ge_of_eventually_le _ hC)
    (isBoundedUnder_of_eventually_ge (h (a-1) (by linarith)))).2 h

private theorem leading_constants_of_upper
    (upper : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∃ σ : Equiv.Perm (Fin n),
      permutationArea σ ≤ C / Real.log n) :
    2 ≤ liminf (fun n : ℕ => Real.log n * beta n) atTop ∧
      Real.pi^2/4 ≤ liminf (fun n : ℕ => Real.log n * alpha n) atTop := by
  obtain ⟨C,_,hC⟩ := upper
  have bound : ∀ᶠ n : ℕ in atTop, Real.log n * alpha n ≤ C := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    obtain ⟨σ,hσ⟩ := hC n hn
    rw [mul_comm]
    exact (le_div_iff₀ hlog).mp ((alpha_le σ).trans hσ)
  have cmp : ∀ᶠ n : ℕ in atTop, Real.log n * beta n ≤ C := by
    filter_upwards [bound, eventually_ge_atTop (2 : ℕ)] with n hb hn
    exact (mul_le_mul_of_nonneg_left (beta_le_alpha n)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))).trans hb
  exact ⟨liminf_of_upper (fun _ h => eventually_beta_lower h) cmp,
    liminf_of_upper (fun _ h => eventually_alpha_lower h) bound⟩

private theorem theta_of_explicit_bounds (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hl : ∀ n : ℕ, 2 ≤ n → (1+2*Real.log n)⁻¹ ≤ f n)
    {C : ℝ} (hu : ∀ n : ℕ, 2 ≤ n → f n ≤ C / Real.log n) :
    f =Θ[atTop] (fun n : ℕ => (Real.log n)⁻¹) := by
  constructor
  · apply isBigO_iff.mpr
    refine ⟨C, ?_⟩
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    simpa [Real.norm_eq_abs, abs_of_nonneg (hf n), abs_of_pos hlog,
      div_eq_mul_inv] using hu n hn
  · apply isBigO_iff.mpr
    refine ⟨3, ?_⟩
    filter_upwards [eventually_ge_atTop 2, (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
      with n hn hlog
    change (1 : ℝ) ≤ Real.log n at hlog
    have hpos : 0 < Real.log n := by linarith
    have hden : 0 < 1+2*Real.log n := by linarith
    have inv_le : (Real.log n)⁻¹ ≤ 3*(1+2*Real.log n)⁻¹ := by
      field_simp
      linarith
    calc
      ‖(Real.log n)⁻¹‖ = (Real.log n)⁻¹ := abs_of_nonneg (inv_nonneg.mpr hpos.le)
      _ ≤ 3*(1+2*Real.log n)⁻¹ := inv_le
      _ ≤ 3*‖f n‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (hf n)]; linarith [hl n hn]

/-- The same upper construction implies the logarithmic order in both models. -/
private theorem order_of_permutation_upper
    (upper : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∃ σ : Equiv.Perm (Fin n),
      permutationArea σ ≤ C / Real.log n) :
    (beta =Θ[atTop] (fun n : ℕ => (Real.log n)⁻¹)) ∧
    (alpha =Θ[atTop] (fun n : ℕ => (Real.log n)⁻¹)) := by
  obtain ⟨C, _, hC⟩ := upper
  have hα (n : ℕ) (hn : 2 ≤ n) : alpha n ≤ C / Real.log n := by
    obtain ⟨σ,hσ⟩ := hC n hn
    exact (alpha_le σ).trans hσ
  have hlo (n : ℕ) (hn : 2 ≤ n) := beta_log_lower (show 0 < n by omega)
  exact ⟨theta_of_explicit_bounds beta beta_nonneg hlo (fun n hn => (beta_le_alpha n).trans (hα n hn)),
    theta_of_explicit_bounds alpha (fun n => (beta_nonneg n).trans (beta_le_alpha n))
      (fun n hn => (hlo n hn).trans (beta_le_alpha n)) hα⟩

/-- Kaczynski's second conjecture for the freely sliding minimum and its
permutation counterpart, both measured by planar Lebesgue area. -/
theorem kaczynski_second_conjecture :
    (beta =Θ[atTop] (fun n : ℕ => (Real.log n)⁻¹)) ∧
    (alpha =Θ[atTop] (fun n : ℕ => (Real.log n)⁻¹)) :=
  order_of_permutation_upper FiniteUpper.permutation_upper

/-- The lower leading constants in the two logarithmic area laws. -/
theorem lower_leading_constants :
    2 ≤ liminf (fun n : ℕ => Real.log n * beta n) atTop ∧
      Real.pi^2/4 ≤ liminf (fun n : ℕ => Real.log n * alpha n) atTop :=
  leading_constants_of_upper FiniteUpper.permutation_upper

end
end PermutationStrips.Conjecture
