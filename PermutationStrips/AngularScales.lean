import PermutationStrips.AngularSymmetry

/-!
# The normalized angular weight and dyadic scale selection

Admissibility controls the weight only in the open-closed interval (0,1/2].
Clamping the argument before evaluating the truncated weight therefore supplies
a globally measurable extension without any regularity assumption elsewhere.
-/

open MeasureTheory Set
open scoped Interval

namespace PermutationStrips.Angular
noncomputable section

theorem integrable_truncated {b : ℝ → ℝ} (hb : Admissible b) {a d : ℝ} (ha : 0 < a)
    (had : a ≤ d) (hd : d ≤ 1/2) : IntervalIntegrable (fun r => b r/r) volume a d := by
  have sub : uIcc a d ⊆ Ioc (0:ℝ) (1/2) := by
    rw [uIcc_of_le had]; exact fun _ h => ⟨ha.trans_le h.1,h.2.trans hd⟩
  have hi : IntervalIntegrable b volume a d := (hb.1.mono sub).intervalIntegrable
  simpa only [div_eq_mul_inv] using hi.mul_continuousOn (continuousOn_id.inv₀ (fun r hr => (sub hr).1.ne'))

theorem truncated_nonneg {b : ℝ → ℝ} (hb : Admissible b) {δ : ℝ}
    (hδ : 0 < δ) (hh : δ ≤ 1/2) : 0 ≤ truncated b δ :=
  intervalIntegral.integral_nonneg hh fun r hr =>
    div_nonneg (hb.2 r ⟨hδ.trans_le hr.1,hr.2⟩).1 (hδ.le.trans hr.1)

theorem truncated_mono_cutoff {b : ℝ → ℝ} (hb : Admissible b) {δ d : ℝ}
    (hδ : 0 < δ) (hd : δ ≤ d) (hh : d ≤ 1/2) : truncated b d ≤ truncated b δ := by
  unfold truncated
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (integrable_truncated hb hδ hd hh) (integrable_truncated hb (hδ.trans_le hd) hh le_rfl)]
  exact le_add_of_nonneg_left (intervalIntegral.integral_nonneg hd fun r hr =>
    div_nonneg (hb.2 _ ⟨hδ.trans_le hr.1,hr.2.trans hh⟩).1 (hδ.le.trans hr.1))

def scaleFactor (b : ℝ → ℝ) (k : ℕ) : ℝ := 1+truncated b (Real.exp (-(k:ℝ)))

theorem cutoff_le_half {k : ℕ} (hk : 2 ≤ k) : Real.exp (-(k:ℝ)) ≤ 1/2 := by
  rw [Real.exp_neg, one_div]
  apply inv_anti₀ (by norm_num)
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  linarith [Real.add_one_le_exp (k:ℝ)]

theorem one_le_scaleFactor {b : ℝ → ℝ} (hb : Admissible b) {k : ℕ}
    (hk : 2 ≤ k) : 1 ≤ scaleFactor b k :=
  le_add_of_nonneg_right (truncated_nonneg hb (Real.exp_pos _) (cutoff_le_half hk))

/-- Small radii are controlled by the truncation integral using monotonicity. -/
theorem below_cutoff {b : ℝ → ℝ} (hb : Admissible b) {k : ℕ} (hk : 2 ≤ k)
    {r : ℝ} (hr : 0 < r) (hc : r ≤ Real.exp (-(k:ℝ))) :
    b r ≤ 2*scaleFactor b k / k := by
  let c := Real.exp (-(k:ℝ))
  have cp : 0 < c := Real.exp_pos _
  have ch : c ≤ 1/2 := cutoff_le_half hk
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < (k:ℝ) := by linarith
  have br := (hb.2 r ⟨hr,hc.trans ch⟩).1
  have h := intervalIntegral.integral_mono_on ch
    (f := fun x => b r*x⁻¹) (g:=fun x => b x/x)
    ((continuousOn_const.mul (continuousOn_id.inv₀ (fun x hx => by
      rw [uIcc_of_le ch] at hx; exact (cp.trans_le hx.1).ne'))).intervalIntegrable)
    (integrable_truncated hb cp ch le_rfl) (by
      intro x hx
      dsimp only; rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right
        (hb.1 ⟨hr,hc.trans ch⟩ ⟨cp.trans_le hx.1,hx.2⟩ (hc.trans hx.1)) (cp.le.trans hx.1))
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos cp (by norm_num),
    Real.log_div (by norm_num) cp.ne', Real.log_div (by norm_num) (by norm_num), Real.log_one] at h
  have hlog : Real.log c = -(k:ℝ) := Real.log_exp _
  change _ ≤ truncated b c at h
  rw [hlog] at h
  have htwo : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  apply (le_div_iff₀ hpos).2
  change b r*k ≤ 2*(1+truncated b c)
  nlinarith only [h,mul_le_mul_of_nonneg_left htwo br,mul_le_mul_of_nonneg_left hk' br]

/-- The square-root envelope and the normalized truncated weight satisfy all
hypotheses of the finite block construction at scale `k`. -/
theorem exists_scale_weight {b : ℝ → ℝ} (hb : Admissible b) {k : ℕ} (hk : 2 ≤ k) :
    ∃ w : ℝ → ℝ, Measurable w ∧ (∀ r ∈ Ioc (0:ℝ) (1/2), w r ∈ Icc 0 1) ∧
      MonotoneOn w (Ioc (0:ℝ) (1/2)) ∧ IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2)) ∧
      (∫ r in Ioc (0:ℝ) (1/2), w r/r) ≤ 3 ∧
      (∀ r ∈ Ioc (0:ℝ) (1/2), Real.sqrt r ≤ w r) ∧
      (∀ r ∈ Icc (Real.exp (-(k:ℝ))) (1/2), b r ≤ scaleFactor b k * w r) ∧
      ∀ r ∈ Ioo (0:ℝ) (Real.exp (-(k:ℝ))), b r ≤ 2*scaleFactor b k/k := by
  classical
  let c := Real.exp (-(k:ℝ))
  let A := scaleFactor b k
  have cp : 0<c := Real.exp_pos _
  have ch : c≤1/2 := cutoff_le_half hk
  have A1 : 1≤A := one_le_scaleFactor hb hk
  have Ap : 0<A := by linarith
  let clamp (r : ℝ) := max c (min r (1/2))
  have cl (r : ℝ) : clamp r ∈ Icc c (1/2) := ⟨le_max_left ..,max_le ch (min_le_right ..)⟩
  have cv (r : ℝ) : clamp r ∈ Ioc (0:ℝ) (1/2) := ⟨cp.trans_le (cl r).1,(cl r).2⟩
  have clamp_mono : Monotone clamp := monotone_const.max (monotone_id.min monotone_const)
  let v (r : ℝ) := if c ≤ r then b (clamp r)/A else 0
  have v0 (r : ℝ) : 0 ≤ v r := by dsimp [v]; split <;> first | positivity | exact div_nonneg (hb.2 _ (cv r)).1 Ap.le
  have v1 (r : ℝ) : v r ≤ 1 := by
    dsimp [v]; split
    · apply (div_le_one Ap).2; exact (hb.2 _ (cv r)).2.trans A1
    · norm_num
  have vm : Monotone v := by
    intro x y hxy
    by_cases hx : c≤x
    · dsimp [v]; rw [if_pos hx,if_pos (hx.trans hxy)]
      exact div_le_div_of_nonneg_right (hb.1 (cv x) (cv y) (clamp_mono hxy)) Ap.le
    · simpa only [v,if_neg hx] using v0 y
  have vone {r : ℝ} (hr : r ∈ Icc c (1/2)) : v r = b r/A := by
    simp only [v,clamp,if_pos hr.1,min_eq_left hr.2,max_eq_right hr.1]
  let w (r : ℝ) := max (Real.sqrt r) (v r)
  have wm : Monotone w := Real.sqrt_monotone.max vm
  have wn (r : ℝ) : 0 ≤ w r := (Real.sqrt_nonneg r).trans (le_max_left ..)
  have w1 {r : ℝ} (hr : r ∈ Ioc (0:ℝ) (1/2)) : w r ≤ 1 := by
    apply max_le _ (v1 r)
    exact (Real.sqrt_le_one).2 (hr.2.trans (by norm_num))
  have vi : IntegrableOn (fun r => v r/r) (Ioc (0:ℝ) (1/2)) := by
    apply IntegrableOn.of_bound measure_Ioc_lt_top (vm.measurable.div measurable_id).aestronglyMeasurable c⁻¹
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioc] with r hr
    simp only [id_eq]
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (v0 _) hr.1.le)]
    by_cases h : c ≤ r
    · exact (div_le_div_of_nonneg_right (v1 r) hr.1.le).trans (by simpa [one_div] using inv_anti₀ cp h)
    · simp [v,h,inv_nonneg.mpr cp.le]
  have vis : IntervalIntegrable (fun r => v r/r) volume 0 (1/2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2 vi
  have subint (a d : ℝ) (ha : a ∈ Icc (0:ℝ) (1/2)) (hd : d ∈ Icc (0:ℝ) (1/2)) :
      IntervalIntegrable (fun r => v r/r) volume a d := by
    apply vis.mono_set
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
    exact uIcc_subset_Icc ha hd
  have zeroI : (∫ r in (0:ℝ)..c, v r/r) = 0 := by
    calc
      _ = ∫ _ in (0:ℝ)..c, (0:ℝ) := by
        apply intervalIntegral.integral_congr_ae
        have hn : ∀ᵐ x : ℝ ∂volume, x ≠ c := by simp [ae_iff]
        filter_upwards [hn] with x hx
        intro h
        rw [uIoc_of_le cp.le] at h
        simp [v,not_le.mpr (lt_of_le_of_ne h.2 hx)]
      _ = _ := by simp
  have tailI : (∫ r in c..(1/2:ℝ), v r/r) = truncated b c/A := by
    calc
      _ = ∫ r in c..(1/2:ℝ), (b r/r)/A := by
        apply intervalIntegral.integral_congr; intro r hr
        rw [uIcc_of_le ch] at hr; dsimp only; rw [vone hr]; ring
      _ = _ := intervalIntegral.integral_div ..
  have smallV : (∫ r in Ioc (0:ℝ) (1/2), v r/r) ≤ 1 := by
    rw [← intervalIntegral.integral_of_le (by norm_num),← intervalIntegral.integral_add_adjacent_intervals
      (subint 0 c (by constructor <;> norm_num) ⟨cp.le,ch⟩)
      (subint c (1/2) ⟨cp.le,ch⟩ (by constructor <;> norm_num)),zeroI,zero_add,tailI]
    apply (div_le_one Ap).2
    change truncated b c ≤ 1+truncated b c; linarith
  have si : IntegrableOn (fun r : ℝ => (Real.sqrt r)⁻¹) (Ioc (0:ℝ) (1/2)) :=
    inv_sqrt_integrable.1.mono_set (Ioc_subset_Ioc le_rfl (by norm_num))
  have smallS : (∫ r in Ioc (0:ℝ) (1/2), (Real.sqrt r)⁻¹) ≤ 2 := by
    rw [← intervalIntegral.integral_of_le (by norm_num)]
    calc
      _ ≤ ∫ r in (0:ℝ)..1, (Real.sqrt r)⁻¹ := intervalIntegral.integral_mono_interval le_rfl
        (by norm_num) (by norm_num) (Filter.Eventually.of_forall fun _ => inv_nonneg.mpr (Real.sqrt_nonneg _)) inv_sqrt_integrable
      _ = 2 := inv_sqrt_integral
  have point {r : ℝ} (hr : r ∈ Ioc (0:ℝ) (1/2)) : w r/r ≤ (Real.sqrt r)⁻¹+v r/r := by
    have hs : Real.sqrt r/r = (Real.sqrt r)⁻¹ := by
      have h := Real.sqrt_pos.2 hr.1
      field_simp [h.ne',hr.1.ne']
      exact Real.sq_sqrt hr.1.le
    rw [show w r/r = max (Real.sqrt r/r) (v r/r) by rw [← max_div_div_right hr.1.le],hs]
    exact max_le (le_add_of_nonneg_right (div_nonneg (v0 _) hr.1.le))
      (le_add_of_nonneg_left (inv_nonneg.mpr (Real.sqrt_nonneg _)))
  have wi : IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2)) := by
    apply (si.add vi).mono' (wm.measurable.div measurable_id).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioc] with r hr
    simp only [id_eq]
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (wn _) hr.1.le)]
    exact point hr
  refine ⟨w,wm.measurable,fun r hr => ⟨wn r,w1 hr⟩,wm.monotoneOn _,wi,?_,
    fun _ _ => le_max_left ..,?_,fun _ hr => below_cutoff hb hk hr.1 hr.2.le⟩
  · have h := integral_mono_ae wi (si.add vi) ((ae_restrict_mem (μ:=volume) measurableSet_Ioc).mono
      (fun r hr => point hr))
    simp only [Pi.add_apply] at h
    rw [integral_add si vi] at h
    linarith
  · intro r hr
    have h : v r ≤ w r := le_max_right ..
    rw [vone hr] at h
    simpa [mul_comm] using (div_le_iff₀ Ap).1 h

/-- Either the logarithmic scale is bounded, or an admissible dyadic level
has cutoff above δ and its thickening error costs at most `2/log(1/δ)`. -/
theorem choose_dyadic (C : ℝ) {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/2) :
    Real.log (1/δ) < 4*max C 1 ∨
      ∃ j : ℕ, let k : ℝ := 2^(j+1)
        2*max C 1*k ≤ Real.log (1/δ) ∧ Real.log (1/δ) ≤ 4*max C 1*k ∧
        δ ≤ Real.exp (-k) ∧ δ*Real.exp (C*k) ≤ 2/Real.log (1/δ) := by
  let D := max C 1
  let L := Real.log (1/δ)
  have D1 : 1 ≤ D := le_max_right ..
  have Dpos : 0 < D := by linarith
  have C_le : C ≤ D := le_max_left ..
  by_cases h : L < 4*D
  · exact Or.inl h
  apply Or.inr
  have hL : 4*D ≤ L := le_of_not_gt h
  have Lpos : 0 < L := Real.log_pos ((lt_div_iff₀ hd).2 (by linarith))
  have H : 1 ≤ L/(4*D) := (le_div_iff₀ (by positivity)).2 (by linarith)
  obtain ⟨j,lo,hi⟩ := exists_nat_pow_near H (by norm_num : (1:ℝ) < 2)
  let k : ℝ := 2^(j+1)
  have kp : 0 < k := by dsimp [k]; positivity
  have lbound : 2*D*k ≤ L := by
    dsimp [k]; rw [pow_succ]
    linarith only [(le_div_iff₀ (by positivity)).1 lo]
  have ubound : L ≤ 4*D*k := by linarith only [(div_lt_iff₀ (by positivity)).1 hi]
  have ed : δ = Real.exp (-L) := by simp [L,one_div,Real.exp_log hd]
  have km : k ≤ L := by nlinarith only [lbound,mul_le_mul_of_nonneg_right D1 kp.le,kp]
  refine ⟨j,lbound,ubound,?_,?_⟩
  · rw [ed]; exact Real.exp_le_exp.mpr (neg_le_neg km)
  · change δ*Real.exp (C*k) ≤ 2/L
    rw [ed,← Real.exp_add]
    calc
      _ ≤ Real.exp (-(L/2)) := Real.exp_le_exp.mpr (by nlinarith only [lbound,mul_le_mul_of_nonneg_right C_le kp.le])
      _ ≤ 2/L := by
        rw [Real.exp_neg,← one_div]
        apply (div_le_div_iff₀ (Real.exp_pos _) Lpos).2
        linarith [Real.add_one_le_exp (L/2)]

/-- Convert dyadic estimates into one uniform bound, including the coarse
scales where the bounded fallback is used. The factor `a` can equal one for
Favard length or `1 + truncated b δ` for the angular supremum. -/
theorem all_scales_upper {B D C a y δ : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) (ha : 1 ≤ a)
    (hd : 0 < δ) (hh : δ ≤ 1/2) (hcoarse : y ≤ B)
    (hfine : ∀ j : ℕ, let k : ℝ := 2^(j+1)
      δ ≤ Real.exp (-k) → y ≤ D*a/k + D*(δ*Real.exp (C*k))) :
    y ≤ ((4*max C 1*(B+D)+2*D)*a) / Real.log (1/δ) := by
  let L := Real.log (1/δ)
  let E := max C 1
  have ep : 0 ≤ E := zero_le_one.trans (le_max_right ..)
  have lp : 0 < L := Real.log_pos ((lt_div_iff₀ hd).2 (by linarith))
  have hA : 0 ≤ a := zero_le_one.trans ha
  rcases choose_dyadic C hd hh with small | ⟨j,_,hu,hcut,herr⟩
  · apply (le_div_iff₀ lp).2
    have he : B*L ≤ B*(4*E) := mul_le_mul_of_nonneg_left small.le hB
    have h0 : 0 ≤ 4*E*(B+D)+2*D := by positivity
    nlinarith only [mul_le_mul_of_nonneg_right hcoarse lp.le,he,
      mul_nonneg ep hD,mul_le_mul_of_nonneg_left ha h0,hD]
  · let k : ℝ := 2^(j+1)
    have kp : 0 < k := by dsimp [k]; positivity
    have bound := hfine j hcut
    have inner : D*a/k ≤ (4*E*D*a)/L := by
      apply (div_le_div_iff₀ kp lp).2
      nlinarith only [mul_le_mul_of_nonneg_left hu (mul_nonneg hD hA)]
    have err : D*(δ*Real.exp (C*k)) ≤ (2*D)/L := by
      convert mul_le_mul_of_nonneg_left herr hD using 1; ring
    change y ≤ D*a/k + D*(δ*Real.exp (C*k)) at bound
    change y ≤ _ / L
    apply bound.trans
    calc
      _ ≤ (4*E*D*a)/L+(2*D)/L := add_le_add inner err
      _ ≤ _ := by
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ lp.le
        change _ ≤ (4*E*(B+D)+2*D)*a
        nlinarith only [mul_nonneg (mul_nonneg ep hB) hA,mul_le_mul_of_nonneg_left ha hD]

end
end PermutationStrips.Angular
