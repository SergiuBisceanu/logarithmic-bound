import PermutationStrips.Weighted
import PermutationStrips.Pattern
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The directional energy of squares over one equal grid

The top intervals may be placed independently. A distant pair of grid columns
uses the weighted crossing estimate; adjacent columns and the diagonal use the
integral of the regularized density. The resulting budget is logarithmic even
when the angular cutoff reaches one grid spacing.
-/

open MeasureTheory Set
open scoped Interval BigOperators

namespace PermutationStrips.AngularLower
open Crossings Weighted
noncomputable section

/-- Endpoint squares; the lower endpoints are indexed by the grid,
and the upper starts are expressed in grid units. -/
def squares {n : ℕ} (b : Fin n → ℝ) : Set (ℝ × ℝ) :=
  ⋃ i, Icc ((n:ℝ)⁻¹*i.val) ((n:ℝ)⁻¹*(i.val+1)) ×ˢ
       Icc ((n:ℝ)⁻¹*b i) ((n:ℝ)⁻¹*(b i+1))

theorem compact_squares {n : ℕ} (b : Fin n → ℝ) : IsCompact (squares b) :=
  isCompact_iUnion fun _ => isCompact_Icc.prod isCompact_Icc

theorem projected_squares {n : ℕ} (b : Fin n → ℝ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    projection t '' squares b = ⋃ i, (Prod.mk t) ⁻¹' strip (n:ℝ)⁻¹ i.val (b i) := by
  let w := (n:ℝ)⁻¹
  ext x
  constructor
  · rintro ⟨⟨a,d⟩, hz, rfl⟩
    obtain ⟨i, h⟩ := mem_iUnion.mp hz
    obtain ⟨⟨ha,ha'⟩,hd,hd'⟩ := h
    refine mem_iUnion.mpr ⟨i,?_⟩
    change w*path i.val (b i) t ≤ (1-t)*a+t*d ∧ (1-t)*a+t*d ≤ w*(path i.val (b i) t+1)
    change w*_ ≤ a at ha
    change a ≤ w*_ at ha'
    change w*_ ≤ d at hd
    change d ≤ w*_ at hd'
    unfold path
    constructor
    · nlinarith only [mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht.2),
        mul_le_mul_of_nonneg_left hd ht.1]
    · nlinarith only [mul_le_mul_of_nonneg_left ha' (sub_nonneg.mpr ht.2),
        mul_le_mul_of_nonneg_left hd' ht.1]
  · intro hx
    obtain ⟨i,hl,hr⟩ := mem_iUnion.mp hx
    let s := x - w*path i.val (b i) t
    have h₁ : 0 ≤ s := sub_nonneg.mpr hl
    have h₂ : s ≤ w := by change x ≤ w*(path i.val (b i) t+1) at hr; dsimp [s]; linarith
    refine ⟨(w*i.val+s,w*b i+s),mem_iUnion.mpr ⟨i,?_⟩,?_⟩
    · change (_ ≤ _ ∧ _ ≤ _) ∧ _ ≤ _ ∧ _ ≤ _
      dsimp [w] at *
      constructor <;> constructor <;> linarith
    · dsimp [projection,s,path]; ring

/-- The multiplicity second moment at height `t`. -/
def energy {n : ℕ} (b : Fin n → ℝ) (t : ℝ) : ℝ :=
  (n:ℝ)⁻¹ * ∑ i, ∑ j, overlap b i j t

private theorem continuous_energy {n : ℕ} (b : Fin n → ℝ) : Continuous (energy b) :=
  continuous_const.mul (continuous_finset_sum _ fun _ _ =>
    continuous_finset_sum _ fun _ _ => continuous_overlap ..)

private theorem energy_nonneg {n : ℕ} (b : Fin n → ℝ) (t : ℝ) : 0 ≤ energy b t := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => le_max_right ..

/-- Cauchy–Schwarz on the genuine union of projected intervals. -/
theorem one_le_length_energy {n : ℕ} (hn : 0 < n) (b : Fin n → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hb' : ∀ i, b i+1 ≤ n) {t : ℝ} (ht : t ∈ Ioc (0:ℝ) 1) :
    1 ≤ volume.real (projection t '' squares b) * energy b t := by
  classical
  let w := (n:ℝ)⁻¹
  let S (i : Fin n) := (Prod.mk t) ⁻¹' strip w i.val (b i)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hw : 0 < w := inv_pos.mpr hnR
  have bounds {x : ℝ} (hx : x+1 ≤ n) : w*(x+1) ≤ 1 := by
    simpa [w, ← div_eq_inv_mul] using (div_le_one hnR).2 hx
  have pair (i j : Fin n) : spaceMeasure.real (S i ∩ S j) = w*overlap b i j t := by
    change spaceMeasure.real ((Prod.mk t) ⁻¹' (strip w i.val (b i) ∩ strip w j.val (b j))) = _
    rw [section_pair hw (Nat.cast_nonneg _) (hb i) (bounds (by exact_mod_cast i.isLt))
      (bounds (hb' i)) ht, length_inter_slice]
    rfl
  have one (i : Fin n) : spaceMeasure.real (S i) = w := by
    simpa [overlap, tent] using pair i i
  have dual (c : ℝ) : 2*c-c^2*energy b t ≤ spaceMeasure.real (⋃ i, S i) := by
    have h := union_lower spaceMeasure S (fun i => measurable_prodMk_left (measurable_strip ..)) c
    simp_rw [one, pair, ← Finset.mul_sum] at h
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      show (n:ℝ)*w=1 by dsimp [w]; field_simp,mul_one] at h
    simpa only [energy, mul_assoc] using h
  have hu : spaceMeasure.real (⋃ i, S i) ≤ 1 := by
    simpa [spaceMeasure,measureReal_def] using
      (measureReal_mono (μ:=spaceMeasure) (subset_univ (⋃ i, S i)))
  have hpos : 0 < energy b t := by linarith [dual 1]
  have hd := dual (energy b t)⁻¹
  have hu' : spaceMeasure.real (⋃ i, S i) ≤ volume.real (projection t '' squares b) := by
    rw [projected_squares b ⟨ht.1.le,ht.2⟩]
    change spaceMeasure.real (⋃ i,S i) ≤ volume.real (⋃ i,S i)
    rw [spaceMeasure,measureReal_restrict_apply' measurableSet_Icc]
    refine measureReal_mono inter_subset_left ?_
    have hc := (compact_squares b).image (by unfold projection; fun_prop : Continuous (projection t))
    rw [projected_squares b ⟨ht.1.le,ht.2⟩] at hc
    exact hc.measure_lt_top.ne
  have invbound : (energy b t)⁻¹ ≤ volume.real (projection t '' squares b) := by
    calc
      _ = 2*(energy b t)⁻¹-((energy b t)⁻¹)^2*energy b t := by field_simp [hpos.ne']; ring
      _ ≤ _ := hd.trans hu'
  simpa [hpos.ne'] using mul_le_mul_of_nonneg_right invbound hpos.le

private theorem integral_test_sq {ε : ℝ} (hε : 0 < ε) :
    (∫ t in (0:ℝ)..1, (test ε t)^2) = Real.log (ε+1)-Real.log ε := by
  have hd (t : ℝ) (ht : t ∈ uIcc (0:ℝ) 1) :
      HasDerivAt (fun t : ℝ => Real.log (ε+t)) ((test ε t)^2) t := by
    rw [uIcc_of_le zero_le_one] at ht
    rw [test_sq hε ht.1]
    have h := (((hasDerivAt_id t).const_add ε).log (by dsimp; linarith [ht.1]))
    simpa [id_eq,one_div] using h
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd (((continuous_test hε).pow 2).intervalIntegrable ..)

private theorem grid_budget {n : ℕ} (hn : 2 ≤ n) (b : Fin n → ℝ) :
    (∫ t in (0:ℝ)..1, (test (n:ℝ)⁻¹ t)^2 * energy b t) ≤
      2*(harmonic n:ℝ)+3*Real.log ((n:ℝ)+1) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  let ε := (n:ℝ)⁻¹
  let L := Real.log ((n:ℝ)+1)
  have hε : 0 < ε := inv_pos.mpr hnR
  have hL : 0 < L := Real.log_pos (by linarith)
  let f (i j : Fin n) (t : ℝ) := (test ε t)^2*overlap b i j t
  have cont (i j : Fin n) : Continuous (f i j) :=
    ((continuous_test hε).pow 2).mul (continuous_overlap ..)
  have pair (i j : Fin n) : (∫ t in (0:ℝ)..1, f i j t) ≤ cost L⁻¹ (Nat.dist i.val j.val) := by
    by_cases near : Nat.dist i.val j.val ≤ 1
    · rw [cost, if_pos near, inv_inv]
      calc
        _ ≤ ∫ t in (0:ℝ)..1, (test ε t)^2 := by
          apply intervalIntegral.integral_mono_on zero_le_one ((cont ..).intervalIntegrable ..)
            (((continuous_test hε).pow 2).intervalIntegrable ..)
          intro t _
          apply mul_le_of_le_one_right (sq_nonneg _)
          exact max_le (by linarith [abs_nonneg (path j.val (b j) t - path i.val (b i) t)]) zero_le_one
        _ = L := by
          rw [integral_test_sq hε, ← Real.log_div (by positivity) hε.ne']
          congr 1; dsimp [ε]; field_simp; ring
    · simpa only [cost,if_neg near,f] using weighted_pair hε b i j
  have h := (Finset.sum_le_sum (s:=Finset.univ) fun i _ =>
    Finset.sum_le_sum (s:=Finset.univ) fun j _ => pair i j).trans (total_cost n (inv_pos.mpr hL))
  simp only [inv_inv] at h
  have form (t : ℝ) : (test ε t)^2*energy b t = (n:ℝ)⁻¹ * ∑ i, ∑ j, f i j t := by
    simp only [energy,f, ← Finset.mul_sum]
    ring
  change (∫ t in (0:ℝ)..1, (test ε t)^2*energy b t) ≤ _
  simp_rw [form]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finset_sum
    (fun i _ => (continuous_finset_sum _ fun j _ => cont i j).intervalIntegrable ..)]
  simp_rw [intervalIntegral.integral_finset_sum (fun j _ => (cont _ j).intervalIntegrable ..)]
  simpa [ε,L,hnR.ne'] using mul_le_mul_of_nonneg_left h hε.le

/-- Directional lower estimate with an arbitrary majorant for weighted projected
lengths, uniform in the freely sliding top intervals and the cutoff distance. -/
theorem height_weight_bound {n : ℕ} (hn : 2 ≤ n) (b : Fin n → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hb' : ∀ i, b i+1 ≤ n) {δ M : ℝ}
    (hδ : (n:ℝ)⁻¹ ≤ δ) (hhalf : δ ≤ 1/2) (hM : 0 ≤ M) (f : ℝ → ℝ)
    (hf : IntervalIntegrable (fun t => f t/t) volume δ (1/2))
    (hf₀ : ∀ t ∈ Icc δ (1/2), 0 ≤ f t)
    (cap : ∀ t ∈ Icc δ (1/2), f t * volume.real (projection t '' squares b) ≤ M) :
    (∫ t in δ..(1/2:ℝ), f t/t) ≤ 24 * Real.log n * M := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hε : 0 < (n:ℝ)⁻¹ := by positivity
  have dpos := hε.trans_le hδ
  let g (t : ℝ) := (test (n:ℝ)⁻¹ t)^2 * energy b t
  have hg : Continuous g := ((continuous_test hε).pow 2).mul (continuous_energy b)
  have gn t : 0 ≤ g t := mul_nonneg (sq_nonneg _) (energy_nonneg b t)
  have pt (t : ℝ) (ht : t ∈ Icc δ (1/2)) : f t / t ≤ (2*M)*g t := by
    have tp := dpos.trans_le ht.1
    have ep : 0 ≤ energy b t := energy_nonneg ..
    have hc := one_le_length_energy (show 0 < n by omega) b hb hb' (t:=t)
      ⟨tp,by linarith [ht.2]⟩
    have fbound : f t ≤ M * energy b t := by
      linarith only [mul_le_mul_of_nonneg_left hc (hf₀ t ht), mul_le_mul_of_nonneg_right (cap t ht) ep]
    dsimp [g]; rw [test_sq hε tp.le, ← one_div]
    have he : 0 < (n:ℝ)⁻¹+t := by positivity
    calc
      f t/t ≤ (M*energy b t)/t := div_le_div_of_nonneg_right fbound tp.le
      _ ≤ (2*M)*(1/((n:ℝ)⁻¹+t)*energy b t) := by
        have hrec : 1/t ≤ 2/((n:ℝ)⁻¹+t) := (div_le_div_iff₀ tp he).2 (by linarith [hδ.trans ht.1])
        have h := mul_le_mul_of_nonneg_left hrec (mul_nonneg hM ep)
        convert h using 1 <;> ring
  have rangele : (∫ t in δ..(1/2:ℝ), g t) ≤ ∫ t in (0:ℝ)..1, g t :=
    intervalIntegral.integral_mono_interval dpos.le hhalf (by norm_num)
      (Filter.Eventually.of_forall gn) (hg.intervalIntegrable ..)
  have hlog : Real.log 2 ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) hnR
  have hlog' : Real.log ((n:ℝ)+1) ≤ 2*Real.log n := by
    calc
      _ ≤ Real.log (2*(n:ℝ)) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2+Real.log n := Real.log_mul (by norm_num) (by positivity)
      _ ≤ _ := by linarith
  have H : (∫ t in (0:ℝ)..1, g t) ≤ 12*Real.log n := by
    have h := grid_budget hn b
    change (∫ t in (0:ℝ)..1, g t) ≤ _ at h
    linarith only [h, harmonic_le_one_add_log n, hlog',hlog,Real.log_two_gt_d9]
  calc
    _ ≤ ∫ t in δ..(1/2:ℝ), (2*M)*g t := intervalIntegral.integral_mono_on hhalf hf
      ((continuous_const.mul hg).intervalIntegrable ..) pt
    _ = _ := intervalIntegral.integral_const_mul ..
    _ ≤ 24 * Real.log n * M := by nlinarith only [mul_le_mul_of_nonneg_left (rangele.trans H) hM]

/-- The integrated projected lengths equal the physical free-top strip area. -/
theorem squares_area {n : ℕ} (hn : 0 < n) (b : Fin n → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hb' : ∀ i, b i+1 ≤ n) :
    (∫ t in (0:ℝ)..1, volume.real (projection t '' squares b)) =
      squareMeasure.real (⋃ i, strip (n:ℝ)⁻¹ i.val (b i)) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  rw [area_sections (MeasurableSet.iUnion fun _ => measurable_strip ..),
    intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [projected_squares b ⟨ht.1.le,ht.2⟩, preimage_iUnion, spaceMeasure,
    measureReal_restrict_apply' measurableSet_Icc, inter_eq_left.mpr]
  intro x hx
  obtain ⟨i,hl,hu⟩ := mem_iUnion.mp hx
  have hn' : (i.val:ℝ)+1 ≤ n := by exact_mod_cast i.isLt
  have lo : 0 ≤ path i.val (b i) t := add_nonneg
    (mul_nonneg (sub_nonneg.mpr ht.2) (Nat.cast_nonneg _)) (mul_nonneg ht.1.le (hb _))
  have hi : path i.val (b i) t+1 ≤ n := by
    unfold path
    nlinarith only [mul_le_mul_of_nonneg_left hn' (sub_nonneg.mpr ht.2),
      mul_le_mul_of_nonneg_left (hb' i) ht.1.le]
  refine ⟨(mul_nonneg (inv_pos.mpr hnR).le lo).trans hl,hu.trans ?_⟩
  simpa [← div_eq_inv_mul] using (div_le_one hnR).2 hi

end
end PermutationStrips.AngularLower
