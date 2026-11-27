import PermutationStrips.Crossings
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Data.Nat.Dist

/-!
# Weighted area lower bounds for sliding and permutation strips

The height test is `1 / √(ε+t)`. For bottom gaps of at least two grid units,
a nonzero overlap forces the relative velocity times the height to be at least
the gap minus one. This bounds the weighted contribution of a distant pair
without imposing any order on the top intervals. Its integral tends to two,
giving the free-top lower leading constant two. For a permutation, reflecting
time exchanges the two uniform grids. Averaging the squared tests from the
two ends gives an arcsine integral and the lower leading constant `π² / 4`.
-/

open MeasureTheory Set Filter
open scoped Interval BigOperators Topology

namespace PermutationStrips.Weighted
open Crossings
noncomputable section

private def test (ε t : ℝ) : ℝ := (Real.sqrt (ε + max t 0))⁻¹

private theorem continuous_test {ε : ℝ} (hε : 0 < ε) : Continuous (test ε) := by
  unfold test
  apply Continuous.inv₀ (by fun_prop)
  intro t
  exact (Real.sqrt_pos.2 (by linarith [le_max_right t 0])).ne'

private theorem test_sq {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    test ε t ^ 2 = (ε+t)⁻¹ := by
  rw [test, max_eq_left ht, inv_pow, Real.sq_sqrt (by linarith)]

private theorem integral_test {ε : ℝ} (hε : 0 < ε) :
    (∫ t in (0 : ℝ)..1, test ε t) = 2 * (Real.sqrt (ε+1) - Real.sqrt ε) := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => 2 * Real.sqrt (ε+t)) (test ε x) x := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have hpos : 0 < ε+x := by linarith [hx.1]
    have h := (((hasDerivAt_id x).const_add ε).sqrt hpos.ne').const_mul 2
    convert h using 1
    simp [test, max_eq_left hx.1, id]
    ring
  simpa [mul_sub] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_test hε).intervalIntegrable ..)

private theorem tent_mass_le {p v : ℝ} (hp : 1 ≤ p) (hv : 0 < v) :
    (∫ t in (0 : ℝ)..1, tent (p-v*t)) ≤ v⁻¹ := by
  rw [intervalIntegral.integral_comp_sub_mul tent hv.ne' p]
  simp only [mul_one, mul_zero, sub_zero, smul_eq_mul]
  have h : (∫ x in (p-v)..p, tent x) ≤ 1 := by
    calc
      _ ≤ ∫ x in min (p-v) (-1)..p, tent x := intervalIntegral.integral_mono_interval
        (min_le_left ..) (by linarith) le_rfl (Eventually.of_forall fun _ => le_max_right ..)
        (continuous_tent.intervalIntegrable ..)
      _ = 1 := integral_tent _ _ (min_le_right ..) hp
  simpa using mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hv.le)

/-- The bound for a single distant pair. The two top positions are arbitrary. -/
private theorem far_pair {ε p v : ℝ} (hε : 0 < ε) (hp : 1 < p) :
    (∫ t in (0 : ℝ)..1, (test ε t)^2 * tent (p - v*t)) ≤ (p-1)⁻¹ := by
  have hi : Continuous (fun t : ℝ => tent (p-v*t)) := continuous_tent.comp (by fun_prop)
  by_cases hv : 0 < v
  · have pt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        (test ε t)^2 * tent (p-v*t) ≤ (v/(p-1))*tent (p-v*t) := by
      by_cases hn : 0 < tent (p-v*t)
      · have hgap : p-v*t < 1 := by
          have h := (lt_max_iff.mp hn).resolve_right (lt_irrefl _)
          linarith [le_abs_self (p-v*t)]
        rw [test_sq hε ht.1, ← one_div]
        apply mul_le_mul_of_nonneg_right _ hn.le
        apply (div_le_div_iff₀ (by linarith [ht.1]) (by linarith)).2
        nlinarith [mul_pos hv hε]
      · have hz := le_antisymm (le_of_not_gt hn) (le_max_right (1-|p-v*t|) 0)
        simp [hz]
    calc
      _ ≤ ∫ t in (0 : ℝ)..1, (v/(p-1))*tent (p-v*t) :=
        intervalIntegral.integral_mono_on zero_le_one
          (((continuous_test hε).pow 2).mul hi |>.intervalIntegrable ..)
          ((continuous_const.mul hi).intervalIntegrable ..) pt
      _ = _ := by rw [intervalIntegral.integral_const_mul]
      _ ≤ (v/(p-1))*v⁻¹ := mul_le_mul_of_nonneg_left (tent_mass_le hp.le hv)
        (div_nonneg hv.le (sub_nonneg.mpr hp.le))
      _ = _ := by field_simp
  · have hz : (∫ t in (0 : ℝ)..1, (test ε t)^2 * tent (p-v*t)) = 0 := by
      calc
        _ = ∫ _ in (0 : ℝ)..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le zero_le_one] at ht
          have hvt := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hv) ht.1
          have hgap : 1 ≤ p - v*t := by linarith
          simp [tent, abs_of_nonneg (by linarith : 0 ≤ p-v*t), max_eq_right (sub_nonpos.mpr hgap)]
        _ = 0 := by simp
    rw [hz]; exact inv_nonneg.mpr (sub_nonneg.mpr hp.le)

private def cost (ε : ℝ) (d : ℕ) : ℝ :=
  if d ≤ 1 then ε⁻¹ else ((d-1 : ℕ):ℝ)⁻¹

private theorem cost_prefix (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∑ i ∈ Finset.range n, cost ε (i+1) ≤ ε⁻¹ + (harmonic n : ℝ) := by
  cases n with
  | zero => simp [inv_nonneg.mpr hε.le]
  | succ n =>
    rw [Finset.sum_range_succ']
    have ht (i : ℕ) : cost ε (i+1+1) = (((i+1:ℕ):ℝ))⁻¹ := by simp [cost]
    simp_rw [ht]
    have hH : (∑ i ∈ Finset.range n, (((i+1:ℕ):ℝ))⁻¹) = (harmonic n : ℝ) := by
      simp [harmonic]
    rw [hH, harmonic_succ]
    simp [cost]
    linarith [show 0 ≤ ((n:ℝ)+1)⁻¹ by positivity]

private theorem total_cost (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (∑ i : Fin n, ∑ j : Fin n, cost ε (Nat.dist i.val j.val)) ≤
      (n:ℝ) * (2 * (harmonic n : ℝ) + 3 * ε⁻¹) := by
  have reduce (i : ℕ) : (∑ j : Fin n, cost ε (Nat.dist i j.val)) =
      ∑ j ∈ Finset.range n, cost ε (Nat.dist i j) := Fin.sum_univ_eq_sum_range (fun j => cost ε (Nat.dist i j)) n
  simp_rw [reduce]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range n, cost ε (Nat.dist i j)) n]
  clear reduce
  induction n with
  | zero => simp
  | succ n ih =>
    have row : (∑ i ∈ Finset.range n, cost ε (Nat.dist n i)) ≤ ε⁻¹ + (harmonic n : ℝ) := by
      calc
        _ = ∑ i ∈ Finset.range n, cost ε ((n-1-i)+1) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hin := Finset.mem_range.mp hi
          rw [Nat.dist_eq_sub_of_le_right hin.le]
          congr 1; omega
        _ = ∑ i ∈ Finset.range n, cost ε (i+1) :=
          Finset.sum_range_reflect (fun i => cost ε (i+1)) n
        _ ≤ _ := cost_prefix n hε
    have col : (∑ i ∈ Finset.range n, cost ε (Nat.dist i n)) ≤ ε⁻¹ + (harmonic n : ℝ) := by
      simpa only [Nat.dist_comm n] using row
    rw [Finset.sum_range_succ]
    simp_rw [Finset.sum_range_succ, Finset.sum_add_distrib]
    simp only [Nat.dist_self, cost, if_pos (by decide : 0 ≤ 1)] at *
    rw [harmonic_succ]
    push_cast
    nlinarith [show 0 ≤ (n:ℝ) * ((n:ℝ)+1)⁻¹ by positivity,
      show 0 ≤ ((n:ℝ)+1)⁻¹ by positivity]

private def overlap {n : ℕ} (b : Fin n → ℝ) (i j : Fin n) (t : ℝ) : ℝ :=
  tent (path j.val (b j) t - path i.val (b i) t)

private theorem continuous_overlap {n : ℕ} (b : Fin n → ℝ) (i j : Fin n) :
    Continuous (overlap b i j) :=
  continuous_tent.comp (by unfold path; fun_prop)

private theorem weighted_pair {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (b : Fin n → ℝ) (i j : Fin n) :
    (∫ t in (0 : ℝ)..1, (test ε t)^2 * overlap b i j t) ≤
      cost ε (Nat.dist i.val j.val) := by
  by_cases near : Nat.dist i.val j.val ≤ 1
  · rw [cost, if_pos near]
    calc
      _ ≤ ∫ _ in (0 : ℝ)..1, ε⁻¹ := by
        apply intervalIntegral.integral_mono_on zero_le_one
          ((((continuous_test hε).pow 2).mul (continuous_overlap ..)).intervalIntegrable ..)
          (continuous_const.intervalIntegrable ..)
        intro t ht
        have hnon := abs_nonneg (path j.val (b j) t - path i.val (b i) t)
        have ht1 : overlap b i j t ≤ 1 := max_le (by linarith) zero_le_one
        have htest := inv_anti₀ hε (show ε ≤ ε+t by linarith [ht.1])
        rw [test_sq hε ht.1]
        exact (mul_le_mul_of_nonneg_left ht1 (inv_nonneg.mpr (by linarith [ht.1]))).trans (by simpa using htest)
      _ = _ := by simp
  · have ordered (k l : Fin n) (hkl : k ≤ l) (hfar : ¬Nat.dist k.val l.val ≤ 1) :
        (∫ t in (0 : ℝ)..1, (test ε t)^2 * overlap b k l t) ≤
          cost ε (Nat.dist k.val l.val) := by
      have hn : k.val ≤ l.val := hkl
      rw [Nat.dist_eq_sub_of_le hn] at hfar ⊢
      let p : ℝ := l.val - k.val
      let v : ℝ := p - (b l - b k)
      have hp : 1 < p := by
        have hh : (k.val : ℝ)+1 < l.val := by exact_mod_cast (show k.val+1 < l.val by omega)
        dsimp [p]; linarith
      have shape (t : ℝ) : overlap b k l t = tent (p-v*t) := by
        unfold overlap
        congr 1; unfold path p v; ring
      simp_rw [shape]
      rw [cost, if_neg hfar, Nat.cast_sub (by omega : 1 ≤ l.val-k.val), Nat.cast_sub hn,
        Nat.cast_one]
      exact far_pair hε hp
    rcases le_total i j with hij | hji
    · exact ordered i j hij near
    · have sym (t : ℝ) : overlap b i j t = overlap b j i t := by
        simp [overlap, tent, abs_sub_comm]
      simp_rw [sym, Nat.dist_comm i.val j.val]
      exact ordered j i hji (by simpa only [Nat.dist_comm j.val] using near)

private theorem integral_overlap_budget {n : ℕ} (hn : 0 < n) (b : Fin n → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    (n:ℝ)⁻¹ * (∫ t in (0 : ℝ)..1, ∑ i, ∑ j, (test ε t)^2 * overlap b i j t) ≤
      2 * (harmonic n : ℝ) + 3 * ε⁻¹ := by
  have hint (i j : Fin n) : IntervalIntegrable
      (fun t => (test ε t)^2 * overlap b i j t) volume 0 1 :=
    (((continuous_test hε).pow 2).mul (continuous_overlap ..)).intervalIntegrable ..
  have row (i : Fin n) : IntervalIntegrable (fun t => ∑ j, (test ε t)^2 * overlap b i j t) volume 0 1 :=
    (continuous_finset_sum _ fun j _ => ((continuous_test hε).pow 2).mul (continuous_overlap ..)).intervalIntegrable ..
  rw [intervalIntegral.integral_finset_sum (fun i _ => row i)]
  simp_rw [intervalIntegral.integral_finset_sum (fun j _ => hint _ j)]
  have hc := (Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => weighted_pair hε b i j).trans (total_cost n hε)
  simpa [hn.ne'] using mul_le_mul_of_nonneg_left hc (show 0 ≤ (n:ℝ)⁻¹ by positivity)

private theorem test_lower {n : ℕ} (hn : 0 < n) (b : Fin n → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hb' : ∀ i, b i+1 ≤ n) (g : ℝ → ℝ) (hg : Continuous g)
    {E : ℝ} (hE : 0 < E)
    (hbudget : (n:ℝ)⁻¹ * (∫ t in (0:ℝ)..1, ∑ i, ∑ j, (g t)^2 * overlap b i j t) ≤ E) :
    (∫ t in (0:ℝ)..1, g t)^2 / E ≤ squareMeasure.real (⋃ i, strip (n:ℝ)⁻¹ i.val (b i)) := by
  classical
  let w := (n:ℝ)⁻¹
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hw : 0 < w := inv_pos.mpr hnR
  let S (i : Fin n) := strip w i.val (b i)
  let U := ⋃ i, S i
  let L (t : ℝ) := spaceMeasure.real ((Prod.mk t) ⁻¹' U)
  let K (t : ℝ) := ∑ i, ∑ j, (g t)^2 * overlap b i j t
  let m := ∫ t in (0:ℝ)..1, g t
  let c := m/E
  have ms (i : Fin n) : MeasurableSet (S i) := measurable_strip ..
  have mu : MeasurableSet U := MeasurableSet.iUnion ms
  have hL : Integrable L timeMeasure := by
    apply Integrable.of_bound (C := (1:ℝ)) (Measurable.aestronglyMeasurable
      (measurable_measure_prodMk_left (ν := spaceMeasure) mu).ennreal_toReal)
    filter_upwards with t
    have ht := measureReal_mono (μ := spaceMeasure)
      (subset_univ ((Prod.mk t) ⁻¹' U))
    simpa [L, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, spaceMeasure] using ht
  have hK : Continuous K := continuous_finset_sum _ fun _ _ =>
    continuous_finset_sum _ fun _ _ => (hg.pow 2).mul (continuous_overlap ..)
  have bounds {x : ℝ} (hx : x + 1 ≤ n) : w*(x+1) ≤ 1 := by
    simpa [w, ← div_eq_inv_mul] using (div_le_one hnR).2 hx
  have pair (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) (i j : Fin n) :
      spaceMeasure.real (((Prod.mk t) ⁻¹' S i) ∩ ((Prod.mk t) ⁻¹' S j)) = w * overlap b i j t := by
    change spaceMeasure.real ((Prod.mk t) ⁻¹' (strip w i.val (b i) ∩ strip w j.val (b j))) = _
    rw [section_pair hw (Nat.cast_nonneg _) (hb i)
      (bounds (by exact_mod_cast i.isLt)) (bounds (hb' i)) ht, length_inter_slice]
    rfl
  have pt (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) :
      2*c*g t - (c^2*w)*K t ≤ L t := by
    have one (i : Fin n) : spaceMeasure.real ((Prod.mk t) ⁻¹' S i) = w := by
      have h := pair t ht i i
      simpa [overlap, tent] using h
    have h := union_lower spaceMeasure (fun i => (Prod.mk t) ⁻¹' S i)
      (fun i => measurable_prodMk_left (ms i)) (c*g t)
    simp_rw [one, pair t ht, ← Finset.mul_sum] at h
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      show (n:ℝ)*w = 1 by dsimp [w]; field_simp, mul_one] at h
    change _ ≤ spaceMeasure.real ((Prod.mk t) ⁻¹' ⋃ i, S i)
    rw [preimage_iUnion]
    convert h using 1
    dsimp [K]
    simp_rw [← Finset.mul_sum]
    ring
  have hint : Integrable (fun t => 2*c*g t - (c^2*w)*K t) timeMeasure :=
    ((continuous_const.mul hg).sub
      (continuous_const.mul hK)).intervalIntegrable 0 1 |>.1
  have h := integral_mono_ae hint hL
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => pt t ht)
  rw [← area_sections mu] at h
  change (∫ t in Ioc (0:ℝ) 1, 2*c*g t-(c^2*w)*K t) ≤ _ at h
  rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_sub
    ((continuous_const.mul hg).intervalIntegrable ..)
    ((continuous_const.mul hK).intervalIntegrable ..), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  have hbound : w*(∫ t in (0:ℝ)..1, K t) ≤ E := hbudget
  change 2*c*m - c^2*w*(∫ t in (0:ℝ)..1, K t) ≤ squareMeasure.real U at h
  change m^2/E ≤ squareMeasure.real U
  calc
    m^2/E = 2*c*m-c^2*E := by dsimp [c]; field_simp; ring
    _ ≤ _ := le_trans (by nlinarith only [mul_le_mul_of_nonneg_left hbound (sq_nonneg c)]) h

/-- An explicit lower bound at every `n` and every positive regularization `ε`.
No assumption on relative order or separation of the upper intervals is used. -/
theorem regularized_sliding_lower {n : ℕ} (hn : 0 < n) (b : Fin n → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hb' : ∀ i, b i+1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    (2 * (Real.sqrt (ε+1) - Real.sqrt ε))^2 / (2*(harmonic n:ℝ) + 3*ε⁻¹) ≤
      squareMeasure.real (⋃ i, strip (n:ℝ)⁻¹ i.val (b i)) := by
  have hh : 0 ≤ (harmonic n:ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    positivity
  simpa only [integral_test hε] using test_lower hn b hb hb' (test ε) (continuous_test hε)
    (by positivity) (integral_overlap_budget hn b hε)

/-- The free-top lower leading constant, expressed uniformly over all admissible
configurations at each grid size. This is the eventual-bound formulation of liminf ≥ 2. -/
theorem eventually_sliding_lower {a : ℝ} (ha : a < 2) :
    ∀ᶠ n : ℕ in atTop, ∀ b : Fin n → ℝ, (∀ i, 0 ≤ b i) → (∀ i, b i+1 ≤ n) →
      a ≤ Real.log n * squareMeasure.real (⋃ i, strip (n:ℝ)⁻¹ i.val (b i)) := by
  let F (x : ℝ) := (2*(Real.sqrt (x+1)-Real.sqrt x))^2
  have hF : Continuous F := by unfold F; fun_prop
  have hnear : ∀ᶠ x in 𝓝[>] (0:ℝ), a < F x/2 :=
    ((hF.div_const 2).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually_const_lt
      (by norm_num [F]; exact ha)
  have hgt : ∀ᶠ x in 𝓝[>] (0:ℝ), 0 < x := self_mem_nhdsWithin
  obtain ⟨ε, hε, hae⟩ := (hgt.and hnear).exists
  change 0 < ε at hε
  let L (n : ℕ) : ℝ := Real.log n
  have hlog : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n => F ε / (2+(2+3*ε⁻¹)*(L n)⁻¹)) atTop (𝓝 (F ε/2)) := by
    simpa using (tendsto_const_nhds (x := F ε)).div
      ((tendsto_const_nhds (x := (2:ℝ))).add
        ((tendsto_const_nhds (x := 2+3*ε⁻¹)).mul (tendsto_inv_atTop_zero.comp hlog)))
      (by norm_num)
  filter_upwards [hlim.eventually_const_lt hae, eventually_ge_atTop (2:ℕ)] with n h₁ hn
  intro b hb hb'
  have hpos : 0 < L n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hh : 0 ≤ (harmonic n:ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    positivity
  have lower := regularized_sliding_lower (show 0 < n by omega) b hb hb' hε
  change F ε / (2*(harmonic n:ℝ)+3*ε⁻¹) ≤ _ at lower
  calc
    a ≤ F ε / (2+(2+3*ε⁻¹)*(L n)⁻¹) := h₁.le
    _ = L n * (F ε / (2*(1+L n)+3*ε⁻¹)) := by
      have he := hε.ne'
      have hl := hpos.ne'
      field_simp
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hpos.le
      refine le_trans (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) ?_) lower
      linarith [harmonic_le_one_add_log n]

private def coord (t : ℝ) : ℝ := max (-1) (min 1 (2*t-1))

private theorem coord_eq {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : coord t = 2*t-1 := by
  unfold coord
  rw [min_eq_right (by linarith [ht.2]), max_eq_right (by linarith [ht.1])]

private def symTest (ε t : ℝ) : ℝ :=
  ((1+2*ε) * Real.sqrt (1-(coord t/(1+2*ε))^2))⁻¹

private theorem coord_bounds {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    coord t/(1+2*ε) ∈ Ioo (-1:ℝ) 1 := by
  have hc : 0 < 1+2*ε := by linarith
  have hlo : -1 ≤ coord t := le_max_left ..
  have hhi : coord t ≤ 1 := max_le (by norm_num) (min_le_left ..)
  constructor
  · apply (lt_div_iff₀ hc).2; linarith
  · apply (div_lt_iff₀ hc).2; linarith

private theorem radicand_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 < 1-(coord t/(1+2*ε))^2 := by
  obtain ⟨hl,hu⟩ := coord_bounds hε t
  nlinarith [mul_pos (sub_pos.mpr hu) (sub_pos.mpr hl)]

private theorem continuous_symTest {ε : ℝ} (hε : 0 < ε) : Continuous (symTest ε) := by
  unfold symTest
  apply Continuous.inv₀ (by unfold coord; fun_prop)
  intro t
  exact mul_ne_zero (by positivity) (Real.sqrt_pos.2 (radicand_pos hε t)).ne'

private theorem symTest_sq {ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Icc (0:ℝ) 1) :
    (symTest ε t)^2 = ((test ε t)^2+(test ε (1-t))^2)/(4*(1+2*ε)) := by
  rw [symTest, inv_pow, mul_pow, Real.sq_sqrt (radicand_pos hε t).le,
    coord_eq ht, test_sq hε ht.1, test_sq hε (sub_nonneg.mpr ht.2)]
  have he : 0 < ε+t := by linarith [ht.1]
  have he' : 0 < ε+(1-t) := by linarith [ht.2]
  have hc : (1+2*ε) ≠ 0 := by positivity
  have h₁ : (1+2*ε)^2 * (1-((2*t-1)/(1+2*ε))^2) = 4*(ε+t)*(ε+(1-t)) := by
    field_simp
    ring
  rw [h₁]
  field_simp
  ring

private theorem integral_symTest {ε : ℝ} (hε : 0 < ε) :
    (∫ t in (0:ℝ)..1, symTest ε t) = Real.arcsin ((1+2*ε)⁻¹) := by
  let c := 1+2*ε
  have hc : 0 < c := by dsimp [c]; positivity
  have hd (t : ℝ) (ht : t ∈ uIcc (0:ℝ) 1) :
      HasDerivAt (fun t : ℝ => (1/2:ℝ)*Real.arcsin ((2*t-1)/c)) (symTest ε t) t := by
    rw [uIcc_of_le zero_le_one] at ht
    obtain ⟨hl,hu⟩ := coord_bounds hε t
    rw [coord_eq ht] at hl hu
    have hlin := (((hasDerivAt_id t).const_mul 2).sub_const 1).div_const c
    have h := ((Real.hasDerivAt_arcsin hl.ne' hu.ne).comp t hlin).const_mul (1/2:ℝ)
    convert h using 1
    unfold symTest
    rw [coord_eq ht]
    simp only [c, mul_inv_rev, div_eq_mul_inv]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_symTest hε).intervalIntegrable ..)
  rw [h]
  simp [c, neg_div, one_div, Real.arcsin_neg]
  ring_nf

private def tops {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℝ := (σ i).val

private theorem reverse_overlap {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) (t : ℝ) :
    overlap (tops σ) i j t = overlap (tops σ.symm) (σ i) (σ j) (1-t) := by
  simp only [overlap, tops, Equiv.symm_apply_apply, path]
  congr 1
  ring

private theorem symmetric_budget {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n))
    {ε : ℝ} (hε : 0 < ε) :
    (n:ℝ)⁻¹ * (∫ t in (0:ℝ)..1, ∑ i, ∑ j,
      (symTest ε t)^2 * overlap (tops σ) i j t) ≤ (harmonic n:ℝ) + 3*ε⁻¹ / 2 := by
  let F (s : Equiv.Perm (Fin n)) (t : ℝ) :=
    ∑ i, ∑ j, (test ε t)^2 * overlap (tops s) i j t
  have hF (s : Equiv.Perm (Fin n)) : Continuous (F s) :=
    continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ =>
      ((continuous_test hε).pow 2).mul (continuous_overlap ..)
  let c := (4*(1+2*ε))⁻¹
  have cpos : 0 < c := by dsimp [c]; positivity
  have refl (t : ℝ) : (∑ i, ∑ j, (test ε (1-t))^2 * overlap (tops σ) i j t) =
      F σ.symm (1-t) := by
    simp_rw [reverse_overlap σ]
    calc
      _ = ∑ i, ∑ j, (test ε (1-t))^2 * overlap (tops σ.symm) (σ i) j (1-t) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp σ (fun j => _ * overlap _ (σ i) j _)
      _ = _ := Equiv.sum_comp σ (fun i => ∑ j, (test ε (1-t))^2 * overlap _ i j _)
  have shape (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (∑ i, ∑ j, (symTest ε t)^2 * overlap (tops σ) i j t) =
        c * (F σ t + F σ.symm (1-t)) := by
    rw [← refl, mul_add]
    unfold F
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [symTest_sq hε ht]
    dsimp [c]; ring
  have rev : (∫ t in (0:ℝ)..1, F σ.symm (1-t)) = ∫ t in (0:ℝ)..1, F σ.symm t := by
    simp
  have hrev : Continuous (fun t : ℝ => F σ.symm (1-t)) :=
    (hF σ.symm).comp (by fun_prop : Continuous (fun t : ℝ => 1-t))
  have ff := integral_overlap_budget hn (tops σ) hε
  have fr := integral_overlap_budget hn (tops σ.symm) hε
  change _ * (∫ t in (0:ℝ)..1, F σ t) ≤ _ at ff
  change _ * (∫ t in (0:ℝ)..1, F σ.symm t) ≤ _ at fr
  rw [intervalIntegral.integral_congr (g := fun t => c * (F σ t + F σ.symm (1-t)))
    (by intro t ht; exact shape t (by simpa using ht)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((hF σ).intervalIntegrable ..)
      (hrev.intervalIntegrable ..), rev]
  have hh : 0 ≤ (harmonic n:ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]; positivity
  have hcoef : c ≤ (1/4:ℝ) := by
    dsimp [c]
    rw [← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add ff fr) cpos.le,
    mul_le_mul_of_nonneg_right hcoef
      (show 0 ≤ (2*(harmonic n:ℝ)+3*ε⁻¹)+(2*(harmonic n:ℝ)+3*ε⁻¹) by positivity)]

/-- A finite symmetric bound using the ordering constraints at both edges. -/
theorem regularized_permutation_lower {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n))
    {ε : ℝ} (hε : 0 < ε) :
    (Real.arcsin ((1+2*ε)⁻¹))^2 / ((harmonic n:ℝ)+3*ε⁻¹/2) ≤ permutationArea σ := by
  have hh : 0 ≤ (harmonic n:ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]; positivity
  simpa only [integral_symTest hε] using test_lower hn (tops σ) (fun i => Nat.cast_nonneg _)
    (fun i => by dsimp [tops]; exact_mod_cast (σ i).isLt) (symTest ε) (continuous_symTest hε)
    (by positivity) (symmetric_budget hn σ hε)

/-- The sharpest lower leading constant in the paper for permutation matchings,
expressed uniformly in the permutation at every sufficiently large grid size. -/
theorem eventually_permutation_lower {a : ℝ} (ha : a < Real.pi^2/4) :
    ∀ᶠ n : ℕ in atTop, ∀ σ : Equiv.Perm (Fin n), a ≤ Real.log n * permutationArea σ := by
  let F (x : ℝ) := (Real.arcsin ((1+2*x)⁻¹))^2
  have hF : ContinuousAt F 0 := by unfold F; fun_prop (disch := norm_num)
  have hnear : ∀ᶠ x in 𝓝[>] (0:ℝ), a < F x :=
    (hF.tendsto.mono_left nhdsWithin_le_nhds).eventually_const_lt (by
      simp only [F, mul_zero, add_zero, inv_one, Real.arcsin_one]
      linarith only [ha])
  have hgt : ∀ᶠ x in 𝓝[>] (0:ℝ), 0 < x := self_mem_nhdsWithin
  obtain ⟨ε, hε, hae⟩ := (hgt.and hnear).exists
  change 0 < ε at hε
  let L (n : ℕ) : ℝ := Real.log n
  have hlog : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n => F ε / (1+(1+3*ε⁻¹/2)*(L n)⁻¹)) atTop (𝓝 (F ε)) := by
    simpa using (tendsto_const_nhds (x := F ε)).div
      ((tendsto_const_nhds (x := (1:ℝ))).add
        ((tendsto_const_nhds (x := 1+3*ε⁻¹/2)).mul (tendsto_inv_atTop_zero.comp hlog)))
      (by norm_num)
  filter_upwards [hlim.eventually_const_lt hae, eventually_ge_atTop (2:ℕ)] with n h₁ hn
  intro σ
  have hpos : 0 < L n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hh : 0 ≤ (harmonic n:ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    positivity
  have lower := regularized_permutation_lower (show 0 < n by omega) σ hε
  change F ε / ((harmonic n:ℝ)+3*ε⁻¹/2) ≤ _ at lower
  calc
    a ≤ F ε / (1+(1+3*ε⁻¹/2)*(L n)⁻¹) := h₁.le
    _ = L n * (F ε / (1+L n+3*ε⁻¹/2)) := by
      have he := hε.ne'
      have hl := hpos.ne'
      field_simp
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hpos.le
      refine le_trans (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) ?_) lower
      linarith [harmonic_le_one_add_log n]

end
end PermutationStrips.Weighted
