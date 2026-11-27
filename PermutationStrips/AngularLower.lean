import PermutationStrips.AngularLowerGeometry
import PermutationStrips.AngularCoordinates
import PermutationStrips.AngularSymmetry
import PermutationStrips.Sliding

/-! Angular lower bounds for every grid matching and every compact set with a visible axis. -/

open MeasureTheory Set
open scoped Interval

namespace PermutationStrips.AngularLower
open Angular
noncomputable section

private theorem trunc_integrable {f : ℝ → ℝ} (hf : Admissible f) {δ : ℝ} (hd : 0 < δ)
    (hδ : δ ≤ 1/2) : IntervalIntegrable (fun t => f t/t) volume δ (1/2) := by
  have sub : uIcc δ (1/2:ℝ) ⊆ Ioc 0 (1/2) := by
    rw [uIcc_of_le hδ]
    exact fun _ h => ⟨hd.trans_le h.1,h.2⟩
  have hi : IntervalIntegrable f volume δ (1/2) := (hf.1.mono sub).intervalIntegrable
  simpa only [div_eq_mul_inv] using hi.mul_continuousOn
    (continuousOn_id.inv₀ (fun t ht => (sub ht).1.ne'))

private theorem nonneg_weight {f : ℝ → ℝ} (hf : Admissible f) {K : Set (ℝ × ℝ)} (hc : IsCompact K) :
    0 ≤ weighted f K := by
  have h : (1/2:ℝ) ∈ Ioc (0:ℝ) (1/2) := by constructor <;> norm_num
  exact (mul_nonneg (hf.2 _ h).1 measureReal_nonneg).trans (weighted_height_le hf hc h)

private theorem free_lower {n : ℕ} (hn : 2 ≤ n) (b : Fin n → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hb' : ∀ i, b i+1 ≤ n) {f : ℝ → ℝ} (hf : Admissible f)
    {δ : ℝ} (hδ : (n:ℝ)⁻¹ ≤ δ) (hh : δ ≤ 1/2) :
    1 ≤ 4*Real.log n * favard (squares b) ∧
    truncated f δ ≤ 24*Real.log n * weighted f (squares b) := by
  have hn0 : 0 < n := by omega
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_le_log (by norm_num) hnR
  have logpos : 0 < Real.log (n:ℝ) := (Real.log_pos (by norm_num : (1:ℝ) < 2)).trans_le hlog
  have hc := compact_squares b
  have hd : 0 < δ := (by positivity : 0 < (n:ℝ)⁻¹).trans_le hδ
  constructor
  · have ha := area_le_favard hc
    rw [squares_area hn0 b hb hb'] at ha
    have H := Sliding.sliding_log_lower hn0 b hb hb'
    simp only [one_div] at H
    have den : 0 < 1+2*Real.log n := by positivity
    have F : 0 ≤ favard (squares b) := measureReal_nonneg.trans ha
    have he := (div_le_iff₀ den).mp (show 1/(1+2*Real.log n) ≤ _ by simpa [one_div] using H.trans ha)
    have coeff : 1+2*Real.log n ≤ 4*Real.log n := by linarith [Real.log_two_gt_d9]
    nlinarith only [he,mul_le_mul_of_nonneg_right coeff F]
  · exact height_weight_bound hn b hb hb' hδ hh (nonneg_weight hf hc) f
      (trunc_integrable hf hd hh) (fun t ht => (hf.2 _ ⟨hd.trans_le ht.1,ht.2⟩).1)
      (fun t ht => weighted_height_le hf hc ⟨hd.trans_le ht.1,ht.2⟩)

/-- Both lower bounds on every equal grid, with absolute constants. -/
theorem grid_lower {f : ℝ → ℝ} (hf : Admissible f) {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n)) :
    let K := (Pattern.equalGrid (by omega : 0 < n) σ).carrier
    1 ≤ 4*Real.log n * favard K ∧ truncated f (1/n) ≤ 24*Real.log n * weighted f K := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hδ : (n:ℝ)⁻¹ ≤ 1/2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hnR
  have h := free_lower hn (fun i => ((σ i).val:ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun i => by dsimp; exact_mod_cast (σ i).isLt) hf le_rfl hδ
  rw [squares_equal_grid (show 0 < n by omega)] at h
  simpa only [one_div] using h

private theorem horizontal_lower {f : ℝ → ℝ} (hf : Admissible f) {K : Set (ℝ × ℝ)}
    (hc : IsCompact K) (hs : K ⊆ unitSquare) (hv : Icc (0:ℝ) 1 ⊆ Prod.fst '' K)
    {δ : ℝ} (hδ : 0 < δ) (hh : δ ≤ 1/2) :
    1 ≤ 8*Real.log (1/δ) * favard (thick δ K) ∧
      truncated f δ ≤ 48*Real.log (1/δ) * weighted f (thick δ K) := by
  let n := ⌈δ⁻¹⌉₊
  obtain ⟨hn,hd,hlog⟩ := ceil_grid hδ hh
  obtain ⟨b,hb,hb',sub⟩ := select_squares hs hv (show 0 < n by omega) hd
  obtain ⟨F,W⟩ := free_lower hn b hb hb' hf hd hh
  have hsc := compact_squares b
  have htc := compact_thick hc δ
  have hF := favard_mono hsc htc sub
  have hW := weighted_mono hf htc sub
  have fn : 0 ≤ favard (squares b) := intervalIntegral.integral_nonneg Real.pi_pos.le
    (fun _ _ => measureReal_nonneg)
  have wn := nonneg_weight hf hsc
  have LD : 0 ≤ Real.log (1/δ) := Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
  constructor
  · calc
      1 ≤ 4*Real.log n * favard (squares b) := F
      _ ≤ (8*Real.log (1/δ)) * favard (squares b) :=
        mul_le_mul_of_nonneg_right (by dsimp [n]; linarith only [hlog]) fn
      _ ≤ _ := mul_le_mul_of_nonneg_left hF (by positivity)
  · calc
      _ ≤ 24*Real.log n * weighted f (squares b) := W
      _ ≤ (48*Real.log (1/δ)) * weighted f (squares b) :=
        mul_le_mul_of_nonneg_right (by dsimp [n]; linarith only [hlog]) wn
      _ ≤ _ := mul_le_mul_of_nonneg_left hW (by positivity)

/-- For every compact subset of the unit square with at least one full
coordinate projection, each neighbourhood obeys both angular lower bounds. -/
theorem compact_lower {f : ℝ → ℝ} (hf : Admissible f) {K : Set (ℝ × ℝ)}
    (hc : IsCompact K) (hs : K ⊆ unitSquare)
    (visible : Icc (0:ℝ) 1 ⊆ Prod.fst '' K ∨ Icc (0:ℝ) 1 ⊆ Prod.snd '' K)
    {δ : ℝ} (hδ : 0 < δ) (hh : δ ≤ 1/2) :
    1 ≤ 8*Real.log (1/δ) * favard (thick δ K) ∧
      truncated f δ ≤ 48*Real.log (1/δ) * weighted f (thick δ K) := by
  rcases visible with hx|hy
  · exact horizontal_lower hf hc hs hx hδ hh
  · have sub : Prod.swap '' K ⊆ unitSquare := by
      rintro _ ⟨p,hp,rfl⟩
      exact ⟨(hs hp).2,(hs hp).1⟩
    have hv : Icc (0:ℝ) 1 ⊆ Prod.fst '' (Prod.swap '' K) := by simpa only [image_image] using hy
    have h := horizontal_lower hf (hc.image continuous_swap) sub hv hδ hh
    rwa [thick_swap, favard_swap (compact_thick hc δ), weighted_swap] at h

end
end PermutationStrips.AngularLower
