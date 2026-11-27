import PermutationStrips.Pattern
import Mathlib

/-! Unnormalised Favard length, weighted oblique projections and square neighbourhoods. -/

open Set MeasureTheory
open scoped Pointwise

namespace PermutationStrips.Angular
noncomputable section

def unitSquare : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc 0 1
def proj (θ : ℝ) (p : ℝ × ℝ) : ℝ := p.1 * Real.cos θ + p.2 * Real.sin θ
def speed (θ : ℝ) : ℝ := |Real.cos θ| + |Real.sin θ|
def rho (θ : ℝ) : ℝ := min |Real.cos θ| |Real.sin θ| / speed θ
def length (K : Set (ℝ × ℝ)) (θ : ℝ) : ℝ := volume.real (proj θ '' K)
def favard (K : Set (ℝ × ℝ)) : ℝ := ∫ θ in (0:ℝ)..Real.pi, length K θ
def weighted (b : ℝ → ℝ) (K : Set (ℝ × ℝ)) : ℝ :=
  sSup ((fun θ => b (rho θ) * length K θ) '' {θ | 0 < rho θ})
def thick (δ : ℝ) (K : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  Set.image2 (·+·) K (Icc (-δ) δ ×ˢ Icc (-δ) δ)
def truncated (b : ℝ → ℝ) (δ : ℝ) : ℝ := ∫ r in δ..(1/2:ℝ), b r / r
def Admissible (b : ℝ → ℝ) : Prop :=
  MonotoneOn b (Ioc 0 (1/2)) ∧ ∀ r ∈ Ioc 0 (1/2), b r ∈ Icc 0 1
def mirror (p : ℝ × ℝ) : ℝ × ℝ := (p.1,1-p.2)

theorem continuous_proj (θ : ℝ) : Continuous (proj θ) := by unfold proj; fun_prop
theorem compact_thick {K : Set (ℝ × ℝ)} (hK : IsCompact K) (δ : ℝ) : IsCompact (thick δ K) :=
  hK.add (isCompact_Icc.prod isCompact_Icc)

theorem measurable_length {K : Set (ℝ × ℝ)} (hK : IsCompact K) : Measurable (length K) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let graph := {z : (ℝ × ℝ) × K | z.1.2 = proj z.1.1 z.2.val}
  have hg : IsClosed graph := by
    apply isClosed_eq (by fun_prop)
    unfold proj; fun_prop
  have he : Prod.fst '' graph = {p : ℝ × ℝ | p.2 ∈ proj p.1 '' K} := by
    ext ⟨t,x⟩
    constructor
    · rintro ⟨⟨q,y⟩,hg',hq⟩; cases hq
      exact ⟨y.1,y.2,hg'.symm⟩
    · rintro ⟨y,hy,he⟩
      exact ⟨((t,x),⟨y,hy⟩),he.symm,rfl⟩
  have hclosed := isClosedMap_fst_of_compactSpace graph hg
  rw [he] at hclosed
  exact (measurable_measure_prodMk_left hclosed.measurableSet).ennreal_toReal

theorem speed_pos (θ : ℝ) : 0 < speed θ := by
  have h := Real.sin_sq_add_cos_sq θ
  by_contra! hn
  have h₁ : |Real.cos θ| = 0 := by unfold speed at hn; linarith [abs_nonneg (Real.cos θ),abs_nonneg (Real.sin θ)]
  have h₂ : |Real.sin θ| = 0 := by unfold speed at hn; linarith [abs_nonneg (Real.sin θ)]
  rw [abs_eq_zero.mp h₁, abs_eq_zero.mp h₂] at h; norm_num at h

theorem speed_bounds (θ : ℝ) : 1 ≤ speed θ ∧ speed θ ≤ 2 := by
  have hc := abs_nonneg (Real.cos θ)
  have hs := abs_nonneg (Real.sin θ)
  have sum : |Real.sin θ|^2+|Real.cos θ|^2=1 := by simp [sq_abs,Real.sin_sq_add_cos_sq]
  have h1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have h2 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  unfold speed
  constructor
  · nlinarith [mul_nonneg hc (sub_nonneg.mpr h1),mul_nonneg hs (sub_nonneg.mpr h2)]
  · linarith

theorem rho_bounds (θ : ℝ) : rho θ ∈ Icc (0:ℝ) (1/2) := by
  refine ⟨div_nonneg (le_min (abs_nonneg _) (abs_nonneg _)) (speed_pos θ).le,?_⟩
  apply (div_le_iff₀ (speed_pos θ)).mpr
  unfold speed; linarith [min_le_left |Real.cos θ| |Real.sin θ|,min_le_right |Real.cos θ| |Real.sin θ|]

theorem length_mono {A B : Set (ℝ × ℝ)} (hB : IsCompact B) (h : A ⊆ B) (θ : ℝ) :
    length A θ ≤ length B θ :=
  measureReal_mono (image_mono h) ((hB.image (continuous_proj θ)).measure_lt_top.ne)

theorem length_bounded {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ, length K θ ≤ C := by
  obtain ⟨R,hR,hr⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨4*R,by positivity,?_⟩
  intro θ
  have sub : proj θ '' K ⊆ Icc (-2*R) (2*R) := by
    rintro x ⟨p,hp,rfl⟩
    have hx := (norm_fst_le p).trans (hr p hp)
    have hy := (norm_snd_le p).trans (hr p hp)
    have hc : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    have hs : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
    have H : |proj θ p| ≤ 2*R := by
      unfold proj
      calc
        _ ≤ _ := abs_add_le ..
        _ ≤ R*1+R*1 := by rw [abs_mul,abs_mul]; exact add_le_add
                            (mul_le_mul hx hc (abs_nonneg _) hR.le) (mul_le_mul hy hs (abs_nonneg _) hR.le)
        _ = _ := by ring
    exact ⟨by linarith [(abs_le.mp H).1],(abs_le.mp H).2⟩
  have m := measureReal_mono (μ := volume) sub (by simp)
  rw [Real.volume_real_Icc_of_le (by linarith)] at m
  unfold length; linarith

theorem intervalIntegrable_length {K : Set (ℝ × ℝ)} (hK : IsCompact K) (a b : ℝ) :
    IntervalIntegrable (length K) volume a b := by
  obtain ⟨C,_,hb⟩ := length_bounded hK
  apply intervalIntegrable_iff.mpr
  apply IntegrableOn.of_bound measure_Ioc_lt_top (measurable_length hK).aestronglyMeasurable C
  filter_upwards with t
  change ‖length K t‖ ≤ C
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ length K t from measureReal_nonneg)]
  exact hb t

theorem favard_mono {A B : Set (ℝ × ℝ)} (ha : IsCompact A) (hb : IsCompact B) (sub : A ⊆ B) :
    favard A ≤ favard B :=
  intervalIntegral.integral_mono_on Real.pi_pos.le (intervalIntegrable_length ha ..)
    (intervalIntegrable_length hb ..) (fun θ _ => length_mono hb sub θ)

theorem weighted_bdd {b : ℝ → ℝ} (hb : Admissible b) {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    BddAbove ((fun θ => b (rho θ)*length K θ) '' {θ | 0 < rho θ}) := by
  obtain ⟨C,_,h⟩ := length_bounded hK
  refine ⟨C,?_⟩
  rintro _ ⟨θ,hθ,rfl⟩
  exact (mul_le_of_le_one_left measureReal_nonneg (hb.2 _ ⟨hθ,(rho_bounds θ).2⟩).2).trans (h θ)

theorem le_weighted {b : ℝ → ℝ} (hb : Admissible b) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    {θ : ℝ} (hθ : 0 < rho θ) : b (rho θ)*length K θ ≤ weighted b K :=
  le_csSup (weighted_bdd hb hK) ⟨θ,hθ,rfl⟩

theorem weighted_nonempty (b : ℝ → ℝ) (K : Set (ℝ × ℝ)) :
    (((fun θ => b (rho θ)*length K θ) '' {θ | 0 < rho θ}) : Set ℝ).Nonempty := by
  refine ⟨_,Real.pi/4,?_,rfl⟩
  change 0 < rho _
  unfold rho speed
  rw [Real.sin_pi_div_four, Real.cos_pi_div_four]; positivity

theorem weighted_mono {b : ℝ → ℝ} (hb : Admissible b) {A B : Set (ℝ × ℝ)} (hB : IsCompact B) (sub : A ⊆ B) :
    weighted b A ≤ weighted b B := by
  apply csSup_le (weighted_nonempty b A)
  rintro _ ⟨θ,hθ,rfl⟩
  exact (mul_le_mul_of_nonneg_left (length_mono hB sub θ) (hb.2 _ ⟨hθ,(rho_bounds θ).2⟩).1).trans (le_weighted hb hB hθ)

end
end PermutationStrips.Angular
