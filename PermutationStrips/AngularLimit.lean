import PermutationStrips.AngularGeometry
import PermutationStrips.AngularScales
import PermutationStrips.CompactLimit

/-! Estimates on a single nested limit, before choosing its blocks. -/

open Set MeasureTheory
namespace PermutationStrips.Angular
open CompactPlane
noncomputable section

/-- The uniform finite estimates used at stage j of the nested construction. -/
structure BlocksFor (b : ℝ → ℝ) (B : ℕ → FinitePattern) : Prop where
  count : ∀ j, (Fintype.card (B j).index : ℝ) ≤ Real.exp (1000*(2:ℝ)^(j+1))
  diameter : ∀ j, Metric.diam (toEuclidean '' (B j).pat.carrier) ≤ 1+1000/(2:ℝ)^(j+1)
  width : ∀ j i, (B j).pat.w i ≤ 1/2
  local_geometry : ∀ j, LocalGeometry (B j).pat
  favard_bound : ∀ j, favard (B j).pat.carrier ≤ 16000/(2:ℝ)^(j+1)
  weighted_bound : ∀ j, weighted b (B j).pat.carrier ≤ 1000*scaleFactor b (2^(j+1))/(2:ℝ)^(j+1)
  sqrt_bound : ∀ j θ, 0 < rho θ → Real.sqrt (rho θ)*length (B j).pat.carrier θ ≤ 1000/(2:ℝ)^(j+1)

theorem thick_mono_radius {δ ε : ℝ} (h : δ ≤ ε) (K : Set (ℝ × ℝ)) : thick δ K ⊆ thick ε K :=
  Set.image2_subset Subset.rfl (Set.prod_mono (Icc_subset_Icc (neg_le_neg h) h) (Icc_subset_Icc (neg_le_neg h) h))

theorem length_box {K : Set (ℝ × ℝ)} {R : ℝ} (hR : 0 ≤ R)
    (hK : K ⊆ Icc (-R) R ×ˢ Icc (-R) R) (θ : ℝ) : length K θ ≤ 4*R := by
  have sub : proj θ '' K ⊆ Icc (-2*R) (2*R) := by
    rintro x ⟨p,h,rfl⟩
    have H := abs_le.mp (uniform_displacement (hK h) θ)
    exact ⟨by linarith [H.1],H.2⟩
  have h := measureReal_mono (μ := volume) sub (by simp)
  rw [Real.volume_real_Icc_of_le (by linarith)] at h
  exact h.trans_eq (by ring)

theorem length_unit {K : Set (ℝ × ℝ)} (h : K ⊆ unitSquare) (θ : ℝ) : length K θ ≤ 4 := by
  have hs : K ⊆ Icc (-(1:ℝ)) 1 ×ˢ Icc (-1) 1 := by
    intro p hp
    obtain ⟨⟨h₁,h₂⟩,h₃,h₄⟩ := h hp
    exact ⟨⟨by linarith,h₂⟩,by linarith,h₄⟩
  simpa using length_box zero_le_one hs θ

theorem length_thick_unit {K : Set (ℝ × ℝ)} (h : K ⊆ unitSquare)
    {δ : ℝ} (hδ : δ ≤ 1) (θ : ℝ) : length (thick δ K) θ ≤ 8 := by
  have hs : thick δ K ⊆ Icc (-(2:ℝ)) 2 ×ˢ Icc (-2) 2 := by
    rintro _ ⟨p,hp,v,⟨⟨hx,hx'⟩,hy,hy'⟩,rfl⟩
    obtain ⟨⟨a,b⟩,c,d⟩ := h hp
    change (-2 ≤ p.1+v.1 ∧ p.1+v.1 ≤ 2) ∧ -2 ≤ p.2+v.2 ∧ p.2+v.2 ≤ 2
    constructor <;> constructor <;> linarith
  exact (length_box (by norm_num : (0:ℝ) ≤ 2) hs θ).trans_eq (by norm_num)

theorem scale_upper_of_length {b : ℝ → ℝ} (hb : Admissible b) {S P : Set (ℝ × ℝ)}
    (hS : IsCompact S) (hP : IsCompact P) {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ θ, length S θ ≤ length P θ + D) :
    favard S ≤ favard P + Real.pi*D ∧ weighted b S ≤ weighted b P + D := by
  constructor
  · unfold favard
    calc
      _ ≤ ∫ θ in (0:ℝ)..Real.pi, (length P θ+D) :=
        intervalIntegral.integral_mono_on Real.pi_pos.le (intervalIntegrable_length hS ..)
          ((intervalIntegrable_length hP ..).add intervalIntegrable_const) (fun t _ => h t)
      _ = _ := by rw [intervalIntegral.integral_add (intervalIntegrable_length hP ..) intervalIntegrable_const]; simp
  · apply csSup_le (weighted_nonempty b S)
    rintro _ ⟨θ,hθ,rfl⟩
    have hh := hb.2 (rho θ) ⟨hθ,(rho_bounds θ).2⟩
    calc
      _ ≤ b (rho θ)*(length P θ+D) := mul_le_mul_of_nonneg_left (h θ) hh.1
      _ ≤ weighted b P + D := by
        rw [mul_add]; exact add_le_add (le_weighted hb hP hθ) (mul_le_of_le_one_left hD hh.2)

theorem coarse_bounds {b : ℝ → ℝ} (hb : Admissible b) {S : Set (ℝ × ℝ)}
    (hS : IsCompact S) (hs : S ⊆ unitSquare) {δ : ℝ} (hd : δ ≤ 1) :
    favard (thick δ S) ≤ 8*Real.pi ∧ weighted b (thick δ S) ≤ 8 := by
  have bound := length_thick_unit hs hd
  constructor
  · calc
      _ ≤ ∫ _ in (0:ℝ)..Real.pi, (8:ℝ) := intervalIntegral.integral_mono_on Real.pi_pos.le
        (intervalIntegrable_length (compact_thick hS δ) ..) intervalIntegrable_const (fun θ _ => bound θ)
      _ = _ := by simp;ring
  · apply csSup_le (weighted_nonempty _ _)
    rintro _ ⟨θ,hθ,rfl⟩
    exact (mul_le_of_le_one_left measureReal_nonneg (hb.2 _ ⟨hθ,(rho_bounds θ).2⟩).2).trans (bound θ)

theorem limit_subset_unit (B : ℕ → FinitePattern) : limitSet B ⊆ unitSquare :=
  (limitSet_subset_level B 0).trans (carrier_subset_unit _)

theorem level_count (B : ℕ → FinitePattern) {C : ℝ} (hc : 0 ≤ C)
    (hs : ∀ j : ℕ, (Fintype.card (B j).index : ℝ) ≤ Real.exp (C * (2:ℝ)^(j+1))) (j : ℕ) :
    (Fintype.card (level B j).index : ℝ) ≤ Real.exp (2*C*(2:ℝ)^j) := by
  induction j with
  | zero =>
    change (Fintype.card (Fin 1):ℝ) ≤ _
    simp only [Fintype.card_fin,Nat.cast_one,pow_zero,mul_one]
    exact Real.one_le_exp (by positivity)
  | succ j ih =>
    change (@Fintype.card ((level B j).index × (B j).index) _ : ℝ) ≤ _
    rw [Fintype.card_prod, Nat.cast_mul]
    calc
      _ ≤ Real.exp (2*C*(2:ℝ)^j)*Real.exp (C*(2:ℝ)^(j+1)) := mul_le_mul ih (hs j) (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add,pow_succ];congr 1;ring

theorem limit_scale (B : ℕ → FinitePattern) {b : ℝ → ℝ} (hb : Admissible b)
    {C : ℝ} (hc : 0 ≤ C)
    (hs : ∀ j : ℕ, (Fintype.card (B j).index : ℝ) ≤ Real.exp (C*(2:ℝ)^(j+1)))
    (j : ℕ) {δ : ℝ} (hd : 0 ≤ δ) :
    let K := thick δ (limitSet B)
    let E := 4 * δ * Real.exp (2*C*(2:ℝ)^(j+1))
    favard K ≤ favard (B j).pat.carrier + Real.pi*E ∧
      weighted b K ≤ weighted b (B j).pat.carrier + E := by
  apply scale_upper_of_length hb (compact_thick (compact_limitSet _) _) (compact_carrier _) (by positivity)
  intro θ
  have hh : limitSet B ⊆ ((level B j).pat.insert (B j).pat).carrier := limitSet_subset_level B (j+1)
  apply (length_thick_sub _ _ hh hd θ).trans
  apply add_le_add_left
  have cnt := level_count B hc hs (j+1)
  change (Fintype.card ((level B j).index × (B j).index):ℝ) ≤ _ at cnt
  nlinarith [mul_le_mul_of_nonneg_right cnt hd]

end
end PermutationStrips.Angular
