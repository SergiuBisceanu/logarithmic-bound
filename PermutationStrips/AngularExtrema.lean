import PermutationStrips.AngularLower
import PermutationStrips.AngularScales

/-! The compact infimum and the equal-grid minimum in the angular profile law. -/

open MeasureTheory Set
open scoped Interval

namespace PermutationStrips.Angular
noncomputable section

/-- Compact subsets of the square having at least one full coordinate projection. -/
def visibleCompact (K : Set (ℝ × ℝ)) : Prop :=
  IsCompact K ∧ K ⊆ unitSquare ∧
    (Prod.fst '' K = Icc (0:ℝ) 1 ∨ Prod.snd '' K = Icc (0:ℝ) 1)

def compactInf (b : ℝ → ℝ) (δ : ℝ) : ℝ :=
  sInf ((fun K => favard (thick δ K)+weighted b (thick δ K)) '' {K | visibleCompact K})

def gridMin (b : ℝ → ℝ) (n : ℕ) (hn : 0<n) : ℝ :=
  sInf (range (fun σ : Equiv.Perm (Fin n) =>
    favard (Pattern.equalGrid hn σ).carrier+weighted b (Pattern.equalGrid hn σ).carrier))

theorem visible_unitSquare : visibleCompact unitSquare := by
  refine ⟨isCompact_Icc.prod isCompact_Icc,Subset.rfl,Or.inl ?_⟩
  ext x; constructor
  · rintro ⟨p,hp,rfl⟩; exact hp.1
  · intro hx; exact ⟨(x,0),⟨hx,by constructor <;> norm_num⟩,rfl⟩

private theorem favard_pos_weak (K : Set (ℝ × ℝ)) : 0 ≤ favard K :=
  intervalIntegral.integral_nonneg Real.pi_pos.le (fun _ _ => measureReal_nonneg)

private theorem weighted_pos_weak {b : ℝ → ℝ} (hb : Admissible b)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) : 0 ≤ weighted b K := by
  have h : (1/2:ℝ) ∈ Ioc (0:ℝ) (1/2) := by constructor <;> norm_num
  exact (mul_nonneg (hb.2 _ h).1 measureReal_nonneg).trans (weighted_height_le hb hK h)

private theorem bdd_compact_values {b : ℝ → ℝ} (hb : Admissible b) (δ : ℝ) :
    BddBelow ((fun K => favard (thick δ K)+weighted b (thick δ K)) '' {K | visibleCompact K}) := by
  refine ⟨0,?_⟩
  rintro _ ⟨K,hK,rfl⟩
  exact add_nonneg (favard_pos_weak _) (weighted_pos_weak hb (compact_thick hK.1 δ))

theorem compactInf_le {b : ℝ → ℝ} (hb : Admissible b) {K : Set (ℝ × ℝ)}
    (hK : visibleCompact K) (δ : ℝ) :
    compactInf b δ ≤ favard (thick δ K)+weighted b (thick δ K) :=
  csInf_le (bdd_compact_values hb δ) ⟨K,hK,rfl⟩

/-- The finite set of permutations contains a minimizer for the joint objective. -/
theorem gridMin_attained (b : ℝ → ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ σ : Equiv.Perm (Fin n), let K := (Pattern.equalGrid hn σ).carrier
      favard K+weighted b K = gridMin b n hn := by
  let v (σ : Equiv.Perm (Fin n)) := favard (Pattern.equalGrid hn σ).carrier +
    weighted b (Pattern.equalGrid hn σ).carrier
  exact (range_nonempty v).csInf_mem (finite_range v)

theorem gridMin_le (b : ℝ → ℝ) {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    let K := (Pattern.equalGrid hn σ).carrier
    gridMin b n hn ≤ favard K+weighted b K := by
  let v (σ : Equiv.Perm (Fin n)) := favard (Pattern.equalGrid hn σ).carrier +
    weighted b (Pattern.equalGrid hn σ).carrier
  exact csInf_le (finite_range v).bddBelow (mem_range_self σ)

private theorem combine {I L F M : ℝ} (hL : 0<L)
    (hf : 1 ≤ 8*L*F) (hm : I ≤ 48*L*M) : (1+I)/(48*L) ≤ F+M := by
  apply (div_le_iff₀ (by positivity)).2
  linarith only [hf,hm]

theorem compactInf_lower {b : ℝ → ℝ} (hb : Admissible b) {δ : ℝ} (hd : 0<δ) (hh : δ≤1/2) :
    (1+truncated b δ)/(48*Real.log (1/δ)) ≤ compactInf b δ := by
  apply le_csInf (s:=((fun K => favard (thick δ K)+weighted b (thick δ K)) '' {K | visibleCompact K}))
    (⟨_,unitSquare,visible_unitSquare,rfl⟩)
  rintro _ ⟨K,hK,rfl⟩
  obtain ⟨Fc,Wc⟩ := AngularLower.compact_lower hb hK.1 hK.2.1
    (hK.2.2.imp Eq.ge Eq.ge) hd hh
  exact combine (Real.log_pos ((lt_div_iff₀ hd).2 (by linarith))) Fc Wc

theorem gridMin_lower {b : ℝ → ℝ} (hb : Admissible b) {n : ℕ} (hn : 2≤n) :
    (1+truncated b (1/n))/(48*Real.log n) ≤ gridMin b n (by omega) := by
  have hn0 : 0<n := by omega
  have Lp : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
  obtain ⟨σ,he⟩ := gridMin_attained b hn0
  let K := (Pattern.equalGrid hn0 σ).carrier
  have Kc : IsCompact K := isCompact_iUnion fun _ => isCompact_Icc.prod isCompact_Icc
  obtain ⟨F,W⟩ := AngularLower.grid_lower hb hn σ
  have Fn := favard_pos_weak K
  have Wn := weighted_pos_weak hb Kc
  change 1 ≤ 4*Real.log n*favard K at F
  change truncated b (1/n) ≤ 24*Real.log n*weighted b K at W
  change favard K+weighted b K = _ at he
  rw [← he]
  apply combine Lp
  · nlinarith only [F,mul_nonneg Lp.le Fn]
  · nlinarith only [W,mul_nonneg Lp.le Wn]

/-- A witness for the upper bound and a universal lower bound give the
literal compact infimum law, with the same constant on the two sides. -/
theorem compact_law {b : ℝ → ℝ} (hb : Admissible b) {δ C : ℝ} (hd : 0<δ) (hh : δ≤1/2)
    (upper : ∃ K, visibleCompact K ∧ favard (thick δ K)+weighted b (thick δ K) ≤
      C*(1+truncated b δ)/Real.log (1/δ)) :
    (1+truncated b δ)/(max 48 C * Real.log (1/δ)) ≤ compactInf b δ ∧
      compactInf b δ ≤ max 48 C * (1+truncated b δ)/Real.log (1/δ) := by
  have Lp := Real.log_pos ((lt_div_iff₀ hd).2 (by linarith) : 1 < 1/δ)
  have A : 0 ≤ 1+truncated b δ := by linarith [truncated_nonneg hb hd hh]
  obtain ⟨K,hK,h⟩ := upper
  constructor
  · exact (div_le_div_of_nonneg_left A (by positivity) (mul_le_mul_of_nonneg_right (le_max_left ..) Lp.le)).trans
      (compactInf_lower hb hd hh)
  · exact (compactInf_le hb hK δ).trans (h.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right ..) A) Lp.le))

/-- The same comparison for the attained minimum on every grid, including n=2. -/
theorem grid_law {b : ℝ → ℝ} (hb : Admissible b) {n : ℕ} (hn : 2≤n) {C : ℝ}
    (upper : ∃ σ : Equiv.Perm (Fin n), let K := (Pattern.equalGrid (by omega) σ).carrier
      favard K+weighted b K ≤ C*(1+truncated b (1/n))/Real.log n) :
    (1+truncated b (1/n))/(max 48 C*Real.log n) ≤ gridMin b n (by omega) ∧
      gridMin b n (by omega) ≤ max 48 C*(1+truncated b (1/n))/Real.log n := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < (n:ℝ) := by linarith
  have Lp := Real.log_pos (by linarith : 1 < (n:ℝ))
  have hh : 1/(n:ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hnR
  have A : 0 ≤ 1+truncated b (1/n) := by linarith [truncated_nonneg hb (one_div_pos.mpr hp) hh]
  obtain ⟨σ,h⟩ := upper
  constructor
  · exact (div_le_div_of_nonneg_left A (by positivity) (mul_le_mul_of_nonneg_right (le_max_left ..) Lp.le)).trans
      (gridMin_lower hb hn)
  · exact (gridMin_le b (by omega) σ).trans (h.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right ..) A) Lp.le))

end
end PermutationStrips.Angular
