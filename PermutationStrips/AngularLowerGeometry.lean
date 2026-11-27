import PermutationStrips.AngularLowerEnergy
import PermutationStrips.Angular

/-! Selecting equal squares above a visible axis without any upper marginal assumption. -/

open MeasureTheory Set
open scoped Interval

namespace PermutationStrips.AngularLower
open Angular
noncomputable section

theorem squares_equal_grid {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    squares (fun i => ((σ i).val:ℝ)) = (Pattern.equalGrid hn σ).carrier := by
  unfold squares Pattern.carrier
  apply iUnion_congr; intro i
  dsimp [Pattern.equalGrid,Pattern.gridStart]
  congr 2 <;> ring

/-- In every column choose a point of the compact set and put a square of side
`1/n` around its height. Distinct columns impose no constraint on their top starts. -/
theorem select_squares {K : Set (ℝ × ℝ)} (sub : K ⊆ unitSquare)
    (visible : Icc (0:ℝ) 1 ⊆ Prod.fst '' K) {n : ℕ} (hn : 0 < n)
    {δ : ℝ} (hδ : (n:ℝ)⁻¹ ≤ δ) :
    ∃ b : Fin n → ℝ, (∀ i, 0 ≤ b i) ∧ (∀ i, b i+1 ≤ n) ∧ squares b ⊆ thick δ K := by
  classical
  let w := (n:ℝ)⁻¹
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hw : 0 < w := inv_pos.mpr hnR
  have hw1 : w ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hn)
  have anchor (i : Fin n) : ∃ y : ℝ, (w*i.val, y) ∈ K := by
    have hh : w*i.val ∈ Icc (0:ℝ) 1 :=
      ⟨mul_nonneg hw.le (Nat.cast_nonneg _),by
        simpa [w,← div_eq_inv_mul] using (div_le_one hnR).2 (by exact_mod_cast i.isLt.le)⟩
    obtain ⟨⟨x,y⟩,hy,hx⟩ := visible hh
    exact ⟨y,by simpa only [← hx] using hy⟩
  choose y hy using anchor
  let a (i : Fin n) := min (y i) (1-w)
  let b (i : Fin n) := (n:ℝ)*a i
  have hunit (i : Fin n) : y i ∈ Icc (0:ℝ) 1 := (sub (hy i)).2
  have apos (i : Fin n) : 0 ≤ a i := le_min (hunit i).1 (sub_nonneg.mpr hw1)
  have alo (i : Fin n) : a i ≤ y i := min_le_left ..
  have aup (i : Fin n) : y i ≤ a i+w := by
    dsimp [a]
    rw [← min_add_add_right]
    exact le_min (by linarith) (by linarith [(hunit i).2])
  have left (i : Fin n) : w*b i = a i := by dsimp [w,b]; field_simp
  have right (i : Fin n) : w*(b i+1) = a i+w := by rw [mul_add,left,mul_one]
  refine ⟨b,fun i => mul_nonneg hnR.le (apos i),fun i => ?_,?_⟩
  · have hi : a i ≤ 1-w := min_le_right ..
    have h := mul_le_mul_of_nonneg_left hi hnR.le
    change (n:ℝ)*a i+1 ≤ n
    have h1 : (n:ℝ)*w=1 := by dsimp [w]; field_simp
    nlinarith
  · intro p hp
    obtain ⟨i,hx,hy'⟩ := mem_iUnion.mp hp
    change p.1 ∈ Icc (w*i.val) (w*(i.val+1)) at hx
    change p.2 ∈ Icc (w*b i) (w*(b i+1)) at hy'
    rw [left,right] at hy'
    apply mem_image2.mpr
    refine ⟨(w*i.val,y i),hy i,(p.1-w*i.val,p.2-y i),?_,?_⟩
    · refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> dsimp
      · linarith [hx.1,hw.le]
      · linarith [hx.2]
      · linarith [hy'.1,aup i]
      · linarith [hy'.2,alo i]
    · ext <;> simp

theorem thick_swap (δ : ℝ) (K : Set (ℝ × ℝ)) :
    thick δ (Prod.swap '' K) = Prod.swap '' thick δ K := by
  ext p
  constructor
  · rintro ⟨_,⟨q,hq,rfl⟩,v,hv,rfl⟩
    exact ⟨q+v.swap, ⟨q,hq,v.swap,⟨hv.2,hv.1⟩,rfl⟩,rfl⟩
  · rintro ⟨_,⟨q,hq,v,hv,rfl⟩,rfl⟩
    exact ⟨q.swap,⟨q,hq,rfl⟩,v.swap,⟨hv.2,hv.1⟩,rfl⟩

theorem ceil_grid {δ : ℝ} (hδ : 0 < δ) (hhalf : δ ≤ 1/2) :
    2 ≤ ⌈δ⁻¹⌉₊ ∧ ((⌈δ⁻¹⌉₊:ℕ):ℝ)⁻¹ ≤ δ ∧
    Real.log (⌈δ⁻¹⌉₊:ℕ) ≤ 2*Real.log (1/δ) := by
  let n := ⌈δ⁻¹⌉₊
  have h2 : (2:ℝ) ≤ δ⁻¹ := by rw [← one_div,le_div_iff₀ hδ]; linarith
  have hn : (2:ℝ) ≤ n := h2.trans (Nat.le_ceil _)
  refine ⟨by exact_mod_cast hn, (inv_le_comm₀ (by positivity : 0 < (n:ℝ)) hδ).2 (Nat.le_ceil _),?_⟩
  have hlog := Real.log_le_log (by norm_num) h2
  calc
    Real.log (n:ℝ) ≤ Real.log (2*δ⁻¹) := Real.log_le_log (by positivity)
      (by linarith [Nat.ceil_lt_add_one (inv_nonneg.mpr hδ.le)])
    _ = Real.log 2+Real.log δ⁻¹ := Real.log_mul (by norm_num) (by positivity)
    _ ≤ _ := by rw [one_div]; linarith

end
end PermutationStrips.AngularLower
