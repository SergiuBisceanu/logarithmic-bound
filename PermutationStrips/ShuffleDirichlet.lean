import Mathlib

/-! Simultaneous approximation of the phases governing near-axis shuffle overlaps. -/

namespace PermutationStrips.Shuffle

/-- Two of the first `L^d + 1` multiples lie in the same one of `L^d` boxes
of the `d`-torus. The assertion includes the empty family of phases. -/
theorem exists_simultaneous_approx {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (L : ℕ) (hL : 0 < L) : ∃ q : ℕ, 1 ≤ q ∧ q ≤ L ^ Fintype.card ι ∧
      ∀ i, ∃ z : ℤ, |(q : ℝ) * b i - z| ≤ 1 / (L : ℝ) := by
  classical
  let D := L ^ Fintype.card ι
  let f (n : ℕ) (i : ι) := Int.fract ((n : ℝ) * b i)
  have hp : (0 : ℝ) < L := by exact_mod_cast hL
  let box (n : Fin (D+1)) (i : ι) : Fin L := ⟨⌊(L:ℝ) * f n i⌋₊, by
    apply (Nat.floor_lt (mul_nonneg hp.le (Int.fract_nonneg _))).mpr
    exact mul_lt_of_lt_one_right hp (Int.fract_lt_one _)⟩
  obtain ⟨x, y, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt box (by simp [D])
  obtain ⟨a, c, hac, he⟩ : ∃ a c : Fin (D+1), a < c ∧ box a = box c := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨x,y,h,heq⟩
    · exact ⟨y,x,h,heq.symm⟩
  have hac' : a.val < c.val := hac
  refine ⟨c.val - a.val, by omega, by have := c.isLt; omega, fun i => ?_⟩
  refine ⟨⌊(c.val:ℝ)*b i⌋ - ⌊(a.val:ℝ)*b i⌋, ?_⟩
  have same : ⌊(L:ℝ)*f a i⌋₊ = ⌊(L:ℝ)*f c i⌋₊ := congrArg Fin.val (congrFun he i)
  have lo (n : Fin (D+1)) := Nat.floor_le (mul_nonneg hp.le (Int.fract_nonneg ((n.val:ℝ)*b i)))
  have hi (n : Fin (D+1)) := Nat.lt_floor_add_one ((L:ℝ)*f n i)
  have ha := lo a; have hc := lo c
  change (⌊(L:ℝ)*f a i⌋₊:ℝ) ≤ (L:ℝ)*f a i at ha
  change (⌊(L:ℝ)*f c i⌋₊:ℝ) ≤ (L:ℝ)*f c i at hc
  have ha' := hi a; have hc' := hi c
  rw [same] at ha ha'
  rw [Nat.cast_sub hac'.le, Int.cast_sub, show ((c.val:ℝ)-(a.val:ℝ))*b i -
      ((⌊(c.val:ℝ)*b i⌋:ℝ) - (⌊(a.val:ℝ)*b i⌋:ℝ)) = f c i - f a i by
        change _ = Int.fract ((c.val:ℝ)*b i) - Int.fract ((a.val:ℝ)*b i)
        rw [← Int.self_sub_floor, ← Int.self_sub_floor]; ring]
  rw [abs_le]; constructor
  · apply (neg_le_iff_add_nonneg).mpr
    rw [← mul_nonneg_iff_of_pos_right hp, add_mul, sub_mul, div_mul_cancel₀ _ hp.ne']
    nlinarith only [ha',hc]
  · apply (le_div_iff₀ hp).mpr; nlinarith only [hc',ha]

/-- Some scale between `T` and `L^d*T` puts every `(u_i+1)*s` within
`1/L` of an integer. In the shuffle projection the slope variable is `s=t/(2-t)`. -/
theorem exists_resonant_scale {ι : Type*} [Fintype ι] (u : ι → ℝ)
    (L : ℕ) (hL : 0 < L) {T : ℝ} (hT : 0 ≤ T) :
    ∃ s : ℝ, T ≤ s ∧ s ≤ (L : ℝ) ^ Fintype.card ι * T ∧
      ∀ i, ∃ z : ℤ, |(u i + 1) * s - z| ≤ 1 / (L : ℝ) := by
  obtain ⟨q, hq, hD, h⟩ := exists_simultaneous_approx (fun i => (u i + 1) * T) L hL
  refine ⟨(q:ℝ)*T, ?_, mul_le_mul_of_nonneg_right (by exact_mod_cast hD) hT, fun i => ?_⟩
  · exact le_mul_of_one_le_left hT (by exact_mod_cast hq)
  · obtain ⟨z, hz⟩ := h i
    exact ⟨z, by simpa only [mul_left_comm (q:ℝ)] using hz⟩

end PermutationStrips.Shuffle
