import PermutationStrips.CompactFamily
import PermutationStrips.CompactLimit

/-! Regularity at elementary scales for the two ordered families of a shuffle. -/

open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace PermutationStrips.CompactPlane

noncomputable section

/-- A row of nearby components supplies a whole block of consecutive cells in
the requested ball. The row length can be arbitrarily large. -/
theorem localGeometry_of_rows {ι : Type*} {m : ℕ} (P : Pattern ι) {h : ℝ}
    (hh : 0 < h) (hm : 1/8 ≤ m*h)
    (rows : ∀ i, ∃ (f : Fin m ↪ ι) (k : Fin m), f k=i ∧ (∀ j, h ≤ P.w (f j)) ∧
      ∀ j p, p ∈ cell P (f j) → ∀ z, z ∈ cell P i →
        dist p z ≤ 4*h + 4*h*|(j.val:ℝ)-k.val|) : LocalGeometry P := by
  classical
  intro i z hz r hr hr8 hs
  obtain ⟨f,k,hk,hw,hd⟩ := rows i
  have h8 : h ≤ r/8 := (hw k).trans (hk ▸ hs)
  let d := r/(16*h)
  have dpos : 0 ≤ d := div_nonneg hr.le (by positivity)
  let J := min m (⌊d⌋₊ + 1)
  have Jm : J ≤ m := min_le_left ..
  have Jpos : 0 < J := lt_min (Nat.zero_lt_of_lt k.isLt) (Nat.zero_lt_succ _)
  let s := min k.val (m-J)
  have sk : s ≤ k.val := min_le_left ..
  have sJ : s+J ≤ m := Nat.add_le_of_le_sub Jm (min_le_right ..)
  have ks : k.val < s+J := by dsimp [s]; omega
  let f' : Fin J ↪ Fin m := ⟨fun j => ⟨s+j.val,by omega⟩,fun _ _ he => Fin.ext (by simpa using congrArg Fin.val he)⟩
  refine ⟨Finset.univ.map (f'.trans f),?_,?_⟩
  · have count : r/64 ≤ J*h := by
      by_cases hm' : m ≤ ⌊d⌋₊+1
      · rw [show J=m from min_eq_left hm']; linarith
      · rw [show J=⌊d⌋₊+1 from min_eq_right (le_of_not_ge hm')]
        push_cast
        have hd' := Nat.lt_floor_add_one d
        have he : d*(16*h) = r := by dsimp [d]; field_simp
        nlinarith [mul_le_mul_of_nonneg_right hd'.le hh.le]
    apply count.trans
    rw [Finset.sum_map]
    calc
      (J:ℝ)*h = ∑ _j : Fin J, h := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => hw (f' j)
  · intro l hl p hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hl
    have hdist := hd (f' j) p hp z hz
    have dj : |((f' j).val:ℝ)-k.val| ≤ d := by
      have fval : (f' j).val = s+j.val := rfl
      have hupper : (f' j).val ≤ k.val + ⌊d⌋₊ := by rw [fval]; dsimp [J] at *; omega
      have hlower : k.val ≤ (f' j).val + ⌊d⌋₊ := by rw [fval]; dsimp [J] at *; omega
      have hh₁ : ((f' j).val:ℝ) ≤ (k.val:ℝ)+ ⌊d⌋₊ := by exact_mod_cast hupper
      have hh₂ : (k.val:ℝ) ≤ ((f' j).val:ℝ)+ ⌊d⌋₊ := by exact_mod_cast hlower
      exact abs_le.mpr ⟨by linarith [Nat.floor_le dpos],by linarith [Nat.floor_le dpos]⟩
    have eh : d*(16*h) = r := by dsimp [d]; field_simp
    change dist p z < r
    nlinarith [mul_le_mul_of_nonneg_left dj hh.le]

private theorem abs_coord {a b x y w e : ℝ} (hx : x ∈ Icc a (a+w)) (hy : y ∈ Icc b (b+e))
    {D : ℝ} (hab : |a-b| ≤ D) : |x-y| ≤ max w e + D := by
  rcases abs_le.mp hab with ⟨l,r⟩
  exact abs_le.mpr ⟨by linarith [hx.1,hy.2,le_max_right w e],by linarith [hx.2,hy.1,le_max_left w e]⟩

theorem localGeometry_equalGrid_diag {m : ℕ} (hm : 0<m) :
    LocalGeometry (Pattern.equalGrid hm (Equiv.refl _)) := by
  let P := Pattern.equalGrid hm (Equiv.refl (Fin m))
  let h := 1/(m:ℝ)
  have mp : 0 < (m:ℝ) := by exact_mod_cast hm
  apply localGeometry_of_rows P (m:=m) (h:=h) (by dsimp [h]; positivity)
  · dsimp [h]; field_simp; linarith
  · intro k
    refine ⟨Function.Embedding.refl _,k,rfl,fun _ => le_rfl,?_⟩
    intro j p hp z hz
    have gap : |P.x j-P.x k| = h*|(j.val:ℝ)-k.val| := by
      dsimp [P,Pattern.equalGrid,Pattern.gridStart,h]
      rw [← sub_div,abs_div,abs_of_pos mp]; ring
    have hx := abs_coord hp.1 hz.1 gap.le
    have hy := abs_coord hp.2 hz.2 gap.le
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    change |p.1-z.1| ≤ max h h + _ at hx
    change |p.2-z.2| ≤ max h h + _ at hy
    rw [max_self] at hx hy
    exact max_le (by nlinarith [show 0 ≤ h by dsimp [h]; positivity, mul_nonneg (show 0≤h by dsimp [h]; positivity) (abs_nonneg ((j.val:ℝ)-k.val))])
      (by nlinarith [show 0 ≤ h by dsimp [h]; positivity, mul_nonneg (show 0≤h by dsimp [h]; positivity) (abs_nonneg ((j.val:ℝ)-k.val))])

theorem localGeometry_equalGrid_one :
    LocalGeometry (Pattern.equalGrid (by decide : 0<1) (Equiv.refl _)) := localGeometry_equalGrid_diag _

end
end PermutationStrips.CompactPlane
