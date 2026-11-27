import PermutationStrips.CompactRegular
import PermutationStrips.AngularBlockPath

/-! Each color of the shuffle has an ordered row of neighboring squares, including
the final square absorbing the fractional part of the scale. -/

open Set
namespace PermutationStrips.CompactPlane
noncomputable section

private theorem width_base (u : ℝ) (hu : 4≤u) (i : Fin ⌊u⌋₊) :
    1/u ≤ (Shuffle.basePartition u hu).w i ∧ (Shuffle.basePartition u hu).w i ≤ 2/u := by
  have hp : 0<u := by linarith
  change 1/u ≤ ((if i.val+1<⌊u⌋₊ then ((i.val+1:ℕ):ℝ) else u)-(i.val:ℝ))/u ∧ _
  change _ ∧ ((if i.val+1<⌊u⌋₊ then ((i.val+1:ℕ):ℝ) else u)-(i.val:ℝ))/u ≤ 2/u
  split_ifs with h
  · push_cast; constructor <;> apply (div_le_div_iff_of_pos_right hp).mpr <;> linarith
  · have he : i.val+1=⌊u⌋₊ := by have := i.isLt; omega
    have he' : (i.val:ℝ)+1=(⌊u⌋₊:ℕ) := by exact_mod_cast he
    constructor <;> apply (div_le_div_iff_of_pos_right hp).mpr <;>
      linarith [Nat.floor_le hp.le,Nat.lt_floor_add_one u]

private theorem row_coords {u : ℝ} (hu : 4≤u) (b : Bool) (i : Fin ⌊u⌋₊)
    (z : ℝ×ℝ) (hz : z ∈ cell (Shuffle.shufflePattern u hu) (b,i)) :
    z.1 ∈ Icc (i.val/u) (i.val/u+2/u) ∧
    z.2 ∈ Icc ((i.val/u+(if b then 0 else 1))/2) ((i.val/u+(if b then 0 else 1))/2+1/u) := by
  have hunit : (2:ℝ)/u=2*(1/u) := by ring
  let v := (Shuffle.basePartition u hu).w i
  have w := width_base u hu i
  change 1/u ≤ v ∧ v ≤ 2/u at w
  have wpos : 0<v := (Shuffle.basePartition u hu).wpos i
  have hx := hz.1
  have hy := hz.2
  change z.1 ∈ Icc (i.val/u+(if b then v/2 else 0)) (i.val/u+(if b then v/2 else 0)+v/2) at hx
  change z.2 ∈ Icc ((i.val/u+(if b then 0 else 1))/2) ((i.val/u+(if b then 0 else 1))/2+v/2) at hy
  refine ⟨?_,⟨hy.1,by linarith [hy.2,w.2]⟩⟩
  cases b <;> simp only [Bool.false_eq_true,if_false,if_true,add_zero] at hx <;>
    exact ⟨by linarith [hx.1],by linarith [hx.2,w.2]⟩

theorem localGeometry_shuffle (u : ℝ) (hu : 4≤u) : LocalGeometry (Shuffle.shufflePattern u hu) := by
  have hp : 0<u := by linarith
  have hunit : (2:ℝ)/u=2*(1/u) := by ring
  let h := 1/(2*u)
  apply localGeometry_of_rows _ (m:=⌊u⌋₊) (h:=h) (by dsimp [h]; positivity)
  · dsimp [h]
    rw [← mul_div_assoc,le_div_iff₀ (by positivity)]
    linarith [Nat.lt_floor_add_one u]
  · rintro ⟨b,k⟩
    refine ⟨⟨fun j => (b,j), (fun _ _ he => congrArg Prod.snd he)⟩,k,rfl,?_,?_⟩
    · intro j
      change 1/(2*u) ≤ (Shuffle.basePartition u hu).w j/2
      linarith only [(width_base u hu j).1,show (1:ℝ)/(2*u)=(1/u)/2 by ring]
    · intro j p hp' z hz
      have cj := row_coords hu b j p hp'
      have ck := row_coords hu b k z hz
      let D := |(j.val:ℝ)-k.val|/u
      have hD : 0≤D := div_nonneg (abs_nonneg _) hp.le
      have hd : |(j.val:ℝ)/u-(k.val:ℝ)/u|=D := by rw [←sub_div,abs_div,abs_of_pos hp]
      have gap := abs_le.mp hd.le
      have hl1 : p.1-z.1 ≤ 2/u+D := by linarith [cj.1.2,ck.1.1,gap.2]
      have hl2 : z.1-p.1 ≤ 2/u+D := by linarith [ck.1.2,cj.1.1,gap.1]
      have hl3 : p.2-z.2 ≤ 2/u+D := by linarith [cj.2.2,ck.2.1,gap.2,one_div_pos.mpr hp]
      have hl4 : z.2-p.2 ≤ 2/u+D := by linarith [ck.2.2,cj.2.1,gap.1,one_div_pos.mpr hp]
      have hh : 2/u+D ≤ 4*h+4*h*|(j.val:ℝ)-k.val| := by
        dsimp [h]; change _ ≤ _+_ * _
        have eq : 4*(1/(2*u))*|(j.val:ℝ)-k.val|=2*D := by dsimp [D]; ring
        rw [eq,show (4:ℝ)*(1/(2*u))=2/u by ring]; linarith
      rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
      exact (max_le (abs_le.mpr ⟨by linarith,hl1⟩) (abs_le.mpr ⟨by linarith,hl3⟩)).trans hh

theorem localGeometry_path (p : AngularBlock.Path) : LocalGeometry p.pattern := by
  induction p with
  | seed => exact localGeometry_equalGrid_one
  | step u hu rev inner ih =>
    apply localGeometry_insert _ ih
    cases rev
    · exact localGeometry_shuffle u hu
    · exact localGeometry_transpose (localGeometry_shuffle u hu)

end
end PermutationStrips.CompactPlane
