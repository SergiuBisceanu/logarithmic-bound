import PermutationStrips.AngularBlockPath
import PermutationStrips.AngularLinearGame

/-! The exponential moment is controlled within one genuine path: an insertion can
only decrease each section, and an active stage saves a quadratic amount on average. -/

open Set MeasureTheory
open scoped BigOperators
namespace PermutationStrips.AngularBlock
noncomputable section

private def clock (i c : ℕ) := 1+min i c

/-- One path of the specified depth controls the exponential moment against any
terminal weights. The clock advances at the first c active stages of each height. -/
theorem exists_moment_path {J : Type*} [Fintype J] (t : J → ℝ) (ht : ∀ j, t j ∈ Icc 0 1)
    (cut : J → ℕ) (U : ℕ → ℝ) (hU : ∀ i, 16 ≤ U i)
    (hc : ∀ i j, i < cut j → 8 ≤ U i*radius (t j)) (n : ℕ)
    (a : J → ℝ) (ha : ∀ j, 0 ≤ a j) :
    ∃ p : Path, p.depth=n ∧ (Fintype.card p.Index : ℝ) ≤ ∏ i ∈ Finset.range n, 4*U i ∧
      ∑ j, a j*(moment (1+min n (cut j)) (len p.pattern (t j))-2) ≤ 0 := by
  classical
  induction n generalizing a with
  | zero =>
    refine ⟨.seed,rfl,by simp [Path.Index],?_⟩
    apply Finset.sum_nonpos
    intro j _
    apply mul_nonpos_of_nonneg_of_nonpos (ha j)
    exact sub_nonpos.mpr (by simpa using moment_one_le_two (Path.seed.pattern.section_length_le_one (ht j)))
  | succ n ih =>
    let m := fun j => clock n (cut j)
    let m' := fun j => clock (n+1) (cut j)
    let b := fun j => if n<cut j then 1-momentThreshold (m j) else 1
    have hm (j) : 0<m j := by dsimp [m,clock]; omega
    have hb (j) : 0≤b j := by
      dsimp [b]; split_ifs <;> linarith [(momentThreshold_bounds (m j) (hm j)).2]
    obtain ⟨p,hd,hcount,hprev⟩ := ih (fun j => a j*b j) (fun j => mul_nonneg (ha j) (hb j))
    let x := fun j => len p.pattern (t j)
    have hx (j) : x j ∈ Icc 0 1 := ⟨measureReal_nonneg,p.pattern.section_length_le_one (ht j)⟩
    let s := fun j => momentSlope (m' j) (x j)
    have hs (j) : 0≤s j := momentSlope_nonneg (m' j) (hx j).1
    obtain ⟨rev,u,hu,hgain⟩ := weighted_shell p.pattern t (fun j => a j*s j) ht
      (fun j => mul_nonneg (ha j) (hs j)) (fun j => n<cut j) (hU n) (hc n)
    have hu4 : 4≤u := by linarith [hU n,hu.1]
    let p' := Path.step u hu4 rev p
    let y := fun j => len p'.pattern (t j)
    have hyx (j) : y j ≤ x j := by
      have hl := Shuffle.insertion_saving p.pattern u hu4 rev (ht j)
      have h0 : 0≤Shuffle.regularSaving (p.pattern.sectionAt (t j)) (Shuffle.orientedHeight rev (t j)) u :=
        div_nonneg ENNReal.toReal_nonneg (by linarith)
      exact sub_nonneg.mp (h0.trans hl)
    refine ⟨p',by simp [p',Path.depth,hd],?_,?_⟩
    · change (Fintype.card ((Bool × Fin ⌊u⌋₊) × p.Index):ℝ) ≤ _
      rw [Fintype.card_prod,Nat.cast_mul,Finset.prod_range_succ,mul_comm (∏ i ∈ Finset.range n, _)]
      exact mul_le_mul (Shuffle.card_children_le (by linarith) hu.2) hcount (Nat.cast_nonneg _)
        (by linarith [hU n])
    · let g := fun j => if n<cut j then (x j)^2/128 else 0
      change ∑ j, (a j*s j)*g j ≤ ∑ j, (a j*s j)*(x j-y j) at hgain
      change ∑ j, (a j*b j)*(moment (m j) (x j)-2) ≤ 0 at hprev
      have step (j) : moment (m' j) (y j)-2 ≤
          b j*(moment (m j) (x j)-2) + s j*(g j-(x j-y j)) := by
        have sec := moment_secant (m' j) (hx j).1 (show 0≤y j from measureReal_nonneg) (hyx j)
        change _ ≤ _-s j*(x j-y j) at sec
        by_cases act : n<cut j
        · have he : m' j=m j+1 := by dsimp [m',m,clock]; omega
          have damp := moment_damped (m j) (hm j) (hx j)
          rw [←he] at damp
          change moment (m' j) (x j)-s j*((x j)^2/128) ≤ _ at damp
          simp only [b,g,if_pos act]
          linarith only [sec,damp]
        · have he : m' j=m j := by dsimp [m',m,clock]; omega
          simp only [b,g,if_neg act]
          rw [he] at sec ⊢
          linarith only [sec]
      have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => mul_le_mul_of_nonneg_left (step j) (ha j))
      change ∑ j, a j*(moment (m' j) (y j)-2) ≤ 0
      simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,mul_assoc] at hsum hgain hprev ⊢
      linarith only [hsum,hgain,hprev]

end
end PermutationStrips.AngularBlock
