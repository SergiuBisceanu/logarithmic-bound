import PermutationStrips.AngularPathLoss
import PermutationStrips.ShuffleResonance

/-! A common height with aligned large scales limits the total projection loss. -/

open Set MeasureTheory
open scoped BigOperators

namespace PermutationStrips.AngularBlock
noncomputable section

/-- Phase alignment is required only at large scales that actually occur in this path. -/
theorem Path.length_lower_of_aligned_scales (p : Path) {A ε t : ℝ}
    (hA : 0<A) (hε : ε ∈ Icc 0 (1/8)) (ht : t ∈ Icc 0 (1/4))
    (hphase : ∀ i ∈ p.largeSteps A, ∃ z : ℤ,
      |(p.scaleAt i+1)*t/(2-t)-z| ≤ ε) :
    1-(p.depth:ℝ)*(4*A*t)-((p.largeSteps A).card:ℝ)*(8*(t+ε+1/A)) ≤ len p.pattern t := by
  apply p.length_lower_of_split_loss (⟨ht.1,by linarith [ht.2]⟩ : t ∈ Icc 0 1)
    A (4*A*t) (8*(t+ε+1/A)) (mul_nonneg (by positivity) ht.1)
  intro i rev inner
  by_cases hlarge : A ≤ p.scaleAt i
  · rw [if_pos hlarge]
    obtain ⟨z,hz⟩ := hphase i ((p.mem_largeSteps A i).mpr hlarge)
    have h := Shuffle.insertion_loss_aligned inner.pattern (p.scaleAt i) (p.scaleAt_ge_four i)
      rev ht hε z hz
    have hinv := one_div_le_one_div_of_le hA hlarge
    exact h.trans (by linarith)
  · rw [if_neg hlarge]
    have h := Shuffle.insertion_loss_small inner.pattern (p.scaleAt i) (p.scaleAt_ge_four i) rev ht
    apply h.trans
    exact mul_le_mul_of_nonneg_right (by linarith [lt_of_not_ge hlarge]) ht.1

/-- At an aligned height all but a small fraction of the original unit section
survives. Both the length of the path and its actual number of squares enter the bound. -/
theorem Path.length_at_resonance (p : Path) {k : ℕ} {m t : ℝ}
    (hk : 0<k) (hm : 0<m) (hd : p.depth=k)
    (hbudget : (Fintype.card p.Index:ℝ) ≤ Real.exp (8*(k:ℝ)))
    (hB : 1024*(k:ℝ) ≤ Real.exp ((k:ℝ)/(4*m)))
    (ht0 : 0<t) (ht : t ≤ 1/(Real.exp ((k:ℝ)/(4*m)))^2)
    (hphase : ∀ i ∈ p.largeSteps (Real.exp ((k:ℝ)/(4*m))), ∃ z : ℤ,
      |(p.scaleAt i+1)*t/(2-t)-z| ≤ 1/(4096*m)) : 1/2 ≤ len p.pattern t := by
  let B := Real.exp ((k:ℝ)/(4*m))
  let d : ℝ := (p.largeSteps B).card
  let ε := min (1/8:ℝ) (1/(4096*m))
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have bp : 0 < B := Real.exp_pos _
  change 1024*(k:ℝ) ≤ B at hB
  change t ≤ 1/B^2 at ht
  have b1 : 1 ≤ B := by linarith
  have dp : 0 ≤ d := by dsimp [d]; positivity
  have dm : d ≤ 32*m := p.largeSteps_card_le (by exact_mod_cast hk) hm hbudget
  have dk : d ≤ (k:ℝ) := by
    dsimp [d]
    exact_mod_cast (Finset.card_le_univ (p.largeSteps B)).trans_eq (by simp [hd])
  have ep : ε ∈ Icc 0 (1/8) := ⟨le_min (by norm_num) (by positivity),min_le_left _ _⟩
  have phase (i) (hi : i ∈ p.largeSteps B) : ∃ z : ℤ, |(p.scaleAt i+1)*t/(2-t)-z| ≤ ε := by
    have d1 : (1:ℝ) ≤ d := by
      dsimp [d]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Finset.card_pos.mpr ⟨i,hi⟩).ne')
    have e1 : 1/(4096*m) ≤ (1/8:ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    simpa only [ε,min_eq_right e1] using hphase i hi
  have bt : B*t ≤ 1/B := (mul_le_mul_of_nonneg_left ht bp.le).trans_eq (by field_simp)
  have tb : t ≤ 1/B := by
    linarith only [bt, mul_nonneg (sub_nonneg.mpr b1) ht0.le]
  have tk : t ∈ Icc 0 (1/4) := ⟨ht0.le,tb.trans (one_div_le_one_div_of_le (by norm_num) (by linarith))⟩
  have h := p.length_lower_of_aligned_scales bp ep tk phase
  change 1-(p.depth:ℝ)*(4*B*t)-d*(8*(t+ε+1/B)) ≤ _ at h
  rw [hd] at h
  have kb : (k:ℝ)*(1/B) ≤ 1/1024 := by
    rw [mul_one_div,div_le_div_iff₀ bp (by norm_num)]
    linarith
  have db : d*(1/B) ≤ 1/1024 :=
    (mul_le_mul_of_nonneg_right dk (by positivity)).trans kb
  have de : d*ε ≤ 1/128 := by
    calc
      _ ≤ (32*m)*(1/(4096*m)) := mul_le_mul dm (min_le_right _ _) ep.1 (by positivity)
      _ = _ := by field_simp; ring
  have s := mul_le_mul_of_nonneg_left bt (Nat.cast_nonneg k)
  have dt := (mul_le_mul_of_nonneg_left tb dp).trans db
  nlinarith only [h,s,kb,dt,db,de]

end
end PermutationStrips.AngularBlock
