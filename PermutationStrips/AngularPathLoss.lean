import PermutationStrips.AngularBlockPath

/-! Multiplicity-sensitive accounting for the scales in an actual shuffle path. -/

open Set MeasureTheory
open scoped BigOperators

namespace PermutationStrips.AngularBlock
noncomputable section

/-- The scale at a particular occurrence, with the outermost shuffle first. -/
def Path.scaleAt : (p : Path) → Fin p.depth → ℝ
  | .seed => Fin.elim0
  | .step u _ _ p => Fin.cases u p.scaleAt

theorem Path.scaleAt_ge_four (p : Path) (i : Fin p.depth) : 4 ≤ p.scaleAt i := by
  induction p with
  | seed => exact Fin.elim0 i
  | step u hu rev inner ih =>
    exact Fin.cases hu (fun j => ih j) i

theorem Path.index_card_pos (p : Path) : 0 < Fintype.card p.Index := by
  induction p with
  | seed => simp [Path.Index]
  | step u hu rev inner ih =>
    change 0 < Fintype.card ((Bool × Fin ⌊u⌋₊) × inner.Index)
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    exact Nat.mul_pos (Nat.mul_pos (by decide) (Nat.floor_pos.mpr (by linarith))) ih

/-- The logarithm of every scale is paid for by the logarithm of the square count. -/
theorem Path.sum_log_scale_le (p : Path) :
    ∑ i, Real.log (p.scaleAt i) ≤ Real.log (Fintype.card p.Index) := by
  induction p with
  | seed => simp [Path.Index,Path.depth]
  | step u hu rev inner ih =>
    change (∑ i : Fin (inner.depth+1), Real.log (Fin.cases u inner.scaleAt i)) ≤
      Real.log (Fintype.card ((Bool × Fin ⌊u⌋₊) × inner.Index))
    have hf := Nat.lt_floor_add_one u
    have harity : u ≤ (2:ℝ)*⌊u⌋₊ := by linarith
    have hz : 0 < (Fintype.card inner.Index:ℝ) := by exact_mod_cast inner.index_card_pos
    simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, Fintype.card_prod,
      Fintype.card_bool,Fintype.card_fin, Nat.cast_mul,Nat.cast_ofNat]
    rw [Real.log_mul (by linarith : (2:ℝ)*⌊u⌋₊ ≠ 0) hz.ne']
    exact add_le_add (Real.log_le_log (by linarith) harity) ih

/-- The filter retains repeated occurrences of the same scale. -/
def Path.largeSteps (p : Path) (A : ℝ) : Finset (Fin p.depth) :=
  Finset.univ.filter fun i => A ≤ p.scaleAt i

@[simp] theorem Path.mem_largeSteps (p : Path) (A : ℝ) (i : Fin p.depth) :
    i ∈ p.largeSteps A ↔ A ≤ p.scaleAt i := by simp [Path.largeSteps]

theorem Path.largeSteps_log_bound (p : Path) (z : ℝ) :
    ((p.largeSteps (Real.exp z)).card:ℝ)*z ≤ Real.log (Fintype.card p.Index) := by
  classical
  calc
    _ = ∑ _i ∈ p.largeSteps (Real.exp z), z := by simp
    _ ≤ ∑ i ∈ p.largeSteps (Real.exp z), Real.log (p.scaleAt i) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := (p.mem_largeSteps (Real.exp z) i).mp hi
      simpa using Real.log_le_log (Real.exp_pos _) h
    _ ≤ ∑ i, Real.log (p.scaleAt i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      exact Real.log_nonneg (by linarith [p.scaleAt_ge_four i])
    _ ≤ _ := p.sum_log_scale_le

theorem Path.largeSteps_card_le (p : Path) {k m : ℝ} (hk : 0<k) (hm : 0<m)
    (hbudget : (Fintype.card p.Index:ℝ) ≤ Real.exp (8*k)) :
    ((p.largeSteps (Real.exp (k/(4*m)))).card:ℝ) ≤ 32*m := by
  have hpos : 0 < (Fintype.card p.Index:ℝ) := by exact_mod_cast p.index_card_pos
  have hlog := Real.log_le_log hpos hbudget
  rw [Real.log_exp] at hlog
  have h := (p.largeSteps_log_bound (k/(4*m))).trans hlog
  rw [←mul_div_assoc,div_le_iff₀ (by positivity)] at h
  exact (le_of_mul_le_mul_right (by nlinarith only [h] :
    ((p.largeSteps (Real.exp (k/(4*m)))).card:ℝ)*k ≤ (32*m)*k) hk)

/-- All large scale occurrences, keeping both the path and the stage index. -/
abbrev LargeOccurrences {M : ℕ} (paths : Fin M → Path) (A : ℝ) :=
  (j : Fin M) × ↥((paths j).largeSteps A)

theorem largeOccurrences_card_le {M : ℕ} (paths : Fin M → Path) {k m : ℝ}
    (hk : 0<k) (hm : 0<m) (hbudget : ∀ j, (Fintype.card (paths j).Index:ℝ) ≤ Real.exp (8*k)) :
    (Fintype.card (LargeOccurrences paths (Real.exp (k/(4*m)))):ℝ) ≤ 32*m*M := by
  classical
  rw [Fintype.card_sigma,Nat.cast_sum]
  calc
    _ ≤ ∑ _j : Fin M, 32*m := Finset.sum_le_sum fun j _ => by
      simpa only [Fintype.card_coe] using (paths j).largeSteps_card_le hk hm (hbudget j)
    _ = _ := by simp; ring

theorem Path.seed_length {t : ℝ} (ht : t ∈ Icc 0 1) : len Path.seed.pattern t = 1 := by
  show volume.real (Path.seed.pattern.sectionAt t) = 1
  rw [Pattern.sectionAt_eq _ ht]
  have hz (i : Fin 1) : Pattern.gridStart i=0 := by fin_cases i; simp [Pattern.gridStart]
  simp [Path.Index,Path.pattern,Pattern.equalGrid,Pattern.start,projection,hz]
  change volume.real (⋃ _ : Fin 1, Icc (0:ℝ) 1) = 1
  rw [Set.iUnion_const,Real.volume_real_Icc_of_le (by norm_num)]
  norm_num

/-- A bound for the loss at each occurrence telescopes along the actual path. -/
theorem Path.length_lower_of_step_loss (p : Path) {t : ℝ} (ht : t ∈ Icc 0 1)
    (loss : ℝ → ℝ) (hstep : ∀ i : Fin p.depth, ∀ (rev : Bool) (inner : Path),
      len inner.pattern t -
        len ((Shuffle.orientedPattern (p.scaleAt i) (p.scaleAt_ge_four i) rev).insert inner.pattern) t
          ≤ loss (p.scaleAt i)) :
    1 - ∑ i, loss (p.scaleAt i) ≤ len p.pattern t := by
  induction p with
  | seed => simp [Path.depth, Path.seed_length ht]
  | step u hu rev inner ih =>
    have h := ih fun i => hstep i.succ
    have h₀ := hstep (0 : Fin (inner.depth+1)) rev inner
    change len inner.pattern t - len ((Path.step u hu rev inner).pattern) t ≤ loss u at h₀
    change 1 - (∑ i : Fin (inner.depth+1), loss (Fin.cases u inner.scaleAt i)) ≤ _
    simp only [Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ]
    linarith

/-- Small scales cost at most the depth times their common bound. Only the
enumerated large occurrences are charged the potentially larger loss. -/
theorem Path.length_lower_of_split_loss (p : Path) {t : ℝ} (ht : t ∈ Icc 0 1)
    (A small big : ℝ) (hs : 0 ≤ small) (hstep : ∀ i : Fin p.depth,
      ∀ (rev : Bool) (inner : Path), len inner.pattern t -
        len ((Shuffle.orientedPattern (p.scaleAt i) (p.scaleAt_ge_four i) rev).insert inner.pattern) t
          ≤ if A ≤ p.scaleAt i then big else small) :
    1 - (p.depth:ℝ)*small - ((p.largeSteps A).card:ℝ)*big ≤ len p.pattern t := by
  classical
  have h := p.length_lower_of_step_loss ht (fun u => if A≤u then big else small) hstep
  have hsum : (∑ i, if A ≤ p.scaleAt i then big else small) ≤
      (p.depth:ℝ)*small+((p.largeSteps A).card:ℝ)*big := by
    calc
      _ ≤ ∑ i, (small + if A ≤ p.scaleAt i then big else 0) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs <;> linarith
      _ = _ := by simp [Finset.sum_add_distrib,← Finset.sum_filter,
                        Path.largeSteps]
  linarith

end
end PermutationStrips.AngularBlock
