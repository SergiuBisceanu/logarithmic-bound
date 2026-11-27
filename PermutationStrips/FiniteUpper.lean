import PermutationStrips.AreaShell
import PermutationStrips.Iteration
import PermutationStrips.Insertion
import PermutationStrips.GridTransfer
import PermutationStrips.ShuffleStep

/-! The finite upper bound. Search for a height interval on which a shuffle
saves enough area to cover the logarithm of its number of children. -/

open Set MeasureTheory

namespace PermutationStrips.FiniteUpper

open Pattern AreaShell

private noncomputable def len {ι : Type*} (P : Pattern ι) (t : ℝ) : ℝ := volume.real (P.sectionAt t)

private theorem integrable_sub {f : ℝ → ℝ} (hi : IntervalIntegrable f volume 0 1)
    {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) : IntervalIntegrable f volume a b := by
  apply hi.mono_set
  rw [uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)]
  exact uIcc_subset_Icc ha hb

private theorem integrable_sq {ι : Type*} [Finite ι] (P : Pattern ι) :
    IntervalIntegrable (fun t => (len P t)^2) volume 0 1 := by
  let f := (Icc (0:ℝ) 1).indicator (len P)
  have hm : Measurable f := P.measurable_length_Icc_indicator
  have he (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) : f t = len P t :=
    indicator_of_mem (show t ∈ Icc (0:ℝ) 1 from ⟨ht.1.le,ht.2⟩) _
  have hi : IntegrableOn (fun t => (f t)^2) (Ioc (0:ℝ) 1) := by
    apply IntegrableOn.of_bound measure_Ioc_lt_top (hm.pow_const 2).aestronglyMeasurable 1
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    rw [he t ht, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ measureReal_nonneg (P.section_length_le_one ⟨ht.1.le,ht.2⟩)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact hi.congr_fun (fun t ht => by rw [he t ht]) measurableSet_Ioc

private theorem transpose_integral {ι : Type*} (P : Pattern ι) {a b : ℝ}
    (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1) :
    (∫ t in a..b, len P.transpose t) = ∫ t in (1-b)..(1-a), len P t := by
  rw [← intervalIntegral.integral_comp_sub_left]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  unfold len
  rw [sectionAt_transpose P ⟨ha.trans ht.1,ht.2.trans hb⟩]

private theorem orient {ι : Type*} [Finite ι] (P : Pattern ι) :
    ∃ Q : Pattern ι, Q.area = P.area ∧ P.area ≤ 2*∫ t in (0:ℝ)..(1/2), len Q t := by
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  have hh : (1/2:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  have h1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  have hi : IntervalIntegrable (len P) volume 0 1 := P.intervalIntegrable_length
  have split := intervalIntegral.integral_add_adjacent_intervals
    (integrable_sub hi h0 hh) (integrable_sub hi hh h1)
  change _ + _ = P.area at split
  by_cases h : P.area ≤ 2*∫ t in (0:ℝ)..(1/2), len P t
  · exact ⟨P,rfl,h⟩
  · refine ⟨P.transpose, ?_, ?_⟩
    · change (∫ t in (0:ℝ)..1, len P.transpose t) = _
      rw [transpose_integral P zero_le_one le_rfl le_rfl]
      norm_num [Pattern.area, len]
    · rw [transpose_integral P (by norm_num) (by norm_num) (by norm_num)]
      norm_num only [sub_zero, show 1-(1/2:ℝ)=1/2 by norm_num]
      linarith

private theorem useful_shell {ι : Type*} [Finite ι] (P : Pattern ι) (hA : 0 < P.area) :
    ∃ (Q : Pattern ι) (j : ℕ), Q.area = P.area ∧
      (P.area/16*((j:ℝ)+1))^2 ≤ ∫ t in radius (j+1)..radius j, (len Q t)^2 := by
  obtain ⟨Q,he,hm⟩ := orient P
  have h := Q.intervalIntegrable_length
  obtain ⟨j,hj⟩ := exists_shell_mass hA (f := len Q)
    (fun _ ha _ hb => integrable_sub h ha hb) (fun _ ht => Q.section_length_le_one ht) hm
  have hr (i : ℕ) : radius i ∈ Icc (0:ℝ) 1 :=
    ⟨(radius_pos i).le, (radius_le_half i).trans (by norm_num)⟩
  exact ⟨Q,j,he,shell_energy hA (integrable_sub h (hr _) (hr _))
    (integrable_sub (integrable_sq _) (hr _) (hr _)) hj⟩

private theorem energy_le_one {ι : Type*} [Finite ι] (P : Pattern ι) (j : ℕ) :
    (∫ t in radius (j+1)..radius j, (len P t)^2) ≤ 1 := by
  have ord : radius (j+1) ≤ radius j := by rw [radius_succ]; linarith [radius_pos j]
  have hr (i : ℕ) : radius i ∈ Icc (0:ℝ) 1 :=
    ⟨(radius_pos i).le, (radius_le_half i).trans (by norm_num)⟩
  calc
    _ ≤ ∫ _ in radius (j+1)..radius j, (1:ℝ) := by
      apply intervalIntegral.integral_mono_on ord (integrable_sub (integrable_sq P) (hr _) (hr _)) intervalIntegrable_const
      intro t ht
      exact pow_le_one₀ measureReal_nonneg (P.section_length_le_one ⟨(hr _).1.trans ht.1,ht.2.trans (hr _).2⟩)
    _ ≤ 1 := by rw [intervalIntegral.integral_const, smul_eq_mul]; nlinarith [(hr (j+1)).1,(hr j).2]

/-- Index and carrier of an arbitrary finite pattern in the deterministic iteration. -/
private structure State where
  index : Type
  enum : Fintype index
  pattern : Pattern index

private noncomputable def State.logSize (s : State) : ℝ := Real.log (@Fintype.card s.index s.enum)

private theorem pattern_nonempty {ι : Type*} (P : Pattern ι) : Nonempty ι := by
  have hx : (1:ℝ) ∈ Ioc (0:ℝ) 1 := by norm_num
  rw [← P.x_cover] at hx
  obtain ⟨i,_⟩ := mem_iUnion.mp hx
  exact ⟨i⟩

private noncomputable def shellScale (j : ℕ) : ℝ := 64*4^j

private theorem shellScale_bounds (j : ℕ) :
    16 ≤ shellScale j ∧ shellScale j * radius (j+1) = 8 ∧
    Real.log (4*shellScale j) ≤ 8*((j:ℝ)+1) := by
  have hp : (1:ℝ) ≤ 4^j := one_le_pow₀ (by norm_num)
  refine ⟨by dsimp [shellScale]; linarith, ?_, ?_⟩
  · dsimp [shellScale, radius]; rw [pow_succ, div_pow, one_pow]
    field_simp
    ring
  · rw [show 4*shellScale j = (2:ℝ)^8 * ((2:ℝ)^2)^j by dsimp [shellScale]; norm_num; ring,
       Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    have hl : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg j)]

private theorem size_on_grid {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (h : Real.log m ≤ Real.log n / 2) : 2*(m:ℝ)/n ≤ 4/Real.log n := by
  have hnp : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmp : (0:ℝ) < m := by exact_mod_cast hm
  have hl : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
  let v := Real.exp (Real.log (n:ℝ)/2)
  have hm' : (m:ℝ) ≤ v := by simpa [v,Real.exp_log hmp] using Real.exp_le_exp.mpr h
  have hv : 0 < v := Real.exp_pos _
  have hs : v*v = (n:ℝ) := by
    dsimp [v]; rw [← Real.exp_add, show Real.log (n:ℝ)/2 + Real.log (n:ℝ)/2 = Real.log n by ring, Real.exp_log hnp]
  have ht : Real.log (n:ℝ) ≤ 2*v := by
    dsimp [v]; linarith [Real.add_one_le_exp (Real.log (n:ℝ)/2)]
  rw [div_le_div_iff₀ hnp hl]
  nlinarith [mul_le_mul hm' ht hl.le hv.le]


private theorem decreasing_step (s : State) (hA : 0 < s.pattern.area) :
    ∃ (s' : State) (d : ℝ), 1 ≤ d ∧ d*s.pattern.area ≤ 1048576 ∧
      s'.logSize ≤ s.logSize+d ∧ s.pattern.area^2*d ≤ 1048576*(s.pattern.area-s'.pattern.area) := by
  letI := s.enum
  obtain ⟨Q,j,hQ,hE⟩ := useful_shell s.pattern hA
  obtain ⟨hU,hact,hprice⟩ := shellScale_bounds j
  have H : ∀ t ∈ Icc (radius (j+1)) (radius j), 0 < t ∧ t ≤ 1/2 ∧ 8 ≤ shellScale j*t := by
    intro t ht
    exact ⟨(radius_pos _).trans_le ht.1, ht.2.trans (radius_le_half _),
      hact.symm.le.trans (mul_le_mul_of_nonneg_left ht.1 (by linarith))⟩
  obtain ⟨u,hu,hs⟩ := Shuffle.exists_area_step Q false hU
    (fun t ht => ⟨(H t ht).1.le,(H t ht).2.1.trans (by norm_num)⟩) H
  let Q' := (Shuffle.orientedPattern u (by linarith [hu.1]) false).insert Q
  let s' : State := ⟨_, inferInstance, Q'⟩
  let A := s.pattern.area
  let d := 8*((j:ℝ)+1)
  have hd : 1 ≤ d := by dsimp [d]; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  have hle : (A/16*((j:ℝ)+1))^2 ≤ 1 := hE.trans (energy_le_one Q j)
  have hdA : d*A ≤ 1048576 := by
    dsimp [d]; nlinarith [sq_nonneg (A/16*((j:ℝ)+1)-1)]
  refine ⟨s',d,hd,hdA,?_,?_⟩
  · let m := @Fintype.card s.index s.enum
    have hmp : (0:ℝ) < m := by exact_mod_cast Fintype.card_pos_iff.mpr (pattern_nonempty s.pattern)
    have hu' : 1 ≤ u := by linarith [hu.1]
    have hfp : (0:ℝ) < ⌊u⌋₊ := by exact_mod_cast (Nat.floor_pos.mpr hu')
    have hF : (⌊u⌋₊ : ℝ) ≤ 2*shellScale j := (Nat.floor_le (by linarith)).trans hu.2
    have hc : (2*(⌊u⌋₊ : ℝ))*(m:ℝ) ≤ (4*shellScale j)*m :=
      mul_le_mul_of_nonneg_right (by linarith) hmp.le
    have he : s'.logSize = Real.log ((2*(⌊u⌋₊ : ℝ))*(m:ℝ)) := by
      simp [s', State.logSize, Q', m, Fintype.card_prod]
    rw [he]
    calc
      _ ≤ Real.log ((4*shellScale j)*(m:ℝ)) := Real.log_le_log (by positivity) hc
      _ = s.logSize + Real.log (4*shellScale j) := by
        rw [Real.log_mul (mul_ne_zero (by norm_num) (by linarith)) hmp.ne', add_comm]; rfl
      _ ≤ _ := add_le_add_left hprice _
  · have ord : radius (j+1) ≤ radius j := by rw [radius_succ]; linarith [radius_pos j]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ord, hQ] at hs
    change (∫ t in radius (j+1)..radius j, (len Q t)^2)/128 ≤ A-s'.pattern.area at hs
    have hsave : (A*((j:ℝ)+1))^2 ≤ 32768*(A-s'.pattern.area) := by
      change (A/16*((j:ℝ)+1))^2 ≤ _ at hE
      nlinarith
    have hj : (0:ℝ) ≤ (j:ℝ)*((j:ℝ)+1) := by positivity
    have hcost : A^2*d ≤ 8*(A*((j:ℝ)+1))^2 := by
      dsimp [d]; nlinarith [mul_nonneg (sq_nonneg A) hj]
    change A^2*d ≤ _
    nlinarith [sq_nonneg (A*((j:ℝ)+1))]

/-- Every equal grid admits a permutation whose genuine planar covered area is O(1/log n).
The numerical constant is used only for the order estimate. -/
theorem permutation_upper : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    ∃ σ : Equiv.Perm (Fin n), Crossings.permutationArea σ ≤ C / Real.log n := by
  let C : ℝ := 1048576
  have hC : 0 < C := by norm_num [C]
  refine ⟨4*C+4,by positivity,?_⟩
  intro n hn
  have hn0 : 0 < n := by omega
  have hl : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
  let k := Real.log n/(4*C)
  have hk : 0 < k := by dsimp [k]; positivity
  let base : State := ⟨Fin 1,inferInstance,Pattern.equalGrid (n := 1) (by decide) (Equiv.refl _)⟩
  have init : base.logSize = 0 := by simp [base,State.logSize]
  obtain ⟨s,ha,hN⟩ := Iteration.reach (fun s : State => s.pattern.area) State.logSize base init
    hC decreasing_step hk
  letI := s.enum
  have hcard := Fintype.card_pos_iff.mpr (pattern_nonempty s.pattern)
  obtain ⟨σ,hs⟩ := s.pattern.exists_permutationArea_le hn0
  refine ⟨σ,hs.trans ?_⟩
  have hz : 2*C*k = Real.log n/2 := by dsimp [k]; field_simp; norm_num
  have hgrid := size_on_grid hn hcard (hN.trans_eq hz)
  have harea : s.pattern.area ≤ 4*C/Real.log n := by
    simpa [k, div_div_eq_mul_div] using ha
  linarith [add_div (4*C) 4 (Real.log (n:ℝ))]

end PermutationStrips.FiniteUpper
