import PermutationStrips.AngularBlockMesh
import PermutationStrips.InsertionLoss
import PermutationStrips.CompactPlane

/-! Near an axis the shuffle loses little projection length when its regular
red and blue starts nearly alternate. The last, unequal pair may be discarded. -/

open Set MeasureTheory Function
open scoped BigOperators
namespace PermutationStrips.Shuffle
noncomputable section

private def digit (t u : ℝ) (b : Bool) (j : ℕ) :=
  (2-t)*(j:ℝ) + if b then 1-t else t*u

/-- Retain equally long disjoint subintervals of the first n regular intervals
of each color, in units of one regular child width. -/
private theorem keep {t u l : ℝ} (hu : 4≤u) (ht : t∈Icc 0 1) {n : ℕ}
    (hn : n<⌊u⌋₊) (hl : l∈Icc 0 1)
    (sep : ∀ p q : Bool × Fin n, p≠q →
      l ≤ |digit t u p.1 p.2.val-digit t u q.1 q.2.val|) :
    (n:ℝ)*l/u ≤ volume.real ((shufflePattern u hu).sectionAt t) := by
  let a (p : Bool × Fin n) := digit t u p.1 p.2.val/(2*u)
  let d := l/(2*u)
  let I (p : Bool × Fin n) := Ioc (a p) (a p+d)
  have den : 0<2*u := by linarith
  have hd : 0≤d := div_nonneg hl.1 den.le
  have dis : Pairwise (Disjoint on I) := by
    intro p q h
    have gap : d ≤ |a p-a q| := by
      dsimp [a,d]; rw [← sub_div,abs_div,abs_of_pos den]
      exact div_le_div_of_nonneg_right (sep p q h) den.le
    rcases le_total (a p) (a q) with hp|hp
    · rw [abs_of_nonpos (sub_nonpos.mpr hp)] at gap
      exact Ioc_disjoint_Ioc_of_le (by linarith)
    · rw [abs_of_nonneg (sub_nonneg.mpr hp)] at gap
      exact (Ioc_disjoint_Ioc_of_le (by linarith : a q+d ≤ a p)).symm
  have sub : (⋃ p, I p) ⊆ (shufflePattern u hu).sectionAt t := by
    rw [Pattern.sectionAt_eq _ ht]
    apply iUnion_subset
    rintro ⟨b,j⟩ x hx
    let i : Fin ⌊u⌋₊ := ⟨j.val,j.isLt.trans hn⟩
    obtain ⟨hs,hw⟩ := regularCoords u hu t i (by dsimp [i]; omega) b
    have eq : (if b then blueStart t (i.val:ℝ) else redStart t u (i.val:ℝ)) =
        digit t u b j.val := by cases b <;> dsimp [i,digit,blueStart,redStart] <;> ring
    refine mem_iUnion.mpr ⟨(b,i),?_⟩
    rw [hs,hw,eq]
    exact ⟨hx.1.le,hx.2.trans (add_le_add_left (div_le_div_of_nonneg_right hl.2 den.le) _)⟩
  have hm (p : Bool × Fin n) : volume.real (I p) = d := by
    simp [I,Real.volume_Ioc,measureReal_def,ENNReal.toReal_ofReal hd]
  have m := measureReal_mono (μ:=volume) sub ((Pattern.isCompact_sectionAt _ ht).measure_lt_top.ne)
  rw [measureReal_iUnion_fintype dis (fun _ => measurableSet_Ioc) (fun _ => measure_Ioc_lt_top.ne)] at m
  simpa [hm,d,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using m

private theorem same_digit {t u : ℝ} (ht : t≤1) (b : Bool) {i j : ℕ} (h : i≠j) :
    1 ≤ |digit t u b i-digit t u b j| := by
  have eq : digit t u b i-digit t u b j = (2-t)*((i:ℝ)-j) := by dsimp [digit]; ring
  rw [eq,abs_mul,abs_of_nonneg (by linarith : 0≤2-t)]
  have dist : 1≤|(i:ℝ)-j| := by
    rcases lt_or_gt_of_ne h with h|h
    · have hh : (i:ℝ)+1 ≤ j := by exact_mod_cast h
      exact le_abs.mpr (Or.inr (by linarith))
    · have hh : (j:ℝ)+1 ≤ i := by exact_mod_cast h
      exact le_abs.mpr (Or.inl (by linarith))
  simpa using mul_le_mul (by linarith : 1≤2-t) dist zero_le_one (by linarith : 0≤2-t)

private theorem digit_resonance {t u ε : ℝ} (ht : t∈Icc 0 (1/4)) (hε : 0≤ε) (z : ℤ)
    (ha : |(u+1)*t/(2-t)-z|≤ε) (i j : ℕ) :
    1-t-2*ε ≤ |digit t u true j-digit t u false i| := by
  have den : 0<2-t := by linarith [ht.2]
  have err : |(u+1)*t-(2-t)*z|≤2*ε := by
    have eh : (u+1)*t-(2-t)*z = ((u+1)*t/(2-t)-z)*(2-t) := by field_simp
    rw [eh,abs_mul,abs_of_pos den]
    exact (mul_le_mul_of_nonneg_right ha den.le).trans (by nlinarith [mul_nonneg hε ht.1])
  let h : ℤ := j-i-z
  have diff : digit t u true j-digit t u false i =
      1+(2-t)*(h:ℝ)-((u+1)*t-(2-t)*z) := by dsimp [digit,h]; push_cast; ring
  rw [diff,le_abs]
  by_cases hh : 0≤h
  · left
    have h' : (0:ℝ)≤h := by exact_mod_cast hh
    linarith [mul_nonneg den.le h',(abs_le.mp err).2,ht.1]
  · right
    have h' : (h:ℝ)≤-1 := by exact_mod_cast (show h≤ -1 by omega)
    linarith [mul_le_mul_of_nonneg_left h' den.le,(abs_le.mp err).1]

private theorem plain_outer_loss {t u ε : ℝ} (hu : 4≤u) (ht : t∈Icc 0 (1/4))
    (hε : ε∈Icc 0 (1/8)) (z : ℤ) (ha : |(u+1)*t/(2-t)-z|≤ε) :
    1-volume.real ((shufflePattern u hu).sectionAt t) ≤ 8*(t+ε+1/u) := by
  let n := ⌊u⌋₊-1
  have hfl : 1≤⌊u⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hn : n<⌊u⌋₊ := by dsimp [n]; omega
  have nlow : u-2≤(n:ℝ) := by
    dsimp [n]; rw [Nat.cast_sub hfl]; push_cast; linarith [Nat.lt_floor_add_one u]
  let l := 1-t-2*ε
  have hl : l∈Icc 0 1 := ⟨by dsimp [l]; linarith [ht.2,hε.2],by dsimp [l]; linarith [ht.1,hε.1]⟩
  have sep (p q : Bool × Fin n) (h : p≠q) :
      l ≤ |digit t u p.1 p.2.val-digit t u q.1 q.2.val| := by
    obtain ⟨b,i⟩ := p; obtain ⟨c,j⟩ := q
    cases b <;> cases c
    · exact hl.2.trans (same_digit (by linarith [ht.2]) false (fun e => h (Prod.ext rfl (Fin.ext e))))
    · rw [abs_sub_comm]; exact digit_resonance ht hε.1 z ha _ _
    · exact digit_resonance ht hε.1 z ha _ _
    · exact hl.2.trans (same_digit (by linarith [ht.2]) true (fun e => h (Prod.ext rfl (Fin.ext e))))
  have h := keep hu ⟨ht.1,by linarith [ht.2]⟩ hn hl sep
  have hu0 : 0<u := by linarith
  have hkeep := (div_le_iff₀ hu0).mp h
  have hm := mul_le_mul_of_nonneg_right nlow hl.1
  apply (le_of_mul_le_mul_right _ hu0)
  dsimp [l] at hm hkeep
  rw [mul_assoc (8:ℝ),add_mul,one_div,inv_mul_cancel₀ hu0.ne']
  nlinarith [mul_nonneg ht.1 hu0.le,mul_nonneg hε.1 hu0.le,ht.1,hε.1]

/-- Near the top, omit the outermost blue and red indices. The remaining
blue intervals end before the first red one. No phase condition is needed. -/
private theorem transposed_outer_loss {t u : ℝ} (hu : 4≤u) (ht : t∈Icc 0 (1/4)) :
    1-volume.real ((shufflePattern u hu).sectionAt (1-t)) ≤ 2*t+2/u := by
  let q := (1-2*t)*u
  have up : 0<u := by linarith
  have qlow : 1≤q := by dsimp [q]; nlinarith [mul_nonneg (by linarith [ht.2] : 0≤1/4-t) up.le]
  have qu : q≤u := by dsimp [q]; nlinarith [mul_nonneg ht.1 up.le]
  let n := ⌊q⌋₊-1
  have hfl : 1≤⌊q⌋₊ := Nat.floor_pos.mpr qlow
  have hn : n<⌊u⌋₊ := lt_of_lt_of_le (by dsimp [n]; omega) (Nat.floor_mono qu)
  have nlow : q-2≤(n:ℝ) := by
    dsimp [n]; rw [Nat.cast_sub hfl]; push_cast; linarith [Nat.lt_floor_add_one q]
  have nup : (n:ℝ)≤q := by
    dsimp [n]; rw [Nat.cast_sub hfl]; push_cast; linarith [Nat.floor_le (by linarith : 0≤q)]
  have br (i j : Fin n) : 1≤digit (1-t) u false i.val-digit (1-t) u true j.val := by
    have ji : (j.val:ℝ)+1 ≤ n := by exact_mod_cast j.isLt
    have hi := mul_nonneg (by linarith [ht.1] : 0≤1+t) (Nat.cast_nonneg i.val)
    have hj := mul_le_mul_of_nonneg_left (ji.trans nup) (by linarith [ht.1] : 0≤1+t)
    dsimp [digit,q] at hj ⊢
    nlinarith only [hi,hj,mul_nonneg (sq_nonneg t) up.le]
  have sep (p q : Bool × Fin n) (h : p≠q) :
      1 ≤ |digit (1-t) u p.1 p.2.val-digit (1-t) u q.1 q.2.val| := by
    obtain ⟨b,i⟩ := p; obtain ⟨c,j⟩ := q
    cases b <;> cases c
    · exact same_digit (by linarith [ht.1]) false (fun e => h (Prod.ext rfl (Fin.ext e)))
    · exact le_abs.mpr (Or.inl (br i j))
    · rw [abs_sub_comm]; exact le_abs.mpr (Or.inl (br j i))
    · exact same_digit (by linarith [ht.1]) true (fun e => h (Prod.ext rfl (Fin.ext e)))
  have h := keep hu (show 1-t∈Icc 0 1 from ⟨by linarith [ht.2],by linarith [ht.1]⟩) hn
    (show (1:ℝ)∈Icc 0 1 by norm_num) sep
  rw [mul_one,div_le_iff₀ up] at h
  apply (le_of_mul_le_mul_right _ up)
  rw [add_mul,div_mul_cancel₀ _ up.ne']
  dsimp [q] at nlow
  nlinarith

/-- At a small height both orientations cost at most the number of endpoints
times their maximum displacement, uniformly in the inner pattern. -/
theorem insertion_loss_small {ι : Type*} [Fintype ι] (P : Pattern ι)
    (u : ℝ) (hu : 4≤u) (rev : Bool) {t : ℝ} (ht : t∈Icc 0 (1/4)) :
    volume.real (P.sectionAt t)-volume.real (((orientedPattern u hu rev).insert P).sectionAt t) ≤ 4*u*t := by
  let A := orientedPattern u hu rev
  have ht1 : t∈Icc 0 1 := ⟨ht.1,by linarith [ht.2]⟩
  apply (CompactPlane.insertion_loss_le_outer A P ht1).trans
  have zero : A.sectionAt 0 = Icc 0 1 := by
    simpa [Pattern.sectionAt,projection] using CompactPlane.fst_carrier A
  have h := AngularBlock.length_shift A (show (0:ℝ)∈Icc 0 1 by norm_num) ht1
  simp only [AngularBlock.len,zero,Real.volume_real_Icc_of_le zero_le_one,sub_zero,zero_sub,abs_neg,
    abs_of_nonneg ht.1,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat] at h
  nlinarith [mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith : 0≤u)) ht.1]

/-- At a common resonant height, either orientation loses at most order
t + ε + 1/u, for every inner pattern and every real parameter u. -/
theorem insertion_loss_aligned {ι : Type*} [Fintype ι] (P : Pattern ι)
    (u : ℝ) (hu : 4≤u) (rev : Bool) {t : ℝ} (ht : t∈Icc 0 (1/4))
    {ε : ℝ} (hε : ε∈Icc 0 (1/8)) (z : ℤ) (ha : |(u+1)*t/(2-t)-z|≤ε) :
    volume.real (P.sectionAt t)-volume.real (((orientedPattern u hu rev).insert P).sectionAt t) ≤
      8*(t+ε+1/u) := by
  have ht1 : t∈Icc 0 1 := ⟨ht.1,by linarith [ht.2]⟩
  apply (CompactPlane.insertion_loss_le_outer _ P ht1).trans
  cases rev
  · exact plain_outer_loss hu ht hε z ha
  · change 1-volume.real ((shufflePattern u hu).transpose.sectionAt t) ≤ _
    rw [Pattern.sectionAt_transpose _ ht1]
    have h := transposed_outer_loss hu ht
    rw [show 2/u=2*(1/u) by ring] at h
    linarith [ht.1,hε.1,show 0≤1/u by positivity]

end
end PermutationStrips.Shuffle
