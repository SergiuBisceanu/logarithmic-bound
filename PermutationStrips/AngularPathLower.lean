import PermutationStrips.AngularResonantPath
import PermutationStrips.AngularPlateau
import PermutationStrips.ShuffleDirichlet

/-! A common near-axis height for a short list of genuine shuffle paths. -/

open Set MeasureTheory Filter
open scoped BigOperators
namespace PermutationStrips.AngularBlock
noncomputable section

/-- The number of large scale occurrences controls the logarithmic cost of
finding one resonance for every path. -/
private theorem resonant_height {k m M : ℕ} (p : Fin M → Path)
    (hk : 0 < k) (hm : 0 < m)
    (hcard : ∀ j, (Fintype.card (p j).Index:ℝ) ≤ Real.exp (8*(k:ℝ)))
    (hshort : 128*(m:ℝ)^2 * Real.log (4096*(m:ℝ))*M ≤ k)
    {B T : ℝ} (hB : B = Real.exp ((k:ℝ)/(4*m))) (hB2 : 2 ≤ B)
    (hT : 0 < T) (hTB : T*B^4=1) :
    ∃ t ∈ Ioo (0:ℝ) 1, T ≤ radius t ∧ t ≤ 1/B^2 ∧
      ∀ j, ∀ i ∈ (p j).largeSteps B, ∃ z : ℤ,
        |((p j).scaleAt i+1)*t/(2-t)-z| ≤ 1/(4096*(m:ℝ)) := by
  classical
  let J := LargeOccurrences p B
  let L := 4096*m
  have lp : 0 < L := Nat.mul_pos (by decide) hm
  have mp : 0 < (m:ℝ) := by exact_mod_cast hm
  have bp : 0 < B := by linarith
  have lc : (L:ℝ) = 4096*(m:ℝ) := by simp [L]
  have d : (Fintype.card J:ℝ) ≤ 32*m*M := by
    dsimp only [J]; rw [hB]
    exact largeOccurrences_card_le p (by exact_mod_cast hk) mp hcard
  have leLog : (Fintype.card J:ℝ)*Real.log L ≤ (k:ℝ)/(4*m) := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ (32*(m:ℝ)*M)*(Real.log L)*(4*m) := by
        gcongr
      _ = 128*(m:ℝ)^2 * Real.log (4096*(m:ℝ))*M := by rw [lc]; ring
      _ ≤ _ := hshort
  have powBound : (L:ℝ)^Fintype.card J ≤ B := by
    calc
      _ = Real.exp ((Fintype.card J:ℝ)*Real.log L) := by
        rw [Real.exp_nat_mul,Real.exp_log (by exact_mod_cast lp : (0:ℝ) < L)]
      _ ≤ _ := (Real.exp_le_exp.mpr leLog).trans_eq hB.symm
  obtain ⟨s,hs,hsmax,phase⟩ := Shuffle.exists_resonant_scale
    (fun j : J => (p j.1).scaleAt j.2.val) L lp hT.le
  have sp : 0 < s := hT.trans_le hs
  have sb : s*B^3 ≤ 1 := calc
    _ ≤ (B*T)*B^3 := mul_le_mul_of_nonneg_right
      (hsmax.trans (mul_le_mul_of_nonneg_right powBound hT.le)) (by positivity)
    _ = T*B^4 := by ring
    _ = 1 := hTB
  have s1 : s ≤ 1 := (le_mul_of_one_le_right sp.le (one_le_pow₀ (by linarith : 1 ≤ B))).trans sb
  let t := 2*s/(1+s)
  have tp : 0 < t := by dsimp [t]; positivity
  have st : s ≤ t := (le_div_iff₀ (by positivity : 0 < 1+s)).mpr
    (by nlinarith only [mul_le_mul_of_nonneg_left s1 sp.le])
  have t2s : t ≤ 2*s := div_le_self (by positivity) (by linarith)
  have tb : t ≤ 1/B^2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ (2*s)*B^2 := mul_le_mul_of_nonneg_right t2s (by positivity)
      _ ≤ s*B^3 := by nlinarith only [mul_le_mul_of_nonneg_left hB2 (by positivity : 0 ≤ s*B^2)]
      _ ≤ 1 := sb
  have tq : t ≤ 1/4 := tb.trans (one_div_le_one_div_of_le (by norm_num) (by nlinarith [sq_nonneg (B-2)]))
  refine ⟨t,⟨tp,by linarith⟩,?_,tb,?_⟩
  · rw [radius,min_eq_left (by linarith : t ≤ 1-t)]
    exact hs.trans st
  · intro j i hi
    obtain ⟨z,hz⟩ := phase ⟨j,⟨i,hi⟩⟩
    have inv : t/(2-t)=s := (div_eq_iff (by linarith)).mpr (by dsimp [t]; field_simp; ring)
    rw [mul_div_assoc,inv,←lc]
    exact ⟨z,hz⟩

/-- The monotone angular profiles in the finite block lemma. -/
def AdmissibleProfile (v : ℝ → ℝ) : Prop :=
  Measurable v ∧ (∀ r ∈ Ioc (0:ℝ) (1/2), v r ∈ Icc 0 1) ∧ MonotoneOn v (Ioc (0:ℝ) (1/2)) ∧
    IntegrableOn (fun r => v r/r) (Ioc (0:ℝ) (1/2)) ∧
    (∫ r in Ioc (0:ℝ) (1/2), v r/r) ≤ 1

/-- The depth and square-count budget of the angular upper bound. -/
def PathBudget {M : ℕ} (k : ℕ) (p : Fin M → Path) : Prop :=
  ∀ i, (p i).depth=k ∧ (Fintype.card (p i).Index:ℝ) ≤ Real.exp (8*(k:ℝ))

def weightedMean {M : ℕ} (v : ℝ → ℝ) (p : Fin M → Path) (t : ℝ) : ℝ :=
  max (v (radius t)) (Real.sqrt (radius t)) * ((∑ i, len (p i).pattern t)/(M:ℝ))

/-- At one common interior height, every path retains at least half its section,
and the admissible profile is on its plateau. The scales and orientations are free. -/
theorem common_plateau_height {m k M : ℕ} (hm : 0 < m) (hk : 32768*m^2 ≤ k)
    (p : Fin M → Path) (hp : PathBudget k p)
    (hshort : 128*(m:ℝ)^2 * Real.log (4096*(m:ℝ))*M ≤ k) :
    ∃ t ∈ Ioo (0:ℝ) 1, (m:ℝ)/k ≤ plateauWeight m k (radius t) ∧
      ∀ j, 1/2 ≤ len (p j).pattern t := by
  have kp : 0 < k := lt_of_lt_of_le (by positivity) hk
  have mp : 0 < (m:ℝ) := by exact_mod_cast hm
  have kb : (1:ℝ) ≤ k := by exact_mod_cast kp
  have hB := plateauBase_lower hm hk
  obtain ⟨t,ht,hT,htB,hphase⟩ := resonant_height p kp hm (fun j => (hp j).2) hshort
    (B:=plateauBase m k) rfl (by linarith) (T:=plateauCutoff m k) (Real.exp_pos _)
    (plateauCutoff_mul_base_pow m k)
  refine ⟨t,ht,plateauWeight_ge hT,fun j => ?_⟩
  exact (p j).length_at_resonance kp mp (hp j).1 (hp j).2 hB ht.1 htB (hphase j)

/-- For every fixed angular constant, a positive linear fraction of k paths is
necessary in the worst case over admissible profiles, before they are packed. -/
theorem exists_hard_profile (C : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop, ∃ v, AdmissibleProfile v ∧
      ∀ (M : ℕ), 0 < M → (M:ℝ) ≤ c*k → ∀ p : Fin M → Path, PathBudget k p →
        ∃ t ∈ Ioo (0:ℝ) 1, C/k < weightedMean v p t := by
  let m := ⌈2*max C 0⌉₊+1
  have hm : 0 < m := Nat.succ_pos _
  have mp : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hC : C < (m:ℝ)/2 := by
    dsimp [m]; push_cast; linarith [Nat.le_ceil (2*max C 0),le_max_left C 0]
  let D := 128*(m:ℝ)^2 * Real.log (4096*(m:ℝ))
  have logpos : 0 < Real.log (4096*(m:ℝ)) := Real.log_pos (by linarith)
  have dpos : 0 < D := by dsimp [D]; positivity
  refine ⟨D⁻¹,inv_pos.mpr dpos,?_⟩
  filter_upwards [eventually_ge_atTop (32768*m^2)] with k hk
  have hmk : m ≤ k := by nlinarith [Nat.one_le_iff_ne_zero.mpr hm.ne']
  have kp : 0 < (k:ℝ) := by exact_mod_cast hm.trans_le hmk
  refine ⟨plateauProfile m k,plateauProfile_properties hm hmk,?_⟩
  intro M hM hlim p hp
  have small : D*(M:ℝ) ≤ k := calc
    _ ≤ D*(D⁻¹*(k:ℝ)) := mul_le_mul_of_nonneg_left hlim dpos.le
    _ = _ := by field_simp
  obtain ⟨t,ht,hw,hl⟩ := common_plateau_height hm hk p hp small
  have Mp : 0 < (M:ℝ) := by exact_mod_cast hM
  have av : 1/2 ≤ (∑ i, len (p i).pattern t)/(M:ℝ) := by
    apply (le_div_iff₀ Mp).mpr
    exact (by simp [mul_comm] : (1/2:ℝ)*M = ∑ _i : Fin M, (1/2:ℝ)).le.trans
      (Finset.sum_le_sum (s:=Finset.univ) fun i _ => hl i)
  refine ⟨t,ht,?_⟩
  calc
    C/k < ((m:ℝ)/2)/k := (div_lt_div_iff_of_pos_right kp).mpr hC
    _ = ((m:ℝ)/k)*(1/2) := by ring
    _ ≤ weightedMean (plateauProfile m k) p t := mul_le_mul hw av (by norm_num) (by
      exact (div_nonneg (Nat.cast_nonneg _) kp.le).trans hw)

end
end PermutationStrips.AngularBlock
