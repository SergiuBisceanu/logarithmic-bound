import PermutationStrips.AngularBlock

/-! For one common ensemble the exceptional heights have an exponential tail.
The threshold is chosen after the paths, and the profile may have jumps. -/

open Set MeasureTheory
open scoped BigOperators
namespace PermutationStrips.AngularBlock
noncomputable section

/-- A finite family of positive exponential tests gives a sharp counting bound
on the number of tests above a threshold. -/
private theorem tail_card {J : Type*} [Fintype J] (z : J → ℝ) (M : ℕ)
    (hs : (∑ j, Real.exp (z j)) ≤ (Fintype.card J:ℝ)*2^M) (a : ℝ) :
    let d := Finset.univ.filter (fun j => (M:ℝ)*(Real.log 2+a)<z j)
    (d.card:ℝ) ≤ (Fintype.card J:ℝ)*Real.exp (-(M:ℝ)*a) := by
  classical
  let d := Finset.univ.filter (fun j => (M:ℝ)*(Real.log 2+a)<z j)
  let T := Real.exp ((M:ℝ)*(Real.log 2+a))
  have bound : (d.card:ℝ)*T ≤ (Fintype.card J:ℝ)*2^M := calc
    _ = ∑ _j ∈ d, T := by simp
    _ ≤ ∑ j ∈ d, Real.exp (z j) := Finset.sum_le_sum fun j hj =>
      Real.exp_le_exp.mpr (Finset.mem_filter.mp hj).2.le
    _ ≤ ∑ j, Real.exp (z j) := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun j _ _ => (Real.exp_pos _).le)
    _ ≤ _ := hs
  have eq : Real.exp (-(M:ℝ)*a)*T = (2:ℝ)^M := by
    dsimp only [T]
    rw [← Real.exp_add,show -(M:ℝ)*a+M*(Real.log 2+a)=(M:ℝ)*Real.log 2 by ring,
      Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  apply (le_of_mul_le_mul_right _ (Real.exp_pos ((M:ℝ)*(Real.log 2+a))))
  change (d.card:ℝ)*T ≤ ((Fintype.card J:ℝ)*_)*T
  rwa [mul_assoc,eq]

/-- At depth k, M actual paths of size at most exp(8k) attain the 1/k
weighted profile outside a set of Lebesgue measure exponentially small in M. -/
theorem profile_exceptional {w : ℝ → ℝ} (hm : Measurable w)
    (hw : ∀ r ∈ Ioc (0:ℝ) (1/2), w r ∈ Icc 0 1)
    (hmono : MonotoneOn w (Ioc (0:ℝ) (1/2)))
    (hi : IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2)))
    (hI : (∫ r in Ioc (0:ℝ) (1/2), w r/r) ≤ 3) (k M : ℕ) (hk : 0<k) (hM : 0<M) :
    ∃ p : Fin M → Path, (∀ i, (p i).depth=k ∧ (Fintype.card (p i).Index:ℝ) ≤ Real.exp (8*k)) ∧
      ∀ a : ℝ, volume.real {x ∈ Ioo (0:ℝ) 1 | (256*(Real.log 2+a)+1)/k <
        w (radius x)*((∑ i, len (p i).pattern x)/(M:ℝ))} ≤ 2*Real.exp (-(M:ℝ)*a) := by
  classical
  have kp : (0:ℝ)<k := by exact_mod_cast hk
  have mp : (0:ℝ)<M := by exact_mod_cast hM
  let B := Real.exp (8*(k:ℝ))
  let n := ⌈(k:ℝ)*B⌉₊
  have hn : 0<n := Nat.ceil_pos.mpr (mul_pos kp (Real.exp_pos _))
  have np : (0:ℝ)<n := by exact_mod_cast hn
  let J := Bool × Fin n
  let t := meshHeight n
  let z (j : J) := w (radius (t j))
  let c (j : J) := ⌊(k:ℝ)*z j⌋₊
  let U i := 16*Real.exp (Schedule.cost k i w)
  have hr (j : J) : radius (t j) ∈ Ioc 0 (1/2) := by
    rw [show t j = meshHeight n j from rfl,radius_meshHeight hn]; exact meshRad_mem hn _
  have hc (j : J) : c j≤k := by
    exact_mod_cast (Nat.floor_le (mul_nonneg kp.le (hw _ (hr j)).1)).trans
      (mul_le_of_le_one_right kp.le (hw _ (hr j)).2)
  let X := {p : Path // p.depth=k ∧ (Fintype.card p.Index:ℝ) ≤ B}
  let v (p : X) (j : J) := ((k:ℝ)*z j)*len p.val.pattern (t j)/256
  have test (a : J → ℝ) (ha : ∀ j, 0≤a j) : ∃ p, ∑ j, a j*Real.exp (v p j) ≤ 2*∑ j, a j := by
    obtain ⟨p,hd,hp,he⟩ := exists_moment_path t (meshHeight_mem hn) c U
      (fun _ => scheduled_scale_ge w) (fun i j => scheduled_scale_active hm hw hmono hi (hr j)) k a ha
    refine ⟨⟨p,hd,hp.trans (schedule_budget hm hw hi hI)⟩,?_⟩
    have le (j) : Real.exp (v ⟨p,hd,hp.trans (schedule_budget hm hw hi hI)⟩ j) ≤
        moment (1+min k (c j)) (len p.pattern (t j)) := by
      rw [moment,min_eq_right (hc j),Nat.cast_add,Nat.cast_one]
      apply Real.exp_le_exp.mpr
      unfold v; dsimp only
      gcongr; linarith [Nat.lt_floor_add_one ((k:ℝ)*z j)]
    have h := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => mul_le_mul_of_nonneg_left (le j) (ha j))
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul] at he
    linarith only [h,he]
  obtain ⟨s,hs⟩ := exists_moment_potential v test M
  refine ⟨fun i => (s i).val,fun i => (s i).property,fun a => ?_⟩
  let score (j : J) := ∑ i, v (s i) j
  let d := Finset.univ.filter (fun j => (M:ℝ)*(Real.log 2+a)<score j)
  let cell (j : J) := Icc (t j-1/(2*n:ℝ)) (t j+1/(2*n:ℝ))
  have hcell (j) : volume.real (cell j) = 1/(n:ℝ) := by
    dsimp only [cell]; rw [Real.volume_real_Icc_of_le (by linarith [show 0≤1/(2*(n:ℝ)) by positivity])]; ring
  have cover : {x ∈ Ioo (0:ℝ) 1 | (256*(Real.log 2+a)+1)/k <
      w (radius x)*((∑ i, len (s i).val.pattern x)/(M:ℝ))} ⊆ ⋃ j ∈ d, cell j := by
    rintro x ⟨hx,bad⟩
    obtain ⟨j,hjr,hjt⟩ := mesh_round hn hx
    have diff (i : Fin M) : len (s i).val.pattern x ≤ len (s i).val.pattern (t j)+1/(k:ℝ) := by
      apply (length_shift _ ⟨hx.1.le,hx.2.le⟩ (meshHeight_mem hn j)).trans
      apply add_le_add_left
      calc
        _ ≤ 2*B*(1/(2*(n:ℝ))) := by gcongr; exact (s i).property.2
        _ = B/n := by ring
        _ ≤ 1/(k:ℝ) := (div_le_div_iff₀ np kp).mpr (by linarith [show (k:ℝ)*B≤n from Nat.le_ceil _])
    have step (i : Fin M) : w (radius x)*len (s i).val.pattern x ≤
        z j*len (s i).val.pattern (t j)+1/(k:ℝ) := calc
      _ ≤ z j*len (s i).val.pattern x := mul_le_mul_of_nonneg_right
        (hmono (radius_mem_of_interior hx) (hr j) hjr) measureReal_nonneg
      _ ≤ z j*(len (s i).val.pattern (t j)+1/(k:ℝ)) := mul_le_mul_of_nonneg_left (diff i) (hw _ (hr j)).1
      _ ≤ _ := by rw [mul_add]; gcongr; exact mul_le_of_le_one_left (by positivity) (hw _ (hr j)).2
    have sum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => step i)
    simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul] at sum
    have mem : j ∈ d := by
      apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      simp only [score,v,← Finset.sum_div,← Finset.mul_sum]
      rw [mul_div_assoc',lt_div_iff₀ mp,div_mul_eq_mul_div,div_lt_iff₀ kp] at bad
      rw [lt_div_iff₀ (by norm_num : (0:ℝ)<256)]
      have h := mul_le_mul_of_nonneg_right sum kp.le
      rw [add_mul,mul_assoc (M:ℝ),one_div,inv_mul_cancel₀ kp.ne',mul_one] at h
      nlinarith only [h,bad]
    exact mem_iUnion₂.mpr ⟨j,mem,by have h := abs_le.mp hjt; exact ⟨by linarith [h.1],by linarith [h.2]⟩⟩
  calc
    _ ≤ volume.real (⋃ j ∈ d, cell j) := measureReal_mono cover (by
      apply ne_of_lt; exact (d.finite_toSet.isCompact_biUnion (fun j _ => isCompact_Icc)).measure_lt_top)
    _ ≤ ∑ j ∈ d, volume.real (cell j) := measureReal_biUnion_finset_le _ _
    _ = (d.card:ℝ)/(n:ℝ) := by simp [hcell,div_eq_mul_inv]
    _ ≤ _ := by
      apply (div_le_iff₀ np).mpr
      have h := tail_card score M hs a
      change (d.card:ℝ) ≤ _ at h
      simpa [J,mul_assoc,mul_comm,mul_left_comm] using h

end
end PermutationStrips.AngularBlock
