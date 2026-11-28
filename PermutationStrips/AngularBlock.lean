import PermutationStrips.AngularBlockMesh
import PermutationStrips.Schedule
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The finite simultaneous weighted block. The choice of the shell at every stage
uses the same deterministic scale schedule, for arbitrary monotone measurable weights. -/

open Set MeasureTheory
open scoped BigOperators

namespace PermutationStrips.AngularBlock
noncomputable section

private theorem envelope_weight {k : ℕ} (hk : 0<k) {z : ℝ} (hz : z ∈ Icc 0 1) :
    z*envelope k ⌊(k:ℝ)*z⌋₊ ≤ 128/(k:ℝ) := by
  have hn : 0≤ (k:ℝ)*z := mul_nonneg (Nat.cast_nonneg _) hz.1
  have hle : ⌊(k:ℝ)*z⌋₊ ≤ k := by
    exact_mod_cast (Nat.floor_le hn).trans (mul_le_of_le_one_right (Nat.cast_nonneg _) hz.2)
  have hfloor := Nat.lt_floor_add_one ((k:ℝ)*z)
  unfold envelope
  rw [min_eq_right hle]
  have hp : (0:ℝ)<k := by exact_mod_cast hk
  apply (le_div_iff₀ hp).mpr
  rw [mul_right_comm,mul_div_assoc',div_le_iff₀ (by positivity)]
  nlinarith

private theorem schedule_budget {k : ℕ} {w : ℝ → ℝ} (hm : Measurable w)
    (hw : ∀ r ∈ Ioc (0:ℝ) (1/2), w r ∈ Icc 0 1)
    (hi : IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2)))
    (hI : (∫ r in Ioc (0:ℝ) (1/2), w r/r) ≤ 3) :
    (∏ i ∈ Finset.range k, 4*(16*Real.exp (Schedule.cost k i w))) ≤ Real.exp (8*k) := by
  have he (i) : (4:ℝ)*(16*Real.exp (Schedule.cost k i w)) =
      Real.exp (Real.log 64 + Schedule.cost k i w) := by
    rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<64)]; ring
  simp_rw [he]
  rw [← Real.exp_sum,Real.exp_le_exp,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hcost := Schedule.total_cost (k:=k) hm hw hi
  have hlog : Real.log 64 ≤ 5 := by
    rw [show (64:ℝ)=(2:ℝ)^6 by norm_num,Real.log_pow]
    norm_num; linarith [Real.log_two_lt_d9]
  nlinarith [mul_le_mul_of_nonneg_left hI (Nat.cast_nonneg k),
    mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)]

/-- Weighted paths at all heights for an arbitrary sample size and exponential rate.
Rounding a mesh height toward one half costs at most one additional unit of 1/k. -/
theorem exists_weighted_ensemble {w : ℝ → ℝ} (hm : Measurable w)
    (hw : ∀ r ∈ Ioc (0:ℝ) (1/2), w r ∈ Icc 0 1)
    (hmono : MonotoneOn w (Ioc (0:ℝ) (1/2)))
    (hi : IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2)))
    (hI : (∫ r in Ioc (0:ℝ) (1/2), w r/r) ≤ 3)
    (k M : ℕ) (hk : 0<k) (hM : 0<M) {η : ℝ} (hη : 0<η) (hη1 : η≤1) :
    ∃ p : Fin M → Path, (∀ i, (p i).depth=k ∧ (Fintype.card (p i).Index : ℝ) ≤ Real.exp (8*k)) ∧
      ∀ t ∈ Ioo (0:ℝ) 1, w (radius t)*((∑ i, len (p i).pattern t)/(M:ℝ)) ≤
        (1+128*(1+η))/k + 10*k/(η*M) := by
  classical
  have hkp : (0:ℝ)<k := by exact_mod_cast hk
  let B := Real.exp (8*k)
  have hB : 1≤B := Real.one_le_exp (by positivity)
  let n := ⌈(k:ℝ)*B⌉₊
  have hn : 0<n := Nat.ceil_pos.mpr (mul_pos hkp (by linarith))
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let J := Bool × Fin n
  let t := meshHeight n
  let r := fun j : J => radius (t j)
  let c := fun j => ⌊(k:ℝ)*w (r j)⌋₊
  have hr (j : J) : r j ∈ Ioc 0 (1/2) := by
    change radius (meshHeight n j) ∈ _
    rw [radius_meshHeight hn]
    exact meshRad_mem hn _
  let U := fun i => 16*Real.exp (Schedule.cost k i w)
  have hU (i) : 16≤U i := by
    have hp : 0≤Schedule.cost k i w := by
      apply setIntegral_nonneg measurableSet_Ioc
      intro x hx
      unfold Schedule.density
      split_ifs <;> simp [hx.1.le]
    have := Real.one_le_exp hp
    dsimp [U]; linarith
  have hc (i j) (h : i<c j) : 8 ≤ U i*radius (t j) := by
    apply Schedule.active_scale hm (fun x hx => (hw x hx).1) hmono hi (hr j)
    rw [Schedule.active_eq (hw _ (hr j))]
    exact Finset.mem_range.mpr h
  have hMp : (0:ℝ)<M := by exact_mod_cast hM
  have hkn : (k:ℝ)*B ≤ n := Nat.le_ceil _
  have hnup : (n:ℝ) ≤ (k:ℝ)*B+1 := (Nat.ceil_lt_add_one (mul_nonneg hkp.le (by linarith : 0≤B))).le
  have hk1 : 1≤(k:ℝ) := by exact_mod_cast hk
  have h1 : 1≤(k:ℝ)*B := by simpa using mul_le_mul hk1 hB zero_le_one hkp.le
  have hlog : Real.log (Fintype.card J) ≤ 10*k := by
    apply (Real.log_le_iff_le_exp (by exact_mod_cast Fintype.card_pos (α:=J))).mpr
    have hfour : 4*(k:ℝ) ≤ Real.exp (2*k) := by
      calc
        _ ≤ (1+(k:ℝ))^2 := by nlinarith [sq_nonneg ((k:ℝ)-1)]
        _ ≤ (Real.exp k)^2 := pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (k:ℝ)]) 2
        _ = _ := by rw [sq,←Real.exp_add]; congr 1; ring
    calc
      (Fintype.card J:ℝ) = 2*(n:ℝ) := by simp [J]
      _ ≤ 4*(k:ℝ)*B := by linarith
      _ ≤ Real.exp (2*k)*B := mul_le_mul_of_nonneg_right hfour (by linarith)
      _ = _ := by dsimp [B]; rw [←Real.exp_add]; congr 1; ring
  obtain ⟨p,hcard,hmean⟩ := weighted_paths_on_mesh k M hM t (fun j => w (r j))
    (meshHeight_mem hn) (fun j => hw _ (hr j)) c U hU hc (μ:=128/k) (by positivity)
    (fun j => envelope_weight hk (hw _ (hr j))) hη hη1
  have hp (i) : (Fintype.card (p i).Index : ℝ) ≤ B := (hcard i).2.trans (schedule_budget hm hw hi hI)
  refine ⟨p,fun i => ⟨(hcard i).1,hp i⟩,?_⟩
  intro x hx
  obtain ⟨j,hjr,hjt⟩ := mesh_round hn hx
  have hx01 : x ∈ Icc 0 1 := ⟨hx.1.le,hx.2.le⟩
  have hjs := meshHeight_mem hn j
  have hxrad : radius x ∈ Ioc 0 (1/2) := ⟨lt_min hx.1 (sub_pos.mpr hx.2),hjr.trans (hr j).2⟩
  have hweight := hmono hxrad (hr j) hjr
  have hwj := hw _ (hr j)
  have hB1 : B/n ≤ 1/(k:ℝ) := (div_le_div_iff₀ (by exact_mod_cast hn : (0:ℝ)<n) hkp).mpr
    (by linarith)
  have hf (i) : len (p i).pattern x ≤ len (p i).pattern (t j) + 1/(k:ℝ) := by
    have h := length_shift (p i).pattern hx01 hjs
    apply h.trans (add_le_add_left _ _)
    calc
      _ ≤ 2*B*(1/(2*(n:ℝ))) := by gcongr; exact hp i
      _ = B/n := by ring
      _ ≤ _ := hB1
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hf i)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  let H := fun s => (∑ i, len (p i).pattern s)/(M:ℝ)
  have hshift : H x ≤ H (t j)+1/k := by
    dsimp only [H]; rw [div_le_iff₀ hMp]
    exact hsum.trans_eq (by field_simp)
  have hnon : 0≤H x := div_nonneg (Finset.sum_nonneg fun _ _ => measureReal_nonneg) hMp.le
  have htail := div_le_div_of_nonneg_right hlog (mul_nonneg hη.le hMp.le)
  calc
    _ ≤ w (r j)*H x := mul_le_mul_of_nonneg_right hweight hnon
    _ ≤ w (r j)*(H (t j)+1/k) := mul_le_mul_of_nonneg_left hshift hwj.1
    _ ≤ ((1+η)*(128/k)+Real.log (Fintype.card J)/(η*M))+1/k := by
      rw [mul_add]
      exact add_le_add (hmean j) (mul_le_of_le_one_left (by positivity) hwj.2)
    _ ≤ ((1+η)*(128/k)+10*k/(η*M))+1/k := by linarith
    _ = _ := by ring

/-- Exactly k squared paths control the weighted lengths at all heights. -/
theorem exists_quadratic_ensemble {w : ℝ → ℝ} (hm : Measurable w)
    (hw : ∀ r ∈ Ioc (0:ℝ) (1/2), w r ∈ Icc 0 1)
    (hmono : MonotoneOn w (Ioc (0:ℝ) (1/2)))
    (hi : IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2)))
    (hI : (∫ r in Ioc (0:ℝ) (1/2), w r/r) ≤ 3)
    (k : ℕ) (hk : 0<k) :
    ∃ p : Fin (k^2) → Path, (∀ i, (p i).depth=k ∧ (Fintype.card (p i).Index : ℝ) ≤ Real.exp (8*k)) ∧
      ∀ t ∈ Ioo (0:ℝ) 1, w (radius t)*((∑ i, len (p i).pattern t)/(k:ℝ)^2) ≤ 201/k := by
  have hkp : (0:ℝ)<k := by exact_mod_cast hk
  obtain ⟨p,hp,h⟩ := exists_weighted_ensemble hm hw hmono hi hI k (k^2) hk (by positivity)
    (η:=1/4) (by norm_num) (by norm_num)
  refine ⟨p,hp,fun t ht => ?_⟩
  simpa only [Nat.cast_pow] using (h t ht).trans_eq
    (show _=201/(k:ℝ) by push_cast; field_simp; ring)

/-- A larger quadratic sample recovers the 130/k all-height bound. -/
theorem exists_quadratic_ensemble_130 {w : ℝ → ℝ} (hm : Measurable w)
    (hw : ∀ r ∈ Ioc (0:ℝ) (1/2), w r ∈ Icc 0 1)
    (hmono : MonotoneOn w (Ioc (0:ℝ) (1/2)))
    (hi : IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2)))
    (hI : (∫ r in Ioc (0:ℝ) (1/2), w r/r) ≤ 3)
    (k : ℕ) (hk : 0<k) :
    ∃ p : Fin (5120*k^2) → Path, (∀ i, (p i).depth=k ∧ (Fintype.card (p i).Index : ℝ) ≤ Real.exp (8*k)) ∧
      ∀ t ∈ Ioo (0:ℝ) 1, w (radius t)*((∑ i, len (p i).pattern t)/(5120*(k:ℝ)^2)) ≤ 130/k := by
  have hkp : (0:ℝ)<k := by exact_mod_cast hk
  obtain ⟨p,hp,h⟩ := exists_weighted_ensemble hm hw hmono hi hI k (5120*k^2) hk (by positivity)
    (η:=1/256) (by norm_num) (by norm_num)
  refine ⟨p,hp,fun t ht => ?_⟩
  simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using (h t ht).trans_eq
    (show _=130/(k:ℝ) by push_cast; field_simp; ring)

/-- The original cubic list and the 130/k estimate are also available. -/
theorem exists_cubic_ensemble {w : ℝ → ℝ} (hm : Measurable w)
    (hw : ∀ r ∈ Ioc (0:ℝ) (1/2), w r ∈ Icc 0 1)
    (hmono : MonotoneOn w (Ioc (0:ℝ) (1/2)))
    (hi : IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2)))
    (hI : (∫ r in Ioc (0:ℝ) (1/2), w r/r) ≤ 3)
    (k : ℕ) (hk : 0 < k) :
    ∃ p : Fin (40*k^3) → Path,
      (∀ i, (Fintype.card (p i).Index : ℝ) ≤ Real.exp (8*k)) ∧
      ∀ t ∈ Ioo (0:ℝ) 1, w (radius t) * ((∑ i, len (p i).pattern t)/(40*(k:ℝ)^3)) ≤ 130/k := by
  have hkp : (0:ℝ)<k := by exact_mod_cast hk
  obtain ⟨p,hp,h⟩ := exists_weighted_ensemble hm hw hmono hi hI k (40*k^3) hk (by positivity)
    (η:=1/256) (by norm_num) (by norm_num)
  refine ⟨p,fun i => (hp i).2,fun t ht => ?_⟩
  by_cases hs : k≤130
  · have hr : radius t ∈ Ioc 0 (1/2) := by
      refine ⟨lt_min ht.1 (sub_pos.mpr ht.2),?_⟩
      unfold radius; rcases le_total t (1-t) with h|h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; linarith
    have hnorm : (∑ i, len (p i).pattern t)/(40*(k:ℝ)^3) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      exact (Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
        (p i).pattern.section_length_le_one ⟨ht.1.le,ht.2.le⟩)).trans_eq (by simp)
    apply (mul_le_of_le_one_left (by positivity : 0≤(∑ i, len (p i).pattern t)/(40*(k:ℝ)^3))
      (hw _ hr).2).trans (hnorm.trans ?_)
    exact (le_div_iff₀ hkp).mpr (by simpa using (show (k:ℝ)≤130 by exact_mod_cast hs))
  · have h128 : (128:ℝ) ≤ k := by exact_mod_cast (show 128≤k by omega)
    have hbound : 10*(k:ℝ)/((1/256)*(40*k^3)) ≤ 1/(2*k) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg (sq_nonneg (k:ℝ)) (sub_nonneg.mpr h128)]
    have he := h t ht
    push_cast at he
    exact he.trans ((add_le_add_left hbound _).trans_eq (by field_simp; ring))

/-- The cubic sample count contributes at most 7k to the logarithmic budget. -/
theorem cubic_size_le_exp (k : ℕ) (hk : 0 < k) : 40*(k:ℝ)^3 ≤ Real.exp (7*k) := by
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have h : (13:ℝ)/5 ≤ Real.exp k := by
    apply le_trans _ (Real.exp_le_exp.mpr hk1)
    linarith [Real.exp_one_gt_d9]
  have hc : (40:ℝ) ≤ (Real.exp k)^4 :=
    (by norm_num : (40:ℝ) ≤ (13/5:ℝ)^4).trans (pow_le_pow_left₀ (by norm_num) h 4)
  have hk' : (k:ℝ) ≤ Real.exp k := by linarith [Real.add_one_le_exp (k:ℝ)]
  calc
    _ ≤ (Real.exp k)^4 * (Real.exp k)^3 :=
      mul_le_mul hc (pow_le_pow_left₀ (Nat.cast_nonneg _) hk' 3) (by positivity) (by positivity)
    _ = Real.exp (7*k) := by rw [←pow_add,←Real.exp_nat_mul]; norm_num

/-- The exponential budget formulation follows from the cubic ensemble. -/
theorem exists_ensemble {w : ℝ → ℝ} (hm : Measurable w)
    (hw : ∀ r ∈ Ioc (0:ℝ) (1/2), w r ∈ Icc 0 1)
    (hmono : MonotoneOn w (Ioc (0:ℝ) (1/2)))
    (hi : IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2)))
    (hI : (∫ r in Ioc (0:ℝ) (1/2), w r/r) ≤ 3)
    (k : ℕ) (hk : 0 < k) :
    ∃ M : ℕ, ∃ p : Fin M → Path, k ≤ M ∧ (M:ℝ) ≤ Real.exp (110*k) ∧
      (∀ i, (Fintype.card (p i).Index : ℝ) ≤ Real.exp (100*k)) ∧
      ∀ t ∈ Ioo (0:ℝ) 1, w (radius t) * ((∑ i, len (p i).pattern t)/M) ≤ 130/k := by
  obtain ⟨p,hp,hw'⟩ := exists_cubic_ensemble hm hw hmono hi hI k hk
  refine ⟨40*k^3,p,?_,?_,fun i => (hp i).trans (Real.exp_le_exp.mpr (by linarith)),?_⟩
  · nlinarith [Nat.one_le_iff_ne_zero.mpr hk.ne',Nat.pow_le_pow_right (n:=k) hk (by decide : 1≤3)]
  · push_cast; exact (cubic_size_le_exp k hk).trans (Real.exp_le_exp.mpr (by linarith))
  · simpa using hw'

end
end PermutationStrips.AngularBlock
