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

/-- A fixed list of exactly forty times k cubed genuine paths controls every height,
including at discontinuities of the weight. -/
theorem exists_cubic_ensemble {w : ℝ → ℝ} (hm : Measurable w)
    (hw : ∀ r ∈ Ioc (0:ℝ) (1/2), w r ∈ Icc 0 1)
    (hmono : MonotoneOn w (Ioc (0:ℝ) (1/2)))
    (hi : IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2)))
    (hI : (∫ r in Ioc (0:ℝ) (1/2), w r/r) ≤ 3)
    (k : ℕ) (hk : 0 < k) :
    ∃ p : Fin (40*k^3) → Path,
      (∀ i, (Fintype.card (p i).Index : ℝ) ≤ Real.exp (8*k)) ∧
      ∀ t ∈ Ioo (0:ℝ) 1, w (radius t) * ((∑ i, len (p i).pattern t)/(40*(k:ℝ)^3)) ≤ 130/k := by
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
  let M := 40*k^3
  have hM : 0<M := by dsimp [M]; positivity
  have hMp : (0:ℝ)<M := by exact_mod_cast hM
  have hM_eq : (M:ℝ) = 40*(k:ℝ)^3 := by simp [M]
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
  have hsize : 4*(k:ℝ)^2*Real.log (Fintype.card J) ≤ M := by
    rw [hM_eq]
    exact (mul_le_mul_of_nonneg_left hlog (by positivity : 0≤4*(k:ℝ)^2)).trans_eq (by ring)
  obtain ⟨p,hcard,hmean⟩ := paths_on_mesh_of_log k M hk hM hsize t (meshHeight_mem hn) c U hU hc
  have hp (i) : (Fintype.card (p i).Index : ℝ) ≤ B := (hcard i).trans (schedule_budget hm hw hi hI)
  refine ⟨p,hp,?_⟩
  intro x hx
  rw [←hM_eq]
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
  have hmean' := hmean j
  change (∑ i, len (p i).pattern (t j))/(M:ℝ) ≤ envelope k (c j)+1/k at hmean'
  have hmeanx : (∑ i, len (p i).pattern x)/(M:ℝ) ≤ envelope k (c j)+2/k := by
    rw [div_le_iff₀ hMp] at hmean' ⊢
    change _ ≤ _ + (M:ℝ)*(1/k) at hsum
    exact hsum.trans ((add_le_add_right hmean' _).trans_eq (by ring))
  have hwbound := envelope_weight hk hwj
  change w (r j)*envelope k (c j) ≤ 128/(k:ℝ) at hwbound
  have hnon : 0 ≤ (∑ i, len (p i).pattern x)/(M:ℝ) := div_nonneg
    (Finset.sum_nonneg fun _ _ => measureReal_nonneg) hMp.le
  calc
    _ ≤ w (r j)*((∑ i, len (p i).pattern x)/(M:ℝ)) := mul_le_mul_of_nonneg_right hweight hnon
    _ ≤ w (r j)*(envelope k (c j)+2/k) := mul_le_mul_of_nonneg_left hmeanx hwj.1
    _ ≤ _ := by
      rw [mul_add]
      have hlast := mul_le_of_le_one_left (by positivity : (0:ℝ)≤2/k) hwj.2
      exact (add_le_add hwbound hlast).trans_eq (by ring)

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
