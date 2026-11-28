import PermutationStrips.AngularBlockMomentPath
import PermutationStrips.AngularBlockGame
import PermutationStrips.GridTransfer

/-! A bounded common ensemble on a one-sided mesh of heights. The mesh rounds
towards height one half, so the weight may jump at any radius. -/

open Set MeasureTheory
open scoped BigOperators
namespace PermutationStrips.AngularBlock
noncomputable section

private abbrev BudgetPath (k : ℕ) (U : ℕ → ℝ) :=
  {p : Path // p.depth=k ∧ (Fintype.card p.Index : ℝ) ≤ ∏ i ∈ Finset.range k, 4*U i}

private def excess {k : ℕ} {U : ℕ → ℝ} {J : Type*}
    (t : J → ℝ) (cut : J → ℕ) (p : BudgetPath k U) (j : J) : ℝ :=
  len p.val.pattern (t j) - envelope k (cut j)

private theorem excess_bound {J : Type*} {k : ℕ} {U : ℕ → ℝ} (t : J → ℝ)
    (ht : ∀ j, t j ∈ Icc 0 1) (cut : J → ℕ) (p : BudgetPath k U) (j : J) :
    |excess t cut p j| ≤ 1 := by
  have henv : 0 ≤ envelope k (cut j) ∧ envelope k (cut j) ≤ 1 := by
    unfold envelope
    exact ⟨by positivity,(div_le_iff₀ (by positivity)).mpr (by simp)⟩
  have hlo : 0 ≤ len p.val.pattern (t j) := measureReal_nonneg
  have hhi := p.val.pattern.section_length_le_one (ht j)
  unfold excess
  exact abs_le.mpr ⟨by linarith [henv.2],by linarith [henv.1]⟩

private theorem excess_test {J : Type*} [Fintype J] (k : ℕ)
    (t : J → ℝ) (ht : ∀ j, t j ∈ Icc 0 1)
    (cut : J → ℕ) (U : ℕ → ℝ) (hU : ∀ i, 16 ≤ U i)
    (hc : ∀ i j, i < cut j → 8 ≤ U i * radius (t j)) (a : J → ℝ) (ha : ∀ j, 0 ≤ a j) :
    ∃ p : BudgetPath k U, ∑ j, a j*excess t cut p j ≤ 0 := by
  obtain ⟨p,hd,hp,hp'⟩ := exists_path_at_depth t ht cut U hU hc k a ha
  exact ⟨⟨p,hd,hp⟩,hp'⟩

private theorem mean_le {J : Type*} {k M : ℕ} {U : ℕ → ℝ} (t : J → ℝ)
    (cut : J → ℕ) (s : Fin M → BudgetPath k U) (hM : 0<M) (j : J)
    (h : ∑ i, excess t cut (s i) j ≤ (M:ℝ)/k) :
    (∑ i, len (s i).val.pattern (t j))/(M:ℝ) ≤ envelope k (cut j)+1/k := by
  simp only [excess,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at h
  apply (div_le_iff₀ (by exact_mod_cast hM : (0:ℝ)<M)).mpr
  calc
    _ ≤ (M:ℝ)/k + (M:ℝ)*envelope k (cut j) := by linarith
    _ = _ := by ring

/-- A common sample at arbitrary prescribed heights, from a second-moment estimate. -/
theorem paths_on_mesh {J : Type*} [Fintype J] [Nonempty J] (k : ℕ) (hk : 0 < k)
    (t : J → ℝ) (ht : ∀ j, t j ∈ Icc 0 1)
    (cut : J → ℕ) (U : ℕ → ℝ) (hU : ∀ i, 16 ≤ U i)
    (hc : ∀ i j, i < cut j → 8 ≤ U i * radius (t j)) :
    ∃ s : Fin (k^2*Fintype.card J) → Path,
      (∀ i, (Fintype.card (s i).Index : ℝ) ≤ ∏ i ∈ Finset.range k, 4*U i) ∧
      ∀ j, (∑ i, len (s i).pattern (t j)) / (k^2*Fintype.card J : ℕ) ≤
        envelope k (cut j)+1/k := by
  let q := Fintype.card J
  let M := k^2*q
  have hq : 0<q := Fintype.card_pos
  have hM : 0<M := Nat.mul_pos (pow_pos hk 2) hq
  obtain ⟨s,hs⟩ := exists_sample (excess t cut) (excess_bound t ht cut) (excess_test k t ht cut U hU hc) M
  refine ⟨fun i => (s i).val,fun i => (s i).property.2,fun j => mean_le t cut s hM j ((hs j).trans_eq ?_)⟩
  change Real.sqrt ((k^2*q:ℕ)*q) = (k^2*q:ℕ)/k
  have he : ((k^2*q:ℕ):ℝ)/k = (k:ℝ)*q := by push_cast; field_simp
  rw [he,← Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg q))]
  congr 1; push_cast; ring

/-- Exponential weights approximate the scalar envelope to within 1/k using
only logarithmically many samples in the number of mesh heights at fixed k. -/
theorem paths_on_mesh_of_log {J : Type*} [Fintype J] [Nonempty J] (k M : ℕ)
    (hk : 0<k) (hM : 0<M) (hsize : 4*(k:ℝ)^2*Real.log (Fintype.card J) ≤ M)
    (t : J → ℝ) (ht : ∀ j, t j ∈ Icc 0 1)
    (cut : J → ℕ) (U : ℕ → ℝ) (hU : ∀ i, 16 ≤ U i)
    (hc : ∀ i j, i < cut j → 8 ≤ U i * radius (t j)) :
    ∃ s : Fin M → Path,
      (∀ i, (Fintype.card (s i).Index : ℝ) ≤ ∏ i ∈ Finset.range k, 4*U i) ∧
      ∀ j, (∑ i, len (s i).pattern (t j))/(M:ℝ) ≤ envelope k (cut j)+1/k := by
  obtain ⟨s,hs⟩ := exists_sample_of_log (excess t cut) (excess_bound t ht cut)
    (excess_test k t ht cut U hU hc) k M hk hsize
  exact ⟨fun i => (s i).val,fun i => (s i).property.2,fun j => mean_le t cut s hM j (hs j)⟩

/-- Control the weighted lengths directly. Their common benchmark μ contributes
multiplicatively to the growth of the exponential potential. -/
theorem weighted_paths_on_mesh {J : Type*} [Fintype J] [Nonempty J] (k M : ℕ) (hM : 0<M)
    (t z : J → ℝ) (ht : ∀ j, t j ∈ Icc 0 1) (hz : ∀ j, z j ∈ Icc 0 1)
    (cut : J → ℕ) (U : ℕ → ℝ) (hU : ∀ i, 16 ≤ U i)
    (hc : ∀ i j, i < cut j → 8 ≤ U i * radius (t j))
    {μ η : ℝ} (hμ : 0≤μ) (hbench : ∀ j, z j*envelope k (cut j) ≤ μ)
    (hη : 0<η) (hη1 : η≤1) :
    ∃ s : Fin M → Path,
      (∀ i, (s i).depth=k ∧ (Fintype.card (s i).Index : ℝ) ≤ ∏ i ∈ Finset.range k, 4*U i) ∧
      ∀ j, z j*((∑ i, len (s i).pattern (t j))/(M:ℝ)) ≤
        (1+η)*μ + Real.log (Fintype.card J)/(η*M) := by
  let x := fun (p : BudgetPath k U) j => z j*len p.val.pattern (t j)
  have bx (p j) : x p j ∈ Icc 0 1 := ⟨mul_nonneg (hz j).1 measureReal_nonneg,
    (mul_le_of_le_one_left measureReal_nonneg (hz j).2).trans (p.val.pattern.section_length_le_one (ht j))⟩
  have test (a : J → ℝ) (ha : ∀ j, 0≤a j) : ∃ p, ∑ j, a j*x p j ≤ μ*∑ j, a j := by
    obtain ⟨p,hp⟩ := excess_test k t ht cut U hU hc (fun j => a j*z j)
      (fun j => mul_nonneg (ha j) (hz j).1)
    have bound := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => mul_le_mul_of_nonneg_left (hbench j) (ha j))
    simp only [excess,mul_sub,Finset.sum_sub_distrib,mul_assoc] at hp
    refine ⟨p,?_⟩
    change ∑ j, a j*(z j*len p.val.pattern (t j)) ≤ _
    exact (sub_nonpos.mp hp).trans (bound.trans_eq (by rw [←Finset.sum_mul,mul_comm]))
  obtain ⟨s,hs⟩ := exists_sample_nonneg_rate x bx hμ test M hη hη1
  refine ⟨fun i => (s i).val,fun i => (s i).property,fun j => ?_⟩
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  have eq : z j*(∑ i, len (s i).val.pattern (t j))/(M:ℝ) ≤
      (Real.log (Fintype.card J)/η+(1+η)*(M:ℝ)*μ)/M := by
    rw [Finset.mul_sum]
    exact (div_le_div_iff_of_pos_right hm).mpr (hs j)
  calc
    _ = z j*(∑ i, len (s i).val.pattern (t j))/(M:ℝ) := by ring
    _ ≤ _ := eq
    _ = _ := by field_simp; ring

/-- The exponential moment along one path changes the sample cost to logarithmic
in the number of mesh heights, uniformly in the depth. -/
theorem moment_paths_on_mesh {J : Type*} [Fintype J] [Nonempty J] (k M : ℕ) (hk : 0<k) (hM : 0<M)
    (t z : J → ℝ) (ht : ∀ j, t j ∈ Icc 0 1) (hz : ∀ j, z j ∈ Icc 0 1)
    (U : ℕ → ℝ) (hU : ∀ i, 16 ≤ U i)
    (hc : ∀ i j, i < ⌊(k:ℝ)*z j⌋₊ → 8 ≤ U i*radius (t j)) :
    ∃ s : Fin M → Path,
      (∀ i, (s i).depth=k ∧ (Fintype.card (s i).Index : ℝ) ≤ ∏ i ∈ Finset.range k, 4*U i) ∧
      ∀ j, z j*((∑ i, len (s i).pattern (t j))/(M:ℝ)) ≤
        256*(Real.log (Fintype.card J)/(M:ℝ)+Real.log 2)/k := by
  let cut := fun j => ⌊(k:ℝ)*z j⌋₊
  have hcut (j) : cut j≤k := by
    exact_mod_cast (Nat.floor_le (mul_nonneg (Nat.cast_nonneg k) (hz j).1)).trans
      (mul_le_of_le_one_right (Nat.cast_nonneg _) (hz j).2)
  let v := fun (p : BudgetPath k U) j => (1+(cut j:ℝ))*len p.val.pattern (t j)/256
  have test (a : J → ℝ) (ha : ∀ j, 0≤a j) : ∃ p, ∑ j, a j*Real.exp (v p j) ≤ 2*∑ j, a j := by
    obtain ⟨p,hd,hp,he⟩ := exists_moment_path t ht cut U hU hc k a ha
    refine ⟨⟨p,hd,hp⟩,?_⟩
    simp only [min_eq_right (hcut _),moment,Nat.cast_add,Nat.cast_one,mul_sub,
      Finset.sum_sub_distrib,←Finset.sum_mul] at he
    exact (sub_nonpos.mp he).trans_eq (mul_comm _ 2)
  obtain ⟨s,hs⟩ := exists_sample_moment v test M
  refine ⟨fun i => (s i).val, fun i => (s i).property, fun j => ?_⟩
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  have hm' : (0:ℝ)<M := by exact_mod_cast hM
  let L := ∑ i, len (s i).val.pattern (t j)
  have hsum : (1+(cut j:ℝ))*L/256 ≤ Real.log (Fintype.card J)+(M:ℝ)*Real.log 2 := by
    have h := hs j
    simpa only [v,L,Finset.sum_div,Finset.mul_sum] using h
  have hL : 0≤L := Finset.sum_nonneg fun _ _ => measureReal_nonneg
  have hpre : (k:ℝ)*z j ≤ 1+(cut j:ℝ) := by linarith [Nat.lt_floor_add_one ((k:ℝ)*z j)]
  have hl : ((k:ℝ)*z j)*L ≤ 256*(Real.log (Fintype.card J)+(M:ℝ)*Real.log 2) :=
    (mul_le_mul_of_nonneg_right hpre hL).trans (by linarith only [hsum])
  change z j*(L/(M:ℝ)) ≤ _
  rw [le_div_iff₀ hk',show z j*(L/(M:ℝ))*(k:ℝ) = ((k:ℝ)*z j*L)/(M:ℝ) by ring,div_le_iff₀ hm']
  exact hl.trans_eq (by field_simp)

private def meshRad (n : ℕ) (j : Fin n) : ℝ := (j.val+1 : ℝ)/(2*n)

def meshHeight (n : ℕ) (j : Bool × Fin n) : ℝ :=
  if j.1 then 1 - meshRad n j.2 else meshRad n j.2

theorem meshRad_mem {n : ℕ} (hn : 0 < n) (j : Fin n) : meshRad n j ∈ Ioc (0:ℝ) (1/2) := by
  have hj : (j.val+1:ℝ) ≤ n := by exact_mod_cast j.isLt
  exact ⟨by unfold meshRad; positivity,(div_le_iff₀ (by positivity : (0:ℝ)<2*n)).mpr (by linarith)⟩

theorem radius_meshHeight {n : ℕ} (hn : 0<n) (j : Bool × Fin n) :
    radius (meshHeight n j) = meshRad n j.2 := by
  obtain ⟨b,j⟩ := j
  have h := (meshRad_mem hn j).2
  cases b <;> simp [radius,meshHeight,min_eq_left (by linarith : meshRad n j ≤ 1-meshRad n j),
    min_eq_right (by linarith : meshRad n j ≤ 1-meshRad n j)]

theorem meshHeight_mem {n : ℕ} (hn : 0<n) (j : Bool × Fin n) : meshHeight n j ∈ Icc 0 1 := by
  obtain ⟨b,j⟩ := j
  obtain ⟨h₁,h₂⟩ := meshRad_mem hn j
  cases b <;> simp only [meshHeight,Bool.false_eq_true,if_false,if_true,Set.mem_Icc] <;>
    constructor <;> linarith

/-- At every height, there is a nearby sample height whose weight is at least as large. -/
theorem mesh_round {n : ℕ} (hn : 0<n) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    ∃ j : Bool × Fin n, radius t ≤ radius (meshHeight n j) ∧
      |t - meshHeight n j| ≤ 1/(2*n : ℝ) := by
  let r := radius t
  have hr0 : 0<r := lt_min ht.1 (sub_pos.mpr ht.2)
  have hr1 : r ≤ 1/2 := by
    dsimp [r,radius]; rcases le_total t (1-t) with h|h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hd : (0:ℝ)<2*n := by positivity
  let m := ⌈r*(2*n)⌉₊
  have hx : 0<r*(2*n:ℝ) := mul_pos hr0 hd
  have hm : 0<m := Nat.ceil_pos.mpr hx
  have hmn : m≤n := Nat.ceil_le.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hr1) hd.le])
  let j : Fin n := ⟨m-1,by omega⟩
  have hj : j.val+1=m := by dsimp [j]; omega
  have he : meshRad n j = (m:ℝ)/(2*n) := by unfold meshRad; exact congrArg (fun x : ℝ => x/(2*n)) (by exact_mod_cast hj)
  have hlo : r ≤ meshRad n j := by rw [he]; exact (le_div_iff₀ hd).mpr (Nat.le_ceil _)
  have hup : meshRad n j-r ≤ 1/(2*n:ℝ) := by
    rw [sub_le_iff_le_add,he,div_le_iff₀ hd,add_mul,one_div_mul_cancel hd.ne']
    exact (Nat.ceil_lt_add_one hx.le).le.trans (by ring_nf; rfl)
  by_cases h : t ≤ 1-t
  · have hr : r=t := min_eq_left h
    exact ⟨(false,j),by simpa [radius_meshHeight hn] using hlo,
      by change |t-meshRad n j| ≤ _; rw [←hr,abs_of_nonpos (sub_nonpos.mpr hlo)]; linarith⟩
  · have hr : r=1-t := min_eq_right (le_of_not_ge h)
    exact ⟨(true,j),by simpa [radius_meshHeight hn] using hlo,
      by change |t-(1-meshRad n j)| ≤ _; rw [show t-(1-meshRad n j) = meshRad n j-r by linarith,abs_of_nonneg (sub_nonneg.mpr hlo)]; exact hup⟩

/-- The section length changes by at most twice the number of squares times the height change. -/
theorem length_shift {ι : Type*} [Fintype ι] (P : Pattern ι) {t s : ℝ}
    (ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 1) :
    len P t ≤ len P s + 2*Fintype.card ι*|t-s| := by
  let d := |t-s|
  let l := P.start s
  let r := fun i => l i + P.w i
  have he (i) : |P.start t i - l i| ≤ d := by
    have hx := Pattern.axis_bounds P.x P.w P.wpos P.x_cover i
    have hy := Pattern.axis_bounds P.y P.w P.wpos P.y_cover i
    have hxy : |P.y i - P.x i| ≤ 1 := abs_le.mpr ⟨by linarith [P.wpos i],by linarith [P.wpos i]⟩
    have heq : P.start t i - l i = (t-s)*(P.y i-P.x i) := by unfold l Pattern.start projection; ring
    rw [heq,abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hxy
  have sub : P.sectionAt t ⊆ ⋃ i, Icc (l i-d) (r i+d) := by
    rw [P.sectionAt_eq ht]; intro x hx
    obtain ⟨i,hl,hr⟩ := mem_iUnion.mp hx
    obtain ⟨h₁,h₂⟩ := abs_le.mp (he i)
    exact mem_iUnion.mpr ⟨i,by linarith,by dsimp [r]; linarith⟩
  have endsec : (⋃ i, Icc (l i) (r i)) = P.sectionAt s := (P.sectionAt_eq hs).symm
  exact (measureReal_mono sub (isCompact_iUnion fun _ => isCompact_Icc).measure_lt_top.ne).trans
    (by simpa only [endsec,len] using Pattern.length_inflate_intervals l r (abs_nonneg (t-s)))

end
end PermutationStrips.AngularBlock
