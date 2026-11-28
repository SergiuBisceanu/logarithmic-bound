import PermutationStrips.CompactEnsemble
import PermutationStrips.CompactMirror
import PermutationStrips.ShuffleBoundary

/-! The first inserted path forces a transverse gap between opposite boundary points
of a half-shift ensemble, including for subsets retaining both coordinate projections. -/

open Set

namespace PermutationStrips.CompactPlane

noncomputable section

private def view (flip : Bool) (p : ℝ × ℝ) : ℝ × ℝ := if flip then p.swap else p

private theorem ensemble_coords {M : ℕ} (hM : 0<M) {κ : Fin M → Type*}
    (Q : ∀ j, Pattern (κ j)) (flip : Bool) {p : ℝ × ℝ} (hp : p ∈ (ensemble hM Q).carrier) :
    ∃ j : Fin M, ∃ z ∈ (Q j).carrier,
      let a := ((j.val:ℝ)+(view flip z).1)/(2*M)
      let b := ((j.val:ℝ)+(view flip z).2)/(2*M)
      ((view flip p).1=a ∧ (view flip p).2=1/2+b) ∨
      ((view flip p).1=1/2+a ∧ (view flip p).2=b) := by
  change p ∈ (insertFamily (halfShift hM) fun i => Q i.2).carrier at hp
  rw [family_carrier] at hp
  obtain ⟨⟨i,j⟩,z,hz,rfl⟩ := mem_iUnion.mp hp
  refine ⟨j,z,hz,?_⟩
  have coords : copyPoint (halfShift hM) (i,j) z =
      (((i.val:ℝ)/2 + (1/2)*(j.val/M)) + ((1/2)*(1/M))*z.1,
       ((((Equiv.swap (0:Fin 2) 1) i).val:ℝ)/2 + (1/2)*(j.val/M)) + ((1/2)*(1/M))*z.2) := rfl
  rw [coords]
  fin_cases i <;> cases flip <;> norm_num [view]
  · left; constructor <;> ring
  · right; constructor <;> ring
  · right; constructor <;> ring
  · left; constructor <;> ring

private theorem opposite_gap {M : ℕ} (hM : 0<M) {κ : Fin M → Type*}
    (Q : ∀ j, Pattern (κ j)) (flip : Bool)
    (edge : ∀ z ∈ (Q ⟨0,hM⟩).carrier, (view flip z).1=0 → 1/2≤(view flip z).2)
    {p q : ℝ × ℝ} (hp : p ∈ (ensemble hM Q).carrier) (hq : q ∈ (ensemble hM Q).carrier)
    (p0 : (view flip p).1=0) (q1 : (view flip q).1=1) :
    1/(4*(M:ℝ)) ≤ (view flip p).2-(view flip q).2 := by
  have hm : 0<(M:ℝ) := by exact_mod_cast hM
  have inside (j : Fin M) (z : ℝ × ℝ) (hz : z ∈ (Q j).carrier) :
      (view flip z).1 ∈ Icc (0:ℝ) 1 ∧ (view flip z).2 ∈ Icc (0:ℝ) 1 := by
    have h := carrier_subset_unit _ hz
    cases flip
    · exact h
    · exact ⟨h.2,h.1⟩
  have jbound (j : Fin M) : (j.val:ℝ)+1 ≤ M := by exact_mod_cast j.isLt
  obtain ⟨i,z,hz,h⟩ := ensemble_coords hM Q flip hp
  obtain ⟨j,v,hv,g⟩ := ensemble_coords hM Q flip hq
  dsimp only at h g
  have uz := inside i z hz
  have uv := inside j v hv
  have ll : 1/2+1/(4*(M:ℝ)) ≤ (view flip p).2 := by
    rcases h with ⟨x,y⟩|⟨x,y⟩
    · rw [p0, eq_comm, div_eq_zero_iff] at x
      have zero : (i.val:ℝ)+(view flip z).1=0 := x.resolve_right (ne_of_gt (mul_pos (by norm_num : (0:ℝ)<2) hm))
      have iv : i.val = 0 := by exact_mod_cast (show (i.val:ℝ)=0 by linarith [(Nat.cast_nonneg i.val : (0:ℝ) ≤ i.val),uz.1.1])
      have ie : i = ⟨0,hM⟩ := Fin.ext iv
      subst i
      norm_num at zero y
      have ez := edge z hz zero
      rw [y]
      have sc : 1/(4*(M:ℝ)) = (1/2)/(2*M) := by ring
      rw [sc]; gcongr
    · rw [p0] at x
      linarith [div_nonneg (add_nonneg (Nat.cast_nonneg i.val) uz.1.1) (by positivity : 0≤2*(M:ℝ))]
  have rr : (view flip q).2 ≤ 1/2 := by
    have cap (r : ℝ) (hr : r≤1) : ((j.val:ℝ)+r)/(2*M) ≤ 1/2 := by
      apply (div_le_iff₀ (by positivity)).2; linarith [jbound j]
    rcases g with ⟨x,y⟩|⟨x,y⟩
    · linarith [cap _ uv.1.2]
    · rw [y]; exact cap _ uv.2.2
  linarith

/-- Either boundary orientation of the first path forces a diameter excess in
the flat pack and in every refinement with both full coordinate projections. -/
theorem ensemble_diameter_lower {M : ℕ} (hM : 0<M) {κ : Fin M → Type*}
    (Q : ∀ j, Pattern (κ j)) {S : Set (ℝ × ℝ)} (hS : S ⊆ (ensemble hM Q).carrier)
    (hx : Prod.fst '' S = Icc (0:ℝ) 1) (hy : Prod.snd '' S = Icc (0:ℝ) 1)
    (hb : (∀ z ∈ (Q ⟨0,hM⟩).carrier, z.1=0 → 1/2≤z.2) ∨
      (∀ z ∈ (Q ⟨0,hM⟩).carrier, z.2=0 → 1/2≤z.1)) :
    1+(1/(4*(M:ℝ)))^2 ≤ (Metric.diam (toEuclidean '' S))^2 := by
  obtain ⟨flip,full,edge⟩ : ∃ flip : Bool,
      (fun p => (view flip p).1) '' S = Icc (0:ℝ) 1 ∧
      ∀ z ∈ (Q ⟨0,hM⟩).carrier, (view flip z).1=0 → 1/2≤(view flip z).2 := by
    rcases hb with h|h
    · exact ⟨false,hx,h⟩
    · exact ⟨true,hy,h⟩
  have extract (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : ∃ p ∈ S, (view flip p).1=x := by
    rwa [← full] at hx
  obtain ⟨p,hp,hp0⟩ := extract 0 (by norm_num)
  obtain ⟨q,hq,hq1⟩ := extract 1 (by norm_num)
  have gap := opposite_gap hM Q flip edge (hS hp) (hS hq) hp0 hq1
  have hs : Bornology.IsBounded (toEuclidean '' S) :=
    ((isCompact_Icc.prod isCompact_Icc).image
      (WithLp.prod_continuous_toLp 2 ℝ ℝ)).isBounded.subset
      (image_mono (hS.trans (carrier_subset_unit _)))
  have distBound := Metric.dist_le_diam_of_mem hs (mem_image_of_mem _ hp) (mem_image_of_mem _ hq)
  have dsq : (dist (toEuclidean p) (toEuclidean q))^2 =
      ((view flip p).1-(view flip q).1)^2+((view flip p).2-(view flip q).2)^2 := by
    rw [WithLp.prod_dist_eq_of_L2]
    change (Real.sqrt (|p.1-q.1|^2+|p.2-q.2|^2))^2 = _
    rw [Real.sq_sqrt (by positivity),sq_abs,sq_abs]
    cases flip
    · rfl
    · exact add_comm _ _
  have gapSq := pow_le_pow_left₀ (by positivity : 0≤1/(4*(M:ℝ))) gap 2
  calc
    _ ≤ (dist (toEuclidean p) (toEuclidean q))^2 := by rw [dsq,hp0,hq1]; nlinarith only [gapSq]
    _ ≤ _ := pow_le_pow_left₀ dist_nonneg distBound 2

end
end PermutationStrips.CompactPlane

namespace PermutationStrips.AngularBlock
open CompactPlane

/-- Squared diameter of the reflected half-shift built from actual shuffles.
Only the first slot needs a path of positive depth. -/
theorem halfShift_diameter_lower {M : ℕ} (hM : 0<M) (p : Fin M → Path)
    (hp : 0 < (p ⟨0,hM⟩).depth) :
    let V := ensemble hM fun j => (p j).pattern
    1+(1/(4*(M:ℝ)))^2 ≤ (Metric.diam (toEuclidean '' (V.insert (mirrorPattern V)).carrier))^2 := by
  let V := ensemble hM fun j => (p j).pattern
  let Q := V.insert (mirrorPattern V)
  exact ensemble_diameter_lower hM (fun j => (p j).pattern) (carrier_insert_subset V _)
    (fst_carrier Q) (snd_carrier Q) (path_boundary _ hp)

/-- The diameter target in the finite-block lemma forces at least k/6 slots
per half, counted with multiplicity. -/
theorem halfShift_slots_ge {M k : ℕ} (hM : 0<M) (hk : 2≤k) (p : Fin M → Path)
    (hp : 0 < (p ⟨0,hM⟩).depth)
    (hd : let V := ensemble hM fun j => (p j).pattern
          Metric.diam (toEuclidean '' (V.insert (mirrorPattern V)).carrier) ≤ 1+1/(k:ℝ)^2) :
    k ≤ 6*M := by
  have hm : 0<(M:ℝ) := by exact_mod_cast hM
  have hk' : 2≤(k:ℝ) := by exact_mod_cast hk
  have eps : 1/(k:ℝ)^2 ≤ 1/4 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [sq_nonneg ((k:ℝ)-2)]
  have h := (halfShift_diameter_lower hM p hp).trans (pow_le_pow_left₀ Metric.diam_nonneg hd 2)
  have hgap : 1/(16*(M:ℝ)^2) ≤ 9/(4*(k:ℝ)^2) := by
    rw [show 1/(16*(M:ℝ)^2) = (1/(4*(M:ℝ)))^2 by ring,
      show 9/(4*(k:ℝ)^2) = (9/4)*(1/(k:ℝ)^2) by ring]
    nlinarith only [h, mul_le_mul_of_nonneg_right eps (by positivity : 0≤1/(k:ℝ)^2)]
  have hc := (div_le_div_iff₀ (by positivity) (by positivity)).mp hgap
  exact_mod_cast (show (k:ℝ) ≤ 6*(M:ℝ) by nlinarith [sq_nonneg ((k:ℝ)-6*M)])

end PermutationStrips.AngularBlock
