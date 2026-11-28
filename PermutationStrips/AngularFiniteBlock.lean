import PermutationStrips.AngularBlock
import PermutationStrips.AngularGeometry
import PermutationStrips.CompactMirror
import PermutationStrips.CompactShuffle
import PermutationStrips.CompactEnsemble

/-! A single finite pattern controls every oblique projection at once. Its reflected
inner copy covers the opposite quadrant; its outer copy retains the diameter bound. -/

open Set MeasureTheory
open scoped BigOperators
namespace PermutationStrips.AngularBlock
open CompactPlane
noncomputable section

/-- Two copies of each of the cubic ensemble's paths give a simultaneous block
with an explicit square count and Euclidean diameter. -/
theorem exists_cubic_block {w : ℝ → ℝ} (hm : Measurable w)
    (hw : ∀ r ∈ Ioc (0:ℝ) (1/2), w r ∈ Icc 0 1)
    (hmono : MonotoneOn w (Ioc (0:ℝ) (1/2)))
    (hi : IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2)))
    (hI : (∫ r in Ioc (0:ℝ) (1/2), w r/r) ≤ 3)
    (k : ℕ) (hk : 2≤k) :
    ∃ Q : FinitePattern, (Fintype.card Q.index : ℝ) ≤ (80*(k:ℝ)^3*Real.exp (8*k))^2 ∧
      Metric.diam (toEuclidean '' Q.pat.carrier) ≤ 1+1/(40*(k:ℝ)^3) ∧ (∀ i, Q.pat.w i ≤ 1/2) ∧
      LocalGeometry Q.pat ∧ ∀ θ, 0 < Angular.rho θ →
        w (Angular.rho θ)*Angular.length Q.pat.carrier θ ≤ 260/k := by
  have hk' : 0<k := by omega
  let M := 40*k^3
  have hMr : (M:ℝ)=40*(k:ℝ)^3 := by simp [M]
  have hM : 0<M := by dsimp [M]; positivity
  obtain ⟨p,hcap,hmean⟩ := exists_cubic_ensemble hm hw hmono hi hI k hk'
  let I := Σ i : Fin 2 × Fin M, (p i.2).Index
  let V : Pattern I := ensemble hM fun i => (p i).pattern
  let R := mirrorPattern V
  let Q := V.insert R
  have hV : LocalGeometry V := ensemble_local hM _ fun i => localGeometry_path (p i)
  refine ⟨⟨I×I,inferInstance,Q⟩,?_,?_,?_,localGeometry_insert hV (localGeometry_mirror hV),?_⟩
  · have hcount := ensemble_card hcap
    change (Fintype.card I:ℝ) ≤ _ at hcount
    change (Fintype.card (I×I):ℝ) ≤ _
    rw [Fintype.card_prod,Nat.cast_mul]
    rw [sq]
    apply mul_le_mul _ _ (Nat.cast_nonneg _) (by positivity) <;>
      exact hcount.trans_eq (by rw [hMr]; ring)
  · have hsub := image_mono (f:=toEuclidean) (carrier_insert_subset V R)
    have hdiam := Metric.diam_mono hsub
      ((compact_carrier V).image (WithLp.prod_continuous_toLp 2 ℝ ℝ)).isBounded
    exact hdiam.trans ((ensemble_diameter hM _).trans_eq (by rw [hMr]))
  · intro i
    change V.w i.1 * R.w i.2 ≤ 1/2
    have hwidth := ensemble_width hM (fun i => (p i).pattern) i.1
    have hxy := Pattern.axis_bounds R.x R.w R.wpos R.x_cover i.2
    exact (mul_le_of_le_one_right (V.wpos i.1).le (by linarith [hxy.1,hxy.2])).trans hwidth
  · intro θ hθ
    obtain ⟨t,ht,hr,hcase⟩ := Angular.length_two_signs V.carrier θ
    have ht' : t ∈ Ioo 0 1 := by
      rw [hr,lt_min_iff] at hθ
      exact ⟨hθ.1,by linarith [hθ.2]⟩
    have hw0 := (hw _ ⟨hθ,(Angular.rho_bounds θ).2⟩).1
    have hsect := length_ensemble_le hM (fun i => (p i).pattern) ht
    have htest := hmean t ht'
    rw [←hMr] at htest
    change w (min t (1-t)) * _ ≤ _ at htest
    rw [←hr] at htest
    have hs : w (Angular.rho θ)*len V t ≤ 130/k :=
      (mul_le_mul_of_nonneg_left hsect hw0).trans htest
    have hlen : Angular.length Q.carrier θ ≤ Angular.speed θ*len V t := by
      rcases hcase with h|h
      · exact (Angular.length_insert_le_outer V R θ).trans_eq h
      · rw [←carrier_mirror] at h
        exact (Angular.length_insert_le_inner V R θ).trans_eq h
    have wpos := Angular.speed_pos θ
    calc
      _ ≤ w (Angular.rho θ)*(Angular.speed θ*len V t) := mul_le_mul_of_nonneg_left hlen hw0
      _ = Angular.speed θ*(w (Angular.rho θ)*len V t) := by ring
      _ ≤ 2*(130/k) := mul_le_mul (Angular.speed_bounds θ).2 hs
        (mul_nonneg hw0 measureReal_nonneg) (by norm_num)
      _ = _ := by ring

/-- The explicit budget for the reflected cubic construction is at most exp(32k). -/
theorem cubic_block_size_le_exp (k : ℕ) (hk : 0<k) :
    (80*(k:ℝ)^3*Real.exp (8*k))^2 ≤ Real.exp (32*k) := by
  have hk1 : (1:ℝ)≤k := by exact_mod_cast hk
  have h2 : (2:ℝ)≤Real.exp k := by linarith [Real.add_one_le_exp (k:ℝ)]
  have hinner : 80*(k:ℝ)^3*Real.exp (8*k) ≤ Real.exp (16*k) := by
    calc
      _ = 2*(40*(k:ℝ)^3)*Real.exp (8*k) := by ring
      _ ≤ Real.exp k * Real.exp (7*k)*Real.exp (8*k) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul h2 (cubic_size_le_exp k hk) (by positivity) (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
  calc
    _ ≤ (Real.exp (16*k))^2 := pow_le_pow_left₀ (by positivity) hinner 2
    _ = _ := by rw [sq,←Real.exp_add]; congr 1; ring

/-- Finite simultaneous block with an absolute square-count budget, near-unit
Euclidean diameter, and the regularity certificate for passage to a nested limit. -/
theorem exists_block {w : ℝ → ℝ} (hm : Measurable w)
    (hw : ∀ r ∈ Ioc (0:ℝ) (1/2), w r ∈ Icc 0 1)
    (hmono : MonotoneOn w (Ioc (0:ℝ) (1/2)))
    (hi : IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2)))
    (hI : (∫ r in Ioc (0:ℝ) (1/2), w r/r) ≤ 3)
    (k : ℕ) (hk : 2≤k) :
    ∃ Q : FinitePattern, (Fintype.card Q.index : ℝ) ≤ Real.exp (1000*k) ∧
      Metric.diam (toEuclidean '' Q.pat.carrier) ≤ 1+1000/k ∧ (∀ i, Q.pat.w i ≤ 1/2) ∧
      LocalGeometry Q.pat ∧ ∀ θ, 0 < Angular.rho θ →
        w (Angular.rho θ)*Angular.length Q.pat.carrier θ ≤ 1000/k := by
  have hk' : 0<k := by omega
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  have hkpos : (0:ℝ)<k := by positivity
  obtain ⟨Q,hcount,hdiam,hwidth,hlocal,hθ⟩ := exists_cubic_block hm hw hmono hi hI k hk
  refine ⟨Q,hcount.trans ((cubic_block_size_le_exp k hk').trans (Real.exp_le_exp.mpr (by linarith))),
    hdiam.trans (add_le_add_left ?_ _),hwidth,hlocal,fun θ h => (hθ θ h).trans ?_⟩
  · have hkle : (k:ℝ)≤40*(k:ℝ)^3 := by
      calc
        _ ≤ (k:ℝ)^3 := by simpa using pow_le_pow_right₀ (by linarith : (1:ℝ)≤k) (by decide : 1≤3)
        _ ≤ _ := by linarith [pow_nonneg hkpos.le 3]
    exact (one_div_le_one_div_of_le hkpos hkle).trans ((div_le_div_iff_of_pos_right hkpos).mpr (by norm_num))
  · exact (div_le_div_iff_of_pos_right hkpos).mpr (by norm_num)

end
end PermutationStrips.AngularBlock
