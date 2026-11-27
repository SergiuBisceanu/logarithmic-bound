import PermutationStrips.CompactPlane
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! Nested permutation patterns and Euclidean Hausdorff length. -/

open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal MeasureTheory

namespace PermutationStrips.CompactPlane

noncomputable section

structure FinitePattern where
  index : Type
  enum : Fintype index
  pat : Pattern index

instance (P : FinitePattern) : Fintype P.index := P.enum

def FinitePattern.insert (P Q : FinitePattern) : FinitePattern :=
  ⟨P.index × Q.index, inferInstance, P.pat.insert Q.pat⟩

def level (B : ℕ → FinitePattern) : ℕ → FinitePattern
  | 0 => ⟨Fin 1, inferInstance, Pattern.equalGrid (by decide : 0 < 1) (Equiv.refl _)⟩
  | j+1 => (level B j).insert (B j)

def limitSet (B : ℕ → FinitePattern) := ⋂ j, (level B j).pat.carrier

theorem level_succ_carrier (B : ℕ → FinitePattern) (j : ℕ) :
    (level B (j+1)).pat.carrier =
      ⋃ i, copyPoint (level B j).pat i '' (B j).pat.carrier := carrier_insert ..

theorem level_antitone (B : ℕ → FinitePattern) : Antitone fun j => (level B j).pat.carrier :=
  antitone_nat_of_succ_le fun _ => carrier_insert_subset ..

theorem limitSet_subset_level (B : ℕ → FinitePattern) (j : ℕ) :
    limitSet B ⊆ (level B j).pat.carrier := iInter_subset _ j

theorem compact_limitSet (B : ℕ → FinitePattern) : IsCompact (limitSet B) :=
  (compact_carrier (level B 0).pat).of_isClosed_subset
    (isClosed_iInter fun j => (compact_carrier (level B j).pat).isClosed) (limitSet_subset_level B 0)

private theorem visible_limit (B : ℕ → FinitePattern) (f : ℝ × ℝ → ℝ) (hf : Continuous f)
    (h : ∀ j, f '' (level B j).pat.carrier = Icc 0 1) : f '' limitSet B = Icc 0 1 := by
  apply Subset.antisymm
  · rw [← h 0]; exact image_mono (limitSet_subset_level B 0)
  · intro x hx
    let F j := (level B j).pat.carrier ∩ f ⁻¹' {x}
    have hn (j : ℕ) : (F j).Nonempty := by
      rw [← h j] at hx
      obtain ⟨p,hp,he⟩ := hx
      exact ⟨p,hp,he⟩
    have hc (j : ℕ) : IsCompact (F j) :=
      (compact_carrier (level B j).pat).inter_right (isClosed_singleton.preimage hf)
    obtain ⟨p,hp⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F
      (fun j => inter_subset_inter_left _ (level_antitone B (Nat.le_succ j))) hn (hc 0)
      (fun j => (hc j).isClosed)
    exact ⟨p,mem_iInter.mpr (fun j => (mem_iInter.mp hp j).1),(mem_iInter.mp hp 0).2⟩

theorem fst_limitSet (B : ℕ → FinitePattern) : Prod.fst '' limitSet B = Icc (0:ℝ) 1 :=
  visible_limit B _ continuous_fst fun _ => fst_carrier _

theorem snd_limitSet (B : ℕ → FinitePattern) : Prod.snd '' limitSet B = Icc (0:ℝ) 1 :=
  visible_limit B _ continuous_snd fun _ => snd_carrier _

theorem level_width (B : ℕ → FinitePattern) (hw : ∀ j i, (B j).pat.w i ≤ 1/2) :
    ∀ j i, (level B j).pat.w i ≤ (1/2:ℝ)^j := by
  intro j; induction j with
  | zero => intro i; simp [level, Pattern.equalGrid]
  | succ j ih =>
    rintro ⟨p,q⟩
    change (level B j).pat.w p * (B j).pat.w q ≤ _
    rw [pow_succ]
    exact mul_le_mul (ih p) (hw j q) ((B j).pat.wpos q).le (by positivity)

def xCoord (z : EuclideanPlane) : ℝ := (WithLp.ofLp z).1
def yCoord (z : EuclideanPlane) : ℝ := (WithLp.ofLp z).2

theorem lipschitz_xCoord : LipschitzWith 1 xCoord := by
  simpa [xCoord, Function.comp_def] using LipschitzWith.prod_fst.comp (WithLp.prod_lipschitzWith_ofLp 2 ℝ ℝ)

theorem lipschitz_yCoord : LipschitzWith 1 yCoord := by
  simpa [yCoord, Function.comp_def] using LipschitzWith.prod_snd.comp (WithLp.prod_lipschitzWith_ofLp 2 ℝ ℝ)

def euclideanSet (B : ℕ → FinitePattern) := toEuclidean '' limitSet B

theorem compact_euclideanSet (B : ℕ → FinitePattern) : IsCompact (euclideanSet B) :=
  (compact_limitSet B).image (WithLp.prod_continuous_toLp 2 ℝ ℝ)

theorem visible_x (B : ℕ → FinitePattern) : xCoord '' euclideanSet B = Icc 0 1 := by
  simpa only [euclideanSet, image_image] using fst_limitSet B

theorem visible_y (B : ℕ → FinitePattern) : yCoord '' euclideanSet B = Icc 0 1 := by
  simpa only [euclideanSet, image_image] using snd_limitSet B

/-- A finite cover by copies of the next block uses the improved block diameter
and its widths add to exactly one. All diameters in this estimate are Euclidean. -/
theorem length_limitSet (B : ℕ → FinitePattern) (hw : ∀ j i, (B j).pat.w i ≤ 1/2)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) (he₀ : ∀ j, 0 ≤ e j)
    (hd : ∀ j, Metric.diam (toEuclidean '' (B j).pat.carrier) ≤ 1 + e j) :
    μH[1] (euclideanSet B) = 1 := by
  let d (j : ℕ) (i : (level B j).index) :=
    toEuclidean '' (copyPoint (level B j).pat i '' (B j).pat.carrier)
  have bound (j : ℕ) (i : (level B j).index) :
      EMetric.diam (d j i) ≤ ENNReal.ofReal ((level B j).pat.w i * (1+e j)) := by
    apply EMetric.diam_le
    rintro _ ⟨_,⟨p,hp,rfl⟩,rfl⟩ _ ⟨_,⟨q,hq,rfl⟩,rfl⟩
    rw [edist_dist,euclidean_copy_dist]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ ((level B j).pat.wpos i).le
    exact (Metric.dist_le_diam_of_mem
      ((compact_carrier (B j).pat).image (WithLp.prod_continuous_toLp 2 ℝ ℝ)).isBounded
      (mem_image_of_mem _ hp) (mem_image_of_mem _ hq)).trans (hd j)
  have mesh := level_width B hw
  have limit : Tendsto (fun j : ℕ => (1/2:ℝ)^j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have limits : Tendsto (fun j : ℕ => 1+e j) atTop (𝓝 1) := by simpa using (tendsto_const_nhds (x:=(1:ℝ))).add he
  have size : Tendsto (fun j : ℕ => ENNReal.ofReal ((1/2:ℝ)^j*(1+e j))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, zero_mul, ENNReal.ofReal_zero, Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp (limit.mul limits)
  have h := Measure.hausdorffMeasure_le_liminf_sum 1 (euclideanSet B) _ size d
    (Eventually.of_forall fun j i => (bound j i).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mesh j i) (by linarith [he₀ j]))))
    (Eventually.of_forall fun j => by
      rintro _ ⟨z,hz,rfl⟩
      have hz' := limitSet_subset_level B (j+1) hz
      rw [level_succ_carrier] at hz'
      obtain ⟨i,hi⟩ := mem_iUnion.mp hz'
      exact mem_iUnion.mpr ⟨i,mem_image_of_mem _ hi⟩)
  have hsum (j : ℕ) : (∑ i, EMetric.diam (d j i) ^ (1:ℝ)) ≤ ENNReal.ofReal (1+e j) := by
    simp only [ENNReal.rpow_one]
    calc
      _ ≤ ∑ i, ENNReal.ofReal ((level B j).pat.w i * (1+e j)) := Finset.sum_le_sum fun i _ => bound j i
      _ = ENNReal.ofReal (1+e j) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg ((level B j).pat.wpos i).le (by linarith [he₀ j])),
          ← Finset.sum_mul, (level B j).pat.sum_width, one_mul]
  have ht : Tendsto (fun j => ENNReal.ofReal (1+e j)) atTop (𝓝 1) := by
    simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp limits
  apply le_antisymm (h.trans ((liminf_le_liminf (Eventually.of_forall hsum)).trans_eq ht.liminf_eq))
  have hl := lipschitz_xCoord.hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 1) (euclideanSet B)
  simpa [visible_x, hausdorffMeasure_real] using hl

/-- Lebesgue measure on the unit interval is the pushforward of the restricted
Euclidean Hausdorff measure in either visible coordinate. -/
theorem map_length {S : Set EuclideanPlane} (f : EuclideanPlane → ℝ)
    (hf : LipschitzWith 1 f) (hproj : f '' S = Icc 0 1) (hlen : μH[1] S = 1) :
    Measure.map f (μH[1].restrict S) = volume.restrict (Icc (0:ℝ) 1) := by
  have lower : volume.restrict (Icc (0:ℝ) 1) ≤ Measure.map f (μH[1].restrict S) := by
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.map_apply hf.continuous.measurable hA, Measure.restrict_apply hA,
      Measure.restrict_apply (hA.preimage hf.continuous.measurable)]
    have h := hf.hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 1) (f ⁻¹' A ∩ S)
    simpa [image_preimage_inter, hproj, hausdorffMeasure_real] using h
  haveI : IsFiniteMeasure (volume.restrict (Icc (0:ℝ) 1)) := ⟨by simp⟩
  symm
  apply Measure.eq_of_le_of_measure_univ_eq lower
  simp [Measure.map_apply hf.continuous.measurable,hlen]

end
end PermutationStrips.CompactPlane
