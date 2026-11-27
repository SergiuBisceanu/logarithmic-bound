import PermutationStrips.CompactRegular

/-! Euclidean Ahlfors regularity of the restricted Hausdorff measure on the limit. -/

open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal MeasureTheory

namespace PermutationStrips.CompactPlane
noncomputable section

def lengthMeasure (B : ℕ → FinitePattern) : Measure EuclideanPlane := μH[1].restrict (euclideanSet B)

theorem euclidean_dist_le_twice (p q : ℝ × ℝ) :
    dist (toEuclidean p) (toEuclidean q) ≤ 2*dist p q := by
  apply (euclidean_dist_le_sum p q).trans
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
  linarith [le_max_left |p.1-q.1| |p.2-q.2|, le_max_right |p.1-q.1| |p.2-q.2|]

theorem euclidean_diam_limit_le (B : ℕ → FinitePattern) : Metric.diam (euclideanSet B) ≤ 2 := by
  apply Metric.diam_le_of_forall_dist_le (by norm_num)
  rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩
  have a := carrier_subset_unit _ (limitSet_subset_level B 0 hp)
  have b := carrier_subset_unit _ (limitSet_subset_level B 0 hq)
  apply (euclidean_dist_le_twice p q).trans
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
  have h : max |p.1-q.1| |p.2-q.2| ≤ 1 :=
    max_le (abs_le.mpr ⟨by linarith [b.1.2,a.1.1],by linarith [a.1.2,b.1.1]⟩)
      (abs_le.mpr ⟨by linarith [b.2.2,a.2.1],by linarith [a.2.2,b.2.1]⟩)
  linarith

theorem level_local (B : ℕ → FinitePattern) (hl : ∀ j, LocalGeometry (B j).pat) :
    ∀ j, LocalGeometry (level B j).pat := by
  intro j
  induction j with
  | zero => exact localGeometry_equalGrid_one
  | succ j ih => exact localGeometry_insert ih (hl j)

private theorem full_cells_mass {ι : Type*} [Fintype ι] (P : Pattern ι) (F : Finset ι)
    {S : Set (ℝ × ℝ)} (hproj : Prod.fst '' S = Icc 0 1) (hsub : S ⊆ P.carrier)
    {z : EuclideanPlane} {r : ℝ}
    (hball : ∀ j ∈ F, ∀ p ∈ cell P j, toEuclidean p ∈ Metric.ball z r) :
    ENNReal.ofReal (∑ j ∈ F, P.w j) ≤ μH[1] (Metric.ball z r ∩ (toEuclidean '' S)) := by
  classical
  let I j := Ioc (P.x j) (P.x j+P.w j)
  let A := ⋃ j ∈ F, I j
  let D := Set.range P.x
  have hD : volume D = 0 := (finite_range P.x).countable.measure_zero _
  have hA : volume A = ENNReal.ofReal (∑ j ∈ F, P.w j) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => (P.wpos j).le)]
    change volume (⋃ j ∈ F, I j) = _
    rw [measure_biUnion_finset (P.x_disjoint.set_pairwise _) (fun _ _ => measurableSet_Ioc)]
    simp [Real.volume_Ioc]
  have hcover : A \ D ⊆ xCoord '' (Metric.ball z r ∩ (toEuclidean '' S)) := by
    intro x hx
    obtain ⟨i,hi,hxI⟩ := mem_iUnion₂.mp hx.1
    have hxu : x ∈ Icc (0:ℝ) 1 := Ioc_subset_Icc_self (Pattern.axis_subset _ _ P.x_cover i hxI)
    rw [← hproj] at hxu
    obtain ⟨p,hp,rfl⟩ := hxu
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hsub hp)
    have hne : P.x j ≠ p.1 := fun h => hx.2 ⟨j,h⟩
    have hxj : p.1 ∈ I j := ⟨lt_of_le_of_ne hj.1.1 hne,hj.1.2⟩
    have hij : i=j := by
      by_contra hij
      exact Set.disjoint_left.mp (P.x_disjoint hij) hxI hxj
    subst j
    exact ⟨toEuclidean p, ⟨hball i hi p hj,mem_image_of_mem _ hp⟩,rfl⟩
  calc
    _ = volume (A \ D) := by rw [measure_diff_null hD,hA]
    _ ≤ volume (xCoord '' (Metric.ball z r ∩ (toEuclidean '' S))) := measure_mono hcover
    _ ≤ _ := by
      simpa [hausdorffMeasure_real] using lipschitz_xCoord.hausdorffMeasure_image_le
        (by norm_num : (0:ℝ)≤1) (Metric.ball z r ∩ (toEuclidean '' S))

theorem ball_lower (B : ℕ → FinitePattern) (hw : ∀ j i, (B j).pat.w i ≤ 1/2)
    (hl : ∀ j, LocalGeometry (B j).pat) {z : EuclideanPlane} (hz : z ∈ euclideanSet B)
    {r : ℝ} (hr : 0<r) (hr' : r ≤ Metric.diam (euclideanSet B)) :
    ENNReal.ofReal (r/128) ≤ lengthMeasure B (Metric.ball z r) := by
  obtain ⟨z,hz,rfl⟩ := hz
  have tend : Tendsto (fun j : ℕ => (1/2:ℝ)^j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨j,hj⟩ := (tend.eventually_lt_const (show 0<r/16 by linarith)).exists
  let P := (level B j).pat
  obtain ⟨i,hi⟩ := mem_iUnion.mp (limitSet_subset_level B j hz)
  obtain ⟨F,hm,hF⟩ := level_local B hl j i z hi (r/2) (by linarith)
    (by linarith [euclidean_diam_limit_le B]) (by linarith [level_width B hw j i])
  have hs := full_cells_mass P F (fst_limitSet B) (limitSet_subset_level B j) (z:=toEuclidean z) (r:=r)
    (fun k hk p hp => by
      have hd : dist p z < r/2 := hF k hk hp
      change dist (toEuclidean p) (toEuclidean z) < r
      linarith [euclidean_dist_le_twice p z])
  rw [lengthMeasure, Measure.restrict_apply Metric.isOpen_ball.measurableSet]
  exact (ENNReal.ofReal_le_ofReal (show r/128 ≤ ∑ k ∈ F,P.w k by linarith)).trans hs

theorem ball_upper (B : ℕ → FinitePattern) (hlen : μH[1] (euclideanSet B) = 1)
    (z : EuclideanPlane) (r : ℝ) :
    lengthMeasure B (Metric.ball z r) ≤ ENNReal.ofReal (2*r) := by
  have hmap := map_length xCoord lipschitz_xCoord (visible_x B) hlen
  let A := Icc (xCoord z-r) (xCoord z+r)
  have hs : Metric.ball z r ⊆ xCoord ⁻¹' A := by
    intro p hp
    have h := lipschitz_xCoord.dist_le_mul p z
    rw [Real.dist_eq] at h
    have h₁ : |xCoord p-xCoord z| < r := lt_of_le_of_lt (by simpa using h) hp
    exact ⟨by linarith [(abs_lt.mp h₁).1], by linarith [(abs_lt.mp h₁).2]⟩
  change (μH[1].restrict (euclideanSet B)) _ ≤ _
  apply (measure_mono hs).trans
  rw [← Measure.map_apply lipschitz_xCoord.continuous.measurable (show MeasurableSet A from measurableSet_Icc),hmap]
  calc
    _ ≤ volume A := Measure.restrict_le_self _
    _ = _ := by rw [show A=Icc (xCoord z-r) (xCoord z+r) from rfl, Real.volume_Icc]; congr 1; ring

/-- Geometric and measure-theoretic conclusions for one compact witness.
The length and ball bounds use the Euclidean metric on the endpoint plane. -/
structure WitnessGeometry (S : Set (ℝ × ℝ)) : Prop where
  compact : IsCompact S
  subset_unit : S ⊆ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1
  horizontal : Prod.fst '' S = Icc 0 1
  vertical : Prod.snd '' S = Icc 0 1
  length_one : μH[1] (toEuclidean '' S) = 1
  x_marginal : Measure.map xCoord (μH[1].restrict (toEuclidean '' S)) = volume.restrict (Icc 0 1)
  y_marginal : Measure.map yCoord (μH[1].restrict (toEuclidean '' S)) = volume.restrict (Icc 0 1)
  ahlfors : ∀ z ∈ toEuclidean '' S, ∀ r : ℝ, 0 < r → r ≤ Metric.diam (toEuclidean '' S) →
    ENNReal.ofReal (r/128) ≤ μH[1].restrict (toEuclidean '' S) (Metric.ball z r) ∧
      μH[1].restrict (toEuclidean '' S) (Metric.ball z r) ≤ ENNReal.ofReal (2*r)

theorem witnessGeometry (B : ℕ → FinitePattern)
    (hw : ∀ j i, (B j).pat.w i ≤ 1/2) (hl : ∀ j, LocalGeometry (B j).pat)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) (he₀ : ∀ j, 0 ≤ e j)
    (hd : ∀ j, Metric.diam (toEuclidean '' (B j).pat.carrier) ≤ 1 + e j) :
    WitnessGeometry (limitSet B) := by
  have h := length_limitSet B hw he he₀ hd
  exact ⟨compact_limitSet B, (limitSet_subset_level B 0).trans (carrier_subset_unit _),
    fst_limitSet B, snd_limitSet B, h, map_length xCoord lipschitz_xCoord (visible_x B) h,
    map_length yCoord lipschitz_yCoord (visible_y B) h, fun z hz r hr hr' =>
      ⟨ball_lower B hw hl hz hr hr', ball_upper B h z r⟩⟩

/-- The same Euclidean Hausdorff length serves as the coupling in grid matching
after transferring it to the ordinary product coordinates. -/
theorem WitnessGeometry.hall {S : Set (ℝ × ℝ)} (g : WitnessGeometry S) :
    ∃ μ : Measure (ℝ × ℝ), IsProbabilityMeasure μ ∧ μ Sᶜ = 0 ∧
      μ.map Prod.fst = volume.restrict (Icc (0:ℝ) 1) ∧
      μ.map Prod.snd = volume.restrict (Icc (0:ℝ) 1) := by
  let ν : Measure EuclideanPlane := μH[1].restrict (toEuclidean '' S)
  let f : EuclideanPlane → ℝ × ℝ := WithLp.ofLp
  have mf : Measurable f := WithLp.measurable_ofLp ..
  refine ⟨ν.map f, ⟨?_⟩, ?_, ?_, ?_⟩
  · simp [ν, Measure.map_apply mf, g.length_one]
  · rw [Measure.map_apply mf g.compact.isClosed.measurableSet.compl]
    dsimp only [ν]
    rw [Measure.restrict_apply (g.compact.isClosed.measurableSet.compl.preimage mf)]
    have he : f ⁻¹' Sᶜ ∩ toEuclidean '' S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨h, p,hp,rfl⟩; exact h hp
    rw [he,measure_empty]
  · rw [Measure.map_map measurable_fst mf]; exact g.x_marginal
  · rw [Measure.map_map measurable_snd mf]; exact g.y_marginal

end
end PermutationStrips.CompactPlane
