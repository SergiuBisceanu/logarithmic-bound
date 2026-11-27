import PermutationStrips.ShufflePattern
import Mathlib.MeasureTheory.Integral.Prod

/-! From the shell estimate at one height to a deterministic area-decreasing
insertion of genuine finite patterns. All integrations are Lebesgue integrals. -/

open Set MeasureTheory
open scoped Interval BigOperators

namespace PermutationStrips.Shuffle
noncomputable section

def orientedHeight (rev : Bool) (t : ℝ) := if rev then 1-t else t
def orientedPattern (u : ℝ) (hu : 4 ≤ u) (rev : Bool) : Pattern (Bool × Fin ⌊u⌋₊) :=
  if rev then (shufflePattern u hu).transpose else shufflePattern u hu

theorem oriented_section {ι : Type*} (P : Pattern ι) (u : ℝ) (hu : 4 ≤ u) (rev : Bool)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    ((orientedPattern u hu rev).insert P).sectionAt t =
      colorSection u hu (orientedHeight rev t) (P.sectionAt t) false ∪
      colorSection u hu (orientedHeight rev t) (P.sectionAt t) true := by
  have hs (i) : (orientedPattern u hu rev).start t i = (shufflePattern u hu).start (orientedHeight rev t) i := by
    cases rev <;> simp [orientedPattern,orientedHeight,Pattern.start_transpose]
  have hw (i) : (orientedPattern u hu rev).w i = (shufflePattern u hu).w i := by cases rev <;> rfl
  rw [Pattern.sectionAt_insert _ _ ht]
  simp_rw [hs,hw]
  ext x
  simp only [colorSection,Set.mem_union,Set.mem_iUnion]
  constructor
  · rintro ⟨⟨b,i⟩,hz⟩
    cases b
    · exact Or.inl ⟨i,hz⟩
    · exact Or.inr ⟨i,hz⟩
  · rintro (⟨i,hz⟩|⟨i,hz⟩)
    · exact ⟨(false,i),hz⟩
    · exact ⟨(true,i),hz⟩

theorem insertion_saving {ι : Type*} [Finite ι] (P : Pattern ι) (u : ℝ) (hu : 4 ≤ u)
    (rev : Bool) {t : ℝ} (ht : t ∈ Icc 0 1) :
    regularSaving (P.sectionAt t) (orientedHeight rev t) u ≤
      volume.real (P.sectionAt t) - volume.real (((orientedPattern u hu rev).insert P).sectionAt t) := by
  rw [oriented_section _ _ _ _ ht]
  linarith only [length_colors_add_saving (P.isCompact_sectionAt ht) hu (orientedHeight rev t)]

private def sectionModel {ι : Type*} (P : Pattern ι) (t : ℝ) : Set ℝ :=
  ⋃ i, Icc (P.start t i) (P.start t i + P.w i)

private theorem model_meas {ι : Type*} [Finite ι] (P : Pattern ι) :
    MeasurableSet {z : ℝ×ℝ | z.2 ∈ sectionModel P z.1} := by
  have h : {z : ℝ×ℝ | z.2 ∈ sectionModel P z.1} =
      ⋃ i, {z : ℝ×ℝ | P.start z.1 i ≤ z.2 ∧ z.2 ≤ P.start z.1 i+P.w i} := by
    ext z; simp [sectionModel]
  rw [h]
  apply MeasurableSet.iUnion
  intro i
  exact (measurableSet_le (by unfold Pattern.start projection; fun_prop) measurable_snd).inter
    (measurableSet_le measurable_snd (by unfold Pattern.start projection; fun_prop))

private def gain {ι : Type*} (P : Pattern ι) (rev : Bool) (t u : ℝ) :=
  max 0 (min 1 (regularSaving (sectionModel P t) (orientedHeight rev t) u))

private theorem measurable_gain {ι : Type*} [Finite ι] (P : Pattern ι) (rev : Bool) :
    Measurable (Function.uncurry (gain P rev)) := by
  have hF : MeasurableSet {p : (ℝ×ℝ)×ℝ | p.2 ∈ sectionModel P p.1.1} :=
    (model_meas P).preimage ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hT : Measurable (fun p : ℝ×ℝ => orientedHeight rev p.1) := by
    cases rev <;> unfold orientedHeight <;> simp <;> fun_prop
  exact measurable_const.max (measurable_const.min (measurable_regularSaving_family
    (F:=fun p : ℝ×ℝ => sectionModel P p.1) hF hT measurable_snd))

private theorem gain_eq {ι : Type*} [Finite ι] (P : Pattern ι) (rev : Bool)
    {t u : ℝ} (ht : t ∈ Icc 0 1) (hu : 4 ≤ u) :
    gain P rev t u = regularSaving (P.sectionAt t) (orientedHeight rev t) u := by
  have hsec : sectionModel P t = P.sectionAt t := (P.sectionAt_eq ht).symm
  have hpos : 0 ≤ regularSaving (P.sectionAt t) (orientedHeight rev t) u :=
    div_nonneg ENNReal.toReal_nonneg (by linarith)
  have hle := insertion_saving P u hu rev ht
  have hle₁ := P.section_length_le_one ht
  have hnew : 0 ≤ volume.real (((orientedPattern u hu rev).insert P).sectionAt t) :=
    measureReal_nonneg
  unfold gain
  rw [hsec,min_eq_right (by linarith),max_eq_right hpos]

private theorem gain_norm {ι : Type*} (P : Pattern ι) (rev : Bool) (t u : ℝ) :
    ‖gain P rev t u‖ ≤ 1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (le_max_left _ _)]
  exact max_le (by norm_num) (min_le_left _ _)

private theorem length_Icc_integrable {ι : Type*} [Finite ι] (P : Pattern ι) :
    IntegrableOn (fun t => volume.real (P.sectionAt t)) (Icc (0:ℝ) 1) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  exact P.intervalIntegrable_length.1

private theorem area_loss_bound {ι : Type*} [Finite ι] (P : Pattern ι) (rev : Bool)
    {u a b : ℝ} (hu : 4 ≤ u) (hJ : Icc a b ⊆ Icc 0 1) :
    (∫ t in Icc a b, gain P rev t u) ≤ P.area - ((orientedPattern u hu rev).insert P).area := by
  let Q := (orientedPattern u hu rev).insert P
  let f := fun t => volume.real (P.sectionAt t) - volume.real (Q.sectionAt t)
  have hf : IntegrableOn f (Icc (0:ℝ) 1) := (length_Icc_integrable P).sub (length_Icc_integrable Q)
  have hgn : IntegrableOn (fun t => gain P rev t u) (Icc a b) :=
    IntegrableOn.of_bound measure_Icc_lt_top ((measurable_gain P rev).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun t => gain_norm _ _ _ _)
  have hle (t:ℝ) (ht:t∈Icc 0 1) : gain P rev t u ≤ f t := by
    rw [gain_eq _ _ ht hu]
    exact insertion_saving P u hu rev ht
  calc
    _ ≤ ∫ t in Icc a b, f t := setIntegral_mono_on hgn (hf.mono_set hJ) measurableSet_Icc
      (fun t ht => hle t (hJ ht))
    _ ≤ ∫ t in Icc (0:ℝ) 1, f t := setIntegral_mono_set hf (by
      filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Icc] with t ht
      exact (le_max_left _ _).trans (hle t ht))
      (Filter.Eventually.of_forall hJ)
    _ = _ := by
      change _ = P.area - Q.area
      simp only [Pattern.area,intervalIntegral.integral_of_le zero_le_one,restrict_Ioc_eq_restrict_Icc]
      exact integral_sub (length_Icc_integrable P) (length_Icc_integrable Q)


/-- A single actual insertion captures a fixed fraction of the integrated saving on
any active interval. Transposing only the outer factor reflects the active heights. -/
theorem exists_area_step {ι : Type*} [Finite ι] (P : Pattern ι) (rev : Bool) {U a b : ℝ}
    (hU : 16 ≤ U) (hJ : Icc a b ⊆ Icc 0 1)
    (hactive : ∀ t ∈ Icc a b, 0 < orientedHeight rev t ∧ orientedHeight rev t ≤ 1/2 ∧
      8 ≤ U * orientedHeight rev t) :
    ∃ u, ∃ hu : u ∈ Icc U (2*U), (∫ t in Icc a b, (volume.real (P.sectionAt t))^2) / 128 ≤
      P.area - ((orientedPattern u (by linarith [hu.1]) rev).insert P).area := by
  let J := Icc a b
  let K := Icc U (2*U)
  let G := gain P rev
  let L := fun t => volume.real (P.sectionAt t)
  let E := ∫ t in J, (L t)^2
  have hUp : 0 < U := by linarith
  have hKU : U ∈ K := ⟨le_rfl,by linarith⟩
  have hEn : 0 ≤ E := integral_nonneg (fun t => sq_nonneg _)
  have hL : IntegrableOn L J := (length_Icc_integrable P).mono_set hJ
  have hL₂ : IntegrableOn (fun t => (L t)^2) J := by
    refine hL.mono' (hL.aestronglyMeasurable.pow 2) ?_
    filter_upwards [ae_restrict_mem (μ:=volume) (s:=J) measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have hl : 0 ≤ L t := measureReal_nonneg
    have hr : L t ≤ 1 := P.section_length_le_one (hJ ht)
    nlinarith [mul_nonneg hl (sub_nonneg.mpr hr)]
  letI : IsFiniteMeasure (volume.restrict J) := ⟨by simp [J]⟩
  letI : IsFiniteMeasure (volume.restrict K) := ⟨by simp [K]⟩
  have hG : Integrable (Function.uncurry G) ((volume.restrict J).prod (volume.restrict K)) :=
    Integrable.of_bound (measurable_gain P rev).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => gain_norm P rev z.1 z.2)
  have hbu (t:ℝ) (ht : t∈J) : (L t)^2 * (U/64) ≤ ∫ u in K, G t u := by
    obtain ⟨h₁,h₂,h₃⟩ := hactive t ht
    have hs := shell_average ((P.isCompact_sectionAt (hJ ht)).measurableSet)
      (P.sectionAt_subset_unit (hJ ht)) h₁ h₂ hU h₃
    have hr := (le_div_iff₀ hUp).mp hs
    rw [show (∫ u in K, G t u) = ∫ u in K, regularSaving (P.sectionAt t) (orientedHeight rev t) u from
      setIntegral_congr_fun measurableSet_Icc fun u hu => gain_eq _ _ (hJ ht) (by linarith [hu.1])]
    change (volume.real (P.sectionAt t))^2 * (U/64) ≤ _
    simpa only [measureReal_def, div_eq_mul_inv, mul_assoc, mul_comm U] using hr
  have hmean : E*(U/64) ≤ ∫ u in K, ∫ t in J, G t u := by
    calc
      _ = ∫ t in J, (L t)^2 * (U/64) := (integral_mul_const _ _).symm
      _ ≤ ∫ t in J, ∫ u in K, G t u := setIntegral_mono_on (hL₂.mul_const _) hG.integral_prod_left
        measurableSet_Icc hbu
      _ = _ := integral_integral_swap hG
  have hwit : ∃ u ∈ K, E/128 ≤ ∫ t in J, G t u := by
    by_cases he : E=0
    · refine ⟨U,hKU,?_⟩
      rw [he,zero_div]
      exact integral_nonneg (fun t => le_max_left _ _)
    by_contra! h
    have hhi : (∫ u in K, ∫ t in J, G t u) ≤ ∫ _u in K, E/128 :=
      setIntegral_mono_on hG.integral_prod_right (integrable_const _) measurableSet_Icc
        (fun u hu => (h u hu).le)
    have hvol : volume.real K = U := by
      rw [Real.volume_real_Icc_of_le (by linarith : U ≤ 2*U)]
      ring
    rw [setIntegral_const,hvol,smul_eq_mul] at hhi
    have := mul_pos (lt_of_le_of_ne hEn (Ne.symm he)) hUp
    nlinarith
  obtain ⟨u,hu,hgain⟩ := hwit
  exact ⟨u,hu,hgain.trans (area_loss_bound P rev (by linarith [hu.1]) hJ)⟩

end
end PermutationStrips.Shuffle
