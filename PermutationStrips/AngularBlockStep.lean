import PermutationStrips.ShuffleStep
import Mathlib.MeasureTheory.Integral.Average

/-! Deterministic shell selection against finitely many weighted section lengths. -/

open MeasureTheory Set
open scoped BigOperators

namespace PermutationStrips.AngularBlock
noncomputable section

abbrev len {ι : Type*} (P : Pattern ι) (t : ℝ) := volume.real (P.sectionAt t)

def radius (t : ℝ) := min t (1-t)

theorem weighted_shell {ι J : Type*} [Finite ι] [Fintype J]
    (P : Pattern ι) (t a : J → ℝ) (ht : ∀ j, t j ∈ Icc 0 1)
    (ha : ∀ j, 0 ≤ a j) (active : J → Prop) [DecidablePred active]
    {U : ℝ} (hU : 16 ≤ U)
    (hactive : ∀ j, active j → 8 ≤ U * radius (t j)) :
    ∃ rev : Bool, ∃ u, ∃ hu : u ∈ Icc U (2*U),
      let Q := (Shuffle.orientedPattern u (by linarith [hu.1]) rev).insert P
      ∑ j, a j * (if active j then (len P (t j))^2/128 else 0) ≤
        ∑ j, a j * (len P (t j) - len Q (t j)) := by
  classical
  let K := Icc U (2*U)
  let g := fun b j => Shuffle.regularSaving (P.sectionAt (t j)) (Shuffle.orientedHeight b (t j))
  have hp : 0 < U := by linarith
  have gn (b j) {u : ℝ} (hu : u ∈ K) : 0 ≤ g b j u := by
    exact div_nonneg ENNReal.toReal_nonneg (by linarith [hu.1])
  have gi (b j) : IntegrableOn (g b j) K := by
    have hm : Measurable (g b j) := Shuffle.measurable_regularSaving_family
      (F := fun _ : ℝ => P.sectionAt (t j)) (T := fun _ => Shuffle.orientedHeight b (t j))
      (U := id) ((P.measurableSet_sectionAt (ht j)).preimage measurable_snd)
      measurable_const measurable_id
    refine IntegrableOn.of_bound measure_Icc_lt_top hm.aestronglyMeasurable 1 ?_
    filter_upwards [ae_restrict_mem (μ:=volume) (s:=K) measurableSet_Icc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (gn b j hu)]
    have h := Shuffle.insertion_saving P u (by linarith [hu.1]) b (ht j)
    exact h.trans ((sub_le_self _ measureReal_nonneg).trans (P.section_length_le_one (ht j)))
  have gint (b j) : 0 ≤ ∫ u in K, g b j u := setIntegral_nonneg measurableSet_Icc
    (fun u hu => gn b j hu)
  have target (j : J) :
      (if active j then (len P (t j))^2/64 else 0)*U ≤
        (∫ u in K, g false j u) + ∫ u in K, g true j u := by
    split_ifs with h
    · have hb : ∃ b, Shuffle.orientedHeight b (t j) = radius (t j) := by
        by_cases hl : t j ≤ 1-t j
        · exact ⟨false, (min_eq_left hl).symm⟩
        · exact ⟨true, (min_eq_right (le_of_not_ge hl)).symm⟩
      obtain ⟨b,hb⟩ := hb
      have hu := hactive j h
      have hr : 0 < radius (t j) := pos_of_mul_pos_right (by linarith : 0 < U*radius (t j)) hp.le
      have hh : radius (t j) ≤ 1/2 := by
        unfold radius
        rcases le_total (t j) (1-t j) with ht'|ht'
        · rw [min_eq_left ht']; linarith
        · rw [min_eq_right ht']; linarith
      have hh' := Shuffle.shell_average (P.measurableSet_sectionAt (ht j))
        (P.sectionAt_subset_unit (ht j)) (hb ▸ hr) (hb ▸ hh) hU (hb ▸ hu)
      have hh'' : (len P (t j))^2/64*U ≤ ∫ u in K, g b j u := (le_div_iff₀ hp).mp hh'
      cases b <;> linarith [gint false j, gint true j]
    · linarith [gint false j, gint true j]
  let G := fun u => ∑ j, a j * (g false j u + g true j u)
  have hgi : IntegrableOn G K := integrable_finset_sum _ fun j _ =>
    ((gi false j).add (gi true j)).const_mul (a j)
  have htot : (∑ j, a j * (if active j then (len P (t j))^2/64 else 0))*U ≤ ∫ u in K, G u := by
    unfold G
    rw [integral_finset_sum (f:=fun j u => a j*(g false j u+g true j u)) _ (fun j _ => ((gi false j).add (gi true j)).const_mul (a j)),
      Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [integral_const_mul, integral_add (gi false j) (gi true j), mul_assoc]
    exact mul_le_mul_of_nonneg_left (target j) (ha j)
  have volK : volume.real K = U := by simp [K, Real.volume_real_Icc_of_le (by linarith : U ≤ 2*U)]; ring
  obtain ⟨u,hu,havg⟩ := exists_setAverage_le (μ:=volume) (s:=K)
    (by intro h; rw [measureReal_def,h,ENNReal.toReal_zero] at volK; linarith)
    measure_Icc_lt_top.ne hgi
  rw [setAverage_eq,volK,smul_eq_mul,← div_eq_inv_mul] at havg
  have hboth := ((le_div_iff₀ hp).mpr htot).trans havg
  let V := fun b => ∑ j, a j * g b j u
  have he : G u = V false + V true := by simp [G,V,mul_add,Finset.sum_add_distrib]
  have he' : (∑ j, a j * (if active j then (len P (t j))^2/64 else 0)) =
      2*(∑ j, a j * (if active j then (len P (t j))^2/128 else 0)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; split_ifs <;> ring
  rw [he,he'] at hboth
  have hb : ∃ b, (∑ j, a j * (if active j then (len P (t j))^2/128 else 0)) ≤ V b := by
    rcases le_total (V false) (V true) with h|h
    · exact ⟨true,by linarith⟩
    · exact ⟨false,by linarith⟩
  obtain ⟨b,hb⟩ := hb
  refine ⟨b,u,hu,hb.trans (Finset.sum_le_sum fun j _ => ?_)⟩
  exact mul_le_mul_of_nonneg_left (Shuffle.insertion_saving P u (by linarith [hu.1]) b (ht j)) (ha j)

end
end PermutationStrips.AngularBlock
