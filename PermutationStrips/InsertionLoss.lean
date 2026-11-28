import PermutationStrips.ShufflePattern

/-! An insertion cannot lose more length than its outer pattern loses on the unit square. -/

open Set MeasureTheory
open scoped BigOperators

namespace PermutationStrips.CompactPlane

theorem insertion_loss_le_outer {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Pattern ι) (P : Pattern κ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    volume.real (P.sectionAt t) - volume.real ((A.insert P).sectionAt t) ≤
      1 - volume.real (A.sectionAt t) := by
  let F := P.sectionAt t
  let U := Icc (0:ℝ) 1
  let G (i : ι) (z : ℝ) := A.start t i + A.w i*z
  have outer : A.sectionAt t = ⋃ i, G i '' U := by
    rw [A.sectionAt_eq ht]
    apply iUnion_congr; intro i
    dsimp [G,U]
    simp_rw [add_comm (A.start t i) (A.w i*_)]
    rw [image_affine_Icc' (A.wpos i)]
    simp [add_comm]
  have ins : (A.insert P).sectionAt t = ⋃ i, G i '' F := A.sectionAt_insert P ht
  have sub : (A.insert P).sectionAt t ⊆ A.sectionAt t := by
    rw [outer,ins]; exact iUnion_mono fun i => image_mono (P.sectionAt_subset_unit ht)
  let gaps := ⋃ i, G i '' (U \ F)
  have covered : A.sectionAt t \ (A.insert P).sectionAt t ⊆ gaps := by
    rintro x ⟨hx, hn⟩
    rw [outer] at hx
    obtain ⟨i,z,hz,rfl⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i,z,⟨hz,fun h => hn (ins ▸ mem_iUnion.mpr ⟨i,z,h,rfl⟩)⟩,rfl⟩
  have bounded : gaps ⊆ A.sectionAt t := by
    rw [outer]; exact iUnion_mono fun i => image_mono diff_subset
  have hfin : volume (A.sectionAt t) ≠ ⊤ := (A.isCompact_sectionAt ht).measure_lt_top.ne
  have loss := measureReal_mono covered (ne_top_of_le_ne_top hfin (measure_mono bounded))
  rw [measureReal_diff sub ((A.insert P).measurableSet_sectionAt ht) hfin] at loss
  have sumBound : volume.real gaps ≤ 1 - volume.real F := calc
    _ ≤ ∑ i, volume.real (G i '' (U \ F)) := measureReal_iUnion_fintype_le _
    _ = ∑ i, A.w i * volume.real (U \ F) := by
      apply Finset.sum_congr rfl; intro i _; exact Shuffle.measure_affine _ _ (A.wpos i) _
    _ = _ := by
      rw [← Finset.sum_mul,A.sum_width,one_mul,measureReal_diff (P.sectionAt_subset_unit ht)
        (P.measurableSet_sectionAt ht) measure_Icc_lt_top.ne]
      simp [F]
  change volume.real F - _ ≤ _
  linarith

end PermutationStrips.CompactPlane
