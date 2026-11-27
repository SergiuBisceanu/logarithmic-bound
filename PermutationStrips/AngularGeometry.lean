import PermutationStrips.AngularSymmetry
import PermutationStrips.CompactPlane
import PermutationStrips.GridTransfer

/-! Both signs of orthogonal projection, geometric insertion, and the increase in
projected length when a finite union of endpoint squares is thickened. -/

open Set MeasureTheory
namespace PermutationStrips.Angular
open CompactPlane
noncomputable section

/-- A direction reads the ordinary height section of one of the two reflected diagrams. -/
theorem length_two_signs (K : Set (ℝ × ℝ)) (θ : ℝ) :
    ∃ t ∈ Icc (0:ℝ) 1, rho θ = min t (1-t) ∧
      (length K θ = speed θ * volume.real (projection t '' K) ∨
       length (mirror '' K) θ = speed θ * volume.real (projection t '' K)) := by
  let s := speed θ
  let t := |Real.sin θ|/s
  have hp : 0 < s := speed_pos θ
  have hst : s*t = |Real.sin θ| := by dsimp [t]; field_simp
  have hsc : s*(1-t) = |Real.cos θ| := by
    have hh : s = |Real.cos θ| + |Real.sin θ| := rfl
    linarith
  refine ⟨t,⟨div_nonneg (abs_nonneg _) hp.le, (div_le_one hp).mpr (by dsimp [s,speed]; linarith [abs_nonneg (Real.cos θ)])⟩,?_,?_⟩
  · change min |Real.cos θ| |Real.sin θ| / s = _
    rw [← hsc, ← hst, ← mul_min_of_nonneg _ _ hp.le, min_comm]; field_simp
  · have direct (c : ℝ) (hc : |c|=s) (h₁ : Real.cos θ = c*(1-t)) (h₂ : Real.sin θ=c*t) :
        length K θ = s*volume.real (projection t '' K) := by
      have e : proj θ '' K = (fun z => 0+c*z) '' (projection t '' K) := by
        rw [image_image]; apply image_congr; intro p _
        unfold proj projection; rw [h₁,h₂]; ring
      rw [length,e,affine_length,hc]
    have reflected (c : ℝ) (hc : |c|=s) (h₁ : Real.cos θ = c*(1-t)) (h₂ : Real.sin θ= -c*t) :
        length (mirror '' K) θ = s*volume.real (projection t '' K) := by
      have e : proj θ '' (mirror '' K) = (fun z => Real.sin θ+c*z) '' (projection t '' K) := by
        rw [image_image,image_image]; apply image_congr; intro p _
        dsimp [proj,projection,mirror]; rw [h₁,h₂]; ring
      rw [length,e,affine_length,hc]
    rcases le_total 0 (Real.cos θ) with hc|hc <;> rcases le_total 0 (Real.sin θ) with hs|hs
    · rw [abs_of_nonneg hc] at hsc; rw [abs_of_nonneg hs] at hst
      exact Or.inl (direct s (abs_of_pos hp) hsc.symm hst.symm)
    · rw [abs_of_nonneg hc] at hsc; rw [abs_of_nonpos hs] at hst
      exact Or.inr (reflected s (abs_of_pos hp) hsc.symm (by linarith))
    · rw [abs_of_nonpos hc] at hsc; rw [abs_of_nonneg hs] at hst
      exact Or.inr (reflected (-s) (by rw [abs_neg,abs_of_pos hp]) (by linarith) (by linarith))
    · rw [abs_of_nonpos hc] at hsc; rw [abs_of_nonpos hs] at hst
      exact Or.inl (direct (-s) (by rw [abs_neg,abs_of_pos hp]) (by linarith) (by linarith))

theorem length_insert_le_outer {ι κ : Type*} [Finite ι] (P : Pattern ι) (Q : Pattern κ) (θ : ℝ) :
    length (P.insert Q).carrier θ ≤ length P.carrier θ :=
  length_mono (compact_carrier P) (carrier_insert_subset P Q) θ

theorem length_insert_le_inner {ι κ : Type*} [Fintype ι] (P : Pattern ι) (Q : Pattern κ) (θ : ℝ) :
    length (P.insert Q).carrier θ ≤ length Q.carrier θ := by
  let F := proj θ '' Q.carrier
  let u i := (fun z => proj θ (P.x i,P.y i)+P.w i*z) '' F
  have e : proj θ '' (P.insert Q).carrier = ⋃ i, u i := by
    rw [carrier_insert,image_iUnion]
    apply iUnion_congr; intro i
    dsimp [u,F]; rw [image_image,image_image]
    apply image_congr; intro p _
    dsimp [proj,copyPoint]; ring
  have he (i : ι) : volume.real (u i) = P.w i*length Q.carrier θ := by
    dsimp [u]; rw [affine_length,abs_of_pos (P.wpos i)]; rfl
  rw [length,e]
  calc
    _ ≤ ∑ i, volume.real (u i) := measureReal_iUnion_fintype_le _
    _ = _ := by simp only [he,← Finset.sum_mul, P.sum_width,one_mul]

theorem uniform_displacement {δ : ℝ} {p : ℝ × ℝ} (hp : p ∈ Icc (-δ) δ ×ˢ Icc (-δ) δ) (θ : ℝ) :
    |proj θ p| ≤ 2*δ := by
  have hδ : 0 ≤ δ := by linarith [hp.1.1,hp.1.2]
  have ha := abs_le.mpr hp.1
  have hb := abs_le.mpr hp.2
  have hc : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩
  have hs : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ,Real.sin_le_one θ⟩
  calc
    _ ≤ _ := abs_add_le ..
    _ ≤ δ*1+δ*1 := by rw [abs_mul,abs_mul]; exact add_le_add
                         (mul_le_mul ha hc (abs_nonneg _) hδ) (mul_le_mul hb hs (abs_nonneg _) hδ)
    _ = _ := by ring

/-- Thickening by the coordinate square costs at most 4δ for each component, in every direction. -/
theorem length_thick_pattern {ι : Type*} [Fintype ι] (P : Pattern ι) {δ : ℝ}
    (hd : 0 ≤ δ) (θ : ℝ) :
    length (thick δ P.carrier) θ ≤ length P.carrier θ + 4 * Fintype.card ι * δ := by
  let F := fun i => proj θ '' cell P i
  let l := fun i => sInf (F i)
  let r := fun i => sSup (F i)
  have seg (i : ι) : F i = Icc (l i) (r i) := by
    apply eq_Icc_of_connected_compact
    · exact ((isConnected_Icc (by linarith [P.wpos i])).prod
        (isConnected_Icc (by linarith [P.wpos i]))).image _ (continuous_proj θ).continuousOn
    · exact (isCompact_Icc.prod isCompact_Icc).image (continuous_proj θ)
  have project : proj θ '' P.carrier = ⋃ i, Icc (l i) (r i) := by
    change proj θ '' (⋃ i, cell P i) = _
    rw [image_iUnion]; exact iUnion_congr seg
  have sub : proj θ '' (thick δ P.carrier) ⊆ ⋃ i, Icc (l i-2*δ) (r i+2*δ) := by
    rintro _ ⟨_,⟨p,hp,v,hv,rfl⟩,rfl⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp (project ▸ (mem_image_of_mem (proj θ) hp))
    have h := abs_le.mp (uniform_displacement hv θ)
    have add : proj θ (p+v) = proj θ p + proj θ v := by dsimp [proj]; ring
    exact mem_iUnion.mpr ⟨i,by rw [add]; exact ⟨by linarith [hi.1,h.1],by linarith [hi.2,h.2]⟩⟩
  have compact : IsCompact (⋃ i, Icc (l i-2*δ) (r i+2*δ)) := isCompact_iUnion fun _ => isCompact_Icc
  have hinf := Pattern.length_inflate_intervals l r (δ := 2*δ) (by positivity)
  change volume.real _ ≤ volume.real _ + _
  rw [project]
  exact (measureReal_mono sub compact.measure_lt_top.ne).trans (hinf.trans_eq (by ring))

theorem thick_mono {A B : Set (ℝ × ℝ)} (sub : A ⊆ B) (δ : ℝ) : thick δ A ⊆ thick δ B :=
  Set.image2_subset sub Subset.rfl

theorem length_thick_sub {ι κ : Type*} [Fintype ι] [Fintype κ] (P : Pattern ι) (Q : Pattern κ)
    {S : Set (ℝ × ℝ)} (h : S ⊆ (P.insert Q).carrier) {δ : ℝ} (hd : 0 ≤ δ) (θ : ℝ) :
    length (thick δ S) θ ≤ length Q.carrier θ + 4 * (Fintype.card (ι × κ) : ℝ) * δ := by
  exact (length_mono (compact_thick (compact_carrier _) _) (thick_mono h _) _).trans
    ((length_thick_pattern (P.insert Q) hd _).trans (add_le_add_right (length_insert_le_inner P Q θ) _))

end
end PermutationStrips.Angular
