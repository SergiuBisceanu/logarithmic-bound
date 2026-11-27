import PermutationStrips.CompactPlane

/-! Insert different finite patterns into different parent squares. -/

open Set MeasureTheory
open scoped BigOperators

namespace PermutationStrips.CompactPlane

noncomputable section

private theorem interval_image (a w b d : ℝ) (hw : 0 < w) :
    Ioc (a+w*b) (a+w*b+w*d) = (fun z => w*z+a) '' Ioc b (b+d) := by
  rw [image_affine_Ioc hw]; congr 1 <;> ring

private theorem family_cover {ι : Type*} {κ : ι → Type*} (a w : ι → ℝ)
    (b d : ∀ i, κ i → ℝ) (hw : ∀ i,0<w i)
    (ha : (⋃ i,Ioc (a i) (a i+w i)) = Ioc 0 1)
    (hb : ∀ i,(⋃ j,Ioc (b i j) (b i j+d i j)) = Ioc 0 1) :
    (⋃ p : Sigma κ,Ioc (a p.1+w p.1*b p.1 p.2) (a p.1+w p.1*b p.1 p.2+w p.1*d p.1 p.2))
        = Ioc 0 1 := by
  rw [iUnion_sigma]; simp_rw [interval_image _ _ _ _ (hw _), ← image_iUnion, hb, image_affine_Ioc (hw _)]
  simpa [add_comm] using ha

private theorem family_disjoint {ι : Type*} {κ : ι → Type*} (a w : ι → ℝ)
    (b d : ∀ i, κ i → ℝ) (hw : ∀ i,0<w i)
    (ha : Pairwise fun i j => Disjoint (Ioc (a i) (a i+w i)) (Ioc (a j) (a j+w j)))
    (hc : ∀ i,(⋃ j,Ioc (b i j) (b i j+d i j)) = Ioc 0 1)
    (hd : ∀ i, Pairwise fun j k => Disjoint (Ioc (b i j) (b i j+d i j)) (Ioc (b i k) (b i k+d i k))) :
    Pairwise fun p q : Sigma κ => Disjoint
      (Ioc (a p.1+w p.1*b p.1 p.2) (a p.1+w p.1*b p.1 p.2+w p.1*d p.1 p.2))
      (Ioc (a q.1+w q.1*b q.1 q.2) (a q.1+w q.1*b q.1 q.2+w q.1*d q.1 q.2)) := by
  rintro ⟨i,j⟩ ⟨k,l⟩ hne
  simp only [interval_image _ _ _ _ (hw _)]
  apply Set.disjoint_left.mpr
  rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
  by_cases h : i=k
  · subst k
    have eq : y=x := mul_left_cancel₀ (hw i).ne' (add_right_cancel he)
    exact Set.disjoint_left.mp (hd i (show j≠l from fun h => hne (congrArg (Sigma.mk i) h))) hx (eq ▸ hy)
  · have inside (i : ι) (j : κ i) {x : ℝ} (hx : x ∈ Ioc (b i j) (b i j+d i j)) :
        w i*x+a i ∈ Ioc (a i) (a i+w i) := by
      have hs := Pattern.axis_subset _ _ (hc i) j hx
      exact ⟨by linarith [mul_pos (hw i) hs.1], by linarith [mul_le_mul_of_nonneg_left hs.2 (hw i).le]⟩
    change w k*y+a k = w i*x+a i at he
    exact Set.disjoint_left.mp (ha h) (inside i j hx) (he ▸ inside k l hy)

def insertFamily {ι : Type*} {κ : ι → Type*} (P : Pattern ι) (Q : ∀ i, Pattern (κ i)) : Pattern (Sigma κ) where
  x p := P.x p.1+P.w p.1*(Q p.1).x p.2
  y p := P.y p.1+P.w p.1*(Q p.1).y p.2
  w p := P.w p.1*(Q p.1).w p.2
  wpos p := mul_pos (P.wpos p.1) ((Q p.1).wpos p.2)
  x_cover := family_cover _ _ _ _ P.wpos P.x_cover fun i => (Q i).x_cover
  y_cover := family_cover _ _ _ _ P.wpos P.y_cover fun i => (Q i).y_cover
  x_disjoint := family_disjoint _ _ _ _ P.wpos P.x_disjoint (fun i => (Q i).x_cover) fun i => (Q i).x_disjoint
  y_disjoint := family_disjoint _ _ _ _ P.wpos P.y_disjoint (fun i => (Q i).y_cover) fun i => (Q i).y_disjoint

theorem family_cell {ι : Type*} {κ : ι → Type*} (P : Pattern ι) (Q : ∀ i, Pattern (κ i))
    (i : ι) (j : κ i) : cell (insertFamily P Q) ⟨i,j⟩ = copyPoint P i '' cell (Q i) j :=
  cell_image P (Q i) i j

theorem family_carrier {ι : Type*} {κ : ι → Type*} (P : Pattern ι) (Q : ∀ i, Pattern (κ i)) :
    (insertFamily P Q).carrier = ⋃ i, copyPoint P i '' (Q i).carrier := by
  change (⋃ a : Sigma κ, cell (insertFamily P Q) a) = _
  rw [iUnion_sigma]; simp_rw [family_cell, ← image_iUnion]; rfl

theorem family_subset {ι : Type*} {κ : ι → Type*} (P : Pattern ι) (Q : ∀ i, Pattern (κ i)) :
    (insertFamily P Q).carrier ⊆ P.carrier := by
  rw [family_carrier]
  exact iUnion_subset fun i _ hz => mem_iUnion.mpr ⟨i,copy_carrier_subset P (Q i) i hz⟩

theorem localGeometry_insertFamily {ι : Type*} {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (P : Pattern ι) (Q : ∀ i, Pattern (κ i)) (hP : LocalGeometry P)
    (hQ : ∀ i, LocalGeometry (Q i)) : LocalGeometry (insertFamily P Q) := by
  classical
  rintro ⟨i,j⟩ z hz r hr hr' hsmall
  rw [family_cell] at hz
  obtain ⟨v,hv,rfl⟩ := hz
  change P.w i*(Q i).w j ≤ r/8 at hsmall
  have houter := copy_carrier_subset P (Q i) i (mem_image_of_mem _ (mem_iUnion.mpr ⟨j,hv⟩))
  by_cases h : P.w i ≤ r/8
  · obtain ⟨F,hm,hf⟩ := hP i _ houter r hr hr' h
    refine ⟨F.sigma (fun _ => Finset.univ), ?_, ?_⟩
    · change r/64 ≤ ∑ a ∈ F.sigma (fun i => (Finset.univ : Finset (κ i))), P.w a.1*(Q a.1).w a.2
      simpa [Finset.sum_sigma, ← Finset.mul_sum, Pattern.sum_width] using hm
    · rintro ⟨k,l⟩ hk p hp
      rw [family_cell] at hp
      exact hf k (Finset.mem_sigma.mp hk).1 (copy_carrier_subset P (Q k) k
        (image_mono (subset_iUnion (cell (Q k)) l) hp))
  · have hw := P.wpos i
    have hj : (Q i).w j ≤ (r/P.w i)/8 := by
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<8)).2
      apply (le_div_iff₀ hw).2
      linarith
    obtain ⟨F,hm,hf⟩ := hQ i j v hv (r/P.w i) (div_pos hr hw)
      ((div_le_iff₀ hw).2 (by linarith)) hj
    let emb : κ i ↪ Sigma κ := ⟨Sigma.mk i, sigma_mk_injective⟩
    refine ⟨F.map emb, ?_, ?_⟩
    · rw [Finset.sum_map]; change r/64 ≤ ∑ k ∈ F, P.w i*(Q i).w k
      rw [← Finset.mul_sum]
      have hmul := mul_le_mul_of_nonneg_left hm hw.le
      convert hmul using 1; field_simp
    · intro a ha p hp
      obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨z,hz,rfl⟩ := (family_cell P Q i k) ▸ hp
      rw [Metric.mem_ball,copy_dist]
      have hd : dist z v < r / P.w i := hf k hk hz
      linarith [(lt_div_iff₀ hw).mp hd]

theorem localGeometry_reindex {ι κ : Type*} (P : Pattern ι) (Q : Pattern κ) (e : ι ≃ κ)
    (hc : ∀ i, cell Q (e i) = cell P i) (hw : ∀ i, Q.w (e i) = P.w i)
    (hP : LocalGeometry P) : LocalGeometry Q := by
  classical
  intro j z hz r hr hr' hw'
  obtain ⟨i,rfl⟩ := e.surjective j
  rw [hc] at hz
  rw [hw] at hw'
  obtain ⟨F,hm,hF⟩ := hP i z hz r hr hr' hw'
  refine ⟨F.map e.toEmbedding, ?_, ?_⟩
  · simpa [Finset.sum_map,hw] using hm
  · intro k hk
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hk
    change cell Q (e i) ⊆ _
    rw [hc]; exact hF i hi

theorem localGeometry_insert {ι κ : Type*} [Fintype κ] {P : Pattern ι} {Q : Pattern κ}
    (hP : LocalGeometry P) (hQ : LocalGeometry Q) : LocalGeometry (P.insert Q) :=
  localGeometry_reindex (insertFamily P (fun _ => Q)) (P.insert Q) (Equiv.sigmaEquivProd _ _)
    (fun _ => rfl) (fun _ => rfl) (localGeometry_insertFamily _ _ hP fun _ => hQ)

theorem localGeometry_transpose {ι : Type*} {P : Pattern ι} (hP : LocalGeometry P) :
    LocalGeometry P.transpose := by
  intro i z hz r hr hr' hw
  obtain ⟨F,hm,hF⟩ := hP i z.swap ⟨hz.2,hz.1⟩ r hr hr' hw
  refine ⟨F,hm,fun j hj p hp => ?_⟩
  have h := hF j hj (show p.swap ∈ cell P j from ⟨hp.2,hp.1⟩)
  change max (dist p.2 z.2) (dist p.1 z.1) < r at h
  change max (dist p.1 z.1) (dist p.2 z.2) < r
  rwa [max_comm]

end
end PermutationStrips.CompactPlane
