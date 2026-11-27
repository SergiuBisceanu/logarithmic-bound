import PermutationStrips.Pattern

/-! Composition and transposition of finite permutation patterns. -/

open Set MeasureTheory

namespace PermutationStrips.Pattern

private theorem affineIoc {w : ℝ} (hw : 0 < w) (a b v : ℝ) :
    Ioc (a+w*b) (a+w*b+w*v) = (fun z => a+w*z) '' Ioc b (b+v) := by
  simp_rw [add_comm a (w*_)]
  rw [image_affine_Ioc hw]
  congr 1
  ring

private theorem fiber_cover {κ : Type*} (b v : κ → ℝ)
    (hc : (⋃ j, Ioc (b j) (b j+v j)) = Ioc 0 1) {w : ℝ} (hw : 0 < w) (a : ℝ) :
    (⋃ j, Ioc (a+w*b j) (a+w*b j+w*v j)) = Ioc a (a+w) := by
  simp_rw [affineIoc hw, ← image_iUnion, hc]
  simpa using (affineIoc hw a 0 1).symm

private theorem cover {ι κ : Type*} (a w : ι → ℝ) (b v : κ → ℝ)
    (hw : ∀ i, 0 < w i) (ha : (⋃ i, Ioc (a i) (a i+w i)) = Ioc 0 1)
    (hb : (⋃ j, Ioc (b j) (b j+v j)) = Ioc 0 1) :
    (⋃ p : ι × κ, Ioc (a p.1+w p.1*b p.2) (a p.1+w p.1*b p.2+w p.1*v p.2)) = Ioc 0 1 := by
  rw [iUnion_prod']
  simpa only [fiber_cover b v hb (hw _) _] using ha

private theorem disjoint {ι κ : Type*} (a w : ι → ℝ) (b v : κ → ℝ)
    (hw : ∀ i, 0 < w i) (hb : (⋃ j, Ioc (b j) (b j+v j)) = Ioc 0 1)
    (hda : Pairwise fun i j => Disjoint (Ioc (a i) (a i+w i)) (Ioc (a j) (a j+w j)))
    (hdb : Pairwise fun i j => Disjoint (Ioc (b i) (b i+v i)) (Ioc (b j) (b j+v j))) :
    Pairwise fun p q : ι × κ => Disjoint
      (Ioc (a p.1+w p.1*b p.2) (a p.1+w p.1*b p.2+w p.1*v p.2))
      (Ioc (a q.1+w q.1*b q.2) (a q.1+w q.1*b q.2+w q.1*v q.2)) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ hn
  by_cases hi : i = i'
  · subst i'
    have hj : j ≠ j' := fun h => hn (by rw [h])
    simp only [affineIoc (hw i)]
    apply Set.disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ ⟨z',hz',he⟩
    have he' : z' = z := mul_left_cancel₀ (hw i).ne' (add_left_cancel he)
    exact (Set.disjoint_left.mp (hdb hj)) hz (he' ▸ hz')
  · have sub (i : ι) (j : κ) : Ioc (a i+w i*b j) (a i+w i*b j+w i*v j) ⊆ Ioc (a i) (a i+w i) := by
      rw [← fiber_cover b v hb (hw i)]
      intro x hx; exact mem_iUnion.mpr ⟨j,hx⟩
    exact (hda hi).mono (sub i j) (sub i' j')

/-- Insert a homothetic copy of Q in each component of P. -/
def insert {ι κ : Type*} (P : Pattern ι) (Q : Pattern κ) : Pattern (ι × κ) where
  x p := P.x p.1 + P.w p.1 * Q.x p.2
  y p := P.y p.1 + P.w p.1 * Q.y p.2
  w p := P.w p.1 * Q.w p.2
  wpos p := mul_pos (P.wpos p.1) (Q.wpos p.2)
  x_cover := cover _ _ _ _ P.wpos P.x_cover Q.x_cover
  y_cover := cover _ _ _ _ P.wpos P.y_cover Q.y_cover
  x_disjoint := disjoint _ _ _ _ P.wpos Q.x_cover P.x_disjoint Q.x_disjoint
  y_disjoint := disjoint _ _ _ _ P.wpos Q.y_cover P.y_disjoint Q.y_disjoint

/-- Exchange the two endpoint axes. -/
def transpose {ι : Type*} (P : Pattern ι) : Pattern ι where
  x := P.y
  y := P.x
  w := P.w
  wpos := P.wpos
  x_cover := P.y_cover
  y_cover := P.x_cover
  x_disjoint := P.y_disjoint
  y_disjoint := P.x_disjoint

theorem start_insert {ι κ : Type*} (P : Pattern ι) (Q : Pattern κ) (t : ℝ) (i : ι) (j : κ) :
    (P.insert Q).start t (i,j) = P.start t i + P.w i * Q.start t j := by
  unfold start projection insert
  dsimp
  ring

theorem start_transpose {ι : Type*} (P : Pattern ι) (t : ℝ) (i : ι) :
    P.transpose.start t i = P.start (1-t) i := by
  unfold start projection transpose
  dsimp
  ring

/-- Projection commutes with the insertion homotheties. The inner section has height t. -/
theorem sectionAt_insert {ι κ : Type*} (P : Pattern ι) (Q : Pattern κ) {t : ℝ}
    (ht : t ∈ Icc 0 1) :
    (P.insert Q).sectionAt t = ⋃ i, (fun z => P.start t i + P.w i*z) '' Q.sectionAt t := by
  simp only [sectionAt_eq _ ht, iUnion_prod', image_iUnion]
  apply iUnion_congr
  intro i
  apply iUnion_congr
  intro j
  rw [start_insert]
  change Icc _ (P.start t i + P.w i*Q.start t j + P.w i*Q.w j) = _
  simp_rw [add_comm (P.start t i) (P.w i * _)]
  rw [image_affine_Icc' (P.wpos i)]
  congr 1
  ring

theorem sectionAt_transpose {ι : Type*} (P : Pattern ι) {t : ℝ} (ht : t ∈ Icc 0 1) :
    P.transpose.sectionAt t = P.sectionAt (1-t) := by
  have h : 1-t ∈ Icc (0:ℝ) 1 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  simp only [sectionAt_eq _ ht, sectionAt_eq _ h, start_transpose]
  rfl

end PermutationStrips.Pattern
