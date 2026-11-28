import PermutationStrips.CompactRegular

/-! Place one copy of each sample along each of the two diagonals of the half-shift. -/

open Set MeasureTheory
open scoped BigOperators

namespace PermutationStrips.CompactPlane

noncomputable section

private def swapTwo := Pattern.equalGrid (by decide : 0<2) (Equiv.swap (0:Fin 2) 1)

/-- Two diagonals in opposite half-squares, each with M equal components. -/
def halfShift {M : ℕ} (hM : 0<M) : Pattern (Fin 2 × Fin M) :=
  swapTwo.insert (Pattern.equalGrid hM (Equiv.refl _))

def ensemble {M : ℕ} (hM : 0<M) {κ : Fin M → Type*} (Q : ∀ j, Pattern (κ j)) :
    Pattern (Σ i : Fin 2 × Fin M, κ i.2) := insertFamily (halfShift hM) fun i => Q i.2

theorem ensemble_local {M : ℕ} (hM : 0<M) {κ : Fin M → Type*} [∀ i,Fintype (κ i)]
    (Q : ∀ j, Pattern (κ j)) (hQ : ∀ j, LocalGeometry (Q j)) : LocalGeometry (ensemble hM Q) := by
  have outer : LocalGeometry swapTwo := by
    intro i z hz r hr hr8 hsmall
    have w : swapTwo.w i = 1/2 := by simp [swapTwo,Pattern.equalGrid]
    refine ⟨{i},by simp [w]; linarith,?_⟩
    intro j hj p hp
    have he : j=i := Finset.mem_singleton.mp hj
    subst j
    have h₁ := cell_subset_unit swapTwo i hp
    have h₂ := cell_subset_unit swapTwo i hz
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    rw [w] at hsmall
    exact ⟨abs_lt.mpr ⟨by linarith [h₁.1.1,h₂.1.2],by linarith [h₁.1.2,h₂.1.1]⟩,
      abs_lt.mpr ⟨by linarith [h₁.2.1,h₂.2.2],by linarith [h₁.2.2,h₂.2.1]⟩⟩
  exact localGeometry_insertFamily _ _ (localGeometry_insert outer (localGeometry_equalGrid_diag hM))
    (fun j => hQ j.2)

theorem ensemble_width {M : ℕ} (hM : 0<M) {κ : Fin M → Type*} (Q : ∀ j, Pattern (κ j))
    (i : Σ k : Fin 2 × Fin M, κ k.2) : (ensemble hM Q).w i ≤ 1/2 := by
  obtain ⟨i,k⟩ := i
  have hx := Pattern.axis_bounds (Q i.2).x (Q i.2).w (Q i.2).wpos (Q i.2).x_cover k
  have hp : 0 < (M:ℝ) := by exact_mod_cast hM
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
  change (1 / ((2:ℕ):ℝ) * (1/(M:ℝ))) * (Q i.2).w k ≤ 1/2
  norm_num
  field_simp
  linarith [hx.1,hx.2]

theorem ensemble_card {M : ℕ} {κ : Fin M → Type*} [∀ i,Fintype (κ i)] {N : ℝ}
    (hN : ∀ i, (Fintype.card (κ i):ℝ) ≤ N) :
    (Fintype.card (Σ i : Fin 2 × Fin M, κ i.2) : ℝ) ≤ 2*M*N := by
  rw [Fintype.card_sigma, Nat.cast_sum]
  calc
    _ ≤ ∑ _i : Fin 2 × Fin M, N := Finset.sum_le_sum fun i _ => hN i.2
    _ = _ := by simp [Fintype.card_prod]

private theorem halfShift_diamond {M : ℕ} (hM : 0<M) (p : ℝ × ℝ) (hp : p ∈ (halfShift hM).carrier) :
    |p.1-1/2| + |p.2-1/2| ≤ 1/2 + 1/(2*(M:ℝ)) := by
  change p ∈ (swapTwo.insert (Pattern.equalGrid hM (Equiv.refl _))).carrier at hp
  rw [carrier_insert] at hp
  obtain ⟨i, q,hq,rfl⟩ := mem_iUnion.mp hp
  have hu := carrier_subset_unit _ hq
  obtain ⟨j,hj⟩ := mem_iUnion.mp hq
  have hx : q.1 ∈ Icc (Pattern.gridStart j) (Pattern.gridStart j+1/M) := hj.1
  have hy : q.2 ∈ Icc (Pattern.gridStart j) (Pattern.gridStart j+1/M) := hj.2
  have qx := hu.1; have qy := hu.2
  have half : 1/(2*(M:ℝ)) = (1/(M:ℝ))/2 := by ring
  rw [half]
  simp only [one_div] at hx hy
  fin_cases i <;>
    norm_num [copyPoint, swapTwo, Pattern.equalGrid, Pattern.gridStart] <;>
    (first | rw [abs_of_nonpos (by linarith [qx.2]),abs_of_nonneg (by linarith [qy.1])]
           | rw [abs_of_nonneg (by linarith [qx.1]),abs_of_nonpos (by linarith [qy.2])]) <;>
    linarith [hx.1,hx.2,hy.1,hy.2]

private theorem halfShift_coord_sum {M : ℕ} (hM : 0<M) {p q : ℝ × ℝ}
    (hp : p ∈ (halfShift hM).carrier) (hq : q ∈ (halfShift hM).carrier) :
    |p.1-q.1| + |p.2-q.2| ≤ 1+1/(M:ℝ) := by
  have u := halfShift_diamond hM p hp
  have v := halfShift_diamond hM q hq
  have tri (x y : ℝ) : |x-y| ≤ |x-1/2|+|y-1/2| := by
    rw [← Real.dist_eq, ← Real.dist_eq, ← Real.dist_eq, dist_comm y (1/2:ℝ)]
    exact dist_triangle ..
  have he : 1/(2*(M:ℝ)) = (1/(M:ℝ))/2 := by ring
  linarith [tri p.1 q.1,tri p.2 q.2]

theorem ensemble_diameter {M : ℕ} (hM : 0<M) {κ : Fin M → Type*} (Q : ∀ j, Pattern (κ j)) :
    Metric.diam (toEuclidean '' (ensemble hM Q).carrier) ≤ 1+1/(M:ℝ) := by
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩
  exact (euclidean_dist_le_sum p q).trans (halfShift_coord_sum hM
    (family_subset (halfShift hM) _ hp) (family_subset (halfShift hM) _ hq))

/-- The unit square caps each coordinate difference at one. Intersecting this
constraint with the half-shift diamond makes the Euclidean diameter excess quadratic. -/
theorem ensemble_diameter_sq {M : ℕ} (hM : 0<M) {κ : Fin M → Type*} (Q : ∀ j, Pattern (κ j)) :
    Metric.diam (toEuclidean '' (ensemble hM Q).carrier) ≤ 1+1/(2*(M:ℝ)^2) := by
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩
  let a := |p.1-q.1|
  let b := |p.2-q.2|
  let d := 1/(M:ℝ)
  have hsum : a+b ≤ 1+d := halfShift_coord_sum hM
    (family_subset (halfShift hM) _ hp) (family_subset (halfShift hM) _ hq)
  have up := carrier_subset_unit _ hp
  have uq := carrier_subset_unit _ hq
  have ha : a ≤ 1 := abs_le.mpr ⟨by linarith [up.1.1,uq.1.2],by linarith [up.1.2,uq.1.1]⟩
  have hb : b ≤ 1 := abs_le.mpr ⟨by linarith [up.2.1,uq.2.2],by linarith [up.2.2,uq.2.1]⟩
  have hs : a^2+b^2 ≤ 1+d^2 := by
    rcases le_total (a+b) 1 with h|h
    · nlinarith [mul_self_le_mul_self (add_nonneg (abs_nonneg _) (abs_nonneg _)) h,
        mul_nonneg (abs_nonneg (p.1-q.1)) (abs_nonneg (p.2-q.2)),sq_nonneg d]
    · have ht := mul_self_le_mul_self (sub_nonneg.mpr h) (show a+b-1 ≤ d by linarith)
      nlinarith only [ht,mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  rw [WithLp.prod_dist_eq_of_L2]
  change Real.sqrt (a^2+b^2) ≤ _
  have he : 1/(2*(M:ℝ)^2) = d^2/2 := by dsimp [d]; ring
  rw [he]
  exact Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith only [hs,sq_nonneg (d^2/2)]⟩

/-- The section of the packed sample is bounded by its arithmetic mean. -/
theorem length_ensemble_le {M : ℕ} (hM : 0<M) {κ : Fin M → Type*} (Q : ∀ j, Pattern (κ j))
    {t : ℝ} (_ht : t ∈ Icc 0 1) : volume.real ((ensemble hM Q).sectionAt t) ≤
      (∑ j, volume.real ((Q j).sectionAt t)) / M := by
  let P := halfShift hM
  let F (i : Fin 2 × Fin M) := (fun x => P.start t i+P.w i*x) '' (Q i.2).sectionAt t
  have eq : (ensemble hM Q).sectionAt t = ⋃ i, F i := by
    change projection t '' (insertFamily P _).carrier = _
    rw [family_carrier,image_iUnion]
    apply iUnion_congr; intro i
    unfold F Pattern.sectionAt
    rw [image_image,image_image]
    congr 1; funext z; dsimp [projection,copyPoint,Pattern.start]; ring
  have measureF (i : Fin 2 × Fin M) : volume.real (F i) = P.w i * volume.real ((Q i.2).sectionAt t) := by
    let w := P.w i
    let a := P.start t i
    let T := (Q i.2).sectionAt t
    have hw : 0<w := P.wpos i
    have he : F i = (fun x:ℝ => x + -a) ⁻¹' ((fun x:ℝ => w⁻¹*x) ⁻¹' T) := by
      ext x; change (∃ y ∈ T,a+w*y=x) ↔ w⁻¹*(x + -a) ∈ T
      constructor
      · rintro ⟨y,hy,rfl⟩; convert hy using 1; field_simp; ring
      · intro hy; refine ⟨_,hy,?_⟩; field_simp; ring
    rw [measureReal_def,he,measure_preimage_add_right,Real.volume_preimage_mul_left (inv_ne_zero hw.ne'),
      inv_inv, abs_of_pos hw, ENNReal.toReal_mul, ENNReal.toReal_ofReal hw.le]
    rfl
  rw [eq]
  apply (measureReal_iUnion_fintype_le F).trans
  simp_rw [measureF]
  change (∑ i : Fin 2 × Fin M, (1/((2:ℕ):ℝ) * (1/(M:ℝ))) * volume.real ((Q i.2).sectionAt t)) ≤ _
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← Finset.mul_sum]
  norm_num; ring_nf; exact le_rfl

end
end PermutationStrips.CompactPlane
