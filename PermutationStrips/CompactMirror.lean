import PermutationStrips.CompactFamily
import PermutationStrips.Angular

/-! Reflection of a finite interval matching, including the endpoint conventions. -/

open Set Filter MeasureTheory
open scoped Topology
namespace PermutationStrips.CompactPlane
noncomputable section

private theorem opposite_cover {ι : Type*} [Finite ι] (a w : ι → ℝ) (hw : ∀ i, 0<w i)
    (hcov : (⋃ i,Ioc (a i) (a i+w i))=Ioc 0 1) :
    (⋃ i, Ico (a i) (a i+w i))=Ico 0 1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,h₁,h₂⟩ := mem_iUnion.mp hx
    obtain ⟨hb,ht⟩ := Pattern.axis_bounds a w hw hcov i
    exact ⟨hb.trans h₁,h₂.trans_le ht⟩
  · intro hx
    by_contra hx'
    have right : ∀ᶠ y : ℝ in 𝓝[>] x, x<y := self_mem_nhdsWithin
    have absent (i) : ∀ᶠ y : ℝ in 𝓝[>] x, y∉Ioc (a i) (a i+w i) := by
      by_cases h : x < a i
      · filter_upwards [show Iio (a i) ∈ 𝓝[>] x from mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h)] with y hy
        exact fun hy' => hy.not_gt hy'.1
      · have he : a i+w i ≤ x := le_of_not_gt fun h' => hx' (mem_iUnion.mpr ⟨i,le_of_not_gt h,h'⟩)
        filter_upwards [right] with y hy
        exact fun hy' => (he.trans_lt hy).not_ge hy'.2
    have near : ∀ᶠ y : ℝ in 𝓝[>] x, y ∈ Ioc 0 1 := by
      filter_upwards [right,show Iio 1 ∈ 𝓝[>] x from mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx.2)] with y hy hy'
      exact ⟨hx.1.trans_lt hy,hy'.le⟩
    rw [←hcov] at near
    obtain ⟨y,hy,hy'⟩ := (near.and (eventually_all.mpr absent)).exists
    obtain ⟨i,hi⟩ := mem_iUnion.mp hy
    exact hy' i hi

private theorem reflected_mem (a w x : ℝ) :
    x ∈ Ioc (1-a-w) (1-a-w+w) ↔ 1-x ∈ Ico a (a+w) :=
  ⟨fun hx => ⟨by linarith [hx.2],by linarith [hx.1]⟩,
   fun hx => ⟨by linarith [hx.2],by linarith [hx.1]⟩⟩

private theorem reflected_cover {ι : Type*} [Finite ι] (P : Pattern ι) :
    (⋃ i, Ioc (1-P.y i-P.w i) (1-P.y i-P.w i+P.w i))=Ioc 0 1 := by
  ext x
  simp only [mem_iUnion,reflected_mem]
  rw [← mem_iUnion,opposite_cover P.y P.w P.wpos P.y_cover]
  exact ⟨fun hx => ⟨by linarith [hx.2],by linarith [hx.1]⟩,
    fun hx => ⟨by linarith [hx.2],by linarith [hx.1]⟩⟩

private theorem reflected_disjoint {ι : Type*} (P : Pattern ι) : Pairwise fun i j =>
    Disjoint (Ioc (1-P.y i-P.w i) (1-P.y i-P.w i+P.w i))
      (Ioc (1-P.y j-P.w j) (1-P.y j-P.w j+P.w j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hi hj
  have hi' := (reflected_mem _ _ _).mp hi
  have hj' := (reflected_mem _ _ _).mp hj
  let z := min (P.y i+P.w i) (P.y j+P.w j)
  have hz : 1-x<z := lt_min hi'.2 hj'.2
  exact disjoint_left.mp (P.y_disjoint hij)
    (show z ∈ Ioc _ _ from ⟨hi'.1.trans_lt hz, min_le_left _ _⟩)
    (show z ∈ Ioc _ _ from ⟨hj'.1.trans_lt hz, min_le_right _ _⟩)

def mirrorPattern {ι : Type*} [Finite ι] (P : Pattern ι) : Pattern ι where
  x := P.x
  y i := 1-P.y i-P.w i
  w := P.w
  wpos := P.wpos
  x_cover := P.x_cover
  y_cover := reflected_cover P
  x_disjoint := P.x_disjoint
  y_disjoint := reflected_disjoint P

theorem mem_cell_mirror {ι : Type*} [Finite ι] (P : Pattern ι) (i : ι) (z : ℝ × ℝ) :
    z ∈ cell (mirrorPattern P) i ↔ Angular.mirror z ∈ cell P i := by
  change (_ ∧ 1-P.y i-P.w i ≤ z.2 ∧ z.2 ≤ 1-P.y i-P.w i+P.w i) ↔
    (_ ∧ P.y i ≤ 1-z.2 ∧ 1-z.2 ≤ P.y i+P.w i)
  exact and_congr_right fun _ => ⟨fun h => ⟨by linarith [h.2],by linarith [h.1]⟩,
    fun h => ⟨by linarith [h.2],by linarith [h.1]⟩⟩

theorem carrier_mirror {ι : Type*} [Finite ι] (P : Pattern ι) :
    (mirrorPattern P).carrier = Angular.mirror '' P.carrier := by
  ext z
  change z ∈ ⋃ i, cell (mirrorPattern P) i ↔ z ∈ Angular.mirror '' ⋃ i, cell P i
  constructor
  · intro hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact ⟨Angular.mirror z, mem_iUnion.mpr ⟨i,(mem_cell_mirror P i z).mp hi⟩,by simp [Angular.mirror]⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i,(mem_cell_mirror P i _).mpr (by simpa [Angular.mirror] using hi)⟩

theorem localGeometry_mirror {ι : Type*} [Finite ι] {P : Pattern ι} (hP : LocalGeometry P) :
    LocalGeometry (mirrorPattern P) := by
  intro i z hz r hr hr' hwi
  obtain ⟨F,hm,hf⟩ := hP i (Angular.mirror z) ((mem_cell_mirror P i z).mp hz) r hr hr' hwi
  refine ⟨F,hm,fun j hj p hp => ?_⟩
  have h := hf j hj ((mem_cell_mirror P j p).mp hp)
  change max (dist p.1 z.1) (dist (1-p.2) (1-z.2)) < r at h
  change max (dist p.1 z.1) (dist p.2 z.2) < r
  rwa [dist_sub_left] at h

end
end PermutationStrips.CompactPlane
