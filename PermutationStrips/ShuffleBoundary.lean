import PermutationStrips.AngularBlockPath
import PermutationStrips.CompactPlane

/-! The outermost shuffle forces one coordinate boundary into the opposite half
of the other coordinate. This persists in every descendant of positive depth. -/

open Set

namespace PermutationStrips.Shuffle

theorem twoColors_left_boundary {ι : Type*} (P : Pattern ι) (z : ℝ × ℝ)
    (hz : z ∈ (twoColors P).carrier) (hx : z.1=0) : 1/2 ≤ z.2 := by
  obtain ⟨⟨b,i⟩,hi⟩ := mem_iUnion.mp hz
  cases b
  · have hy := hi.2.1
    change (P.y i+1)/2 ≤ z.2 at hy
    linarith [(Pattern.axis_bounds P.y P.w P.wpos P.y_cover i).1]
  · have hl := hi.1.1
    change P.x i + P.w i/2 ≤ z.1 at hl
    linarith [(Pattern.axis_bounds P.x P.w P.wpos P.x_cover i).1,P.wpos i]

end PermutationStrips.Shuffle

namespace PermutationStrips.AngularBlock

/-- A point on the first coordinate boundary is displaced by at least half in
one of the two orientations, uniformly in the scales and all inner shuffles. -/
theorem path_boundary (p : Path) (hp : 0<p.depth) :
    (∀ z ∈ p.pattern.carrier, z.1=0 → (1/2:ℝ) ≤ z.2) ∨
    (∀ z ∈ p.pattern.carrier, z.2=0 → (1/2:ℝ) ≤ z.1) := by
  cases p with
  | seed => exact (Nat.lt_irrefl 0 hp).elim
  | step u hu b inner =>
    cases b
    · refine Or.inl fun z hz hx => Shuffle.twoColors_left_boundary (Shuffle.basePartition u hu) z ?_ hx
      exact CompactPlane.carrier_insert_subset _ inner.pattern hz
    · refine Or.inr fun z hz hy => Shuffle.twoColors_left_boundary (Shuffle.basePartition u hu) z.swap ?_ hy
      have ho := CompactPlane.carrier_insert_subset (Shuffle.orientedPattern u hu true) inner.pattern hz
      obtain ⟨i,hi⟩ := mem_iUnion.mp ho
      exact mem_iUnion.mpr ⟨i,hi.2,hi.1⟩

end PermutationStrips.AngularBlock
