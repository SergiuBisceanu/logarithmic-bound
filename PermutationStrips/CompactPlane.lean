import PermutationStrips.Insertion
import PermutationStrips.ShufflePattern
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Normed.Lp.ProdLp

/-! Geometry of the finite squares used to construct the compact limit. -/

open Set MeasureTheory
open scoped BigOperators Topology

namespace PermutationStrips.CompactPlane

abbrev EuclideanPlane := WithLp 2 (ℝ × ℝ)
abbrev toEuclidean : (ℝ × ℝ) → EuclideanPlane := WithLp.toLp 2

def cell {ι : Type*} (P : Pattern ι) (i : ι) : Set (ℝ × ℝ) :=
  Icc (P.x i) (P.x i + P.w i) ×ˢ Icc (P.y i) (P.y i + P.w i)

def copyPoint {ι : Type*} (P : Pattern ι) (i : ι) (z : ℝ × ℝ) : ℝ × ℝ :=
  (P.x i + P.w i*z.1, P.y i + P.w i*z.2)

theorem copy_dist {ι : Type*} (P : Pattern ι) (i : ι) (p z : ℝ × ℝ) :
    dist (copyPoint P i p) (copyPoint P i z) = P.w i * dist p z := by
  rw [Prod.dist_eq, Prod.dist_eq, mul_max_of_nonneg _ _ (P.wpos i).le]
  simp only [copyPoint, Real.dist_eq, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_pos (P.wpos i)]

theorem euclidean_copy_dist {ι : Type*} (P : Pattern ι) (i : ι) (p z : ℝ × ℝ) :
    dist (toEuclidean (copyPoint P i p)) (toEuclidean (copyPoint P i z)) =
      P.w i * dist (toEuclidean p) (toEuclidean z) := by
  change dist (toEuclidean ((P.x i,P.y i) + P.w i • p))
    (toEuclidean ((P.x i,P.y i) + P.w i • z)) = _
  simp [WithLp.toLp_add, WithLp.toLp_smul, dist_smul₀, Real.norm_eq_abs, abs_of_pos (P.wpos i)]

theorem cell_subset_unit {ι : Type*} (P : Pattern ι) (i : ι) :
    cell P i ⊆ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 := by
  have hx := Pattern.axis_bounds P.x P.w P.wpos P.x_cover i
  have hy := Pattern.axis_bounds P.y P.w P.wpos P.y_cover i
  intro z hz
  exact ⟨⟨hx.1.trans hz.1.1,hz.1.2.trans hx.2⟩,hy.1.trans hz.2.1,hz.2.2.trans hy.2⟩

theorem carrier_subset_unit {ι : Type*} (P : Pattern ι) :
    P.carrier ⊆ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 := by
  intro z hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  exact cell_subset_unit P i hi

theorem compact_carrier {ι : Type*} [Finite ι] (P : Pattern ι) : IsCompact P.carrier :=
  isCompact_iUnion fun _ => isCompact_Icc.prod isCompact_Icc

private theorem closed_axis {ι : Type*} [Finite ι] (a w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hc : (⋃ i, Ioc (a i) (a i+w i)) = Ioc 0 1) : (⋃ i, Icc (a i) (a i+w i)) = Icc 0 1 := by
  calc
    _ = ⋃ i, closure (Ioc (a i) (a i+w i)) := by
      congr 1; funext i; exact (closure_Ioc (by linarith [hw i])).symm
    _ = closure (⋃ i, Ioc (a i) (a i+w i)) := (closure_iUnion_of_finite _).symm
    _ = Icc 0 1 := by rw [hc,closure_Ioc zero_ne_one]

theorem fst_carrier {ι : Type*} [Finite ι] (P : Pattern ι) :
    Prod.fst '' P.carrier = Icc (0:ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩; exact (carrier_subset_unit P hp).1
  · intro hx
    rw [← closed_axis P.x P.w P.wpos P.x_cover] at hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact ⟨(x,P.y i), mem_iUnion.mpr ⟨i,hi,le_rfl,by linarith [P.wpos i]⟩,rfl⟩

theorem snd_carrier {ι : Type*} [Finite ι] (P : Pattern ι) :
    Prod.snd '' P.carrier = Icc (0:ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨p,hp,rfl⟩; exact (carrier_subset_unit P hp).2
  · intro hy
    rw [← closed_axis P.y P.w P.wpos P.y_cover] at hy
    obtain ⟨i,hi⟩ := mem_iUnion.mp hy
    exact ⟨(P.x i,y), mem_iUnion.mpr ⟨i,⟨le_rfl,by linarith [P.wpos i]⟩,hi⟩,rfl⟩

theorem cell_image {ι κ : Type*} (P : Pattern ι) (Q : Pattern κ) (i : ι) (j : κ) :
    cell (P.insert Q) (i,j) = copyPoint P i '' cell Q j := by
  ext z
  constructor
  · intro hz
    let p := ((z.1-P.x i)/P.w i, (z.2-P.y i)/P.w i)
    have hw := P.wpos i
    obtain ⟨⟨hx,hx'⟩,hy,hy'⟩ := hz
    change P.x i+P.w i*Q.x j ≤ z.1 at hx
    change z.1 ≤ P.x i+P.w i*Q.x j+P.w i*Q.w j at hx'
    change P.y i+P.w i*Q.y j ≤ z.2 at hy
    change z.2 ≤ P.y i+P.w i*Q.y j+P.w i*Q.w j at hy'
    refine ⟨p,⟨⟨(le_div_iff₀ hw).2 (by linarith),(div_le_iff₀ hw).2 (by nlinarith)⟩,
      (le_div_iff₀ hw).2 (by linarith),(div_le_iff₀ hw).2 (by nlinarith)⟩,?_⟩
    ext <;> dsimp [copyPoint,p] <;> field_simp <;> ring
  · rintro ⟨p,⟨⟨hx,hx'⟩,hy,hy'⟩,rfl⟩
    have hw := (P.wpos i).le
    change (_ ≤ P.x i+P.w i*p.1 ∧ P.x i+P.w i*p.1 ≤ _) ∧
      (_ ≤ P.y i+P.w i*p.2 ∧ P.y i+P.w i*p.2 ≤ _)
    dsimp [Pattern.insert]
    constructor <;> constructor <;>
      nlinarith [mul_le_mul_of_nonneg_left hx hw,mul_le_mul_of_nonneg_left hx' hw,
        mul_le_mul_of_nonneg_left hy hw,mul_le_mul_of_nonneg_left hy' hw]

theorem carrier_insert {ι κ : Type*} (P : Pattern ι) (Q : Pattern κ) :
    (P.insert Q).carrier = ⋃ i, copyPoint P i '' Q.carrier := by
  change (⋃ a : ι × κ, cell (P.insert Q) a) = _
  rw [iUnion_prod']
  simp_rw [cell_image, ← image_iUnion]
  rfl

theorem copy_carrier_subset {ι κ : Type*} (P : Pattern ι) (Q : Pattern κ) (i : ι) :
    copyPoint P i '' Q.carrier ⊆ cell P i := by
  rintro _ ⟨z,hz,rfl⟩
  obtain ⟨hx,hy⟩ := carrier_subset_unit Q hz
  change (_ ≤ P.x i+P.w i*z.1 ∧ P.x i+P.w i*z.1 ≤ _) ∧
    (_ ≤ P.y i+P.w i*z.2 ∧ P.y i+P.w i*z.2 ≤ _)
  have hw := (P.wpos i).le
  constructor <;> constructor <;> nlinarith [mul_nonneg hw hx.1,mul_nonneg hw hy.1,
    mul_le_mul_of_nonneg_left hx.2 hw,mul_le_mul_of_nonneg_left hy.2 hw]

theorem carrier_insert_subset {ι κ : Type*} (P : Pattern ι) (Q : Pattern κ) :
    (P.insert Q).carrier ⊆ P.carrier := by
  rw [carrier_insert]
  exact iUnion_subset fun i _ hz => mem_iUnion.mpr ⟨i,copy_carrier_subset P Q i hz⟩

/-- Around a sufficiently small component, a fixed fraction of the radius is
carried by entire components inside the open sup-metric ball. -/
def LocalGeometry {ι : Type*} (P : Pattern ι) : Prop :=
  ∀ i (z : ℝ × ℝ), z ∈ cell P i → ∀ r : ℝ, 0 < r → r ≤ 8 → P.w i ≤ r/8 →
    ∃ F : Finset ι, r/64 ≤ ∑ j ∈ F, P.w j ∧ ∀ j ∈ F, cell P j ⊆ Metric.ball z r

theorem euclidean_dist_le_sum (p q : ℝ × ℝ) :
    dist (toEuclidean p) (toEuclidean q) ≤ |p.1-q.1|+|p.2-q.2| := by
  rw [WithLp.prod_dist_eq_of_L2]
  change Real.sqrt (|p.1-q.1|^2 + |p.2-q.2|^2) ≤ _
  apply Real.sqrt_le_iff.mpr
  exact ⟨add_nonneg (abs_nonneg _) (abs_nonneg _), by nlinarith [mul_nonneg (abs_nonneg (p.1-q.1)) (abs_nonneg (p.2-q.2))]⟩

end PermutationStrips.CompactPlane
