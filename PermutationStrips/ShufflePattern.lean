import PermutationStrips.Insertion
import PermutationStrips.Shuffle

/-! The actual outer pattern for the real-parameter shuffle, including its final two cells. -/

open Set MeasureTheory
open scoped Interval BigOperators

namespace PermutationStrips.Shuffle

noncomputable section

private def edge (u : ℝ) (j : ℕ) : ℝ := if j < ⌊u⌋₊ then j else u

private theorem edge_index {u : ℝ} (i : Fin ⌊u⌋₊) : edge u i = i.val := if_pos i.isLt

private theorem edge_step {u : ℝ} (i : Fin ⌊u⌋₊) (hu : 0 ≤ u) : (i.val : ℝ) < edge u (i.val+1) := by
  unfold edge
  split_ifs with h
  · exact_mod_cast Nat.lt_succ_self _
  · have hi : (i.val : ℝ) < ⌊u⌋₊ := by exact_mod_cast i.isLt
    exact hi.trans_le (Nat.floor_le hu)

private theorem edge_le {u : ℝ} (hu : 0 ≤ u) (j : ℕ) : edge u j ≤ u := by
  dsimp [edge]
  split_ifs with h
  · exact (show (j:ℝ) ≤ ⌊u⌋₊ by exact_mod_cast h.le).trans (Nat.floor_le hu)
  · exact le_rfl

private theorem exists_between_edges (g : ℕ → ℝ) (n : ℕ) {x : ℝ} (hx : g 0 < x)
    (hn : x ≤ g n) : ∃ i < n, g i < x ∧ x ≤ g (i+1) := by
  induction n with
  | zero => linarith
  | succ n ih =>
    by_cases h : x ≤ g n
    · obtain ⟨i,hi,hz⟩ := ih h
      exact ⟨i,by omega,hz⟩
    · exact ⟨n,by omega,lt_of_not_ge h,hn⟩

/-- The one-dimensional partition is the unit grid through its penultimate
endpoint; the last interval absorbs the fractional part of `u`. -/
def basePartition (u : ℝ) (hu : 4 ≤ u) : Pattern (Fin ⌊u⌋₊) := by
  let a := fun i : Fin ⌊u⌋₊ => (i.val:ℝ)/u
  let w := fun i : Fin ⌊u⌋₊ => (edge u (i.val+1) - (i.val:ℝ))/u
  have hpos : 0 < u := by linarith
  have hn : 0 < ⌊u⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hright (i : Fin ⌊u⌋₊) : a i+w i = edge u (i.val+1)/u := by dsimp [a,w]; ring
  have hcov : (⋃ i, Ioc (a i) (a i+w i)) = Ioc 0 1 := by
    ext z
    constructor
    · intro hz
      obtain ⟨i,hz⟩ := mem_iUnion.mp hz
      rw [hright] at hz
      exact ⟨(div_nonneg (Nat.cast_nonneg _) hpos.le).trans_lt hz.1,
        hz.2.trans ((div_le_one hpos).mpr (edge_le hpos.le _))⟩
    · intro hz
      have he0 : edge u 0 = 0 := by simp [edge,hn]
      have hen : edge u ⌊u⌋₊ = u := by simp [edge]
      obtain ⟨j,hj,h₁,h₂⟩ := exists_between_edges (edge u) ⌊u⌋₊
        (x:=z*u) (by rw [he0]; exact mul_pos hz.1 hpos) (by rw [hen]; nlinarith [hz.2,mul_nonneg (sub_nonneg.mpr hz.2) hpos.le])
      let i : Fin ⌊u⌋₊ := ⟨j,hj⟩
      refine mem_iUnion.mpr ⟨i,?_⟩
      rw [hright]
      exact ⟨(div_lt_iff₀ hpos).mpr (by simpa [edge,hj,i] using h₁),(le_div_iff₀ hpos).mpr h₂⟩
  have hsep (i j : Fin ⌊u⌋₊) (hij : i<j) : Disjoint (Ioc (a i) (a i+w i)) (Ioc (a j) (a j+w j)) := by
    apply Ioc_disjoint_Ioc_of_le
    rw [hright]
    have hs : i.val+1 < ⌊u⌋₊ := lt_of_le_of_lt (Nat.succ_le_of_lt hij) j.isLt
    dsimp [edge,a]
    rw [if_pos hs]
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hij) hpos.le
  have hd : Pairwise fun i j => Disjoint (Ioc (a i) (a i+w i)) (Ioc (a j) (a j+w j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij|hij
    · exact hsep i j hij
    · exact (hsep j i hij).symm
  exact ⟨a,a,w,fun i => div_pos (sub_pos.mpr (edge_step i hpos.le)) hpos,hcov,hcov,hd,hd⟩

/-- Split each base interval into two on the bottom, and stack the two
copies of the top partition in opposite color blocks. False is red. -/
def twoColors {ι : Type*} (P : Pattern ι) : Pattern (Bool × ι) := by
  let x : Bool × ι → ℝ := fun z => P.x z.2 + if z.1 then P.w z.2/2 else 0
  let y : Bool × ι → ℝ := fun z => (P.y z.2 + if z.1 then 0 else 1)/2
  let w : Bool × ι → ℝ := fun z => P.w z.2/2
  let xb := fun (i : ι) => Ioc (P.x i) (P.x i+P.w i)
  let yb := fun (i : ι) => Ioc (P.y i) (P.y i+P.w i)
  have hx (z : Bool × ι) {a:ℝ} (ha : a ∈ Ioc (x z) (x z+w z)) : a ∈ xb z.2 := by
    rcases z with ⟨b,i⟩
    cases b <;> simp [x,w,xb] at * <;> constructor <;> linarith [P.wpos i]
  have hy (b : Bool) (i : ι) (a : ℝ) : a ∈ Ioc (y (b,i)) (y (b,i)+w (b,i)) ↔
      2*a - (if b then 0 else 1) ∈ yb i := by
    cases b <;> simp [y,w,yb] <;> constructor <;> rintro ⟨ha,hb⟩ <;> constructor <;> linarith
  have yunit (i : ι) : yb i ⊆ Ioc 0 1 := by
    rw [← P.y_cover]; exact subset_iUnion _ i
  refine ⟨x,y,w,fun z => half_pos (P.wpos z.2),?_,?_,?_,?_⟩
  · ext a
    constructor
    · intro ha
      obtain ⟨z,hz⟩ := mem_iUnion.mp ha
      rw [← P.x_cover]
      exact mem_iUnion.mpr ⟨z.2,hx z hz⟩
    · intro ha
      rw [← P.x_cover] at ha
      obtain ⟨i,hi⟩ := mem_iUnion.mp ha
      by_cases h : a ≤ P.x i+P.w i/2
      · exact mem_iUnion.mpr ⟨(false,i),by simpa [x,w] using (show P.x i<a ∧ a≤P.x i+P.w i/2 from ⟨hi.1,h⟩)⟩
      · refine mem_iUnion.mpr ⟨(true,i),?_⟩
        simp [x,w]; exact ⟨lt_of_not_ge h,by linarith [hi.2]⟩
  · ext a
    constructor
    · intro ha
      obtain ⟨⟨b,i⟩,hi⟩ := mem_iUnion.mp ha
      have hz := yunit i ((hy b i a).mp hi)
      cases b <;> simp at hz <;> constructor <;> linarith [hz.1,hz.2]
    · intro ha
      by_cases h : 2*a ≤ 1
      · have hz : 2*a ∈ Ioc (0:ℝ) 1 := ⟨by linarith [ha.1], h⟩
        rw [← P.y_cover] at hz
        obtain ⟨i,hi⟩ := mem_iUnion.mp hz
        exact mem_iUnion.mpr ⟨(true,i),(hy true i a).mpr (by simpa using hi)⟩
      · have hz : 2*a-1 ∈ Ioc (0:ℝ) 1 := ⟨by linarith,by linarith [ha.2]⟩
        rw [← P.y_cover] at hz
        obtain ⟨i,hi⟩ := mem_iUnion.mp hz
        exact mem_iUnion.mpr ⟨(false,i),(hy false i a).mpr hi⟩
  · rintro ⟨b,i⟩ ⟨c,j⟩ hne
    apply Set.disjoint_left.mpr
    intro a h1 h2
    by_cases hij : i=j
    · subst j
      cases b <;> cases c <;> first | exact hne rfl |
        (simp only [x,w,Bool.false_eq_true,if_false,if_true,add_zero,mem_Ioc] at h1 h2;
         linarith only [h1.1,h1.2,h2.1,h2.2])
    · exact Set.disjoint_left.mp (P.x_disjoint hij) (hx _ h1) (hx _ h2)
  · rintro ⟨b,i⟩ ⟨c,j⟩ hne
    apply Set.disjoint_left.mpr
    intro a h1 h2
    have h1' := (hy b i a).mp h1
    have h2' := (hy c j a).mp h2
    by_cases he : b=c
    · subst c
      have hij : i≠j := by rintro rfl; exact hne rfl
      exact Set.disjoint_left.mp (P.y_disjoint hij) h1' h2'
    · have h₁ := yunit i h1'
      have h₂ := yunit j h2'
      cases b <;> cases c <;> first | exact he rfl |
        (simp only [Bool.false_eq_true,if_false,if_true,sub_zero,mem_Ioc] at h₁ h₂;
         linarith only [h₁.1,h₁.2,h₂.1,h₂.2])

def shufflePattern (u : ℝ) (hu : 4 ≤ u) : Pattern (Bool × Fin ⌊u⌋₊) :=
  twoColors (basePartition u hu)


/-- A shuffle whose parameter lies in the shell uses at most four times the
lower endpoint of the shell in child squares. -/
theorem card_children_le {u U : ℝ} (hu : 0 ≤ u) (hupper : u ≤ 2*U) :
    (Fintype.card (Bool × Fin ⌊u⌋₊) : ℝ) ≤ 4*U := by
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
  linarith [Nat.floor_le hu]


theorem measure_affine (a w : ℝ) (hw : 0 < w) (F : Set ℝ) :
    volume.real ((fun z => a+w*z) '' F) = w * volume.real F := by
  have he : (fun z => a+w*z) '' F =
      (fun z : ℝ => z+ -a) ⁻¹' ((fun z : ℝ => w⁻¹*z) ⁻¹' F) := by
    ext z
    change (∃ y ∈ F,a+w*y=z) ↔ w⁻¹*(z+-a) ∈ F
    constructor
    · rintro ⟨y,hy,rfl⟩
      convert hy using 1
      field_simp
      ring
    · intro hz
      refine ⟨_,hz,?_⟩
      field_simp
      ring
  rw [measureReal_def,he,measure_preimage_add_right, Real.volume_preimage_mul_left (inv_ne_zero hw.ne'),
    inv_inv, abs_of_pos hw, ENNReal.toReal_mul, ENNReal.toReal_ofReal hw.le]
  rfl

/-- The projected copies of one color, with the longer last child included. -/
def colorSection (u : ℝ) (hu : 4 ≤ u) (t : ℝ) (F : Set ℝ) (b : Bool) : Set ℝ :=
  ⋃ i, (fun z => (shufflePattern u hu).start t (b,i) + (shufflePattern u hu).w (b,i)*z) '' F

theorem color_length_le (u : ℝ) (hu : 4 ≤ u) (t : ℝ) (F : Set ℝ) (b : Bool) :
    volume.real (colorSection u hu t F b) ≤ volume.real F/2 := by
  let P := basePartition u hu
  have hs' := P.sum_width
  calc
    _ ≤ ∑ i : Fin ⌊u⌋₊, volume.real ((fun z => (shufflePattern u hu).start t (b,i) +
        (shufflePattern u hu).w (b,i)*z) '' F) := measureReal_iUnion_fintype_le _
    _ = ∑ i : Fin ⌊u⌋₊, (P.w i/2)*volume.real F := by
      apply Finset.sum_congr rfl
      intro i _
      exact measure_affine _ _ ((shufflePattern u hu).wpos _) _
    _ = _ := by simp_rw [div_mul_eq_mul_div]; rw [← Finset.sum_div,← Finset.sum_mul,hs']; ring

/-- Starts and common width of all children preceding the final pair. -/
theorem regularCoords (u : ℝ) (hu : 4 ≤ u) (t : ℝ)
    (i : Fin ⌊u⌋₊) (hi : i.val+1 < ⌊u⌋₊) (b : Bool) :
    (shufflePattern u hu).start t (b,i) =
      (if b then blueStart t i.val else redStart t u i.val)/(2*u) ∧
    (shufflePattern u hu).w (b,i) = 1/(2*u) := by
  have hne : u ≠ 0 := by linarith
  cases b <;>
    simp [shufflePattern,twoColors,basePartition,Pattern.start,projection,edge,hi,redStart,blueStart]
    <;> constructor <;> (field_simp <;> ring)

private theorem regular_subset_colors {u : ℝ} (hu : 4 ≤ u) (t : ℝ) (F : Set ℝ) :
    ((fun x : ℝ => (2*u)*x) ⁻¹' regularIntersection F t u) ⊆
      colorSection u hu t F false ∩ colorSection u hu t F true := by
  intro x hx
  have hconv := Int.natCast_floor_eq_floor (by linarith : 0 ≤ u)
  have H (b : Bool) (j : ℤ) (hj : j ∈ Finset.Icc (0:ℤ) (⌊u⌋-2))
      (hz : (2*u)*x - (if b then blueStart t j else redStart t u j) ∈ F) :
      x ∈ colorSection u hu t F b := by
    have h := Finset.mem_Icc.mp hj
    have hc : (j.toNat:ℤ) = j := Int.toNat_of_nonneg h.1
    let i : Fin ⌊u⌋₊ := ⟨j.toNat, by omega⟩
    have hir : (i.val:ℝ) = (j:ℝ) := by exact_mod_cast hc
    obtain ⟨hs,hw⟩ := regularCoords u hu t i (by dsimp [i]; omega) b
    refine mem_iUnion.mpr ⟨i, _, hz, ?_⟩
    rw [hs,hw,hir]
    have hne : u ≠ 0 := by linarith
    field_simp
    ring
  obtain ⟨r,hr,hrx⟩ := mem_iUnion₂.mp hx.1
  obtain ⟨b,hb,hbx⟩ := mem_iUnion₂.mp hx.2
  exact ⟨H false r hr hrx,H true b hb hbx⟩

/-- The genuine full-pattern loss dominates the regular-pair saving. -/
theorem length_colors_add_saving {F : Set ℝ} (hF : IsCompact F) {u : ℝ}
    (hu : 4 ≤ u) (t : ℝ) :
    volume.real (colorSection u hu t F false ∪ colorSection u hu t F true) +
      regularSaving F t u ≤ volume.real F := by
  let C := colorSection u hu t F
  have hc (b : Bool) : IsCompact (C b) := isCompact_iUnion fun i =>
    hF.image (show Continuous (fun z : ℝ => (shufflePattern u hu).start t (b,i) +
      (shufflePattern u hu).w (b,i)*z) by fun_prop)
  have hmass := measureReal_union_add_inter (μ:=volume) (hc true).measurableSet
      ((hc false).measure_lt_top.ne) ((hc true).measure_lt_top.ne)
  have hp : 0 < 2*u := by linarith
  have hlow := measureReal_mono (μ:=volume) (regular_subset_colors hu t F)
    ((hc false).inter_right (hc true).isClosed).measure_lt_top.ne
  rw [measureReal_def, Real.volume_preimage_mul_left hp.ne',abs_of_pos (inv_pos.mpr hp),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_nonneg.mpr hp.le)] at hlow
  have hsave : regularSaving F t u ≤ volume.real (C false ∩ C true) := by
    simpa only [regularSaving,div_eq_inv_mul] using hlow
  have hred := color_length_le u hu t F false
  have hblue := color_length_le u hu t F true
  change volume.real (C false ∪ C true) + regularSaving F t u ≤ volume.real F
  change volume.real (C false) ≤ _ at hred
  change volume.real (C true) ≤ _ at hblue
  linarith

end
end PermutationStrips.Shuffle
