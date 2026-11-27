import PermutationStrips.AngularBlockStep

/-! A shuffle path is a concrete sequence of elementary subdivisions. -/

open MeasureTheory Set
open scoped BigOperators

namespace PermutationStrips.AngularBlock
noncomputable section

inductive Path where
  | seed
  | step (u : ℝ) (hu : 4 ≤ u) (rev : Bool) (inner : Path)

def Path.Index : Path → Type
  | .seed => Fin 1
  | .step u _ _ p => (Bool × Fin ⌊u⌋₊) × p.Index

instance Path.fintype : (p : Path) → Fintype p.Index
  | .seed => (inferInstance : Fintype (Fin 1))
  | .step u _ _ p =>
    letI := Path.fintype p
    (inferInstance : Fintype ((Bool × Fin ⌊u⌋₊) × p.Index))

def Path.pattern : (p : Path) → Pattern p.Index
  | .seed => Pattern.equalGrid (n:=1) (by decide) (Equiv.refl _)
  | .step u hu rev p => (Shuffle.orientedPattern u hu rev).insert p.pattern

def envelope (i c : ℕ) : ℝ := 128/(128+(min i c : ℕ))

private theorem envelope_bounds (i c : ℕ) : envelope i c ∈ Icc 0 1 := by
  unfold envelope
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity)).mpr
    simp

private theorem envelope_step (i c : ℕ) :
    envelope i c - (if i<c then (envelope i c)^2/128 else 0) ≤ envelope (i+1) c := by
  by_cases h : i<c
  · have h' : i+1 ≤ c := by omega
    simp only [h, if_pos, envelope, min_eq_left h.le, min_eq_left h', Nat.cast_add, Nat.cast_one]
    have hc : 0 < 128 + (i:ℝ) := by positivity
    have hc' : 0 < 128 + ((i:ℝ)+1) := by positivity
    field_simp
    nlinarith
  · have h' : c ≤ i := by omega
    simp [h,envelope,min_eq_right h',min_eq_right (Nat.le_succ_of_le h')]

/-- For any terminal test, a single actual subdivision path beats the scalar envelope
in weighted sum. Its complexity is bounded uniformly, independently of the test. -/
theorem exists_path {J : Type*} [Fintype J] (t : J → ℝ) (ht : ∀ j, t j ∈ Icc 0 1)
    (cut : J → ℕ) (U : ℕ → ℝ) (hU : ∀ i, 16 ≤ U i)
    (hc : ∀ i j, i < cut j → 8 ≤ U i * radius (t j)) (n : ℕ)
    (a : J → ℝ) (ha : ∀ j, 0 ≤ a j) :
    ∃ p : Path, (Fintype.card p.Index : ℝ) ≤ ∏ i ∈ Finset.range n, 4*U i ∧
      ∑ j, a j*(len p.pattern (t j) - envelope n (cut j)) ≤ 0 := by
  classical
  induction n generalizing a with
  | zero =>
    refine ⟨.seed,by simp [Path.Index],?_⟩
    apply Finset.sum_nonpos
    intro j _
    apply mul_nonpos_of_nonneg_of_nonpos (ha j)
    simpa [envelope] using sub_nonpos.mpr (Path.seed.pattern.section_length_le_one (ht j))
  | succ n ih =>
    let b := fun j => if n<cut j then 1-2*envelope n (cut j)/128 else 1
    have hb (j) : 0 ≤ b j := by
      dsimp [b]; split_ifs <;> linarith [(envelope_bounds n (cut j)).2]
    obtain ⟨p,hp,hs⟩ := ih (fun j => a j*b j) (fun j => mul_nonneg (ha j) (hb j))
    obtain ⟨rev,u,hu,hstep⟩ := weighted_shell p.pattern t a ht ha (fun j => n<cut j)
      (hU n) (hc n)
    have hu4 : 4 ≤ u := by linarith [hU n,hu.1]
    let p' := Path.step u hu4 rev p
    refine ⟨p',?_,?_⟩
    · have hcard : Fintype.card p'.Index = 2*⌊u⌋₊ * Fintype.card p.Index := by
        change Fintype.card ((Bool × Fin ⌊u⌋₊) × p.Index) = _
        simp
      have hfloor := Nat.floor_le (by linarith : 0≤u)
      rw [hcard,Finset.prod_range_succ]
      push_cast
      calc
        _ ≤ (4*U n)*(∏ i ∈ Finset.range n, 4*U i) := mul_le_mul
          (by linarith [hu.2]) hp (Nat.cast_nonneg _) (by linarith [hU n])
        _ = _ := mul_comm _ _
    · let x := fun j => len p.pattern (t j)
      let y := fun j => len p'.pattern (t j)
      let f := fun j => envelope n (cut j)
      let f' := fun j => envelope (n+1) (cut j)
      let g := fun j => if n<cut j then (x j)^2/128 else 0
      change ∑ j, a j*g j ≤ ∑ j, a j*(x j-y j) at hstep
      change ∑ j, (a j*b j)*(x j-f j) ≤ 0 at hs
      have point (j) : (x j - f' j) - g j ≤ b j*(x j-f j) := by
        have denom := envelope_step n (cut j)
        change f j - (if n<cut j then (f j)^2/128 else 0) ≤ f' j at denom
        dsimp only [g,b]
        split_ifs with h
        · rw [if_pos h] at denom
          change _ ≤ (1-2*f j/128)*(x j-f j)
          nlinarith [sq_nonneg (x j-f j)]
        · rw [if_neg h] at denom
          linarith
      have bound := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => mul_le_mul_of_nonneg_left (point j) (ha j))
      simp only [mul_sub,Finset.sum_sub_distrib,mul_assoc] at hstep hs bound ⊢
      change ∑ j, a j*y j - ∑ j, a j*f' j ≤ 0
      linarith

end
end PermutationStrips.AngularBlock
