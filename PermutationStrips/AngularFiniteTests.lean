import PermutationStrips.AngularBlock

/-! At prescribed heights a logarithmic number of genuine depth-k paths suffices.
The required list length depends only on the number of tests, not on their spacing. -/

open Set MeasureTheory
open scoped BigOperators
namespace PermutationStrips.AngularBlock
noncomputable section

/-- A finite family of height tests needs only sixteen times its logarithmic
cardinality in samples. Each selected path uses the same stage budgets. -/
theorem paths_for_finite_tests {J : Type*} [Fintype J] [Nonempty J] (k M : ℕ)
    (hk : 0<k) (hM : 0<M) (hsize : 16*Real.log (Fintype.card J) ≤ M)
    (t z : J → ℝ) (ht : ∀ j, t j ∈ Icc 0 1) (hz : ∀ j, z j ∈ Icc 0 1)
    (U : ℕ → ℝ) (hU : ∀ i, 16≤U i)
    (hc : ∀ i j, i < ⌊(k:ℝ)*z j⌋₊ → 8≤U i*radius (t j)) :
    ∃ p : Fin M → Path,
      (∀ i, (p i).depth=k ∧ (Fintype.card (p i).Index : ℝ) ≤ ∏ i ∈ Finset.range k, 4*U i) ∧
      ∀ j, z j*((∑ i, len (p i).pattern (t j))/(M:ℝ)) ≤ 194/k := by
  obtain ⟨p,hp,hh⟩ := moment_paths_on_mesh k M hk hM t z ht hz U hU hc
  refine ⟨p,hp,fun j => (hh j).trans ?_⟩
  have hr : Real.log (Fintype.card J)/(M:ℝ) ≤ 1/16 :=
    (div_le_iff₀ (by exact_mod_cast hM : (0:ℝ)<M)).mpr (by linarith)
  exact (div_le_div_iff_of_pos_right (by exact_mod_cast hk : (0:ℝ)<k)).mpr
    (by linarith [Real.log_two_lt_d9])

/-- The logarithmic sample size, with one path when there is just one test. -/
def finiteTestCount (J : ℕ) : ℕ := max 1 ⌈16*Real.log J⌉₊

theorem finiteTestCount_pos (J : ℕ) : 0<finiteTestCount J :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..)

theorem log_le_finiteTestCount (J : ℕ) : 16*Real.log J ≤ finiteTestCount J :=
  (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈16*Real.log J⌉₊))

theorem finiteTestCount_le {J : ℕ} (hJ : 0<J) : (finiteTestCount J:ℝ) ≤ 1+16*Real.log J := by
  have hlog : 0≤16*Real.log J := mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hJ))
  unfold finiteTestCount
  rw [Nat.cast_max,Nat.cast_one]
  exact max_le (by linarith) ((Nat.ceil_lt_add_one hlog).le.trans_eq (add_comm _ _))

/-- The scheduled finite test estimate for any admissible integrable profile. -/
theorem profile_on_finite_tests {J : Type*} [Fintype J] [Nonempty J]
    {w : ℝ → ℝ} (hm : Measurable w)
    (hw : ∀ r ∈ Ioc (0:ℝ) (1/2), w r ∈ Icc 0 1)
    (hmono : MonotoneOn w (Ioc (0:ℝ) (1/2)))
    (hi : IntegrableOn (fun r => w r/r) (Ioc (0:ℝ) (1/2)))
    (hI : (∫ r in Ioc (0:ℝ) (1/2), w r/r) ≤ 3)
    (k : ℕ) (hk : 0<k) (t : J → ℝ) (ht : ∀ j, t j ∈ Ioo 0 1) :
    let M := finiteTestCount (Fintype.card J)
    ∃ p : Fin M → Path,
      (∀ i, (p i).depth=k ∧ (Fintype.card (p i).Index : ℝ) ≤ Real.exp (8*k)) ∧
      ∀ j, w (radius (t j))*((∑ i, len (p i).pattern (t j))/(M:ℝ)) ≤ 194/k := by
  let M := finiteTestCount (Fintype.card J)
  let U := fun i => 16*Real.exp (Schedule.cost k i w)
  let r := fun j => radius (t j)
  have hr (j) : r j ∈ Ioc 0 (1/2) := radius_mem_of_interior (ht j)
  obtain ⟨p,hp,hθ⟩ := paths_for_finite_tests k M hk (finiteTestCount_pos _) (log_le_finiteTestCount _)
    t (fun j => w (r j)) (fun j => ⟨(ht j).1.le,(ht j).2.le⟩) (fun j => hw _ (hr j)) U
    (fun _ => scheduled_scale_ge w) (fun _ j => scheduled_scale_active hm hw hmono hi (hr j))
  exact ⟨p,fun i => ⟨(hp i).1,(hp i).2.trans (schedule_budget hm hw hi hI)⟩,hθ⟩

end
end PermutationStrips.AngularBlock
