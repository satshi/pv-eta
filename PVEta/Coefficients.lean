import PVEta.Kernel

/-! Binomial PV weights and the explicit order-four regulator. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace PVEta

def coefficient (N j : ℕ) : ℤ := (-1) ^ j * (N.choose j : ℤ)

lemma coefficient_sum (N : ℕ) (hN : 0 < N) :
    ∑ j ∈ Finset.range (N + 1), coefficient N j = 0 :=
  Int.alternating_sum_range_choose_of_ne (Nat.ne_of_gt hN)

lemma coefficient_tail_sum (N : ℕ) (hN : 0 < N) :
    ∑ j : Fin N, (coefficient N (j.val + 1) : ℝ) = -1 := by
  have h : (∑ j ∈ Finset.range (N + 1), (coefficient N j : ℝ)) = 0 := by
    exact_mod_cast coefficient_sum N hN
  rw [Finset.sum_range_succ'] at h
  simp only [coefficient, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
    Int.cast_one] at h
  rw [show (∑ j : Fin N, (coefficient N (j.val + 1) : ℝ)) =
    ∑ j ∈ Finset.range N, (coefficient N (j + 1) : ℝ) from
      Fin.sum_univ_eq_sum_range (fun j => (coefficient N (j + 1) : ℝ)) N]
  change (∑ j ∈ Finset.range N, (coefficient N (j + 1) : ℝ)) + 1 = 0 at h
  linarith

/-- General binomial regulator. The convergence theorem still requires the
absolute heat-integrability hypothesis; this constructor does not prove it. -/
def binomialRegulator (N : ℕ) (hN : 0 < N) : Regulator where
  count := N
  weight j := coefficient N (j.val + 1)
  scale j := (j.val : ℝ) + 1
  scale_pos j := by positivity
  weight_sum := coefficient_tail_sum N hN

/-- The regulator used for a three-dimensional Dirac operator in the paper. -/
def orderFour : Regulator where
  count := 4
  weight := ![-4, 6, -4, 1]
  scale := ![1, 2, 3, 4]
  scale_pos j := by fin_cases j <;> norm_num
  weight_sum := by norm_num [Fin.sum_univ_succ]

lemma orderFour_bound : orderFour.bound = 15 := by
  dsimp only [Regulator.bound, orderFour]
  norm_num [Fin.sum_univ_succ]

/-- Cancellation of the moments of degree one, two, and three.
The constant moment includes the physical weight +1. -/
theorem orderFour_moments :
    (∑ j : Fin 4, orderFour.weight j * orderFour.scale j) = 0 ∧
    (∑ j : Fin 4, orderFour.weight j * orderFour.scale j ^ 2) = 0 ∧
    (∑ j : Fin 4, orderFour.weight j * orderFour.scale j ^ 3) = 0 := by
  dsimp only [orderFour]
  norm_num [Fin.sum_univ_succ]

lemma orderFour_angle (M x : ℝ) :
    orderFour.angle M x = -4 * Real.arctan (M / x) + 6 * Real.arctan (2 * M / x)
      - 4 * Real.arctan (3 * M / x) + Real.arctan (4 * M / x) := by
  simp [Regulator.angle, orderFour, Fin.sum_univ_succ]
  ring

end PVEta
