import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-!
# Conventions

The heat measure is Lebesgue measure on `(0, infinity)`. Eigenvalues are real
and counted with their full complex multiplicity. Zero modes must be removed
before using the massless phase theorem.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace PVEta

abbrev heatMeasure : Measure ℝ := volume.restrict (Ioi 0)

def mode (x t : ℝ) : ℝ := x * Real.exp (-t * x ^ 2)

def heatTrace (eigenvalue : ℕ → ℝ) (t : ℝ) : ℝ := ∑' k, mode (eigenvalue k) t

def absHeatTrace (eigenvalue : ℕ → ℝ) (t : ℝ) : ℝ := ∑' k, |mode (eigenvalue k) t|

def heatWeight (t : ℝ) : ℝ := (Real.sqrt t)⁻¹

def etaHeat (eigenvalue : ℕ → ℝ) : ℝ :=
  (Real.sqrt Real.pi)⁻¹ * ∫ t, heatWeight t * heatTrace eigenvalue t ∂heatMeasure

/-- A real lift is exponentiated only at the end. -/
def unitPhase (a : ℝ) : ℂ := Complex.exp ((a : ℂ) * Complex.I)

lemma continuous_unitPhase : Continuous unitPhase := by
  exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

lemma unitPhase_half_sq (a : ℝ) : unitPhase (a / 2) ^ 2 = unitPhase a := by
  simp only [unitPhase, pow_two, ← Complex.exp_add, Complex.ofReal_div, Complex.ofReal_ofNat]
  congr 1
  ring

lemma measurable_mode (x : ℝ) : Measurable (mode x) := by
  unfold mode
  fun_prop

lemma measurable_heatWeight : Measurable heatWeight := by
  unfold heatWeight
  fun_prop

lemma heatWeight_nonneg (t : ℝ) : 0 ≤ heatWeight t :=
  inv_nonneg.mpr (Real.sqrt_nonneg t)

/-- The assumptions supplied by the spectral and geometric estimates.

The second integrability condition is deliberately *not* hidden in a conclusion
about a PV phase. It is the absolute majorant used to exchange sum and integral.
-/
structure SpectralHypotheses (eigenvalue : ℕ → ℝ) (kernel : ℝ → ℝ → ℝ) : Prop where
  nonzero : ∀ k, eigenvalue k ≠ 0
  heat_summable : ∀ t, 0 < t → Summable (fun k => |mode (eigenvalue k) t|)
  absolute_integrable : ∀ M, 0 < M →
    Integrable (fun t => |kernel M t| * absHeatTrace eigenvalue t) heatMeasure
  eta_integrable : Integrable (fun t => heatWeight t * |heatTrace eigenvalue t|) heatMeasure

lemma SpectralHypotheses.aestronglyMeasurable_heatTrace {eigenvalue : ℕ → ℝ}
    {kernel : ℝ → ℝ → ℝ} (hs : SpectralHypotheses eigenvalue kernel) :
    AEStronglyMeasurable (heatTrace eigenvalue) heatMeasure := by
  apply aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun n t => ∑ k ∈ Finset.range n, mode (eigenvalue k) t)
  · intro n
    exact (Finset.measurable_sum _ (fun k _ => measurable_mode (eigenvalue k))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hs.heat_summable t ht).of_abs.hasSum.tendsto_sum_nat

end PVEta
