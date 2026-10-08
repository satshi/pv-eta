import PVEta.Basic

/-! The concrete Gaussian regulator kernel, including its large-mass limit. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace PVEta

/-- `cutoff t a = integral_0^a exp(-t u^2) du` when `a >= 0`.
For negative `a` the set integral is zero; only positive masses are used. -/
def cutoff (t a : ℝ) : ℝ := ∫ u in Ioc 0 a, Real.exp (-t * u ^ 2)

def gaussianTotal (t : ℝ) : ℝ := Real.sqrt (Real.pi / t) / 2

lemma gaussianTotal_eq (t : ℝ) :
    gaussianTotal t = (Real.sqrt Real.pi / 2) * heatWeight t := by
  unfold gaussianTotal heatWeight
  rw [Real.sqrt_div Real.pi_pos.le]
  ring

lemma gaussianTotal_nonneg (t : ℝ) : 0 ≤ gaussianTotal t := by
  exact div_nonneg (Real.sqrt_nonneg _) (by norm_num)

lemma measurable_cutoff (a : ℝ) : Measurable (fun t => cutoff t a) := by
  have h : StronglyMeasurable (fun p : ℝ × ℝ => Real.exp (-p.1 * p.2 ^ 2)) := by
    exact (by fun_prop : Continuous _).stronglyMeasurable
  exact h.integral_prod_right'.measurable

lemma cutoff_nonneg (t a : ℝ) : 0 ≤ cutoff t a := by
  exact integral_nonneg (fun _ => (Real.exp_pos _).le)

lemma cutoff_le (t a : ℝ) (ht : 0 < t) : cutoff t a ≤ gaussianTotal t := by
  rw [cutoff, gaussianTotal, ← integral_gaussian_Ioi]
  exact setIntegral_mono_set (integrable_exp_neg_mul_sq ht).integrableOn
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))
    (Filter.Eventually.of_forall (fun _ hu => hu.1))

lemma tendsto_cutoff (t b : ℝ) (ht : 0 < t) (hb : 0 < b) :
    Tendsto (fun M : ℝ => cutoff t (b * M)) atTop (𝓝 (gaussianTotal t)) := by
  have h := intervalIntegral_tendsto_integral_Ioi 0
    (integrable_exp_neg_mul_sq ht).integrableOn (tendsto_id.const_mul_atTop hb)
  rw [integral_gaussian_Ioi] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
  exact intervalIntegral.integral_of_le (mul_nonneg hb.le hM)

/-- The regulator excludes the physical mode j=0; its remaining weights sum to -1. -/
structure Regulator where
  count : ℕ
  weight : Fin count → ℝ
  scale : Fin count → ℝ
  scale_pos : ∀ j, 0 < scale j
  weight_sum : ∑ j, weight j = -1

def Regulator.kernel (R : Regulator) (M t : ℝ) : ℝ :=
  ∑ j, R.weight j * cutoff t (R.scale j * M)

def Regulator.angle (R : Regulator) (M x : ℝ) : ℝ :=
  ∑ j, R.weight j * Real.arctan (R.scale j * M / x)

def Regulator.bound (R : Regulator) : ℝ := ∑ j, |R.weight j|

lemma Regulator.measurable_kernel (R : Regulator) (M : ℝ) : Measurable (R.kernel M) := by
  exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (measurable_cutoff _))

lemma Regulator.kernel_bound (R : Regulator) (M t : ℝ) (ht : 0 < t) :
    |R.kernel M t| ≤ R.bound * gaussianTotal t := by
  calc
    |R.kernel M t| ≤ ∑ j, |R.weight j * cutoff t (R.scale j * M)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |R.weight j| * gaussianTotal t := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (cutoff_nonneg _ _)]
      exact mul_le_mul_of_nonneg_left (cutoff_le _ _ ht) (abs_nonneg _)
    _ = R.bound * gaussianTotal t := (Finset.sum_mul _ _ _).symm

lemma Regulator.tendsto_kernel (R : Regulator) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun M : ℝ => R.kernel M t) atTop (𝓝 (-gaussianTotal t)) := by
  have h := tendsto_finset_sum Finset.univ
    (fun j _ => (tendsto_cutoff t (R.scale j) ht (R.scale_pos j)).const_mul (R.weight j))
  simpa only [← Finset.sum_mul, R.weight_sum, neg_one_mul] using h

end PVEta
