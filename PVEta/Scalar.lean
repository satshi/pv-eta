import PVEta.Kernel

/-! The scalar Laplace--arctangent identity is proved using Fubini and FTC. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace PVEta

lemma integrable_double (x a : ℝ) (hx : x ≠ 0) :
    Integrable (fun p : ℝ × ℝ => x * Real.exp (-p.1 * (x ^ 2 + p.2 ^ 2)))
      (heatMeasure.prod (volume.restrict (Ioc 0 a))) := by
  have hexp : Integrable (fun t : ℝ => |x| * Real.exp (-(x ^ 2) * t)) heatMeasure :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos (sq_pos_of_ne_zero hx)) 0).const_mul |x|
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 a)) := by
    exact integrableOn_const.mpr (Or.inr measure_Ioc_lt_top)
  have hmajor := hexp.mul_prod hone
  simp only [mul_one] at hmajor
  apply hmajor.mono'
  · exact (by fun_prop : Continuous _).aestronglyMeasurable
  · have ht : ∀ᵐ p : ℝ × ℝ ∂heatMeasure.prod (volume.restrict (Ioc 0 a)), 0 < p.1 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
    filter_upwards [ht] with p hp
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg x)
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg p.2]

lemma laplace_value (x u : ℝ) (hx : x ≠ 0) :
    (∫ t, x * Real.exp (-t * (x ^ 2 + u ^ 2)) ∂heatMeasure) = x / (x ^ 2 + u ^ 2) := by
  have hpos : 0 < x ^ 2 + u ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg u)
  rw [integral_const_mul]
  have heq : (fun t : ℝ => Real.exp (-t * (x ^ 2 + u ^ 2))) =
      (fun t : ℝ => Real.exp (-(x ^ 2 + u ^ 2) * t)) := by
    funext t
    congr 1
    ring
  rw [heq, integral_exp_mul_Ioi (neg_neg_of_pos hpos) 0]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]
  rfl

lemma arctan_integral (x a : ℝ) (hx : x ≠ 0) (ha : 0 ≤ a) :
    (∫ u in Ioc 0 a, x / (x ^ 2 + u ^ 2)) = Real.arctan (a / x) := by
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => Real.arctan (u / x))
      (x / (x ^ 2 + u ^ 2)) u := by
    convert ((hasDerivAt_id u).div_const x).arctan using 1
    field_simp
    ring
  have hc : Continuous (fun u : ℝ => x / (x ^ 2 + u ^ 2)) := by
    apply continuous_const.div (continuous_const.add (continuous_id.pow 2))
    intro u
    exact ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg u))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hd u) (hc.intervalIntegrable 0 a)
  rw [intervalIntegral.integral_of_le ha] at h
  simpa using h

lemma integrable_cutoff_mode (x a : ℝ) (hx : x ≠ 0) :
    Integrable (fun t => cutoff t a * mode x t) heatMeasure := by
  have h := (integrable_double x a hx).integral_prod_left
  convert h using 1
  funext t
  unfold cutoff mode
  simp_rw [show ∀ u : ℝ, -t * (x ^ 2 + u ^ 2) = -t * x ^ 2 + -t * u ^ 2 by intro u; ring,
    Real.exp_add, ← mul_assoc, integral_const_mul]
  ring

/-- For positive mass this is precisely the scalar identity used in PV regularization. -/
theorem scalar_arctan_identity (x a : ℝ) (hx : x ≠ 0) (ha : 0 ≤ a) :
    (∫ t, cutoff t a * mode x t ∂heatMeasure) = Real.arctan (a / x) := by
  calc
    (∫ t, cutoff t a * mode x t ∂heatMeasure) =
        ∫ t, (∫ u in Ioc 0 a, x * Real.exp (-t * (x ^ 2 + u ^ 2))) ∂heatMeasure := by
      apply integral_congr_ae
      filter_upwards with t
      unfold cutoff mode
      simp_rw [show ∀ u : ℝ, -t * (x ^ 2 + u ^ 2) = -t * x ^ 2 + -t * u ^ 2 by intro u; ring,
        Real.exp_add, ← mul_assoc, integral_const_mul]
      ring
    _ = ∫ u in Ioc 0 a, ∫ t, x * Real.exp (-t * (x ^ 2 + u ^ 2)) ∂heatMeasure :=
      integral_integral_swap (integrable_double x a hx)
    _ = ∫ u in Ioc 0 a, x / (x ^ 2 + u ^ 2) := by
      apply integral_congr_ae
      filter_upwards with u
      exact laplace_value x u hx
    _ = Real.arctan (a / x) := arctan_integral x a hx ha

lemma Regulator.angle_eq_integral (R : Regulator) (M x : ℝ) (hM : 0 < M) (hx : x ≠ 0) :
    R.angle M x = ∫ t, R.kernel M t * mode x t ∂heatMeasure := by
  unfold Regulator.angle Regulator.kernel
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j _
    simp_rw [mul_assoc]
    rw [integral_const_mul, scalar_arctan_identity x _ hx (mul_pos (R.scale_pos j) hM).le]
  · intro j _
    simpa only [mul_assoc] using (integrable_cutoff_mode x (R.scale j * M) hx).const_mul (R.weight j)

end PVEta
