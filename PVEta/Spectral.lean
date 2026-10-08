import PVEta.Scalar

/-! Absolute spectral summation, the large-mass limit, and the unit-phase product. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace PVEta

/-- The real lift of the regulated spectral phase. Its summability is proved below. -/
def Regulator.phaseLift (R : Regulator) (eigenvalue : ℕ → ℝ) (M : ℝ) : ℝ :=
  ∑' k, R.angle M (eigenvalue k)

def Regulator.phase (R : Regulator) (eigenvalue : ℕ → ℝ) (M : ℝ) : ℂ :=
  unitPhase (R.phaseLift eigenvalue M)

/-- Absolute integration is applied *after* the regulator terms have been grouped. -/
theorem Regulator.hasSum_angle (R : Regulator) (eigenvalue : ℕ → ℝ)
    (hs : SpectralHypotheses eigenvalue R.kernel) (M : ℝ) (hM : 0 < M) :
    HasSum (fun k => R.angle M (eigenvalue k))
      (∫ t, R.kernel M t * heatTrace eigenvalue t ∂heatMeasure) := by
  have hsum : ∀ᵐ t ∂heatMeasure, Summable (fun k => |mode (eigenvalue k) t|) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hs.heat_summable t ht
  have hi : Integrable (fun t => ∑' k, |R.kernel M t| * |mode (eigenvalue k) t|)
      heatMeasure := by
    simpa only [absHeatTrace, tsum_mul_left] using hs.absolute_integrable M hM
  have hpoint : ∀ᵐ t ∂heatMeasure,
      HasSum (fun k => R.kernel M t * mode (eigenvalue k) t)
        (R.kernel M t * heatTrace eigenvalue t) := by
    filter_upwards [hsum] with t ht
    exact ht.of_abs.hasSum.mul_left (R.kernel M t)
  have h : HasSum (fun k => ∫ t, R.kernel M t * mode (eigenvalue k) t ∂heatMeasure)
      (∫ t, R.kernel M t * heatTrace eigenvalue t ∂heatMeasure) :=
    hasSum_integral_of_dominated_convergence
      (fun k t => |R.kernel M t| * |mode (eigenvalue k) t|)
      (fun k => ((R.measurable_kernel M).mul (measurable_mode (eigenvalue k))).aestronglyMeasurable)
      (fun k => Filter.Eventually.of_forall (fun t => by simp only [Real.norm_eq_abs, abs_mul, le_refl]))
      (hsum.mono (fun t ht => ht.mul_left |R.kernel M t|)) hi hpoint
  have heq : (fun k => R.angle M (eigenvalue k)) =
      (fun k => ∫ t, R.kernel M t * mode (eigenvalue k) t ∂heatMeasure) :=
    funext (fun k => R.angle_eq_integral M (eigenvalue k) hM (hs.nonzero k))
  rw [heq]
  exact h

theorem Regulator.phaseLift_eq_integral (R : Regulator) (eigenvalue : ℕ → ℝ)
    (hs : SpectralHypotheses eigenvalue R.kernel) (M : ℝ) (hM : 0 < M) :
    R.phaseLift eigenvalue M = ∫ t, R.kernel M t * heatTrace eigenvalue t ∂heatMeasure :=
  (R.hasSum_angle eigenvalue hs M hM).tsum_eq

/-- Absolute convergence of the grouped arctangent series. -/
theorem Regulator.summable_abs_angle (R : Regulator) (eigenvalue : ℕ → ℝ)
    (hs : SpectralHypotheses eigenvalue R.kernel) (M : ℝ) (hM : 0 < M) :
    Summable (fun k => |R.angle M (eigenvalue k)|) := by
  exact (R.hasSum_angle eigenvalue hs M hM).summable.abs

/-- The regulator has a limit for real mass tending continuously to positive infinity. -/
theorem Regulator.tendsto_phaseLift (R : Regulator) (eigenvalue : ℕ → ℝ)
    (hs : SpectralHypotheses eigenvalue R.kernel) :
    Tendsto (R.phaseLift eigenvalue) atTop (𝓝 (-(Real.pi / 2) * etaHeat eigenvalue)) := by
  let C := R.bound * (Real.sqrt Real.pi / 2)
  have hbound : ∀ M, ∀ᵐ t ∂heatMeasure,
      ‖R.kernel M t * heatTrace eigenvalue t‖ ≤ C * (heatWeight t * |heatTrace eigenvalue t|) := by
    intro M
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |R.kernel M t| * |heatTrace eigenvalue t| ≤
          (R.bound * gaussianTotal t) * |heatTrace eigenvalue t| :=
        mul_le_mul_of_nonneg_right (R.kernel_bound M t ht) (abs_nonneg _)
      _ = C * (heatWeight t * |heatTrace eigenvalue t|) := by
        rw [gaussianTotal_eq]
        ring
  have hlim : ∀ᵐ t ∂heatMeasure,
      Tendsto (fun M => R.kernel M t * heatTrace eigenvalue t) atTop
        (𝓝 (-gaussianTotal t * heatTrace eigenvalue t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (R.tendsto_kernel t ht).mul_const _
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun t => C * (heatWeight t * |heatTrace eigenvalue t|))
    (Filter.Eventually.of_forall (fun M =>
      (R.measurable_kernel M).aestronglyMeasurable.mul hs.aestronglyMeasurable_heatTrace))
    (Filter.Eventually.of_forall hbound) (hs.eta_integrable.const_mul C) hlim
  have hval : (∫ t, -gaussianTotal t * heatTrace eigenvalue t ∂heatMeasure) =
      -(Real.pi / 2) * etaHeat eigenvalue := by
    simp_rw [gaussianTotal_eq]
    simp_rw [show ∀ t : ℝ, -((Real.sqrt Real.pi / 2) * heatWeight t) * heatTrace eigenvalue t =
      -(Real.sqrt Real.pi / 2) * (heatWeight t * heatTrace eigenvalue t) by intro t; ring]
    rw [integral_const_mul]
    unfold etaHeat
    have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
    have hp2 : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
    have hc : -(Real.sqrt Real.pi / 2) = -(Real.pi / 2) * (Real.sqrt Real.pi)⁻¹ := by
      field_simp
      nlinarith
    rw [hc]
    ring
  rw [hval] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
  exact (R.phaseLift_eq_integral eigenvalue hs M hM).symm

/-- The complex Dirac unit phase tends to exp(-i pi eta_heat/2). -/
theorem Regulator.tendsto_phase (R : Regulator) (eigenvalue : ℕ → ℝ)
    (hs : SpectralHypotheses eigenvalue R.kernel) :
    Tendsto (R.phase eigenvalue) atTop
      (𝓝 (unitPhase (-(Real.pi / 2) * etaHeat eigenvalue))) :=
  continuous_unitPhase.continuousAt.tendsto.comp (R.tendsto_phaseLift eigenvalue hs)

/-- Infinite product of normalized mode phases, with no logarithm branch choice. -/
theorem Regulator.hasProd_phase (R : Regulator) (eigenvalue : ℕ → ℝ)
    (hs : SpectralHypotheses eigenvalue R.kernel) (M : ℝ) (hM : 0 < M) :
    HasProd (fun k => unitPhase (R.angle M (eigenvalue k))) (R.phase eigenvalue M) := by
  have h : HasSum (fun k => R.angle M (eigenvalue k)) (R.phaseLift eigenvalue M) :=
    (R.hasSum_angle eigenvalue hs M hM).summable.hasSum
  have hc : HasSum (fun k => (R.angle M (eigenvalue k) : ℂ) * Complex.I)
      ((R.phaseLift eigenvalue M : ℂ) * Complex.I) :=
    (Complex.hasSum_ofReal.mpr h).mul_right Complex.I
  exact hc.cexp

/-- The chosen half lift has the Majorana exponent. Real/Pfaffian geometry is external. -/
theorem Regulator.tendsto_halfPhase (R : Regulator) (eigenvalue : ℕ → ℝ)
    (hs : SpectralHypotheses eigenvalue R.kernel) :
    Tendsto (fun M => unitPhase (R.phaseLift eigenvalue M / 2)) atTop
      (𝓝 (unitPhase (-(Real.pi / 4) * etaHeat eigenvalue))) := by
  have h := (R.tendsto_phaseLift eigenvalue hs).div_const 2
  have heq : (-(Real.pi / 2) * etaHeat eigenvalue) / 2 = -(Real.pi / 4) * etaHeat eigenvalue := by ring
  rw [heq] at h
  exact continuous_unitPhase.continuousAt.tendsto.comp h

end PVEta
