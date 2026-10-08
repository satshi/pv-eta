import PVEta.Spectral
import PVEta.Coefficients

/-! Identification with the normalized complex PV mode factors. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace PVEta

def normalize (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

lemma normalize_mul (z w : ℂ) : normalize (z * w) = normalize z * normalize w := by
  simp only [normalize, norm_mul, Complex.ofReal_mul]
  exact (div_mul_div_comm z _ w _).symm

lemma normalize_zpow (z : ℂ) (c : ℤ) : normalize (z ^ c) = normalize z ^ c := by
  simp only [normalize, norm_zpow, Complex.ofReal_zpow, div_zpow]

lemma normalize_prod {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    normalize (∏ j ∈ s, z j) = ∏ j ∈ s, normalize (z j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [normalize]
  | @insert j s hj ih => simp [Finset.prod_insert hj, normalize_mul, ih]

/-- This fixes the phase unambiguously for either sign of the eigenvalue. -/
lemma normalize_one_add_I (q : ℝ) :
    normalize (1 + (q : ℂ) * Complex.I) = unitPhase (Real.arctan q) := by
  have hn : ‖(1 : ℂ) + (q : ℂ) * Complex.I‖ = Real.sqrt (1 + q ^ 2) := by
    simp [Complex.norm_def, Complex.normSq_apply, pow_two]
  have ha : Complex.arg (1 + (q : ℂ) * Complex.I) = Real.arctan q := by
    simp [Complex.arg, hn, Real.arctan_eq_arcsin]
  have h := Complex.norm_mul_exp_arg_mul_I (1 + (q : ℂ) * Complex.I)
  rw [ha] at h
  have hne : ((‖(1 : ℂ) + (q : ℂ) * Complex.I‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, norm_ne_zero_iff]
    intro he
    have := congrArg Complex.re he
    simp at this
  unfold normalize unitPhase
  apply (div_eq_iff hne).2
  simpa only [mul_comm] using h.symm

lemma unitPhase_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    unitPhase (∑ j ∈ s, a j) = ∏ j ∈ s, unitPhase (a j) := by
  simp [unitPhase, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]

lemma unitPhase_int_mul (c : ℤ) (a : ℝ) :
    unitPhase ((c : ℝ) * a) = unitPhase a ^ c := by
  simp only [unitPhase, Complex.ofReal_mul, Complex.ofReal_intCast, mul_assoc]
  exact Complex.exp_int_mul _ _

/-- An eigenvalue-wise grouped product; the physical factor was canceled using
`sum_j c_j = 0` before writing it in this form. -/
def groupedFactor (R : Regulator) (c : Fin R.count → ℤ) (M x : ℝ) : ℂ :=
  ∏ j, (1 + ((R.scale j * M / x : ℝ) : ℂ) * Complex.I) ^ c j

lemma normalize_groupedFactor (R : Regulator) (c : Fin R.count → ℤ)
    (hc : ∀ j, R.weight j = (c j : ℝ)) (M x : ℝ) :
    normalize (groupedFactor R c M x) = unitPhase (R.angle M x) := by
  unfold groupedFactor Regulator.angle
  rw [normalize_prod, unitPhase_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [normalize_zpow, normalize_one_add_I, hc, unitPhase_int_mul]

/-- The infinite product of normalized *actual grouped complex factors* exists. -/
theorem Regulator.hasProd_normalized (R : Regulator) (c : Fin R.count → ℤ)
    (hc : ∀ j, R.weight j = (c j : ℝ)) (eigenvalue : ℕ → ℝ)
    (hs : SpectralHypotheses eigenvalue R.kernel) (M : ℝ) (hM : 0 < M) :
    HasProd (fun k => normalize (groupedFactor R c M (eigenvalue k)))
      (R.phase eigenvalue M) := by
  simp_rw [normalize_groupedFactor R c hc]
  exact R.hasProd_phase eigenvalue hs M hM

/-- The phase of the normalized infinite PV product has the eta limit. -/
theorem Regulator.tendsto_normalized_product (R : Regulator) (c : Fin R.count → ℤ)
    (hc : ∀ j, R.weight j = (c j : ℝ)) (eigenvalue : ℕ → ℝ)
    (hs : SpectralHypotheses eigenvalue R.kernel) :
    Tendsto (fun M : ℝ => ∏' k, normalize (groupedFactor R c M (eigenvalue k))) atTop
      (𝓝 (unitPhase (-(Real.pi / 2) * etaHeat eigenvalue))) := by
  apply (R.tendsto_phase eigenvalue hs).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
  exact (R.hasProd_normalized c hc eigenvalue hs M hM).tprod_eq.symm

end PVEta
