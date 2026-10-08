import PVEta
import Lean.Util.CollectAxioms

/-!
Audit every kernel-safe declaration in the PVEta namespace, then print the dependencies of
selected principal results. This checks global axioms, not theorem hypotheses.
The audit is a build-time metaprogram, not an oracle used to prove any theorem.
-/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  -- Lean 4.19 also stores unsafe compiler IR helpers in the environment.
  -- They are not logical declarations and cannot be used in safe proofs.
  for (name, info) in env.constants.toList do
    if (`PVEta).isPrefixOf name && !info.isUnsafe then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on disallowed axiom {ax}"
      checked := checked + 1
  if checked == 0 then
    throwError "The audit did not find any PVEta declarations"
  logInfo m!"Axiom audit passed for {checked} kernel-safe PVEta declarations."

#print axioms PVEta.coefficient_sum
#print axioms PVEta.orderFour_moments
#print axioms PVEta.scalar_arctan_identity
#print axioms PVEta.Regulator.kernel_bound
#print axioms PVEta.Regulator.tendsto_kernel
#print axioms PVEta.Regulator.hasSum_angle
#print axioms PVEta.Regulator.summable_abs_angle
#print axioms PVEta.Regulator.tendsto_phaseLift
#print axioms PVEta.normalize_groupedFactor
#print axioms PVEta.Regulator.hasProd_normalized
#print axioms PVEta.Regulator.tendsto_normalized_product
#print axioms PVEta.Regulator.tendsto_halfPhase
#print axioms PVEta.unitPhase_half_sq
