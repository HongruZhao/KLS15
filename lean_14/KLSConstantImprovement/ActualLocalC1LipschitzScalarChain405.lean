import KLSConstantImprovement.ActualLocalWeakVectorChain405

/-! The scalar local raw-H1 chain rule needs only a C1 Lipschitz scalar
map.  A one-coordinate application of the proved vector chain removes the
older unnecessary assumption that the scalar derivative is Lipschitz. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualLocalC1LipschitzScalarChain405
open KLS ActualLocalWeakVectorChain405 ActualVectorDifferential405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem local_C1_lipschitz_scalar_chain
    {f F : Space n → ℝ} {i : Fin n}
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E))
    (hFloc : ∀ E, IsCompact E → MemLp F 2 (volume.restrict E))
    (hw : HasLocalWeakCoordinateDerivative f F i)
    {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η) {L : ℝ≥0} (hLip : LipschitzWith L η) :
    HasLocalWeakCoordinateDerivative (fun x => η (f x))
      (fun x => deriv η (f x)*F x) i := by
  let π : (Unit → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj ()
  let ηv : (Unit → ℝ) → ℝ := fun v => η (v ())
  have hπ : LipschitzWith 1 (fun v : Unit → ℝ => v ()) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul, Pi.sub_apply] using norm_le_pi_norm (v-w) ()
  have hηv : ContDiff ℝ 1 ηv := hη.comp π.contDiff
  have hLv : LipschitzWith L ηv := by simpa only [ηv, Function.comp_def, mul_one] using hLip.comp hπ
  have hp (v : Unit → ℝ) : vectorPartial ηv () v = deriv η (v ()) := by
    have hd := (hη.differentiable one_ne_zero (v ())).hasDerivAt.comp_hasFDerivAt v π.hasFDerivAt
    have he := congrArg (fun D : (Unit → ℝ) →L[ℝ] ℝ => D (Pi.single () 1)) hd.fderiv
    simpa only [vectorPartial, ηv, π, Function.comp_def, _root_.smul_apply, smul_eq_mul,
      ContinuousLinearMap.proj_apply, Pi.single_eq_same, mul_one] using he
  have hc := local_vector_chain (ι := Unit) (fun _ => hf) (fun _ => hFloc)
    (fun _ => hw) hηv hLv
  simpa only [ηv, Fintype.sum_unique, hp] using hc

end KLSConstantImprovement.ActualLocalC1LipschitzScalarChain405
#print axioms KLSConstantImprovement.ActualLocalC1LipschitzScalarChain405.local_C1_lipschitz_scalar_chain
