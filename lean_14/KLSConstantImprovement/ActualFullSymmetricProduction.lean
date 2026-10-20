import KLSConstantImprovement.ActualFullTensorWhitening
import KLSConstantImprovement.FullSymmetricProductionExactLoss

/-! Full-rate error coercivity with actual tensor norms. The scalar inputs
of the prior coercivity lemma are discharged from finite sums, cyclic
projection, actual whitening and the constructed weak source tensor. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualFullSymmetricProduction
open KLS ActualBoundedCanonicalSource ActualFullSymmetricTensorOrdering
open ActualFullTensorWhitening MixedCubicRankSlicing FourthCubicProjectionDefect
variable {ι : Type*} [Fintype ι]
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem actual_tensor_error_decomposition (B : Matrix ι ι ℝ)
    (N T : ι → ι → ι → ℝ) (hN : ∀ i j k, N i j k = N j k i)
    (hT : ∀ i j k, T i j k = T j k i) :
    cubicEnergy (fun i j k => firstAction B N i j k - 2 * T i j k) =
      8 * cubicEnergy T / 3 - 2 * cubicEnergy (firstAction B.transpose N) +
        3 * cubicEnergy (hook (firstAction B.transpose N)) +
          3 * cubicEnergy (fun i j k => cyclicAverage (firstAction B N) i j k -
            (2/3 : ℝ) * T i j k) := by
  let Y := firstAction B N
  have hs := actual_hook_residual_split Y
  have ho := actual_full_tensor_hook_ordering B N hN
  have he := cubicEnergy_sub_mul Y T 2
  have hd := cubicEnergy_sub_mul (cyclicAverage Y) T (2/3)
  rw [pairing_cyclicAverage T Y hT] at hd
  refine FullSymmetricProductionExactLoss.exact_full_symmetric_error
    (cubicEnergy T) (cubicEnergy Y) (cubicEnergy (firstAction B.transpose N))
    (cubicEnergy (cyclicAverage Y)) (cubicEnergy (hook Y))
    (cubicEnergy (hook (firstAction B.transpose N))) (pairing T Y)
    (cubicEnergy (fun i j k => Y i j k - 2*T i j k))
    (cubicEnergy (fun i j k => cyclicAverage Y i j k - (2/3:ℝ)*T i j k))
    ?_ ho ?_ ?_
  · linarith
  · nlinarith
  · nlinarith

theorem actual_tensor_error_coercivity (B : Matrix ι ι ℝ)
    (N T : ι → ι → ι → ℝ) (hN : ∀ i j k, N i j k = N j k i)
    (hT : ∀ i j k, T i j k = T j k i) :
    4 * cubicEnergy T / 3 - cubicEnergy (firstAction B.transpose N) +
      3 * cubicEnergy (hook (firstAction B.transpose N)) / 2 ≤
        cubicEnergy (fun i j k => firstAction B N i j k - 2*T i j k) / 2 := by
  have he := actual_tensor_error_decomposition B N T hN hT
  have hn := cubicEnergy_nonneg (fun i j k =>
    cyclicAverage (firstAction B N) i j k - (2/3:ℝ)*T i j k)
  linarith

variable {n : ℕ}

def whitenedTargetThird {μ : Measure (Space n)} (d : SourceData μ)
    (T : Fin n → Fin n → Fin n → ℝ) (x : Space n) : Fin n → Fin n → Fin n → ℝ :=
  threeSlotAction (CFC.sqrt (coordinateHessian d.potential x)) T

theorem actual_source_error_coercivity_ae {μ : Measure (Space n)} (d : SourceData μ)
    (T : Fin n → Fin n → Fin n → ℝ) (hT : ∀ i j k, T i j k = T j k i)
    (B : Space n → Matrix (Fin n) (Fin n) ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      4 * cubicEnergy (whitenedTargetThird d T x) / 3 -
        cubicEnergy (firstAction (B x).transpose (whitenedSourceThird d x)) +
          3 * cubicEnergy (hook (firstAction (B x).transpose (whitenedSourceThird d x))) / 2 ≤
        cubicEnergy (fun i j k => firstAction (B x) (whitenedSourceThird d x) i j k -
          2 * whitenedTargetThird d T x i j k) / 2 := by
  filter_upwards [source_whitened_third_cyclic_ae d] with x hx
  exact actual_tensor_error_coercivity (B x) (whitenedSourceThird d x)
    (whitenedTargetThird d T x) hx
    (threeSlotAction_preserves_cyclic _ T hT)

end KLSConstantImprovement.ActualFullSymmetricProduction
#print axioms KLSConstantImprovement.ActualFullSymmetricProduction.actual_tensor_error_decomposition
#print axioms KLSConstantImprovement.ActualFullSymmetricProduction.actual_tensor_error_coercivity
#print axioms KLSConstantImprovement.ActualFullSymmetricProduction.actual_source_error_coercivity_ae
