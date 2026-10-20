import ActualFourthCumulantCoordinates

/-! Full coordinate permutation symmetry of the actual cumulants follows
from the actual local log-Laplace smoothness for the original law class. -/
noncomputable section
open MeasureTheory Set Metric
open scoped BigOperators ContDiff
namespace KLS.DeterministicBridgeIntegration
open KLS KLSBelow25.PairTensor
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem actualCumulant_coordinate_symmetric {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ) (d : ℕ) :
    Symmetric (fun α : Fin d→Fin n=>
      cumulantTensor μ d (fun j=>EuclideanSpace.single (α j) 1)) := by
  obtain ⟨r,hr,hD⟩ := hLC.exists_localNormExponentialDomain_one
  have hlog : ContDiffOn ℝ (⊤:ℕ∞) (tiltLogLaplace μ) (ball 0 r) := by
    intro z hz
    exact (contDiffAt_logLaplace_of_localNormExponentialDomain hD
      (by simpa only [mem_ball,dist_zero_right] using hz)).contDiffWithinAt
  intro π α
  unfold cumulantTensor
  simpa only [Function.comp_def] using local_iteratedFDeriv_comp_perm isOpen_ball hlog
    (fun j=>EuclideanSpace.single (α j) 1) π (by simpa using hr : (0:Space n)∈ball 0 r)

theorem actualFourthCumulant_full_symmetric {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) :
    Symmetric (fun α : Fin 4→Fin n=>
      actualFourthCumulantArray μ (α 0) (α 1) (α 2) (α 3)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have heq (α : Fin 4→Fin n) :
      actualFourthCumulantArray μ (α 0) (α 1) (α 2) (α 3)=
      cumulantTensor μ 4 (fun j=>EuclideanSpace.single (α j) 1) := by
    unfold actualFourthCumulantArray
    congr 1
    funext j
    fin_cases j <;> rfl
  intro π α
  change actualFourthCumulantArray μ ((α∘π) 0) ((α∘π) 1) ((α∘π) 2) ((α∘π) 3)=
    actualFourthCumulantArray μ (α 0) (α 1) (α 2) (α 3)
  rw [heq (α∘π),heq α]
  exact actualCumulant_coordinate_symmetric hμ.logConcave 4 π α

/-- Move the last slot into the second position, preserving the ordered tensor. -/
theorem actualFourthCumulant_last_to_second {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (i j k a : Fin n) :
    actualFourthCumulantArray μ i j k a=actualFourthCumulantArray μ i a j k := by
  let π : Equiv.Perm (Fin 4) := (Equiv.swap 2 3).trans (Equiv.swap 1 3)
  have h := actualFourthCumulant_full_symmetric hμ π ![i,j,k,a]
  norm_num [π,Function.comp_def,Equiv.trans_apply,Equiv.swap_apply_def] at h
  exact h.symm

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualCumulant_coordinate_symmetric
#print axioms KLS.DeterministicBridgeIntegration.actualFourthCumulant_last_to_second
