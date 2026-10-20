import KLSConstantImprovement.ActualSourceQuadraticEta405
import KLSConstantImprovement.ActualSourceNaturalGaffney405
import KLSConstantImprovement.ActualAffineRawBindings405
import KLSConstantImprovement.ActualSourceBoundedMassCutoffs405

/-! The actual quadratic Poisson row flux and response F=2U-Z, with a
chosen genuine weak Jacobian supplied by the proved natural Gaffney
construction. No derivative or PDE witness is an input. -/
noncomputable section
open Matrix MeasureTheory Filter Set
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualQuadraticResponseField405
open KLS ActualBoundedCanonicalSource ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405
open ActualSourceLocalizedGaffney405 ActualAffineMatrixTests405 ActualAffineRawBindings405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricInverse ActualQuarticThirdWhitening405
open ActualBoundedRawTestAlgebra405 ActualSourceBoundedMassCutoffs405 ActualWeakCanonicalMetricCore
variable {n : ℕ} {μ : Measure (Space n)}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def quadraticRowFlux (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (i a : Fin n) (x : Space n) : ℝ := naturalCanonicalFlux d (quadraticSourceDatum d (T i)) a x

def quadraticFluxJacobian (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) : Fin n → Fin n → Space n → ℝ :=
  Classical.choose (exists_naturalCanonicalFlux_gaffney d hn (quadraticSourceDatum d B)
    (quadraticSourceDatum_mean_zero d hμ B))

theorem quadratic_row_flux_local_L2 (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (a : Fin n) {E : Set (Space n)} (hE : IsCompact E) :
    MemLp (naturalCanonicalFlux d (quadraticSourceDatum d B) a) 2 (volume.restrict E) :=
  (Classical.choose_spec (exists_naturalCanonicalFlux_gaffney d hn (quadraticSourceDatum d B)
    (quadraticSourceDatum_mean_zero d hμ B))).1 a E hE

theorem quadratic_flux_jacobian_local_L2 (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) {E : Set (Space n)} (hE : IsCompact E) :
    MemLp (quadraticFluxJacobian d hn hμ B a b) 2 (volume.restrict E) :=
  (Classical.choose_spec (exists_naturalCanonicalFlux_gaffney d hn (quadraticSourceDatum d B)
    (quadraticSourceDatum_mean_zero d hμ B))).2.1 a b E hE

theorem quadratic_flux_jacobian_weak (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d (quadraticSourceDatum d B) a)
      (quadraticFluxJacobian d hn hμ B a b) b :=
  (Classical.choose_spec (exists_naturalCanonicalFlux_gaffney d hn (quadraticSourceDatum d B)
    (quadraticSourceDatum_mean_zero d hμ B))).2.2.1 a b

def quadraticResponseMatrix (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i a => 2 * quadraticRowFlux d T i a x - actualAffineMatrix d T x i a

def quadraticResponseDerivative (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i a b : Fin n) (x : Space n) : ℝ :=
  2 * quadraticFluxJacobian d hn hμ (T i) a b x -
    mixFamily (coordinateHessian d.potential x) T b i a

def quadraticResponseGram (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  quadraticResponseMatrix d T x * coordinateHessian d.potential x * (quadraticResponseMatrix d T x).transpose

theorem naturalCanonicalFlux_aestronglyMeasurable (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (i : Fin n) :
    AEStronglyMeasurable (naturalCanonicalFlux d g i) (potentialMeasure d.potential) := by
  have hroot := inverseSqrtMatrix_aestronglyMeasurable_of_ae_posDef
    (measurable_coordinateHessian d.potential) (d.hessian_ae_source.mono fun _ hx => hx.1)
  unfold naturalCanonicalFlux canonicalMetricRoot
  exact Finset.univ.aestronglyMeasurable_fun_sum fun a _ =>
    ((continuous_apply a).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hroot)).mul (Lp.memLp _).aestronglyMeasurable

theorem quadratic_response_local_weak_domains (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∀ i a E, IsCompact E → MemLp (fun x => quadraticResponseMatrix d T x i a) 2 (volume.restrict E)) ∧
    (∀ i a b E, IsCompact E → MemLp (quadraticResponseDerivative d hn hμ T i a b) 2 (volume.restrict E)) ∧
    (∀ i a b, HasLocalWeakCoordinateDerivative (fun x => quadraticResponseMatrix d T x i a)
      (quadraticResponseDerivative d hn hμ T i a b) b) := by
  have hZ (i a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => actualAffineMatrix d T x i a) 2 (volume.restrict E) :=
    (memLp_congr_ae (Eventually.of_forall (affineSliceTest_value d T i a))).mp
      ((affineSliceTest d T i a).value_local E hE)
  have hDZ (i a b : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => mixFamily (coordinateHessian d.potential x) T b i a) 2 (volume.restrict E) :=
    (memLp_congr_ae (Eventually.of_forall (affine_slice_derivative_omega d T i a b))).mp
      ((affineSliceTest d T i a).derivative_local b E hE)
  refine ⟨?_, ?_, ?_⟩
  · intro i a E hE
    exact ((quadratic_row_flux_local_L2 d hn hμ (T i) a hE).const_mul 2).sub (hZ i a E hE)
  · intro i a b E hE
    exact ((quadratic_flux_jacobian_local_L2 d hn hμ (T i) a b hE).const_mul 2).sub (hDZ i a b E hE)
  · intro i a b
    have hZw := (affineSliceTest d T i a).weak_derivative b
    have hZw' : HasLocalWeakCoordinateDerivative (fun x => actualAffineMatrix d T x i a)
        (fun x => mixFamily (coordinateHessian d.potential x) T b i a) b := by
      exact hZw.congr_ae (Eventually.of_forall (affineSliceTest_value d T i a))
        (Eventually.of_forall (affine_slice_derivative_omega d T i a b))
    have huLoc := locallyIntegrable_of_memLp_two_on_compacts
      (fun E hE => quadratic_row_flux_local_L2 d hn hμ (T i) a hE)
    have hDuLoc := locallyIntegrable_of_memLp_two_on_compacts
      (fun E hE => quadratic_flux_jacobian_local_L2 d hn hμ (T i) a b hE)
    have hzLoc := locallyIntegrable_of_memLp_two_on_compacts (hZ i a)
    have hdzLoc := locallyIntegrable_of_memLp_two_on_compacts (hDZ i a b)
    have hu2 : LocallyIntegrable (fun x => 2 * naturalCanonicalFlux d (quadraticSourceDatum d (T i)) a x) volume := by
      convert huLoc.smul (2 : ℝ) using 1
    have hzn : LocallyIntegrable (fun x => (-1 : ℝ) * actualAffineMatrix d T x i a) volume := by
      convert hzLoc.smul (-1 : ℝ) using 1
    have hDu2 : LocallyIntegrable (fun x => 2 * quadraticFluxJacobian d hn hμ (T i) a b x) volume := by
      convert hDuLoc.smul (2 : ℝ) using 1
    have hDzn : LocallyIntegrable (fun x => (-1 : ℝ) * mixFamily (coordinateHessian d.potential x) T b i a) volume := by
      convert hdzLoc.smul (-1 : ℝ) using 1
    have hh := ((quadratic_flux_jacobian_weak d hn hμ (T i) a b).const_mul 2).add
      (hZw'.const_mul (-1)) hu2 hzn hDu2 hDzn
    convert hh using 1 <;> funext x <;> simp only [quadraticResponseMatrix, Matrix.of_apply,
      quadraticRowFlux, quadraticResponseDerivative] <;> ring

end KLSConstantImprovement.ActualQuadraticResponseField405

#print axioms KLSConstantImprovement.ActualQuadraticResponseField405.quadratic_flux_jacobian_weak
#print axioms KLSConstantImprovement.ActualQuadraticResponseField405.naturalCanonicalFlux_aestronglyMeasurable
#print axioms KLSConstantImprovement.ActualQuadraticResponseField405.quadratic_response_local_weak_domains
