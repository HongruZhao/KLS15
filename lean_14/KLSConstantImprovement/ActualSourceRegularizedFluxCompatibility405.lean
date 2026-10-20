import KLSConstantImprovement.ActualSourceRegularizedFluxH1405
import KLSConstantImprovement.ActualCompatibleJacobianCoercivity405
import KLS.HessianMetricMatrixProduct
import KLS.MatrixLogDetSecond

/-!
The actual regularized flux has a compatible Jacobian: H[k,epsilon] DU
is symmetric almost everywhere. The proof uses the genuine inverse
matrix differential and the constructed weak scalar Hessian. Full third
symmetry belongs to the smooth surrogate Hessian only; no Monge--Ampere
identity for that surrogate and no classical derivative of the solution
is asserted.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceRegularizedFluxCompatibility405
open KLS ActualBoundedCanonicalSource ActualSourceMetricRegularization405
open ActualSourceInverseMetricRegularization405 ActualSourceRegularizedEnergyForm405
open ActualSourceRegularizedFluxH1405 ActualCompatibleJacobianCoercivity405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

private theorem coordinateDerivativeMatrix_eq_fderiv
    {A : Space n → Matrix (Fin n) (Fin n) ℝ} (hA : ContDiff ℝ 1 A)
    (j : Fin n) (x : Space n) : coordinateDerivativeMatrix A j x =
      fderiv ℝ A x (EuclideanSpace.single j 1) := by
  ext i a
  exact MatrixCalculus.fderiv_matrix_entry (hA.differentiable_one x) i a _

theorem regularizedMetricInverse_coordinateDerivativeMatrix (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (j : Fin n) (x : Space n) :
    coordinateDerivativeMatrix (regularizedMetricInverse d k ε) j x =
      -(regularizedMetricInverse d k ε x *
        coordinateDerivativeMatrix (regularizedMetricHessian d k ε) j x * regularizedMetricInverse d k ε x) := by
  have hH : ContDiff ℝ 1 (regularizedMetricHessian d k ε) :=
    (regularizedMetricHessian_contDiff d k ε).of_le (by simp)
  have hJ : ContDiff ℝ 1 (regularizedMetricInverse d k ε) :=
    (regularizedMetricInverse_contDiff d k hε).of_le (by simp)
  rw [coordinateDerivativeMatrix_eq_fderiv hH, coordinateDerivativeMatrix_eq_fderiv hJ]
  exact MatrixCalculus.fderiv_matrix_inv_comp_apply (hH.differentiable_one x)
    (regularizedMetricHessian_posDef d k hε x).det_pos.ne' _

private theorem regularizedMetricHessian_entry_derivative (d : SourceData μ) (k : ℕ)
    (ε : ℝ) (i a j : Fin n) (x : Space n) :
    coordinateDerivative (fun y => regularizedMetricHessian d k ε y i a) j x =
      coordinateDerivative (fun y => coordinateHessian (mollify k d.potential) y i a) j x := by
  have hm : ContDiff ℝ 3 (mollify k d.potential) :=
    (mollify_contDiff d.source_C1.continuous.locallyIntegrable k).of_le (by simp)
  have hH : ContDiff ℝ 1 (fun y => coordinateHessian (mollify k d.potential) y i a) :=
    contDiff_coordinateHessian hm (m := 1) (by norm_num) i a
  change coordinateDerivative (fun y => coordinateHessian (mollify k d.potential) y i a +
    ε * (1 : Matrix (Fin n) (Fin n) ℝ) i a) j x = _
  unfold coordinateDerivative
  rw [fderiv_fun_add (hH.differentiable_one x) (differentiableAt_const _)]
  simp only [_root_.add_apply, fderiv_const_apply, _root_.zero_apply, add_zero]

theorem regularizedMetricHessian_third_swap (d : SourceData μ) (k : ℕ)
    (ε : ℝ) (i j a : Fin n) (x : Space n) :
    coordinateDerivative (fun y => regularizedMetricHessian d k ε y i a) j x =
      coordinateDerivative (fun y => regularizedMetricHessian d k ε y j a) i x := by
  rw [regularizedMetricHessian_entry_derivative, regularizedMetricHessian_entry_derivative]
  have hm : ContDiff ℝ 3 (mollify k d.potential) :=
    (mollify_contDiff d.source_C1.continuous.locallyIntegrable k).of_le (by simp)
  have ha : ContDiff ℝ 2 (coordinateDerivative (mollify k d.potential) a) :=
    contDiff_coordinateDerivative hm (m := 2) (by norm_num) a
  exact (coordinateHessian_symmetric ha x).apply i j

def regularizedFluxJacobian (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : Fin n → Fin n → Space n → ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => regularizedFluxDerivative d hn k hε g D i j x

/-- Differentiating the actual inverse coefficients gives H DU = Dp - (DH)U.
This is literal algebra in the already constructed weak derivative formula. -/
theorem regularizedFluxJacobian_mul_identity (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : Fin n → Fin n → Space n → ℝ) (i j : Fin n) (x : Space n) :
    (regularizedMetricHessian d k ε x * regularizedFluxJacobian d hn k hε g D x) i j =
      D i j x - (coordinateDerivativeMatrix (regularizedMetricHessian d k ε) j x *ᵥ
        (fun a => regularizedWeakFlux d hn k hε g a x)) i := by
  let H := regularizedMetricHessian d k ε x
  let J := regularizedMetricInverse d k ε x
  let A := coordinateDerivativeMatrix (regularizedMetricHessian d k ε) j x
  let P := coordinateDerivativeMatrix (regularizedMetricInverse d k ε) j x
  let p (a : Fin n) := weightedH1Derivative d.potential a (regularizedOrdinaryInverse d hn k hε g) x
  let q (a : Fin n) := D a j x
  have hHJ : H * J = 1 := Matrix.mul_nonsing_inv H
    ((Matrix.isUnit_iff_isUnit_det _).mp (regularizedMetricHessian_posDef d k hε x).isUnit)
  have hP : P = -(J * A * J) := regularizedMetricInverse_coordinateDerivativeMatrix d k hε j x
  have hHP : H * P = -(A * J) := by
    rw [hP, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hHJ, Matrix.one_mul]
  have hcol : (fun a => regularizedFluxJacobian d hn k hε g D x a j) = P *ᵥ p + J *ᵥ q := by
    funext a
    simp only [regularizedFluxJacobian, regularizedFluxDerivative, coordinateDerivativeMatrix,
      Matrix.mulVec, dotProduct, Pi.add_apply, Finset.sum_add_distrib, P, J, p, q]
  have he : H *ᵥ (fun a => regularizedFluxJacobian d hn k hε g D x a j) = q - A *ᵥ (J *ᵥ p) := by
    rw [hcol, Matrix.mulVec_add, Matrix.mulVec_mulVec p H P, Matrix.mulVec_mulVec q H J,
      hHP, hHJ, Matrix.one_mulVec, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
    ext a
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
    ring
  exact congrFun he i

theorem regularizedFluxJacobian_compatible_ae (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : Fin n → Fin n → Space n → ℝ)
    (hs : ∀ᵐ x ∂(volume : Measure (Space n)), ∀ i j, D i j x = D j i x) :
    ∀ᵐ x ∂(volume : Measure (Space n)),
      (regularizedMetricHessian d k ε x * regularizedFluxJacobian d hn k hε g D x).IsSymm := by
  filter_upwards [hs] with x hx
  apply Matrix.IsSymm.ext
  intro i j
  have hcurv : (coordinateDerivativeMatrix (regularizedMetricHessian d k ε) j x *ᵥ
      (fun a => regularizedWeakFlux d hn k hε g a x)) i =
      (coordinateDerivativeMatrix (regularizedMetricHessian d k ε) i x *ᵥ
        (fun a => regularizedWeakFlux d hn k hε g a x)) j := by
    change (∑ a : Fin n, coordinateDerivative (fun y => regularizedMetricHessian d k ε y i a) j x *
        regularizedWeakFlux d hn k hε g a x) =
      ∑ a : Fin n, coordinateDerivative (fun y => regularizedMetricHessian d k ε y j a) i x *
        regularizedWeakFlux d hn k hε g a x
    exact Finset.sum_congr rfl fun a _ =>
      congrArg (fun t : ℝ => t * regularizedWeakFlux d hn k hε g a x)
        (regularizedMetricHessian_third_swap d k ε i j a x)
  rw [regularizedFluxJacobian_mul_identity, regularizedFluxJacobian_mul_identity, hx j i, hcurv]

theorem exists_regularizedWeakFlux_compatibleJacobian (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0) :
    ∃ D : Fin n → Fin n → Space n → ℝ,
      (∀ i j E, IsCompact E →
        MemLp (regularizedFluxDerivative d hn k hε g D i j) 2 (volume.restrict E)) ∧
      (∀ i j, HasLocalWeakCoordinateDerivative (regularizedWeakFlux d hn k hε g i)
        (regularizedFluxDerivative d hn k hε g D i j) j) ∧
      (∀ᵐ x ∂(volume : Measure (Space n)),
        (regularizedMetricHessian d k ε x * regularizedFluxJacobian d hn k hε g D x).IsSymm) ∧
      (∀ᵐ x ∂(volume : Measure (Space n)),
        0 ≤ (regularizedFluxJacobian d hn k hε g D x * regularizedFluxJacobian d hn k hε g D x).trace) := by
  obtain ⟨D, _, _, hs, hD, hw⟩ := exists_regularizedWeakFlux_rawH1 d hn k hε g hg
  have hc := regularizedFluxJacobian_compatible_ae d hn k hε g D hs
  refine ⟨D, hD, hw, hc, ?_⟩
  filter_upwards [hc] with x hx
  exact compatible_jacobian_trace_nonneg (regularizedMetricHessian d k ε x)
    (regularizedFluxJacobian d hn k hε g D x) (regularizedMetricHessian_posDef d k hε x) hx

end KLSConstantImprovement.ActualSourceRegularizedFluxCompatibility405
#print axioms KLSConstantImprovement.ActualSourceRegularizedFluxCompatibility405.regularizedMetricInverse_coordinateDerivativeMatrix
#print axioms KLSConstantImprovement.ActualSourceRegularizedFluxCompatibility405.regularizedMetricHessian_third_swap
#print axioms KLSConstantImprovement.ActualSourceRegularizedFluxCompatibility405.regularizedFluxJacobian_mul_identity
#print axioms KLSConstantImprovement.ActualSourceRegularizedFluxCompatibility405.regularizedFluxJacobian_compatible_ae
#print axioms KLSConstantImprovement.ActualSourceRegularizedFluxCompatibility405.exists_regularizedWeakFlux_compatibleJacobian
