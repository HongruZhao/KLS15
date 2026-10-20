import KLSConstantImprovement.ActualSourceRegularizedGaffney405
import KLSConstantImprovement.ActualWhitenedJacobianEnergy405
import KLSConstantImprovement.ActualWeakCanonicalMetricOrdinaryGraph

/-!
Genuine global Hilbert fields for the metric limit. The first block is
H_original^(1/2)u; the second is H_epsilon^(1/2)Du H_epsilon^(-1/2).
Every coordinate's L2 domain follows from the proved actual Gaffney
energy, and the combined Hilbert norm equals the forcing norm.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceRegularizedEnergyVector405
open KLS ActualBoundedCanonicalSource ActualSourceLocalizedGaffney405
open ActualSourceRegularizedGaffney405 ActualSourceMetricRegularization405
open ActualSourceRegularizedEnergyForm405 ActualSourceRegularizedFluxH1405
open ActualSourceRegularizedFluxCompatibility405 ActualWeakCanonicalMetricOrdinaryGraph
open ActualWhitenedJacobianEnergy405 ActualCompactWeakSourceVectorSquare
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

abbrev GaffneyEnergyIndex (n : ℕ) := Fin n ⊕ (Fin n × Fin n)

abbrev GaffneyEnergyAmbient (d : SourceData μ) :=
  PiLp 2 (fun _ : GaffneyEnergyIndex n => Lp ℝ 2 (potentialMeasure d.potential))

def regularizedMassRootCoordinate (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (i : Fin n) (x : Space n) : ℝ :=
  ∑ a : Fin n, canonicalMetricUnroot d.potential x i a * regularizedWeakFlux d hn k hε g a x

def regularizedGaffneyEnergyField (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : Fin n → Fin n → Space n → ℝ) : GaffneyEnergyIndex n → Space n → ℝ
  | Sum.inl i => regularizedMassRootCoordinate d hn k hε g i
  | Sum.inr ij => fun x => whitenedJacobian (regularizedMetricHessian d k ε x)
      (regularizedFluxJacobian d hn k hε g D x) ij.1 ij.2

theorem regularizedMassRootCoordinate_aestronglyMeasurable (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential)) (i : Fin n) :
    AEStronglyMeasurable (regularizedMassRootCoordinate d hn k hε g i) (potentialMeasure d.potential) := by
  unfold regularizedMassRootCoordinate
  apply Finset.aestronglyMeasurable_fun_sum
  intro a _
  exact ((continuous_apply a).comp_aestronglyMeasurable
    ((continuous_apply i).comp_aestronglyMeasurable (sourceMetricUnroot_aestronglyMeasurable d))).mul
      (regularizedWeakFlux_memLp d hn k hε g a).aestronglyMeasurable

private theorem inverseSqrt_posDef (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    (inverseSqrtMatrix A).PosDef := by
  unfold inverseSqrtMatrix
  exact ((CFC.sqrt_nonneg A).posSemidef.posDef_iff_isUnit.mpr
    ((CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit)).inv

theorem regularizedGaffneyEnergyField_aestronglyMeasurable (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : Fin n → Fin n → Space n → ℝ)
    (hDu : ∀ i j, MemLp (regularizedFluxDerivative d hn k hε g D i j) 2 (potentialMeasure d.potential))
    (a : GaffneyEnergyIndex n) :
    AEStronglyMeasurable (regularizedGaffneyEnergyField d hn k hε g D a) (potentialMeasure d.potential) := by
  rcases a with i | ⟨i, j⟩
  · exact regularizedMassRootCoordinate_aestronglyMeasurable d hn k hε g i
  let R := fun x => inverseSqrtMatrix (regularizedMetricHessian d k ε x)
  let S := fun x => (R x)⁻¹
  have hH : ContDiff ℝ 1 (regularizedMetricHessian d k ε) :=
    (regularizedMetricHessian_contDiff d k ε).of_le (by simp)
  have hR : Continuous R := (locallyLipschitz_inverseSqrtMatrix_comp hH.locallyLipschitz
    (regularizedMetricHessian_posDef d k hε)).continuous
  have hS : Continuous S := by
    apply continuous_iff_continuousAt.mpr
    intro x
    change ContinuousAt (fun y : Space n => (R y)⁻¹) x
    have hinv : ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℝ => A⁻¹) (R x) :=
      matrix_inverse_continuousAt_posDef (inverseSqrt_posDef _ (regularizedMetricHessian_posDef d k hε x))
    have hRx : Tendsto R (𝓝 x) (𝓝 (R x)) := hR.continuousAt.tendsto
    exact hinv.tendsto.comp hRx
  change AEStronglyMeasurable (fun x => (S x * regularizedFluxJacobian d hn k hε g D x * R x) i j) _
  simp only [Matrix.mul_apply]
  apply Finset.aestronglyMeasurable_fun_sum
  intro a _
  apply AEStronglyMeasurable.mul
  · apply Finset.aestronglyMeasurable_fun_sum
    intro b _
    exact (((continuous_apply b).comp ((continuous_apply i).comp hS)).aestronglyMeasurable).mul
      (hDu b a).aestronglyMeasurable
  · exact ((continuous_apply j).comp ((continuous_apply a).comp hR)).aestronglyMeasurable

theorem regularizedGaffneyEnergyField_square_sum_ae (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : Fin n → Fin n → Space n → ℝ)
    (hc : ∀ᵐ x ∂(volume : Measure (Space n)),
      (regularizedMetricHessian d k ε x * regularizedFluxJacobian d hn k hε g D x).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (∑ a : GaffneyEnergyIndex n, regularizedGaffneyEnergyField d hn k hε g D a x ^ 2) =
        sourceVectorMass d.potential (regularizedWeakFlux d hn k hε g) x +
          sourceVectorJacobianEnergy (regularizedFluxDerivative d hn k hε g D) x := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, hc.filter_mono hac.ae_le] with x hx hxc
  have hv : (∑ i : Fin n, regularizedMassRootCoordinate d hn k hε g i x ^ 2) =
      sourceVectorMass d.potential (regularizedWeakFlux d hn k hε g) x := by
    let S := canonicalMetricUnroot d.potential x
    let u := fun i => regularizedWeakFlux d hn k hε g i x
    have he : (S *ᵥ u) ⬝ᵥ (S *ᵥ u) = u ⬝ᵥ (coordinateHessian d.potential x *ᵥ u) := by
      rw [← Matrix.dotProduct_transpose_mulVec S u (S *ᵥ u), Matrix.mulVec_mulVec,
        canonicalMetricUnroot_gram_at hx.1]
    change (∑ i : Fin n, (S *ᵥ u) i ^ 2) = _
    rw [show (∑ i : Fin n, (S *ᵥ u) i ^ 2) = (S *ᵥ u) ⬝ᵥ (S *ᵥ u) by
      simp only [dotProduct, pow_two], he]
    exact (matrix_quadratic_sum_eq_dotProduct (coordinateHessian d.potential x) u).symm
  have hZ := whitenedJacobian_frobenius (regularizedMetricHessian d k ε x)
    (regularizedFluxJacobian d hn k hε g D x) (regularizedMetricHessian_posDef d k hε x) hxc
  have hZsum : (∑ i : Fin n, ∑ j : Fin n,
      whitenedJacobian (regularizedMetricHessian d k ε x) (regularizedFluxJacobian d hn k hε g D x) i j ^ 2) =
      sourceVectorJacobianEnergy (regularizedFluxDerivative d hn k hε g D) x := by
    simpa only [matrixFrobeniusSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      sourceVectorJacobianEnergy, regularizedFluxJacobian] using hZ
  calc
    _ = (∑ i : Fin n, regularizedMassRootCoordinate d hn k hε g i x ^ 2) +
        (∑ i : Fin n, ∑ j : Fin n,
          whitenedJacobian (regularizedMetricHessian d k ε x) (regularizedFluxJacobian d hn k hε g D x) i j ^ 2) := by
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, regularizedGaffneyEnergyField]
    _ = _ := congrArg₂ (fun a b : ℝ => a + b) hv hZsum

theorem exists_actual_regularizedGaffney_energyVector (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0) :
    ∃ (D : Fin n → Fin n → Space n → ℝ) (V : GaffneyEnergyAmbient d),
      (∀ i j, MemLp (regularizedFluxDerivative d hn k hε g D i j) 2 (potentialMeasure d.potential)) ∧
      (∀ i j, HasLocalWeakCoordinateDerivative (regularizedWeakFlux d hn k hε g i)
        (regularizedFluxDerivative d hn k hε g D i j) j) ∧
      (∀ᵐ x ∂(volume : Measure (Space n)),
        (regularizedMetricHessian d k ε x * regularizedFluxJacobian d hn k hε g D x).IsSymm) ∧
      (∀ a : GaffneyEnergyIndex n,
        (V a : Space n → ℝ) =ᵐ[potentialMeasure d.potential] regularizedGaffneyEnergyField d hn k hε g D a) ∧
      ‖V‖ ^ 2 = ‖g‖ ^ 2 := by
  obtain ⟨D, hDu, hw, hc, _, hM, hQ, hG, _, _⟩ := exists_regularizedWeakFlux_exact_gaffney d hn k hε g hg
  let ν := potentialMeasure d.potential
  let f := regularizedGaffneyEnergyField d hn k hε g D
  have hm (a : GaffneyEnergyIndex n) : AEStronglyMeasurable (f a) ν :=
    regularizedGaffneyEnergyField_aestronglyMeasurable d hn k hε g D hDu a
  have he := regularizedGaffneyEnergyField_square_sum_ae d hn k hε g D hc
  have hE : Integrable (fun x => sourceVectorMass d.potential (regularizedWeakFlux d hn k hε g) x +
      sourceVectorJacobianEnergy (regularizedFluxDerivative d hn k hε g D) x) ν := hM.add hQ
  have hf (a : GaffneyEnergyIndex n) : MemLp (f a) 2 ν := by
    apply (memLp_two_iff_integrable_sq (hm a)).mpr
    apply hE.mono' ((hm a).pow 2)
    filter_upwards [he] with x hx
    change ‖f a x ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _), ← hx]
    exact Finset.single_le_sum (fun b _ => sq_nonneg (f b x)) (Finset.mem_univ a)
  let V : GaffneyEnergyAmbient d := WithLp.toLp 2 (fun a => (hf a).toLp (f a))
  have hV (a : GaffneyEnergyIndex n) : (V a : Space n → ℝ) =ᵐ[ν] f a := (hf a).coeFn_toLp
  refine ⟨D, V, hDu, hw, hc, hV, ?_⟩
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    (∑ a : GaffneyEnergyIndex n, ‖V a‖ ^ 2) = ∑ a : GaffneyEnergyIndex n, ∫ x, f a x ^ 2 ∂ν := by
      apply Finset.sum_congr rfl
      intro a _
      rw [L2.norm_sq_eq_integral_sq]
      apply integral_congr_ae
      filter_upwards [hV a] with x hx
      rw [hx]
    _ = ∫ x, ∑ a : GaffneyEnergyIndex n, f a x ^ 2 ∂ν := by
      symm
      apply integral_finsetSum
      intro a _
      have hp := (hf a).integrable_mul (hf a)
      change Integrable (fun x => f a x * f a x) ν at hp
      simpa only [pow_two] using hp
    _ = _ := (integral_congr_ae he).trans hG

end KLSConstantImprovement.ActualSourceRegularizedEnergyVector405
#print axioms KLSConstantImprovement.ActualSourceRegularizedEnergyVector405.regularizedMassRootCoordinate_aestronglyMeasurable
#print axioms KLSConstantImprovement.ActualSourceRegularizedEnergyVector405.regularizedGaffneyEnergyField_aestronglyMeasurable
#print axioms KLSConstantImprovement.ActualSourceRegularizedEnergyVector405.regularizedGaffneyEnergyField_square_sum_ae
#print axioms KLSConstantImprovement.ActualSourceRegularizedEnergyVector405.exists_actual_regularizedGaffney_energyVector
