import KLSConstantImprovement.ActualCubicPoincareFourthSector

/-! A same-law affine charge improves the unconditional cubic Poincare
estimate. The canonical cubic has mean gradient zero, so applying the
current original-class endpoint to its affine perturbations retains an
additional coordinate covariance square. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open scoped BigOperators ENNReal ContDiff
namespace KLSConstantImprovement.ActualCubicAffineRegression
open KLS KLS.DeterministicBridge KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicGradientEnergy
open ActualCubicPoincareFourthSector QuadraticCovarianceCharge
variable {n : ℕ}
set_option maxHeartbeats 4500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def affinePerturbation (μ : Measure (Space n)) (T : Array3 (Fin n)) (u : Space n) (x : Space n) : ℝ :=
  tensorPolynomial μ T x+inner ℝ x u

theorem centeredQuadratic_mean_zero {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (H : Matrix (Fin n) (Fin n) ℝ) :
    (∫ x,ActualCubicGradientEnergy.centeredQuadratic H x ∂μ)=0 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hQ := memLp_matrixQuadratic_of_coordinateProducts
    hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul H
  unfold ActualCubicGradientEnergy.centeredQuadratic
  rw [integral_sub (hQ.integrable (by norm_num)) (integrable_const _),
    isotropic_integral_matrixQuadratic hμ.isotropic]
  simp

theorem inner_coordinateDerivative (u : Space n) (i : Fin n) (x : Space n) :
    coordinateDerivative (fun y : Space n => inner ℝ y u) i x=u i := by
  unfold coordinateDerivative
  have hd := fderiv_inner_apply ℝ (f := id) (g := fun _ : Space n => u) (x := x)
    differentiableAt_id (differentiableAt_const u) (EuclideanSpace.single i 1)
  simp only [fderiv_id,fderiv_fun_const,ContinuousLinearMap.id_apply,Pi.zero_apply,ContinuousLinearMap.zero_apply,
    inner_zero_right,zero_add,id_eq,EuclideanSpace.inner_single_left,RCLike.conj_to_real,one_mul] at hd
  exact hd

theorem affinePerturbation_derivative (μ : Measure (Space n)) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (u : Space n) (i : Fin n) (x : Space n) :
    coordinateDerivative (affinePerturbation μ T u) i x=
      3*ActualCubicGradientEnergy.centeredQuadratic (T i) x+u i := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : Space n => inner ℝ y u) :=
    contDiff_id.inner ℝ contDiff_const
  unfold affinePerturbation
  change coordinateDerivative (tensorPolynomial μ T+(fun y : Space n => inner ℝ y u)) i x=_
  rw [coordinateDerivative_add ((tensorPolynomial_contDiff μ T).differentiable (by simp) x)
    (hlin.differentiable (by simp) x),tensorPolynomial_derivative μ T hT12 hT23,
    inner_coordinateDerivative]

theorem affinePerturbation_original_test {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (u : Space n) : LocallyLipschitzTests μ (affinePerturbation μ T u) := by
  have hd : ContDiff ℝ 1 (affinePerturbation μ T u) :=
    ((tensorPolynomial_contDiff μ T).of_le (by simp)).add (contDiff_id.inner ℝ contDiff_const)
  exact ⟨hd.locallyLipschitz,(tensorPolynomial_memLp hμ T).add (hμ.isotropic.memLp_inner u)⟩

theorem affinePerturbation_variance {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (u : Space n) :
    ProbabilityTheory.variance (affinePerturbation μ T u) μ=
      ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      2*inner ℝ (covarianceVector μ (tensorPolynomial μ T)) u+‖u‖^2 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hP := tensorPolynomial_memLp hμ T
  have hlin := hμ.isotropic.memLp_inner u
  have hc : covariance (tensorPolynomial μ T) (fun x => inner ℝ x u) μ=
      inner ℝ (covarianceVector μ (tensorPolynomial μ T)) u := by
    rw [covariance_eq_sub hP hlin,tensorPolynomial_centered hμ T,zero_mul,sub_zero,
      covarianceVector_pairing hμ.isotropic hP u]
    apply integral_congr_ae
    exact .of_forall fun x => by simp only [Pi.mul_apply];ring
  unfold affinePerturbation
  rw [ProbabilityTheory.variance_fun_add hP hlin,hc,hμ.isotropic.real_variance_inner]

theorem affinePerturbation_gradient_energy {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ a b c,T a b c=T b a c)
    (hT23 : ∀ a b c,T a b c=T a c b) (u : Space n) :
    Integrable (fun x => ‖gradient (affinePerturbation μ T u) x‖^2) μ ∧
      (∫ x,‖gradient (affinePerturbation μ T u) x‖^2 ∂μ)=
        9*(fourthContraction μ T+2*tensorSquare T)+‖u‖^2 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let q (i : Fin n) := ActualCubicGradientEnergy.centeredQuadratic (T i)
  have he : (fun x => ‖gradient (affinePerturbation μ T u) x‖^2)=
      fun x => 9*(∑ i,(q i x)^2)+6*(∑ i,u i*q i x)+‖u‖^2 := by
    funext x
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [←coordinateDerivative_eq_gradient,affinePerturbation_derivative μ T hT12 hT23]
    dsimp only [q]
    ring
  have hi0 : Integrable (fun x => 9*(∑ i,(q i x)^2)) μ :=
    (integrable_finsetSum Finset.univ fun i _ => (centeredQuadratic_memLp hμ (T i)).integrable_sq).const_mul 9
  have hi1 : Integrable (fun x => 6*(∑ i,u i*q i x)) μ :=
    (integrable_finsetSum Finset.univ fun i _ =>
      ((centeredQuadratic_memLp hμ (T i)).integrable (by norm_num)).const_mul (u i)).const_mul 6
  have hi2 : Integrable (fun _ : Space n => ‖u‖^2) μ := integrable_const _
  constructor
  · rw [he]
    exact (hi0.add hi1).add hi2
  · have hadd0 := integral_add hi0 hi1
    have hadd1 := integral_add (hi0.add hi1) hi2
    simp only [Pi.add_apply] at hadd0 hadd1
    rw [he,hadd1,hadd0,
      integral_const_mul,integral_const_mul,
      integral_finsetSum Finset.univ (fun i _ => (centeredQuadratic_memLp hμ (T i)).integrable_sq),
      integral_finsetSum Finset.univ (fun i _ =>
        ((centeredQuadratic_memLp hμ (T i)).integrable (by norm_num)).const_mul (u i))]
    simp_rw [integral_const_mul,centeredQuadratic_mean_zero hμ]
    simp only [mul_zero,Finset.sum_const_zero,add_zero,integral_const,probReal_univ,one_smul]
    change 9*(∑ i,∫ x,(ActualCubicGradientEnergy.centeredQuadratic (T i) x)^2 ∂μ)+‖u‖^2=_
    rw [sum_centeredQuadratic_integrals hμ T]

theorem affinePerturbation_poincare {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b) (u : Space n) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      2*inner ℝ (covarianceVector μ (tensorPolynomial μ T)) u+‖u‖^2 ≤
        LongPrefixCubicBellmanEndpoint.bound*(9*(fourthContraction μ T+2*tensorSquare T)+‖u‖^2) := by
  have hb := LongPrefixCubicBellmanEndpoint.original_poincare hn hμ
    (affinePerturbation_original_test hμ T u)
  have henergy := affinePerturbation_gradient_energy hμ T hT12 hT23 u
  have he : energy μ (affinePerturbation μ T u)=
      ENNReal.ofReal (9*(fourthContraction μ T+2*tensorSquare T)+‖u‖^2) := by
    unfold energy
    rw [←ofReal_integral_eq_lintegral_ofReal henergy.1
      (Filter.Eventually.of_forall fun _ => sq_nonneg _),henergy.2]
  rw [he] at hb
  have hr := ENNReal.toReal_mono
    (ne_of_lt (ENNReal.mul_lt_top (ENNReal.div_lt_top (by norm_num) (by norm_num)) ENNReal.ofReal_lt_top)) hb
  change ProbabilityTheory.variance (affinePerturbation μ T u) μ≤_ at hr
  have hnE : 0≤9*(fourthContraction μ T+2*tensorSquare T)+‖u‖^2 := by
    rw [←henergy.2]
    exact integral_nonneg fun _ => sq_nonneg _
  rw [affinePerturbation_variance hμ T u,ENNReal.toReal_mul,ENNReal.toReal_ofReal hnE] at hr
  have hB : (280181882107013433/19531250000000000 : ℝ≥0∞).toReal=
      LongPrefixCubicBellmanEndpoint.bound := by norm_num [LongPrefixCubicBellmanEndpoint.bound]
  rw [hB] at hr
  exact hr

theorem tensorPolynomial_affine_charge {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      ‖covarianceVector μ (tensorPolynomial μ T)‖^2/(LongPrefixCubicBellmanEndpoint.bound-1) ≤
        9*LongPrefixCubicBellmanEndpoint.bound*(fourthContraction μ T+2*tensorSquare T) := by
  let L := covarianceVector μ (tensorPolynomial μ T)
  let C := LongPrefixCubicBellmanEndpoint.bound
  have hC : 0<C-1 := by norm_num [C,LongPrefixCubicBellmanEndpoint.bound]
  have hb := affinePerturbation_poincare hn hμ T hT12 hT23 ((C-1)⁻¹ • L)
  change ProbabilityTheory.variance (tensorPolynomial μ T) μ+2*inner ℝ L ((C-1)⁻¹ • L)+
    ‖(C-1)⁻¹ • L‖^2≤C*(9*(fourthContraction μ T+2*tensorSquare T)+‖(C-1)⁻¹ • L‖^2) at hb
  rw [inner_smul_right,real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hb
  have hid : (C-1)*(C-1)⁻¹=1 := mul_inv_cancel₀ (ne_of_gt hC)
  have hid2 : (C-1)*((C-1)⁻¹)^2=(C-1)⁻¹ := by
    calc
      _ = ((C-1)*(C-1)⁻¹)*(C-1)⁻¹ := by ring
      _ = _ := by rw [hid,one_mul]
  change ProbabilityTheory.variance (tensorPolynomial μ T) μ+‖L‖^2/(C-1)≤
    9*C*(fourthContraction μ T+2*tensorSquare T)
  have hpay : C*((C-1)⁻¹)^2*‖L‖^2-((C-1)⁻¹)^2*‖L‖^2=(C-1)⁻¹*‖L‖^2 := by
    calc
      _ = ((C-1)*((C-1)⁻¹)^2)*‖L‖^2 := by ring
      _ = _ := by rw [hid2]
  rw [div_eq_mul_inv]
  linear_combination hb+hpay

end KLSConstantImprovement.ActualCubicAffineRegression
#print axioms KLSConstantImprovement.ActualCubicAffineRegression.centeredQuadratic_mean_zero
#print axioms KLSConstantImprovement.ActualCubicAffineRegression.inner_coordinateDerivative
#print axioms KLSConstantImprovement.ActualCubicAffineRegression.affinePerturbation_derivative
#print axioms KLSConstantImprovement.ActualCubicAffineRegression.affinePerturbation_original_test
#print axioms KLSConstantImprovement.ActualCubicAffineRegression.affinePerturbation_variance
#print axioms KLSConstantImprovement.ActualCubicAffineRegression.affinePerturbation_gradient_energy
#print axioms KLSConstantImprovement.ActualCubicAffineRegression.affinePerturbation_poincare
#print axioms KLSConstantImprovement.ActualCubicAffineRegression.tensorPolynomial_affine_charge
