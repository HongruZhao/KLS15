import KLSConstantImprovement.ActualCubicQuadraticDeficit

/-! Affine perturbations of the literal mixed cubic/quadratic polynomial.
The original-law test, coordinate covariance, mean gradient, variance, and
Dirichlet energy are all proved before the completed regression square. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open scoped BigOperators ENNReal ContDiff
namespace KLSConstantImprovement.ActualCubicAffineQuadraticRegression
open KLS KLS.DeterministicBridge KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicGradientEnergy
open ActualCubicPoincareFourthSector ActualCubicAffineRegression QuadraticCovarianceCharge
open ActualCubicQuadraticRegression ActualCubicQuadraticDeficit
variable {n : ℕ}
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def affineQuadraticPerturbation (μ : Measure (Space n)) (T : Array3 (Fin n))
    (B : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (u : Space n) (x : Space n) : ℝ :=
  quadraticPerturbation μ T B s x+inner ℝ x u

theorem quadraticPerturbation_contDiff (μ : Measure (Space n)) (T : Array3 (Fin n))
    (B : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (quadraticPerturbation μ T B s) :=
  (tensorPolynomial_contDiff μ T).sub ((centeredQuadratic_contDiff B).const_smul s)

theorem matrixAction_coordinate_mean_zero {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (∫ x,(matrixAction B x) i ∂μ)=0 := by
  change (∫ x,∑ j,B i j*x j ∂μ)=0
  rw [integral_finsetSum Finset.univ (fun j _ => (hμ.isotropic.integrable_coordinate j).const_mul _)]
  simp_rw [integral_const_mul,hμ.isotropic.integral_coordinate,mul_zero]
  simp

theorem quadraticPerturbation_coordinateDerivative_memLp {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (s : ℝ) (i : Fin n) :
    MemLp (coordinateDerivative (quadraticPerturbation μ T B s) i) 2 μ := by
  have he : coordinateDerivative (quadraticPerturbation μ T B s) i=
      fun x => 3*ActualCubicGradientEnergy.centeredQuadratic (T i) x-2*s*(matrixAction B x) i :=
    funext (quadraticPerturbation_derivative μ T hT12 hT23 B hB s i)
  rw [he]
  exact ((centeredQuadratic_memLp hμ (T i)).const_mul 3).sub
    ((matrixAction_coordinate_memLp hμ B i).const_mul (2*s))

theorem quadraticPerturbation_mean_gradient_zero {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (s : ℝ) (i : Fin n) :
    (∫ x,coordinateDerivative (quadraticPerturbation μ T B s) i x ∂μ)=0 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have he : coordinateDerivative (quadraticPerturbation μ T B s) i=
      fun x => 3*ActualCubicGradientEnergy.centeredQuadratic (T i) x-2*s*(matrixAction B x) i :=
    funext (quadraticPerturbation_derivative μ T hT12 hT23 B hB s i)
  have hi0 := ((centeredQuadratic_memLp hμ (T i)).integrable (by norm_num)).const_mul 3
  have hi1 := ((matrixAction_coordinate_memLp hμ B i).integrable (by norm_num)).const_mul (2*s)
  rw [he,integral_sub (f := fun x => 3*ActualCubicGradientEnergy.centeredQuadratic (T i) x)
    (g := fun x => 2*s*(matrixAction B x) i) hi0 hi1,integral_const_mul,integral_const_mul,
    centeredQuadratic_mean_zero hμ,matrixAction_coordinate_mean_zero hμ B i]
  ring

theorem covarianceVector_quadraticPerturbation {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (B : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) :
    covarianceVector μ (quadraticPerturbation μ T B s)=
      covarianceVector μ (tensorPolynomial μ T)-s • covarianceVector μ (ActualCubicGradientEnergy.centeredQuadratic B) := by
  ext i
  change (∫ x,x i*quadraticPerturbation μ T B s x ∂μ)=
    (∫ x,x i*tensorPolynomial μ T x ∂μ)-s*(∫ x,x i*ActualCubicGradientEnergy.centeredQuadratic B x ∂μ)
  have he : (fun x => x i*quadraticPerturbation μ T B s x)=
      fun x => x i*tensorPolynomial μ T x-s*(x i*ActualCubicGradientEnergy.centeredQuadratic B x) := by
    funext x
    unfold quadraticPerturbation
    ring
  rw [he,integral_sub (f := fun x => x i*tensorPolynomial μ T x)
    (g := fun x => s*(x i*ActualCubicGradientEnergy.centeredQuadratic B x))
    ((hμ.isotropic.memLp_coordinate i).integrable_mul (tensorPolynomial_memLp hμ T))
    (((hμ.isotropic.memLp_coordinate i).integrable_mul (centeredQuadratic_memLp hμ B)).const_mul s),
    integral_const_mul]

theorem affineQuadraticPerturbation_original_test {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (B : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (u : Space n) :
    LocallyLipschitzTests μ (affineQuadraticPerturbation μ T B s u) := by
  have hd : ContDiff ℝ 1 (affineQuadraticPerturbation μ T B s u) :=
    ((quadraticPerturbation_contDiff μ T B s).of_le (by simp)).add
      (contDiff_id.inner ℝ contDiff_const)
  exact ⟨hd.locallyLipschitz,((quadraticPerturbation_original_test hμ T B s).2).add
    (hμ.isotropic.memLp_inner u)⟩

theorem affineQuadraticPerturbation_derivative (μ : Measure (Space n)) (T : Array3 (Fin n))
    (B : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (u : Space n) (i : Fin n) (x : Space n) :
    coordinateDerivative (affineQuadraticPerturbation μ T B s u) i x=
      coordinateDerivative (quadraticPerturbation μ T B s) i x+u i := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : Space n => inner ℝ y u) :=
    contDiff_id.inner ℝ contDiff_const
  unfold affineQuadraticPerturbation
  change coordinateDerivative (quadraticPerturbation μ T B s+(fun y => inner ℝ y u)) i x=_
  rw [coordinateDerivative_add ((quadraticPerturbation_contDiff μ T B s).differentiable (by simp) x)
    (hlin.differentiable (by simp) x),inner_coordinateDerivative]

theorem affineQuadraticPerturbation_variance {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (B : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (u : Space n) :
    ProbabilityTheory.variance (affineQuadraticPerturbation μ T B s u) μ=
      ProbabilityTheory.variance (quadraticPerturbation μ T B s) μ+
      2*inner ℝ (covarianceVector μ (quadraticPerturbation μ T B s)) u+‖u‖^2 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hp := (quadraticPerturbation_original_test hμ T B s).2
  have hl := hμ.isotropic.memLp_inner u
  have hc : covariance (quadraticPerturbation μ T B s) (fun x => inner ℝ x u) μ=
      inner ℝ (covarianceVector μ (quadraticPerturbation μ T B s)) u := by
    rw [covariance_eq_sub hp hl,hμ.isotropic.integral_inner,mul_zero,sub_zero,
      covarianceVector_pairing hμ.isotropic hp u]
    apply integral_congr_ae
    exact .of_forall fun x => by simp only [Pi.mul_apply];ring
  unfold affineQuadraticPerturbation
  rw [ProbabilityTheory.variance_fun_add hp hl,hc,hμ.isotropic.real_variance_inner]

theorem affineQuadraticPerturbation_gradient_energy {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ a b c,T a b c=T b a c)
    (hT23 : ∀ a b c,T a b c=T a c b) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsSymm) (s : ℝ) (u : Space n) :
    Integrable (fun x => ‖gradient (affineQuadraticPerturbation μ T B s u) x‖^2) μ ∧
      (∫ x,‖gradient (affineQuadraticPerturbation μ T B s u) x‖^2 ∂μ)=
        9*(fourthContraction μ T+2*tensorSquare T)+4*s^2*matrixFrobeniusSq B-
          12*s*quadraticGradientPairing μ T B+‖u‖^2 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let f := quadraticPerturbation μ T B s
  have he : (fun x => ‖gradient (affineQuadraticPerturbation μ T B s u) x‖^2)=
      fun x => ‖gradient f x‖^2+2*(∑ i,u i*coordinateDerivative f i x)+‖u‖^2 := by
    funext x
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [←coordinateDerivative_eq_gradient,←coordinateDerivative_eq_gradient,
      affineQuadraticPerturbation_derivative]
    dsimp only [f]
    ring
  have henergy := quadraticPerturbation_gradient_energy hμ T hT12 hT23 B hB s
  have hi0 : Integrable (fun x => ‖gradient f x‖^2) μ := henergy.1
  have hi1 : Integrable (fun x => 2*(∑ i,u i*coordinateDerivative f i x)) μ :=
    (integrable_finsetSum Finset.univ fun i _ =>
      ((quadraticPerturbation_coordinateDerivative_memLp hμ T hT12 hT23 B hB s i).integrable
        (by norm_num)).const_mul (u i)).const_mul 2
  have hi2 : Integrable (fun _ : Space n => ‖u‖^2) μ := integrable_const _
  constructor
  · rw [he]
    exact (hi0.add hi1).add hi2
  · have ha := integral_add hi0 hi1
    have hb := integral_add (hi0.add hi1) hi2
    simp only [Pi.add_apply] at ha hb
    rw [he,hb,ha,integral_const_mul,
      integral_finsetSum Finset.univ (fun i _ =>
        ((quadraticPerturbation_coordinateDerivative_memLp hμ T hT12 hT23 B hB s i).integrable
          (by norm_num)).const_mul (u i))]
    simp_rw [integral_const_mul,quadraticPerturbation_mean_gradient_zero hμ T hT12 hT23 B hB s]
    simp only [mul_zero,Finset.sum_const_zero,add_zero,integral_const,probReal_univ,one_smul]
    rw [henergy.2]

theorem affineQuadraticPerturbation_poincare {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (s : ℝ) (u : Space n)
    (C : ℝ) (hC : LongPrefixCubicBellmanEndpoint.bound≤C) :
    ProbabilityTheory.variance (quadraticPerturbation μ T B s) μ+
      2*inner ℝ (covarianceVector μ (quadraticPerturbation μ T B s)) u+‖u‖^2 ≤
    C*(9*(fourthContraction μ T+2*tensorSquare T)+4*s^2*matrixFrobeniusSq B-
      12*s*quadraticGradientPairing μ T B+‖u‖^2) := by
  have hb := LongPrefixCubicBellmanEndpoint.original_poincare hn hμ
    (affineQuadraticPerturbation_original_test hμ T B s u)
  have henergy := affineQuadraticPerturbation_gradient_energy hμ T hT12 hT23 B hB s u
  have he : energy μ (affineQuadraticPerturbation μ T B s u)=
      ENNReal.ofReal (9*(fourthContraction μ T+2*tensorSquare T)+4*s^2*matrixFrobeniusSq B-
        12*s*quadraticGradientPairing μ T B+‖u‖^2) := by
    unfold energy
    rw [←ofReal_integral_eq_lintegral_ofReal henergy.1
      (Filter.Eventually.of_forall fun _ => sq_nonneg _),henergy.2]
  rw [he] at hb
  have hr := ENNReal.toReal_mono
    (ne_of_lt (ENNReal.mul_lt_top (ENNReal.div_lt_top (by norm_num) (by norm_num)) ENNReal.ofReal_lt_top)) hb
  change ProbabilityTheory.variance (affineQuadraticPerturbation μ T B s u) μ≤_ at hr
  have hE : 0≤9*(fourthContraction μ T+2*tensorSquare T)+4*s^2*matrixFrobeniusSq B-
      12*s*quadraticGradientPairing μ T B+‖u‖^2 := by
    rw [←henergy.2]
    exact integral_nonneg fun _ => sq_nonneg _
  rw [affineQuadraticPerturbation_variance hμ T B s u,ENNReal.toReal_mul,ENNReal.toReal_ofReal hE] at hr
  have hCb : (280181882107013433/19531250000000000 : ℝ≥0∞).toReal=
      LongPrefixCubicBellmanEndpoint.bound := by norm_num [LongPrefixCubicBellmanEndpoint.bound]
  rw [hCb] at hr
  exact hr.trans (mul_le_mul_of_nonneg_right hC hE)

theorem quadraticPerturbation_affine_charge {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (s C : ℝ)
    (hC : LongPrefixCubicBellmanEndpoint.bound≤C) :
    ProbabilityTheory.variance (quadraticPerturbation μ T B s) μ+
      ‖covarianceVector μ (quadraticPerturbation μ T B s)‖^2/(C-1)≤
        C*(9*(fourthContraction μ T+2*tensorSquare T)+4*s^2*matrixFrobeniusSq B-
          12*s*quadraticGradientPairing μ T B) := by
  let L := covarianceVector μ (quadraticPerturbation μ T B s)
  have hC1 : 0<C-1 := by
    have hb : 1<LongPrefixCubicBellmanEndpoint.bound := by norm_num [LongPrefixCubicBellmanEndpoint.bound]
    linarith
  have hp := affineQuadraticPerturbation_poincare hn hμ T hT12 hT23 B hB s ((C-1)⁻¹ • L) C hC
  change ProbabilityTheory.variance (quadraticPerturbation μ T B s) μ+
    2*inner ℝ L ((C-1)⁻¹ • L)+‖(C-1)⁻¹ • L‖^2≤
    C*(9*(fourthContraction μ T+2*tensorSquare T)+4*s^2*matrixFrobeniusSq B-
      12*s*quadraticGradientPairing μ T B+‖(C-1)⁻¹ • L‖^2) at hp
  rw [inner_smul_right,real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hp
  have hid : (C-1)*(C-1)⁻¹=1 := mul_inv_cancel₀ (ne_of_gt hC1)
  have hid2 : (C-1)*((C-1)⁻¹)^2=(C-1)⁻¹ := by
    calc
      _ = ((C-1)*(C-1)⁻¹)*(C-1)⁻¹ := by ring
      _ = _ := by rw [hid,one_mul]
  have hpay : C*((C-1)⁻¹)^2*‖L‖^2-((C-1)⁻¹)^2*‖L‖^2=(C-1)⁻¹*‖L‖^2 := by
    calc
      _ = ((C-1)*((C-1)⁻¹)^2)*‖L‖^2 := by ring
      _ = _ := by rw [hid2]
  change ProbabilityTheory.variance (quadraticPerturbation μ T B s) μ+‖L‖^2/(C-1)≤_
  rw [div_eq_mul_inv]
  linear_combination hp+hpay

end KLSConstantImprovement.ActualCubicAffineQuadraticRegression
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticRegression.quadraticPerturbation_contDiff
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticRegression.matrixAction_coordinate_mean_zero
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticRegression.quadraticPerturbation_coordinateDerivative_memLp
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticRegression.quadraticPerturbation_mean_gradient_zero
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticRegression.covarianceVector_quadraticPerturbation
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticRegression.affineQuadraticPerturbation_original_test
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticRegression.affineQuadraticPerturbation_derivative
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticRegression.affineQuadraticPerturbation_variance
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticRegression.affineQuadraticPerturbation_gradient_energy
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticRegression.affineQuadraticPerturbation_poincare
#print axioms KLSConstantImprovement.ActualCubicAffineQuadraticRegression.quadraticPerturbation_affine_charge
