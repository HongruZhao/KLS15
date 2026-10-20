import KLSConstantImprovement.ActualCubicAffineRegression
import KLSConstantImprovement.ActualDeficitBesselBound

/-! Literal mixed cubic/quadratic tests on the original admissible law.
The derivative, variance, mixed energy, and Poincare deficit are computed
for the same polynomial P_T - s q_B; no moment identity is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open scoped BigOperators ENNReal ContDiff
namespace KLSConstantImprovement.ActualCubicQuadraticRegression
open KLS KLS.DeterministicBridge KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise KLSBelow25.CubicCreation
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicGradientEnergy
open ActualCubicPoincareFourthSector ActualCubicAffineRegression QuadraticCovarianceCharge
variable {n : ℕ}
set_option maxHeartbeats 5500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def symmetricAnnihilation (μ : Measure (Space n)) (T : Array3 (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  symmetricMatrix (annihilation (actualThirdCubicArray μ) T)

def quadraticGradientPairing (μ : Measure (Space n)) (T : Array3 (Fin n))
    (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i,∑ j,B i j*symmetricAnnihilation μ T i j

def quadraticPerturbation (μ : Measure (Space n)) (T : Array3 (Fin n))
    (B : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (x : Space n) : ℝ :=
  tensorPolynomial μ T x-s*ActualCubicGradientEnergy.centeredQuadratic B x

theorem symmetricAnnihilation_isSymm (μ : Measure (Space n)) (T : Array3 (Fin n)) :
    (symmetricAnnihilation μ T).IsSymm := by
  ext i j
  exact symmetricMatrix_symm _ j i

theorem centeredQuadratic_contDiff (B : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (ActualCubicGradientEnergy.centeredQuadratic B) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => matrixQuadratic B x-Matrix.trace B)
  exact ((contDiff_matrixQuadratic B).sub contDiff_const).of_le (by simp)

theorem centeredQuadratic_derivative (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (i : Fin n) (x : Space n) :
    coordinateDerivative (ActualCubicGradientEnergy.centeredQuadratic B) i x=
      2*(matrixAction B x) i := by
  rw [coordinateDerivative_eq_gradient]
  unfold ActualCubicGradientEnergy.centeredQuadratic
  rw [gradient_sub_const,gradient_matrixQuadratic B hB x]
  rfl

theorem matrixAction_coordinate_memLp {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    MemLp (fun x => (matrixAction B x) i) 2 μ := by
  change MemLp (fun x => ∑ j,B i j*x j) 2 μ
  exact memLp_finsetSum Finset.univ fun j _ => (hμ.isotropic.memLp_coordinate j).const_mul _

theorem integral_coordinate_centeredQuadratic_eq_annihilation {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n)) (i j : Fin n) :
    (∫ x,x j*ActualCubicGradientEnergy.centeredQuadratic (T i) x ∂μ)=
      annihilation (actualThirdCubicArray μ) T j i := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hm := memLp_matrixQuadratic_of_coordinateProducts
    hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul (T i)
  have he : (fun x : Space n => x j*ActualCubicGradientEnergy.centeredQuadratic (T i) x)=
      fun x => x j*matrixQuadratic (T i) x-Matrix.trace (T i)*x j := by
    funext x
    unfold ActualCubicGradientEnergy.centeredQuadratic
    ring
  rw [he,integral_sub (f := fun x : Space n => x j*matrixQuadratic (T i) x)
    (g := fun x => Matrix.trace (T i)*x j) ((hμ.isotropic.memLp_coordinate j).integrable_mul hm)
    ((hμ.isotropic.integrable_coordinate j).const_mul _),integral_const_mul,
    hμ.isotropic.integral_coordinate,mul_zero,sub_zero,
    ActualDeficitBesselBound.annihilation_eq_quadratic_covariance hμ T j i]
  rfl

theorem centeredQuadratic_matrixAction_integral {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    (∫ x,∑ i,ActualCubicGradientEnergy.centeredQuadratic (T i) x*(matrixAction B x) i ∂μ)=
      quadraticGradientPairing μ T B := by
  have hi (i : Fin n) := (centeredQuadratic_memLp hμ (T i)).integrable_mul
    (matrixAction_coordinate_memLp hμ B i)
  rw [integral_finsetSum Finset.univ
    (f := fun i (x : Space n) => ActualCubicGradientEnergy.centeredQuadratic (T i) x*(matrixAction B x) i)
    (fun i _ => hi i)]
  have he (i : Fin n) :
      (∫ x,ActualCubicGradientEnergy.centeredQuadratic (T i) x*(matrixAction B x) i ∂μ)=
        ∑ j,B i j*annihilation (actualThirdCubicArray μ) T j i := by
    have hx : (fun x => ActualCubicGradientEnergy.centeredQuadratic (T i) x*(matrixAction B x) i)=
        fun x => ∑ j,B i j*(x j*ActualCubicGradientEnergy.centeredQuadratic (T i) x) := by
      funext x
      rw [matrixAction_apply,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hx,integral_finsetSum Finset.univ
      (f := fun j (x : Space n) => B i j*(x j*ActualCubicGradientEnergy.centeredQuadratic (T i) x))
      (fun j _ =>
      ((hμ.isotropic.memLp_coordinate j).integrable_mul
        (centeredQuadratic_memLp hμ (T i))).const_mul (B i j))]
    simp_rw [integral_const_mul,integral_coordinate_centeredQuadratic_eq_annihilation hμ T i]
  simp_rw [he]
  have hsym (i j : Fin n) : B i j=B j i := by
    exact congrFun (congrFun hB j) i
  have ht : (∑ i,∑ j,B i j*annihilation (actualThirdCubicArray μ) T j i)=
      ∑ i,∑ j,B i j*annihilation (actualThirdCubicArray μ) T i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  rw [ht,symmetric_pairing_matrix B (annihilation (actualThirdCubicArray μ) T) hsym]
  rfl

theorem quadraticPerturbation_original_test {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (B : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) :
    LocallyLipschitzTests μ (quadraticPerturbation μ T B s) := by
  have hd : ContDiff ℝ 1 (quadraticPerturbation μ T B s) :=
    ((tensorPolynomial_contDiff μ T).of_le (by simp)).sub
      (((centeredQuadratic_contDiff B).of_le (by simp)).const_smul s)
  exact ⟨hd.locallyLipschitz,(tensorPolynomial_memLp hμ T).sub
    ((centeredQuadratic_memLp hμ B).const_mul s)⟩

theorem quadraticPerturbation_derivative (μ : Measure (Space n)) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (s : ℝ) (i : Fin n) (x : Space n) :
    coordinateDerivative (quadraticPerturbation μ T B s) i x=
      3*ActualCubicGradientEnergy.centeredQuadratic (T i) x-2*s*(matrixAction B x) i := by
  change coordinateDerivative (fun y => tensorPolynomial μ T y-
    (s • ActualCubicGradientEnergy.centeredQuadratic B) y) i x=_
  rw [coordinateDerivative_sub ((tensorPolynomial_contDiff μ T).differentiable (by simp) x)
    (((centeredQuadratic_contDiff B).differentiable (by simp) x).const_smul s),
    coordinateDerivative_smul ((centeredQuadratic_contDiff B).differentiable (by simp) x),
    tensorPolynomial_derivative μ T hT12 hT23,centeredQuadratic_derivative B hB]
  ring

theorem quadraticPerturbation_variance {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (B : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) :
    ProbabilityTheory.variance (quadraticPerturbation μ T B s) μ=
      ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      s^2*ProbabilityTheory.variance (ActualCubicGradientEnergy.centeredQuadratic B) μ-
      2*s*covariance (tensorPolynomial μ T) (ActualCubicGradientEnergy.centeredQuadratic B) μ := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  unfold quadraticPerturbation
  rw [variance_fun_sub (tensorPolynomial_memLp hμ T) ((centeredQuadratic_memLp hμ B).const_mul s),
    variance_const_mul,covariance_const_mul_right]
  ring

theorem quadraticPerturbation_gradient_energy {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ a b c,T a b c=T b a c)
    (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (s : ℝ) :
    Integrable (fun x => ‖gradient (quadraticPerturbation μ T B s) x‖^2) μ ∧
      (∫ x,‖gradient (quadraticPerturbation μ T B s) x‖^2 ∂μ)=
        9*(fourthContraction μ T+2*tensorSquare T)+4*s^2*matrixFrobeniusSq B-
          12*s*quadraticGradientPairing μ T B := by
  let q (i : Fin n) := ActualCubicGradientEnergy.centeredQuadratic (T i)
  have he : (fun x => ‖gradient (quadraticPerturbation μ T B s) x‖^2)=
      fun x => 9*(∑ i,(q i x)^2)+4*s^2*‖matrixAction B x‖^2-
        12*s*(∑ i,q i x*(matrixAction B x) i) := by
    funext x
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,
      ←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [←coordinateDerivative_eq_gradient,quadraticPerturbation_derivative μ T hT12 hT23 B hB]
    dsimp only [q]
    ring
  have hi0 : Integrable (fun x => 9*(∑ i,(q i x)^2)) μ :=
    (integrable_finsetSum Finset.univ fun i _ =>
      (centeredQuadratic_memLp hμ (T i)).integrable_sq).const_mul 9
  have hi1 : Integrable (fun x => 4*s^2*‖matrixAction B x‖^2) μ :=
    (hμ.isotropic.integrable_matrixAction_norm_sq B).const_mul _
  have hi2 : Integrable (fun x => 12*s*(∑ i,q i x*(matrixAction B x) i)) μ :=
    (integrable_finsetSum Finset.univ fun i _ =>
      (centeredQuadratic_memLp hμ (T i)).integrable_mul
        (matrixAction_coordinate_memLp hμ B i)).const_mul _
  constructor
  · rw [he]
    exact (hi0.add hi1).sub hi2
  · have ha := integral_add hi0 hi1
    have hs := integral_sub (hi0.add hi1) hi2
    simp only [Pi.add_apply,Pi.sub_apply] at ha hs
    rw [he,hs,ha,integral_const_mul,integral_const_mul,integral_const_mul,
      integral_finsetSum Finset.univ (fun i _ => (centeredQuadratic_memLp hμ (T i)).integrable_sq)]
    change 9*(∑ i,∫ x,(ActualCubicGradientEnergy.centeredQuadratic (T i) x)^2 ∂μ)+
      4*s^2*(∫ x,‖matrixAction B x‖^2 ∂μ)-
      12*s*(∫ x,∑ i,ActualCubicGradientEnergy.centeredQuadratic (T i) x*(matrixAction B x) i ∂μ)=_
    rw [sum_centeredQuadratic_integrals hμ T,hμ.isotropic.integral_matrixAction_norm_sq B,
      centeredQuadratic_matrixAction_integral hμ T B hB]

theorem quadraticPerturbation_poincare {μ : Measure (Space n)} (hn : 1≤n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (s : ℝ) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      s^2*ProbabilityTheory.variance (ActualCubicGradientEnergy.centeredQuadratic B) μ-
      2*s*covariance (tensorPolynomial μ T) (ActualCubicGradientEnergy.centeredQuadratic B) μ ≤
    LongPrefixCubicBellmanEndpoint.bound*(9*(fourthContraction μ T+2*tensorSquare T)+
      4*s^2*matrixFrobeniusSq B-12*s*quadraticGradientPairing μ T B) := by
  have hb := LongPrefixCubicBellmanEndpoint.original_poincare hn hμ
    (quadraticPerturbation_original_test hμ T B s)
  have henergy := quadraticPerturbation_gradient_energy hμ T hT12 hT23 B hB s
  have he : energy μ (quadraticPerturbation μ T B s)=
      ENNReal.ofReal (9*(fourthContraction μ T+2*tensorSquare T)+
        4*s^2*matrixFrobeniusSq B-12*s*quadraticGradientPairing μ T B) := by
    unfold energy
    rw [←ofReal_integral_eq_lintegral_ofReal henergy.1
      (Filter.Eventually.of_forall fun _ => sq_nonneg _),henergy.2]
  rw [he] at hb
  have hr := ENNReal.toReal_mono
    (ne_of_lt (ENNReal.mul_lt_top (ENNReal.div_lt_top (by norm_num) (by norm_num)) ENNReal.ofReal_lt_top)) hb
  change ProbabilityTheory.variance (quadraticPerturbation μ T B s) μ≤_ at hr
  have hE : 0≤9*(fourthContraction μ T+2*tensorSquare T)+
      4*s^2*matrixFrobeniusSq B-12*s*quadraticGradientPairing μ T B := by
    rw [←henergy.2]
    exact integral_nonneg fun _ => sq_nonneg _
  rw [quadraticPerturbation_variance hμ T B s,ENNReal.toReal_mul,ENNReal.toReal_ofReal hE] at hr
  have hC : (280181882107013433/19531250000000000 : ℝ≥0∞).toReal=
      LongPrefixCubicBellmanEndpoint.bound := by norm_num [LongPrefixCubicBellmanEndpoint.bound]
  rw [hC] at hr
  exact hr

end KLSConstantImprovement.ActualCubicQuadraticRegression
#print axioms KLSConstantImprovement.ActualCubicQuadraticRegression.symmetricAnnihilation_isSymm
#print axioms KLSConstantImprovement.ActualCubicQuadraticRegression.centeredQuadratic_contDiff
#print axioms KLSConstantImprovement.ActualCubicQuadraticRegression.centeredQuadratic_derivative
#print axioms KLSConstantImprovement.ActualCubicQuadraticRegression.matrixAction_coordinate_memLp
#print axioms KLSConstantImprovement.ActualCubicQuadraticRegression.integral_coordinate_centeredQuadratic_eq_annihilation
#print axioms KLSConstantImprovement.ActualCubicQuadraticRegression.centeredQuadratic_matrixAction_integral
#print axioms KLSConstantImprovement.ActualCubicQuadraticRegression.quadraticPerturbation_original_test
#print axioms KLSConstantImprovement.ActualCubicQuadraticRegression.quadraticPerturbation_derivative
#print axioms KLSConstantImprovement.ActualCubicQuadraticRegression.quadraticPerturbation_variance
#print axioms KLSConstantImprovement.ActualCubicQuadraticRegression.quadraticPerturbation_gradient_energy
#print axioms KLSConstantImprovement.ActualCubicQuadraticRegression.quadraticPerturbation_poincare
