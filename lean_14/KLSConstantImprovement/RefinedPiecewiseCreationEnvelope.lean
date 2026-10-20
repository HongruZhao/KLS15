import KLSConstantImprovement.OptimizedDirectCreationEnvelope
import KLSConstantImprovement.RefinedSeed2388BellmanEndpoint

/-! Fresh universal finite-min creation envelope on the actual original law.
The original P_T-s q_SymA Poincare test, original P_T-t q_SymA variance,
g<=8R, literal same-unit covariance and full proper remainder are retained.
C=1434529/100000 safely relaxes the accepted refined endpoint. The new
module has no dependency on a future endpoint and leaves frozen23849 alone.
Uncompiled by this worker; the sole merger owns builds and accepted source.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open scoped BigOperators ENNReal ContDiff
namespace KLSConstantImprovement.OriginalUpperRecovery6PiecewiseEnvelopeDraft
open KLS KLS.DeterministicBridge KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise KLSBelow25.CubicCreation
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicGradientEnergy
open ActualCubicQuadraticRegression ActualCubicQuadraticDeficit
open ActualCubicCreationJointDual ActualDeficitCurvatureConditionalEndpoint
open OriginalUpperRecovery6DirectEnvelopeDraft
variable {n : ℕ}
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def supportC : ℝ := 1434529 / 100000
def supportU (i : Fin 5) : ℝ := ![(13/50 : ℝ), (1/4 : ℝ), (9/40 : ℝ), (1/5 : ℝ), (142337/787880 : ℝ)] i
def supportS (i : Fin 5) : ℝ := ![(18648877/17365918 : ℝ), (4303587/4069058 : ℝ), (38732283/38221522 : ℝ), (1434529/1489686 : ℝ), (612559662819/666590308546 : ℝ)] i
def supportT (i : Fin 5) : ℝ := ![(35863225/8682959 : ℝ), (8607174/2034529 : ℝ), (86071740/19110761 : ℝ), (7172645/1489686 : ℝ), (1695355062780/333295154273 : ℝ)] i
def supportLambda (i : Fin 5) : ℝ := ![(80257064621799/642538966000 : ℝ), (6173620355523/50863225000 : ℝ), (166687749599121/1481083977500 : ℝ), (2057873451841/19862480000 : ℝ), (5769478475638896537649/59765653826348677500 : ℝ)] i
def supportA (i : Fin 5) : ℝ := ![(12910761/74000 : ℝ), (4303587/25000 : ℝ), (12910761/77500 : ℝ), (12910761/80000 : ℝ), (28255917713/179317500 : ℝ)] i

def lineCost (i : Fin 5) (M : ℝ) : ℝ :=
  (9 / supportLambda i) * (8 * supportA i - M)

def piecewiseCost (M : ℝ) : ℝ :=
  min (directCost M)
    (min (lineCost 0 M) (min (lineCost 1 M)
      (min (lineCost 2 M) (min (lineCost 3 M) (lineCost 4 M)))))

theorem supportC_gt_refined : RefinedSeed2388BellmanEndpoint.bound ≤ supportC := by
  norm_num [RefinedSeed2388BellmanEndpoint.bound, supportC]

theorem support_s_eq_u_t (i : Fin 5) : supportS i = supportU i * supportT i := by
  fin_cases i <;> norm_num [supportS, supportU, supportT]

theorem support_u_nonneg (i : Fin 5) : 0 ≤ supportU i := by
  fin_cases i <;> norm_num [supportU]

theorem support_u_lt_one (i : Fin 5) : supportU i < 1 := by
  fin_cases i <;> norm_num [supportU]

theorem support_s_nonneg (i : Fin 5) : 0 ≤ supportS i := by
  fin_cases i <;> norm_num [supportS]

theorem support_s_le_t (i : Fin 5) : supportS i ≤ supportT i := by
  fin_cases i <;> norm_num [supportS, supportT]

theorem support_lambda_positive (i : Fin 5) : 0 < supportLambda i := by
  fin_cases i <;> norm_num [supportLambda]

theorem support_A_positive (i : Fin 5) : 0 < supportA i := by
  fin_cases i <;> norm_num [supportA]

theorem support_lambda_identity (i : Fin 5) : supportC * (12 * supportS i - 4 * (supportS i)^2) -
      8 * supportS i * (supportT i - supportS i) =
      (1 - supportU i) * supportLambda i := by
  fin_cases i <;> norm_num [supportC, supportS, supportT, supportU, supportLambda]

theorem support_A_identity (i : Fin 5) : 9 * supportC = (1 - supportU i) * supportA i := by
  fin_cases i <;> norm_num [supportC, supportU, supportA]

theorem quadraticPerturbation_refined_poincare {μ : Measure (Space n)} (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c, T a b c = T b a c) (hT23 : ∀ a b c, T a b c = T a c b)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (s : ℝ) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ +
      s^2 * ProbabilityTheory.variance (ActualCubicGradientEnergy.centeredQuadratic B) μ -
      2*s*covariance (tensorPolynomial μ T) (ActualCubicGradientEnergy.centeredQuadratic B) μ ≤
    supportC * (9*(fourthContraction μ T + 2*tensorSquare T) +
      4*s^2*matrixFrobeniusSq B - 12*s*quadraticGradientPairing μ T B) := by
  have hb := RefinedSeed2388BellmanEndpoint.original_poincare hn hμ
    (quadraticPerturbation_original_test hμ T B s)
  have henergy := quadraticPerturbation_gradient_energy hμ T hT12 hT23 B hB s
  have he : energy μ (quadraticPerturbation μ T B s) =
      ENNReal.ofReal (9*(fourthContraction μ T + 2*tensorSquare T) +
        4*s^2*matrixFrobeniusSq B - 12*s*quadraticGradientPairing μ T B) := by
    unfold energy
    rw [←ofReal_integral_eq_lintegral_ofReal henergy.1
      (Filter.Eventually.of_forall fun _ => sq_nonneg _), henergy.2]
  rw [he] at hb
  have hr := ENNReal.toReal_mono
    (ne_of_lt (ENNReal.mul_lt_top (ENNReal.div_lt_top (by norm_num) (by norm_num))
      ENNReal.ofReal_lt_top)) hb
  change ProbabilityTheory.variance (quadraticPerturbation μ T B s) μ ≤ _ at hr
  have hE : 0 ≤ 9*(fourthContraction μ T + 2*tensorSquare T) +
      4*s^2*matrixFrobeniusSq B - 12*s*quadraticGradientPairing μ T B := by
    rw [←henergy.2]
    exact integral_nonneg fun _ => sq_nonneg _
  rw [quadraticPerturbation_variance hμ T B s, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hE] at hr
  have hC : (2801814054094494174377/195312500000000000000 : ℝ≥0∞).toReal =
      RefinedSeed2388BellmanEndpoint.bound := by
    norm_num [RefinedSeed2388BellmanEndpoint.bound]
  rw [hC] at hr
  exact hr.trans (mul_le_mul_of_nonneg_right supportC_gt_refined hE)

theorem tensorPolynomial_refined_line_support_posDim {μ : Measure (Space n)}
    (hn : 1 ≤ n) (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c, T a b c = T b a c) (hT23 : ∀ a b c, T a b c = T a c b)
    (i : Fin 5) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ +
      supportLambda i * matrixFrobeniusSq (symmetricAnnihilation μ T) ≤
      supportA i * (fourthContraction μ T + 2*tensorSquare T) := by
  let K := symmetricAnnihilation μ T
  have hK := symmetricAnnihilation_isSymm μ T
  have hp := quadraticPerturbation_refined_poincare hn hμ T hT12 hT23 K hK (supportS i)
  rw [quadraticGradientPairing_symmetricAnnihilation] at hp
  have hv := ProbabilityTheory.variance_nonneg (quadraticPerturbation μ T K (supportT i)) μ
  rw [quadraticPerturbation_variance hμ T K (supportT i)] at hv
  have he := ActualCubicCreationOptimizedSupport.mixed_support_elimination
    (support_s_eq_u_t i) (support_u_nonneg i) (support_s_nonneg i) (support_s_le_t i)
    hp hv (centeredQuadratic_variance_le_eight hμ K hK)
  rw [support_lambda_identity, support_A_identity] at he
  have hfactor : (1-supportU i) *
      (ProbabilityTheory.variance (tensorPolynomial μ T) μ + supportLambda i * matrixFrobeniusSq K) ≤
      (1-supportU i) * (supportA i * (fourthContraction μ T + 2*tensorSquare T)) := by
    convert he using 1 <;> ring
  exact (mul_le_mul_iff_of_pos_left (sub_pos.mpr (support_u_lt_one i))).mp hfactor

theorem tensorPolynomial_refined_line_support {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c, T a b c = T b a c) (hT23 : ∀ a b c, T a b c = T a c b)
    (i : Fin 5) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ +
      supportLambda i * matrixFrobeniusSq (symmetricAnnihilation μ T) ≤
      supportA i * (fourthContraction μ T + 2*tensorSquare T) := by
  cases n with
  | zero =>
      have hz : tensorPolynomial μ T = (fun _ => 0) := by
        funext x
        simp [tensorPolynomial]
      rw [hz]
      change ProbabilityTheory.variance (0 : Space 0 → ℝ) μ + _ ≤ _
      rw [ProbabilityTheory.variance_zero]
      simp [matrixFrobeniusSq, fourthContraction, tensorSquare, square, tripleSum]
  | succ n =>
      exact tensorPolynomial_refined_line_support_posDim (by omega) hμ T hT12 hT23 i

theorem actual_refined_line_charge_unit {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x, (f x)^2 ∂μ) = 1) (i : Fin 5) :
    supportLambda i * matrixFrobeniusSq (symmetricAnnihilation μ (actualCubicNextArray μ f)) ≤
      actualAppellEnergy μ f 3 * (8*supportA i - actualAppellEnergy μ f 3) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let T := actualCubicNextArray μ f
  have hj := tensorPolynomial_refined_line_support hμ T
    (actualCubicNextArray_first_symmetry hμ.logConcave hf)
    (actualCubicNextArray_last_symmetry hμ.logConcave hf) i
  have hF := (fourthContraction_bounds hμ T
    (actualCubicNextArray_last_symmetry hμ.logConcave hf)).2
  have hpaidF := mul_le_mul_of_nonneg_left
    (add_le_add_right hF (2*tensorSquare T)) (support_A_positive i).le
  have hp : ProbabilityTheory.variance (tensorPolynomial μ T) μ +
      supportLambda i * matrixFrobeniusSq (symmetricAnnihilation μ T) ≤
      8*supportA i*tensorSquare T := by nlinarith [hj, hpaidF]
  unfold tensorSquare at hp
  rw [actualCubicNextArray_square] at hp
  have hcs := covariance_sq_le_variance_mul_variance (tensorPolynomial_memLp hμ T) hf
  rw [coefficientPolynomial_covariance hμ hf] at hcs
  have hfvar : ProbabilityTheory.variance f μ ≤ 1 := by
    rw [ProbabilityTheory.variance_eq_sub hf]
    change (∫ x, (f x)^2 ∂μ) - (∫ x, f x ∂μ)^2 ≤ 1
    rw [hunit]
    nlinarith [sq_nonneg (∫ x, f x ∂μ)]
  have hpaid := mul_le_mul_of_nonneg_left hfvar
    (ProbabilityTheory.variance_nonneg (tensorPolynomial μ T) μ)
  change supportLambda i * matrixFrobeniusSq (symmetricAnnihilation μ T) ≤ _
  nlinarith [hcs, hpaid, hp]

theorem actual_refined_line_proper_pairing_sq_unit {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x, (f x)^2 ∂μ) = 1) (i : Fin 5) :
    (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)^2 ≤
      actualAppellEnergy μ f 3 * actualAppellEnergy μ f 2 * lineCost i (actualAppellEnergy μ f 3) := by
  have hs := actual_proper_creation_pairing_sq_le_nine hμ hf
  have hj := actual_refined_line_charge_unit hμ hf hunit i
  have hpaid := mul_le_mul_of_nonneg_right hj (actualAppellEnergy_nonneg μ f 2)
  fin_cases i <;> norm_num [lineCost, supportLambda, supportA] at hpaid ⊢ <;>
    nlinarith [hs, hpaid]

theorem paid_min {J B c d : ℝ} (hc : J^2 ≤ B*c) (hd : J^2 ≤ B*d) :
    J^2 ≤ B*min c d := by
  by_cases h : c ≤ d
  · simpa only [min_eq_left h] using hc
  · simpa only [min_eq_right (le_of_not_ge h)] using hd

theorem actual_piecewise_proper_pairing_sq_unit {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x, (f x)^2 ∂μ) = 1) :
    (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)^2 ≤
      actualAppellEnergy μ f 3 * actualAppellEnergy μ f 2 * piecewiseCost (actualAppellEnergy μ f 3) := by
  unfold piecewiseCost
  apply paid_min (actual_direct_proper_pairing_sq_le_min_unit hμ hf hunit)
  apply paid_min (actual_refined_line_proper_pairing_sq_unit hμ hf hunit 0)
  apply paid_min (actual_refined_line_proper_pairing_sq_unit hμ hf hunit 1)
  apply paid_min (actual_refined_line_proper_pairing_sq_unit hμ hf hunit 2)
  exact paid_min (actual_refined_line_proper_pairing_sq_unit hμ hf hunit 3)
    (actual_refined_line_proper_pairing_sq_unit hμ hf hunit 4)

theorem lineCost_antitone (i : Fin 5) {M X : ℝ} (h : M ≤ X) :
    lineCost i X ≤ lineCost i M := by
  unfold lineCost
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left h _)
    (div_nonneg (by norm_num) (support_lambda_positive i).le)

theorem piecewiseCost_antitone {M X : ℝ} (h : M ≤ X) : piecewiseCost X ≤ piecewiseCost M := by
  unfold piecewiseCost
  apply min_le_min
  · unfold directCost
    exact min_le_min le_rfl
      (mul_le_mul_of_nonneg_left (sub_le_sub_left h directIntercept) directSlope_pos.le)
  · exact min_le_min (lineCost_antitone 0 h)
      (min_le_min (lineCost_antitone 1 h) (min_le_min (lineCost_antitone 2 h)
        (min_le_min (lineCost_antitone 3 h) (lineCost_antitone 4 h))))

theorem piecewiseCost_le_direct (M : ℝ) : piecewiseCost M ≤ directCost M := min_le_left _ _

theorem actual_piecewise_proper_pairing_abs_unit {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x, (f x)^2 ∂μ) = 1) :
    |actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3| ≤
      Real.sqrt (actualAppellEnergy μ f 3) *
        Real.sqrt (actualAppellEnergy μ f 2 * piecewiseCost (actualAppellEnergy μ f 3)) := by
  have hb := Real.abs_le_sqrt (actual_piecewise_proper_pairing_sq_unit hμ hf hunit)
  rw [mul_assoc, Real.sqrt_mul (actualAppellEnergy_nonneg μ f 3)] at hb
  exact hb

end KLSConstantImprovement.OriginalUpperRecovery6PiecewiseEnvelopeDraft
#print axioms KLSConstantImprovement.OriginalUpperRecovery6PiecewiseEnvelopeDraft.quadraticPerturbation_refined_poincare
#print axioms KLSConstantImprovement.OriginalUpperRecovery6PiecewiseEnvelopeDraft.tensorPolynomial_refined_line_support_posDim
#print axioms KLSConstantImprovement.OriginalUpperRecovery6PiecewiseEnvelopeDraft.tensorPolynomial_refined_line_support
#print axioms KLSConstantImprovement.OriginalUpperRecovery6PiecewiseEnvelopeDraft.actual_refined_line_charge_unit
#print axioms KLSConstantImprovement.OriginalUpperRecovery6PiecewiseEnvelopeDraft.actual_refined_line_proper_pairing_sq_unit
#print axioms KLSConstantImprovement.OriginalUpperRecovery6PiecewiseEnvelopeDraft.actual_piecewise_proper_pairing_sq_unit
#print axioms KLSConstantImprovement.OriginalUpperRecovery6PiecewiseEnvelopeDraft.piecewiseCost_antitone
#print axioms KLSConstantImprovement.OriginalUpperRecovery6PiecewiseEnvelopeDraft.piecewiseCost_le_direct
#print axioms KLSConstantImprovement.OriginalUpperRecovery6PiecewiseEnvelopeDraft.actual_piecewise_proper_pairing_abs_unit
