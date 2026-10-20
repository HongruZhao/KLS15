import KLSConstantImprovement.TriplePositiveEnergyFirstCostTail
import KLSConstantImprovement.EventualCubicLeadingCoefficient
import KLSConstantImprovement.ConstantTailFamilyLowerBound
import GeneralResidualCoefficientAlgebra

/-! Necessary floor for the actual scalar generator family with eventual
constant alpha/Young/energy weights and a finite reserved prefix.  The
first cost is only discarded after proving it nonnegative.  This is a
method-family floor, not a lower bound on the optimal KLS constant. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.ActualConstantTailFamilyFloor
open KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSBelow25.PairProjection
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget

def tailQ (K C y a : ℝ) : ℝ := K*a-4/(1-a)+2-K*C/y
def tailG (a : ℝ) : ℝ := 4*a/(3*(1-a))
def tailL (a : ℝ) : ℝ := 4/(1-a)-5
def tailB (K C y a : ℝ) : ℝ := -tailQ K C y a-tailL a+tailG a
def tailA (c a : ℝ) : ℝ := tailL a-(1+c)+tailG a

theorem cleared_upper_identity (K C y a c : ℝ) (d : ℕ)
    (hy : y≠0) (ha : 1-a≠0) (hd : (d : ℝ)-1≠0) :
    ((d : ℝ)-1)*(K*a*(d : ℝ)^2-generalResidualGeneratorLoss a d-1-
      (K*C/y)*(d : ℝ)^2-c)=
      tailQ K C y a*(d : ℝ)^3+tailB K C y a*(d : ℝ)^2+
        tailA c a*(d : ℝ)+(1+c) := by
  unfold tailB tailA tailQ tailL tailG generalResidualGeneratorLoss generalResidualA
  field_simp [hy,ha,hd]
  ring

theorem raw_first_cost_nonneg (P : Parameters) (d : ℕ) (hd : 4 ≤ d)
    (hy : ∀ b,2 ≤ b → 0 < P.young b)
    (ht : ∀ b,2 ≤ b → 0 < P.t b)
    (hth : P.theta d=0) (hl : P.lambda (d-1)=0) (hz : P.zeta (d-2)=0) :
    0 ≤ TriplePositiveEnergyWeightedBudgetDrift.rawFirstCost
      P.young P.t P.theta P.lambda P.zeta d := by
  rw [TriplePositiveEnergyFirstCostTail.rawFirstCost_eq_of_zero
    P.young P.t P.theta P.lambda P.zeta d hd hz]
  rw [PositiveEnergyWeightTail.firstCost_unretained
    P.young P.t P.theta P.lambda d (by omega) hth hl]
  apply Finset.sum_nonneg
  intro b hb
  have hb2 : 2 ≤ b := (Finset.mem_Icc.mp hb).1
  have hbD : b ≤ d-1 := (Finset.mem_Icc.mp hb).2
  have ha2 : 2 ≤ d-b+1 := by omega
  exact div_nonneg (mul_nonneg (hy b hb2).le (ht d (by omega)).le)
    (mul_nonneg (ht (d-b+1) ha2).le (ht b hb2).le)

theorem generator_loss_lower (P : Parameters) {a : ℝ} (ha : a < 1)
    (d : ℕ) (hd : 3 ≤ d) (halpha : P.alpha d=a)
    (hth : P.theta (d+1)=0) (hl : P.lambda d=0) :
    generalResidualGeneratorLoss a d ≤
      PositiveEnergyWeightedGenerator.generatorLoss
        P.K P.young P.t P.alpha P.theta P.lambda d := by
  have hd2 : d≠2 := by omega
  have hg : PositiveEnergyWeightedGenerator.gamma P.K P.t P.theta d=1 := by
    simp [PositiveEnergyWeightedGenerator.gamma,hth]
  have hk : PositiveEnergyWeightedDrift.kappa P.K P.young P.t P.lambda d=0 := by
    simp [PositiveEnergyWeightedDrift.kappa,hl]
  rw [generalResidualGeneratorLoss_eq d hd ha,
    PositiveEnergyWeightedGenerator.generatorLoss,halpha,hg,hk]
  simp only [PositiveEnergyWeightedGenerator.degreeLoss,hd2,ite_false,
    SignedRowReservedNoise.reservedNoiseLoss,one_pow,one_mul,zero_mul,mul_zero,sub_zero]
  have hm : leadingNoiseCoefficient (d : ℝ)/(1-a)-positiveNoiseCoefficient (d : ℝ) ≤
      max (leadingNoiseCoefficient (d : ℝ)/(1-a)-positiveNoiseCoefficient (d : ℝ))
        (SignedRowNoiseHigh.highLeading (d : ℝ)/(1-a)-SignedRowNoiseHigh.highPositive (d : ℝ)) :=
    le_max_left _ _
  exact add_le_add hm (le_refl (d : ℝ))

theorem coefficient_upper (P : Parameters) {y z a : ℝ} (hz : z≠0)
    (ha : a < 1) (d : ℕ) (hd : 4 ≤ d)
    (hyall : ∀ b,2 ≤ b → 0 < P.young b)
    (htall : ∀ b,2 ≤ b → 0 < P.t b)
    (hy : P.young d=y) (ht : P.t d=z) (htprev : P.t (d-1)=z)
    (halpha : P.alpha d=a) (haprev : P.alpha (d-1)=a)
    (hth : P.theta d=0) (hthnext : P.theta (d+1)=0)
    (hl : P.lambda d=0) (hlprev : P.lambda (d-1)=0)
    (hzeta : P.zeta d=0) (hzetaprev : P.zeta (d-2)=0) :
    coefficient P d ≤ P.K*a*(d : ℝ)^2-generalResidualGeneratorLoss a d-1-
      (P.K*P.C/y)*(d : ℝ)^2 := by
  have hraw := raw_first_cost_nonneg P d hd hyall htall hth hlprev hzetaprev
  have hnoise := generator_loss_lower P ha d (by omega) halpha hthnext hl
  have hcharge : tripleHarmonicNeighborCharge P.K P.young P.zeta d=0 := by
    simp [tripleHarmonicNeighborCharge,hzeta]
  have hcost : (P.K*P.C/y)*(d : ℝ)^2 ≤
      TriplePositiveEnergyWeightedGenerator.cost
        P.K P.C P.young P.t P.theta P.lambda P.zeta d := by
    unfold TriplePositiveEnergyWeightedGenerator.cost
    rw [hy,if_pos (by omega : 3 ≤ d),hcharge]
    simp only [mul_zero,add_zero]
    linarith
  have hin : PositiveEnergyWeightedGenerator.incoming P.K P.t P.alpha d=
      P.K*a*(d : ℝ)^2 := by
    unfold PositiveEnergyWeightedGenerator.incoming
    rw [htprev,ht,haprev,div_self hz]
    ring
  unfold coefficient TriplePositiveEnergyWeightedGenerator.coefficient
  rw [hin]
  linarith

/-- The all-rank coefficient condition forces the true asymptotic leading
coefficient to be nonnegative.  Finite first-cost and reserved prefixes
cannot alter it.  No exact polynomial normalization is assumed here. -/
theorem tailQ_nonneg_of_actual_profile (P : Parameters) (y z a : ℝ)
    (hyall : ∀ b,2 ≤ b → 0 < P.young b)
    (htall : ∀ b,2 ≤ b → 0 < P.t b) (ha : a < 1)
    (N : ℕ) (hN : 2 ≤ N)
    (hyoung : ∀ d,N ≤ d → P.young d=y)
    (ht : ∀ d,N ≤ d → P.t d=z)
    (halpha : ∀ d,N ≤ d → P.alpha d=a)
    (hth : ∀ d,N ≤ d → P.theta d=0)
    (hl : ∀ d,N ≤ d → P.lambda d=0)
    (hzeta : ∀ d,N ≤ d → P.zeta d=0)
    (hcoef : ∀ d,5 ≤ d → P.c ≤ coefficient P d) :
    0 ≤ tailQ P.K P.C y a := by
  have hypos : 0 < y := by rw [←hyoung N (le_refl _)]; exact hyall N hN
  have hzpos : 0 < z := by rw [←ht N (le_refl _)]; exact htall N hN
  apply EventualCubicLeadingCoefficient.leading_nonneg
    (tailQ P.K P.C y a) (tailB P.K P.C y a) (tailA P.c a) (1+P.c) (N+5)
  intro d hd
  have hdr : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hu := coefficient_upper P (ne_of_gt hzpos) ha d (by omega) hyall htall
    (hyoung d (by omega)) (ht d (by omega)) (ht (d-1) (by omega))
    (halpha d (by omega)) (halpha (d-1) (by omega))
    (hth d (by omega)) (hth (d+1) (by omega))
    (hl d (by omega)) (hl (d-1) (by omega))
    (hzeta d (by omega)) (hzeta (d-2) (by omega))
  have hc := hcoef d (by omega)
  have hp : 0 ≤ ((d : ℝ)-1)*(P.K*a*(d : ℝ)^2-
      generalResidualGeneratorLoss a d-1-(P.K*P.C/y)*(d : ℝ)^2-P.c) :=
    mul_nonneg (by linarith) (by linarith)
  rwa [cleared_upper_identity P.K P.C y a P.c d
    (ne_of_gt hypos) (by linarith) (by linarith)] at hp

theorem K_lower_of_actual_eventually_constant_profile (P : Parameters) (y z a : ℝ)
    (hK : 0 < P.K) (hC : 0 < P.C)
    (hyall : ∀ b,2 ≤ b → 0 < P.young b)
    (htall : ∀ b,2 ≤ b → 0 < P.t b) (ha0 : 0 ≤ a) (ha : a < 1)
    (N : ℕ) (hN : 2 ≤ N)
    (hyoung : ∀ d,N ≤ d → P.young d=y)
    (ht : ∀ d,N ≤ d → P.t d=z)
    (halpha : ∀ d,N ≤ d → P.alpha d=a)
    (hth : ∀ d,N ≤ d → P.theta d=0)
    (hl : ∀ d,N ≤ d → P.lambda d=0)
    (hzeta : ∀ d,N ≤ d → P.zeta d=0)
    (hcoef : ∀ d,5 ≤ d → P.c ≤ coefficient P d) :
    6+4*Real.sqrt 2 < P.K := by
  have hypos : 0 < y := by rw [←hyoung N (le_refl _)]; exact hyall N hN
  exact ConstantTailFamilyLowerBound.K_lower_of_tail_coefficient
    P.K P.C y a hK hC hypos ha0 ha
    (tailQ_nonneg_of_actual_profile P y z a hyall htall ha N hN
      hyoung ht halpha hth hl hzeta hcoef)

theorem endpoint_lower_of_actual_eventually_constant_profile
    (P : Parameters) (y z a p : ℝ) (hp : 1 ≤ p)
    (hK : 0 < P.K) (hC : 0 < P.C)
    (hyall : ∀ b,2 ≤ b → 0 < P.young b)
    (htall : ∀ b,2 ≤ b → 0 < P.t b) (ha0 : 0 ≤ a) (ha : a < 1)
    (N : ℕ) (hN : 2 ≤ N)
    (hyoung : ∀ d,N ≤ d → P.young d=y)
    (ht : ∀ d,N ≤ d → P.t d=z)
    (halpha : ∀ d,N ≤ d → P.alpha d=a)
    (hth : ∀ d,N ≤ d → P.theta d=0)
    (hl : ∀ d,N ≤ d → P.lambda d=0)
    (hzeta : ∀ d,N ≤ d → P.zeta d=0)
    (hcoef : ∀ d,5 ≤ d → P.c ≤ coefficient P d) :
    7+4*Real.sqrt 2 < 1+P.K*p := by
  have hk := K_lower_of_actual_eventually_constant_profile P y z a hK hC
    hyall htall ha0 ha N hN hyoung ht halpha hth hl hzeta hcoef
  have hm := mul_le_mul_of_nonneg_left hp hK.le
  nlinarith

end KLSConstantImprovement.ActualConstantTailFamilyFloor
#print axioms KLSConstantImprovement.ActualConstantTailFamilyFloor.cleared_upper_identity
#print axioms KLSConstantImprovement.ActualConstantTailFamilyFloor.coefficient_upper
#print axioms KLSConstantImprovement.ActualConstantTailFamilyFloor.tailQ_nonneg_of_actual_profile
#print axioms KLSConstantImprovement.ActualConstantTailFamilyFloor.K_lower_of_actual_eventually_constant_profile
#print axioms KLSConstantImprovement.ActualConstantTailFamilyFloor.endpoint_lower_of_actual_eventually_constant_profile
