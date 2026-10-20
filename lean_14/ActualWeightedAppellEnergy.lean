import ActualAppellQuotientReduction
import ActualAppellEnergyEvolution

/-! A genuine finite weighted sum of the paper's actual Appell energies.
The definition retains the original derivative and factorial normalizations. -/
noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def actualWeightedAppellEnergy {n : ℕ} (μ : Measure (Space n))
    (f : Space n → ℝ) (K : ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d

def actualWeightedAppellPairing {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (f g : Lp ℝ 2 μ) (K : ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
    inner ℝ (fullClassAppellTensor d f) (fullClassAppellTensor d g)

def actualWeightedCovarianceAppellEnergy {n : ℕ} (μ : Measure (Space n))
    (f : Space n → ℝ) (K : ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
    actualCovarianceAppellEnergy μ f d

theorem actualWeightedAppellEnergy_nonneg {n : ℕ} (μ : Measure (Space n))
    (f : Space n → ℝ) {K : ℝ} (hK : 0 < K) (N : ℕ) :
    0 ≤ actualWeightedAppellEnergy μ f K N := by
  apply Finset.sum_nonneg
  intro d hd
  exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (pow_nonneg hK.le _) (sq_nonneg _)))
    (actualAppellEnergy_nonneg _ _ _)

theorem actualWeightedAppellEnergy_congr_ae {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] {f g : Space n → ℝ} (hfg : f =ᵐ[μ] g) (K : ℝ) (N : ℕ) :
    actualWeightedAppellEnergy μ f K N=actualWeightedAppellEnergy μ g K N := by
  unfold actualWeightedAppellEnergy
  exact Finset.sum_congr rfl fun d hd => congrArg (_ * ·) (actualAppellEnergy_congr_ae hfg)

theorem actualWeightedAppellEnergy_eq_Lp {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) (K : ℝ) (N : ℕ) :
    actualWeightedAppellEnergy μ f K N=
      ∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹*‖fullClassAppellTensor d f‖^2 := by
  unfold actualWeightedAppellEnergy
  exact Finset.sum_congr rfl fun d hd => congrArg (_ * ·) (actualAppellEnergy_eq_norm_sq f)

theorem actualWeightedAppellEnergy_eq_pairing {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) (K : ℝ) (N : ℕ) :
    actualWeightedAppellEnergy μ f K N=actualWeightedAppellPairing f f K N := by
  rw [actualWeightedAppellEnergy_eq_Lp]
  simp only [actualWeightedAppellPairing,real_inner_self_eq_norm_sq]

theorem actualWeightedAppellEnergy_zero {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ) (K : ℝ) (N : ℕ) :
    actualWeightedAppellEnergy μ (0 : Lp ℝ 2 μ) K N=0 := by
  rw [actualWeightedAppellEnergy_eq_Lp]
  apply Finset.sum_eq_zero
  intro d hd
  change _*‖fullClassAppellLinearMap hLC d 0‖^2=0
  simp

theorem actualWeightedAppellEnergy_smul {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ) (f : Lp ℝ 2 μ)
    (K a : ℝ) (N : ℕ) :
    actualWeightedAppellEnergy μ (a • f : Lp ℝ 2 μ) K N=
      a^2*actualWeightedAppellEnergy μ f K N := by
  rw [actualWeightedAppellEnergy_eq_Lp,actualWeightedAppellEnergy_eq_Lp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  change _*‖fullClassAppellLinearMap hLC d (a • f)‖^2=
    a^2*((K^d*(d.factorial:ℝ)^2)⁻¹*‖fullClassAppellLinearMap hLC d f‖^2)
  rw [map_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

theorem actualWeightedAppellEnergy_polynomial_continuousOn {n N : ℕ} (K : ℝ) :
    ContinuousOn (fun z : ProbabilityMeasure (Space n) × (DegreeIndex n N → ℝ) =>
      actualWeightedAppellEnergy (z.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial z.2)) K N)
      (normalizedPolynomialPairs (degreeExponent n N)) := by
  apply continuousOn_finsetSum
  intro d hd
  exact ((actualAppellPolynomial_energy_continuousOn (degreeExponent n N)).mono
    (fun z hz => ⟨hz.1,mem_univ _⟩)).const_mul _

theorem actualWeightedAppellEnergy_add_smul {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ) (f g : Lp ℝ 2 μ)
    (K t : ℝ) (N : ℕ) :
    actualWeightedAppellEnergy μ (f+t • g : Lp ℝ 2 μ) K N=
      actualWeightedAppellEnergy μ f K N+2*t*actualWeightedAppellPairing f g K N+
        t^2*actualWeightedAppellEnergy μ g K N := by
  simp only [actualWeightedAppellEnergy_eq_Lp,actualWeightedAppellPairing]
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  change _*‖fullClassAppellLinearMap hLC d (f+t • g)‖^2=
    (K^d*(d.factorial:ℝ)^2)⁻¹*‖fullClassAppellLinearMap hLC d f‖^2+
      2*t*((K^d*(d.factorial:ℝ)^2)⁻¹*
        inner ℝ (fullClassAppellLinearMap hLC d f) (fullClassAppellLinearMap hLC d g))+
      t^2*((K^d*(d.factorial:ℝ)^2)⁻¹*‖fullClassAppellLinearMap hLC d g‖^2)
  rw [map_add,map_smul,norm_add_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  simp only [inner_smul_right]
  ring

theorem actualWeightedAppellEnergy_polynomialLp {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (p : MvPolynomial (Fin n) ℝ) (K : ℝ) (N : ℕ) :
    actualWeightedAppellEnergy μ (polynomialLp hLC p) K N=
      actualWeightedAppellEnergy μ (polynomialEval p) K N :=
  actualWeightedAppellEnergy_congr_ae (polynomialLp_coe hLC p) K N

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actualWeightedAppellEnergy_smul
#print axioms KLS.DeterministicBridgeNext.actualWeightedAppellEnergy_polynomial_continuousOn
