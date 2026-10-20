import ActualWeightedAppellOptimality

/-! Actual Appell energy with arbitrary fixed nonnegative degree weights.
The coordinates and heat/whitening laws retain their original definitions. -/
noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLSConstantImprovement.GeneralWeighted
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def energy {n : ℕ} (μ : Measure (Space n))
    (f : Space n → ℝ) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 N, (w d)*actualAppellEnergy μ f d

def pairing {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (f g : Lp ℝ 2 μ) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 N, (w d)*
    inner ℝ (fullClassAppellTensor d f) (fullClassAppellTensor d g)

def covarianceEnergy {n : ℕ} (μ : Measure (Space n))
    (f : Space n → ℝ) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 N, (w d)*
    actualCovarianceAppellEnergy μ f d

theorem energy_nonneg {n : ℕ} (μ : Measure (Space n))
    (f : Space n → ℝ) (w : ℕ → ℝ) (hw : ∀ d, 2 ≤ d → 0 ≤ w d) (N : ℕ) :
    0 ≤ energy μ f w N := by
  apply Finset.sum_nonneg
  intro d hd
  exact mul_nonneg (hw d (Finset.mem_Icc.mp hd).1)
    (actualAppellEnergy_nonneg _ _ _)

theorem energy_congr_ae {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] {f g : Space n → ℝ} (hfg : f =ᵐ[μ] g) (w : ℕ → ℝ) (N : ℕ) :
    energy μ f w N=energy μ g w N := by
  unfold energy
  exact Finset.sum_congr rfl fun d hd => congrArg (_ * ·) (actualAppellEnergy_congr_ae hfg)

theorem energy_eq_Lp {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) (w : ℕ → ℝ) (N : ℕ) :
    energy μ f w N=
      ∑ d ∈ Finset.Icc 2 N, (w d)*‖fullClassAppellTensor d f‖^2 := by
  unfold energy
  exact Finset.sum_congr rfl fun d hd => congrArg (_ * ·) (actualAppellEnergy_eq_norm_sq f)

theorem energy_eq_pairing {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) (w : ℕ → ℝ) (N : ℕ) :
    energy μ f w N=pairing f f w N := by
  rw [energy_eq_Lp]
  simp only [pairing,real_inner_self_eq_norm_sq]

theorem energy_zero {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ) (w : ℕ → ℝ) (N : ℕ) :
    energy μ (0 : Lp ℝ 2 μ) w N=0 := by
  rw [energy_eq_Lp]
  apply Finset.sum_eq_zero
  intro d hd
  change _*‖fullClassAppellLinearMap hLC d 0‖^2=0
  simp

theorem energy_smul {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ) (f : Lp ℝ 2 μ)
    (w : ℕ → ℝ) (a : ℝ) (N : ℕ) :
    energy μ (a • f : Lp ℝ 2 μ) w N=
      a^2*energy μ f w N := by
  rw [energy_eq_Lp,energy_eq_Lp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  change _*‖fullClassAppellLinearMap hLC d (a • f)‖^2=
    a^2*((w d)*‖fullClassAppellLinearMap hLC d f‖^2)
  rw [map_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

theorem energy_polynomial_continuousOn {n N : ℕ} (w : ℕ → ℝ) :
    ContinuousOn (fun z : ProbabilityMeasure (Space n) × (DegreeIndex n N → ℝ) =>
      energy (z.1 : Measure (Space n))
        (polynomialEval (boundedDegreePolynomial z.2)) w N)
      (normalizedPolynomialPairs (degreeExponent n N)) := by
  apply continuousOn_finsetSum
  intro d hd
  exact ((actualAppellPolynomial_energy_continuousOn (degreeExponent n N)).mono
    (fun z hz => ⟨hz.1,mem_univ _⟩)).const_mul _

theorem energy_add_smul {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ) (f g : Lp ℝ 2 μ)
    (w : ℕ → ℝ) (t : ℝ) (N : ℕ) :
    energy μ (f+t • g : Lp ℝ 2 μ) w N=
      energy μ f w N+2*t*pairing f g w N+
        t^2*energy μ g w N := by
  simp only [energy_eq_Lp,pairing]
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  change _*‖fullClassAppellLinearMap hLC d (f+t • g)‖^2=
    (w d)*‖fullClassAppellLinearMap hLC d f‖^2+
      2*t*((w d)*
        inner ℝ (fullClassAppellLinearMap hLC d f) (fullClassAppellLinearMap hLC d g))+
      t^2*((w d)*‖fullClassAppellLinearMap hLC d g‖^2)
  rw [map_add,map_smul,norm_add_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  simp only [inner_smul_right]
  ring

theorem energy_polynomialLp {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (p : MvPolynomial (Fin n) ℝ) (w : ℕ → ℝ) (N : ℕ) :
    energy μ (polynomialLp hLC p) w N=
      energy μ (polynomialEval p) w N :=
  energy_congr_ae (polynomialLp_coe hLC p) w N

end KLSConstantImprovement.GeneralWeighted
#print axioms KLSConstantImprovement.GeneralWeighted.energy_smul
#print axioms KLSConstantImprovement.GeneralWeighted.energy_polynomial_continuousOn
