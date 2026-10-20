import ActualJointL2QuotientMaximizer

/-! The first-order test-function identity at a constructed genuine joint
law/L² maximum. Local maximality is derived, not assumed. -/
noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem exists_actual_joint_maximizer_stationarity {n k : ℕ}
    {μ₀ : ProbabilityMeasure (Space n)} (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n)))
    {h : ℝ} (hh : 0 < h) {φ φ' : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc 0 1))
    (hφpos : ∀ u ∈ Icc (0 : ℝ) 1, 0 < φ u)
    (hφanti : AntitoneOn φ (Icc (0 : ℝ) 1))
    (hφderiv : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ' u) u)
    (hprevious : ∀ (μ : Measure (Space n)), admissibleMeasure μ → ∀ f : Space n → ℝ,
      MemLp f 2 μ → actualAppellEnergy μ f k ≤ h*(∫ x, (f x)^2 ∂μ)) :
    ∃ (μ : ProbabilityMeasure (Space n)) (hμ : admissibleMeasure (μ : Measure (Space n)))
      (c : DegreeIndex n (k+1) → ℝ),
      let f := polynomialLp hμ.logConcave (boundedDegreePolynomial c)
      ‖f‖ = 1 ∧
      (∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν : Measure (Space n)))
        (g : Lp ℝ 2 (ν : Measure (Space n))),
        coefficientQuotient (fullClassAppellLinearMap hν.logConcave k)
          (fullClassAppellLinearMap hν.logConcave (k+1)) h φ g ≤
        coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
          (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ f) ∧
      ∀ ell : Lp ℝ 2 (μ : Measure (Space n)),
        inner ℝ (fullClassAppellTensor (k+1) f) (fullClassAppellTensor (k+1) ell)+
          ‖fullClassAppellTensor (k+1) f‖^2*
            ((-φ' (‖fullClassAppellTensor k f‖^2/h))/φ (‖fullClassAppellTensor k f‖^2/h))/h*
            inner ℝ (fullClassAppellTensor k f) (fullClassAppellTensor k ell) =
        ‖fullClassAppellTensor (k+1) f‖^2*
          (1+(‖fullClassAppellTensor k f‖^2/h)*
            ((-φ' (‖fullClassAppellTensor k f‖^2/h))/φ (‖fullClassAppellTensor k f‖^2/h)))*
          inner ℝ f ell := by
  obtain ⟨z,hz,hmax⟩ := exists_actual_joint_L2_quotient_maximizer
    hμ₀ hh hφ hφpos hφanti hprevious
  let f := polynomialLp hz.1.logConcave (boundedDegreePolynomial z.2)
  have hnormsq : ‖f‖^2 = 1 :=
    (polynomialCoefficientEnergy_eq_norm_sq _ hz.1 z.2).symm.trans hz.2
  have hunit : ‖f‖ = 1 := by nlinarith [norm_nonneg f]
  have hf : f ≠ 0 := by
    intro he
    simp only [he,norm_zero] at hunit
    norm_num at hunit
  have hglobal : ∀ (ν : ProbabilityMeasure (Space n))
      (hν : admissibleMeasure (ν : Measure (Space n))) (g : Lp ℝ 2 (ν : Measure (Space n))),
      coefficientQuotient (fullClassAppellLinearMap hν.logConcave k)
        (fullClassAppellLinearMap hν.logConcave (k+1)) h φ g ≤
      coefficientQuotient (fullClassAppellLinearMap hz.1.logConcave k)
        (fullClassAppellLinearMap hz.1.logConcave (k+1)) h φ f := by
    intro ν hν g
    exact (hmax ν hν g).trans_eq (polynomial_normalized_quotient_eq hz.1 z.2 hz.2 h φ)
  refine ⟨z.1,hz.1,z.2,hunit,hglobal,?_⟩
  intro ell
  have hu : ‖fullClassAppellTensor k f‖^2/h ∈ Icc (0 : ℝ) 1 := by
    simpa only [hunit,one_pow,mul_one] using actualAppell_ratio_mem_Icc hz.1 hh hprevious f hf
  have hl : IsLocalMax (fun t : ℝ => coefficientQuotient
      (fullClassAppellLinearMap hz.1.logConcave k)
      (fullClassAppellLinearMap hz.1.logConcave (k+1)) h φ (f+t • ell)) 0 := by
    apply Eventually.of_forall
    intro t
    simpa only [zero_smul,add_zero] using hglobal z.1 hz.1 (f+t • ell)
  exact fullClass_test_function_stationarity hz.1.logConcave k f ell hh hunit φ
    (hφderiv _ hu) (hφpos _ hu) hl

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.exists_actual_joint_maximizer_stationarity
