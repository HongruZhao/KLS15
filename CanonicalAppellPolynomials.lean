import PolynomialSpatialDerivatives
import ActualAppellSteinRecursion

/-! Genuine polynomial representatives of adjoints of actual Appell
coefficient observations. Their integral pairings are the actual derivatives. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def actualAppellPolynomial (hμ : admissibleMeasure μ) (d : ℕ)
    (T : EuclideanSpace ℝ (Fin d → Fin n)) : MvPolynomial (Fin n) ℝ :=
  Classical.choose (exists_actualAppellPolynomial_representative hμ d T)

theorem actualAppellPolynomial_degree (hμ : admissibleMeasure μ) (d : ℕ)
    (T : EuclideanSpace ℝ (Fin d → Fin n)) :
    (actualAppellPolynomial hμ d T).totalDegree ≤ d :=
  (Classical.choose_spec (exists_actualAppellPolynomial_representative hμ d T)).1

theorem actualAppellPolynomial_toLp (hμ : admissibleMeasure μ) (d : ℕ)
    (T : EuclideanSpace ℝ (Fin d → Fin n)) :
    polynomialLp hμ.logConcave (actualAppellPolynomial hμ d T) =
      actualAppellPolynomialLp hμ d T :=
  (Classical.choose_spec (exists_actualAppellPolynomial_representative hμ d T)).2

theorem actualAppellPolynomial_pairing (hμ : admissibleMeasure μ) (d : ℕ)
    (T : EuclideanSpace ℝ (Fin d → Fin n)) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, polynomialEval (actualAppellPolynomial hμ d T) x*f x ∂μ) =
      inner ℝ T (WithLp.toLp 2 (fun a => actualAppellCoefficient μ f d a)) := by
  let F : Lp ℝ 2 μ := hf.toLp f
  have hF : (F : Space n → ℝ) =ᵐ[μ] f := hf.coeFn_toLp
  calc
    _ = ∫ x, polynomialEval (actualAppellPolynomial hμ d T) x*F x ∂μ :=
      integral_congr_ae (EventuallyEq.rfl.mul hF.symm)
    _ = inner ℝ (polynomialLp hμ.logConcave (actualAppellPolynomial hμ d T)) F :=
      (inner_polynomialLp_eq_integral _ _ _).symm
    _ = inner ℝ T (fullClassAppellTensor d F) := by
      rw [actualAppellPolynomial_toLp,actualAppellPolynomialLp_pairing]
    _ = _ := by
      congr 1
      apply PiLp.ext
      intro a
      exact actualAppellCoefficient_congr_ae hF d a

def actualBasisAppellPolynomial (hμ : admissibleMeasure μ) (d : ℕ)
    (a : Fin d → Fin n) : MvPolynomial (Fin n) ℝ :=
  actualAppellPolynomial hμ d (EuclideanSpace.single a 1)

theorem actualBasisAppellPolynomial_pairing (hμ : admissibleMeasure μ) (d : ℕ)
    (a : Fin d → Fin n) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, polynomialEval (actualBasisAppellPolynomial hμ d a) x*f x ∂μ) =
      actualAppellCoefficient μ f d a := by
  rw [actualBasisAppellPolynomial,actualAppellPolynomial_pairing hμ d _ hf]
  simp only [EuclideanSpace.inner_single_left,conj_trivial,one_mul]

theorem actualAppellCoefficient_const_fullClass (hLC : measureLogConcave μ)
    (c : ℝ) {d : ℕ} (hd : d ≠ 0) (a : Fin d → Fin n) :
    actualAppellCoefficient μ (fun _ => c) d a = 0 := by
  obtain ⟨r,hr,_,h1⟩ := exists_common_local_exponential_domains hLC
    (memLp_const (μ := μ) (p := 2) c)
  have he : (fun z => ∫ _x : Space n, c ∂exponentialTilt μ z) =ᶠ[𝓝 (0 : Space n)]
      (fun _ => c) := by
    filter_upwards [Metric.ball_mem_nhds (0 : Space n) hr] with z hz
    have hz' : ‖z‖ ≤ r := (by simpa only [Metric.mem_ball,dist_zero_right] using hz : ‖z‖ < r).le
    have hi : Integrable (fun x => Real.exp (inner ℝ z x)) μ := by
      simpa only [one_mul] using h1.integrable_tilt hz'
    letI : IsProbabilityMeasure (exponentialTilt μ z) := isProbabilityMeasure_tilted hi
    simp
  unfold actualAppellCoefficient
  rw [(he.iteratedFDeriv ℝ d).eq_of_nhds,iteratedFDeriv_const_of_ne hd]
  simp

theorem actualAppellPolynomial_integral_zero (hμ : admissibleMeasure μ)
    {d : ℕ} (hd : d ≠ 0) (T : EuclideanSpace ℝ (Fin d → Fin n)) :
    (∫ x, polynomialEval (actualAppellPolynomial hμ d T) x ∂μ)=0 := by
  have hp := actualAppellPolynomial_pairing hμ d T (memLp_const (μ := μ) (p := 2) (1 : ℝ))
  have he : (WithLp.toLp 2 (fun a => actualAppellCoefficient μ (fun _ => (1 : ℝ)) d a) :
      EuclideanSpace ℝ (Fin d → Fin n))=0 := by
    apply PiLp.ext
    intro a
    exact actualAppellCoefficient_const_fullClass hμ.logConcave 1 hd a
  simpa only [mul_one,he,inner_zero_right] using hp

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actualAppellPolynomial_toLp
#print axioms KLS.DeterministicBridgeNext.actualAppellPolynomial_pairing
#print axioms KLS.DeterministicBridgeNext.actualBasisAppellPolynomial_pairing
#print axioms KLS.DeterministicBridgeNext.actualAppellCoefficient_const_fullClass
#print axioms KLS.DeterministicBridgeNext.actualAppellPolynomial_integral_zero
