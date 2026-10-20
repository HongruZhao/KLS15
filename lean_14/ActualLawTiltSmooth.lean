import KLS.LogConcaveLaplaceJets
import KLS.TiltFrechet
import KLS.WeightedTiltTaylorTensor

/-! All-order local smoothness of normalized exponential tilted L²
observables for genuine log-concave probability laws. No compact support,
uniform convexity, or smooth density premise is imposed. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 theorem exists_common_local_exponential_domains
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    ∃ r : ℝ, 0 < r ∧ LocalNormExponentialDomain μ f r ∧
      LocalNormExponentialDomain μ (fun _ => 1) r := by
  obtain ⟨b,hb,hi⟩ := hμ.exists_pos_integrable_exp_norm
  have hExp : MemLp (fun x : Space n => Real.exp ((b/2)*‖x‖)) 2 μ := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    convert hi using 1
    funext x
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hfi : Integrable (fun x : Space n => ‖f x‖*Real.exp ((b/2)*‖x‖)) μ :=
    hf.norm.integrable_mul hExp
  refine ⟨b/4,by positivity,?_,?_⟩
  · exact localNormExponentialDomain_of_one_rate hf.aestronglyMeasurable hfi (by linarith)
  · exact localNormExponentialDomain_of_one_rate aestronglyMeasurable_const
      (by simpa only [norm_one,one_mul] using hi) (by linarith)

 theorem contDiffOn_normalized_tilt_average_of_domains
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r)
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ∫ x, f x ∂exponentialTilt μ z) (ball 0 r) := by
  change ContDiffOn ℝ (⊤ : ℕ∞) (fun z => tiltAverage μ (fun x => inner ℝ z x) f) _
  simp_rw [tiltAverage_eq_ratio]
  have hN : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ∫ x, f x * Real.exp (inner ℝ z x) ∂μ) (ball 0 r) := by
    convert contDiffOn_tiltNumerator_of_localNormExponentialDomain hf using 1
    funext z
    simp only [tiltNumerator,zero_add]
  have hZ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => tiltPartition μ (fun x => inner ℝ z x)) (ball 0 r) := by
    convert contDiffOn_tiltNumerator_of_localNormExponentialDomain h1 using 1
    funext z
    simp only [tiltNumerator,tiltPartition,zero_add,one_mul]
  apply hN.div hZ
  intro z hz
  have hz' : ‖z‖ < r := by simpa only [mem_ball,dist_zero_right] using hz
  apply (integral_exp_pos _).ne'
  simpa only [one_mul] using h1.integrable_tilt hz'.le

/-- The genuine tilted expectation is locally C∞ for every L² observable
of a log-concave probability law. -/
theorem exists_ball_contDiffOn_normalized_tilt_average
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    ∃ r : ℝ, 0 < r ∧ ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ∫ x, f x ∂exponentialTilt μ z) (ball 0 r) := by
  obtain ⟨r,hr,hf,h1⟩ := exists_common_local_exponential_domains hμ hf
  exact ⟨r,hr,contDiffOn_normalized_tilt_average_of_domains hf h1⟩

theorem contDiffAt_normalized_tilt_average
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => ∫ x, f x ∂exponentialTilt μ z) 0 := by
  obtain ⟨r,hr,hs⟩ := exists_ball_contDiffOn_normalized_tilt_average hμ hf
  exact hs.contDiffAt (isOpen_ball.mem_nhds (by simpa using hr))

/-- The unnormalized paper Appell coefficient: the actual order-r
mixed derivative of the normalized tilted expectation. -/
def actualAppellCoefficient (μ : Measure (Space n)) (f : Space n → ℝ)
    (r : ℕ) (a : Fin r → Fin n) : ℝ :=
  iteratedFDeriv ℝ r (fun z => ∫ x, f x ∂exponentialTilt μ z) 0
    (fun j => EuclideanSpace.single (a j) 1)

 theorem actualAppellCoefficient_eq_factorial_taylor
    (φ f : Space n → ℝ) (r : ℕ) (a : Fin r → Fin n) :
    actualAppellCoefficient (potentialMeasure φ) f r a =
      (r.factorial : ℝ)*exponentialTiltCoordinateTaylor φ f r a := by
  unfold actualAppellCoefficient exponentialTiltCoordinateTaylor exponentialTiltTaylorCoefficient
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  field_simp

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.exists_ball_contDiffOn_normalized_tilt_average
#print axioms KLS.DeterministicBridgeIntegration.contDiffAt_normalized_tilt_average
#print axioms KLS.DeterministicBridgeIntegration.actualAppellCoefficient_eq_factorial_taylor
