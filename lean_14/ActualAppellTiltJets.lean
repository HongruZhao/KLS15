import ActualLawTiltSmooth
import ActualAppellSymmetry
import Mathlib

/-! Genuine actual-law tilt jets and their first measure variation.
The tilted-law/translation identity is proved at the measure level;
coefficient evolution is derived from local smoothness, not assumed. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n : ℕ}
set_option maxHeartbeats 1000000

def actualTiltJet (μ : Measure (Space n)) (f : Space n → ℝ)
    (d : ℕ) (theta : Space n) (a : Fin d → Fin n) : ℝ :=
  iteratedFDeriv ℝ d (fun z => ∫ x, f x ∂exponentialTilt μ z) theta
    (fun j => EuclideanSpace.single (a j) 1)

@[simp] theorem actualTiltJet_zero (μ : Measure (Space n)) (f : Space n → ℝ)
    (d : ℕ) (a : Fin d → Fin n) :
    actualTiltJet μ f d 0 a = actualAppellCoefficient μ f d a := rfl

 theorem exponentialTilt_exponentialTilt {μ : Measure (Space n)}
    {theta : Space n}
    (htheta : Integrable (fun x => Real.exp (inner ℝ theta x)) μ) (z : Space n) :
    exponentialTilt (exponentialTilt μ theta) z = exponentialTilt μ (theta+z) := by
  change (μ.tilted (fun x => inner ℝ theta x)).tilted (fun x => inner ℝ z x) =
    μ.tilted (fun x => inner ℝ (theta+z) x)
  rw [tilted_tilted htheta]
  congr 1
  funext x
  simp only [Pi.add_apply,inner_add_left]

/-- The coefficient of the actual tilted probability law is the derivative
jet of the base-law normalized expectation at the tilt parameter. -/
 theorem actualAppellCoefficient_exponentialTilt {μ : Measure (Space n)}
    {theta : Space n}
    (htheta : Integrable (fun x => Real.exp (inner ℝ theta x)) μ)
    (f : Space n → ℝ) (d : ℕ) (a : Fin d → Fin n) :
    actualAppellCoefficient (exponentialTilt μ theta) f d a =
      actualTiltJet μ f d theta a := by
  unfold actualAppellCoefficient actualTiltJet
  simp_rw [exponentialTilt_exponentialTilt htheta]
  have he := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := fun z => ∫ x, f x ∂exponentialTilt μ z) d theta (0 : Space n)
  simpa only [add_zero] using congrArg (fun T => T (fun j => EuclideanSpace.single (a j) 1)) he

/-- A genuine theta derivative of any order-d coefficient is the next
actual mixed derivative. This is the first identity in manuscript (3.7). -/
 theorem hasDerivAt_actualTiltJet_direction
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (a : Fin d → Fin n) (v : Space n) :
    HasDerivAt (fun t : ℝ => actualTiltJet μ f d (t • v) a)
      (iteratedFDeriv ℝ (d+1) (fun z => ∫ x, f x ∂exponentialTilt μ z) 0
        (Fin.cons v (fun j => EuclideanSpace.single (a j) 1))) 0 := by
  let A : Space n → ℝ := fun z => ∫ x, f x ∂exponentialTilt μ z
  let m : Fin d → Space n := fun j => EuclideanSpace.single (a j) 1
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) A 0 := contDiffAt_normalized_tilt_average hLC hf
  have hs' : ContDiffAt ℝ (d+1) A 0 := hs.of_le (by simp)
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ d A) 0 :=
    hs'.differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr d.lt_succ_self)
  have he : DifferentiableAt ℝ (fun z => iteratedFDeriv ℝ d A z m) 0 :=
    hd.continuousMultilinear_apply_const m
  have hpath : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hc := he.hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp)
  convert hc using 1
  · rfl
  · simpa only [Fin.cons_zero,Fin.tail_cons] using
      hd.iteratedFDeriv_succ_apply_left' (m := Fin.cons v m)

 theorem hasDerivAt_actualTiltJet_coordinate
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (a : Fin d → Fin n) (i : Fin n) :
    HasDerivAt (fun t : ℝ => actualTiltJet μ f d
        (t • EuclideanSpace.single i 1) a)
      (actualAppellCoefficient μ f (d+1) (Fin.cons i a)) 0 := by
  have he : (Fin.cons (EuclideanSpace.single i (1 : ℝ))
      (fun j => EuclideanSpace.single (a j) (1 : ℝ)) : Fin (d+1) → Space n) =
      (fun j => EuclideanSpace.single ((Fin.cons i a : Fin (d+1) → Fin n) j) (1 : ℝ)) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  simpa only [actualAppellCoefficient,he] using
    hasDerivAt_actualTiltJet_direction hLC hf d a (EuclideanSpace.single i 1)

/-- The actual coefficient of the actual varying law has this derivative;
this theorem eliminates a separate coefficient-evolution hypothesis. -/
 theorem hasDerivAt_actualAppellCoefficient_tilt_direction
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (a : Fin d → Fin n) (v : Space n) :
    HasDerivAt (fun t : ℝ => actualAppellCoefficient (exponentialTilt μ (t • v)) f d a)
      (iteratedFDeriv ℝ (d+1) (fun z => ∫ x, f x ∂exponentialTilt μ z) 0
        (Fin.cons v (fun j => EuclideanSpace.single (a j) 1))) 0 := by
  obtain ⟨r,hr,hfD,h1D⟩ := exists_common_local_exponential_domains hLC hf
  have he : (fun theta : Space n => actualAppellCoefficient (exponentialTilt μ theta) f d a) =ᶠ[𝓝 0]
      (fun theta => actualTiltJet μ f d theta a) := by
    filter_upwards [ball_mem_nhds (0 : Space n) hr] with theta htheta
    have ht : ‖theta‖ ≤ r := by
      exact (show ‖theta‖ < r by simpa only [mem_ball,dist_zero_right] using htheta).le
    apply actualAppellCoefficient_exponentialTilt
    simpa only [one_mul] using h1D.integrable_tilt ht
  have hpath : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0 : Space n)) := by
    simpa only [id_eq,zero_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const v).continuousAt.tendsto
  have he' : (fun t : ℝ => actualAppellCoefficient (exponentialTilt μ (t • v)) f d a) =ᶠ[𝓝 0]
      (fun t : ℝ => actualTiltJet μ f d (t • v) a) := hpath.eventually he
  exact (hasDerivAt_actualTiltJet_direction hLC hf d a v).congr_of_eventuallyEq he' 

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualAppellCoefficient_exponentialTilt
#print axioms KLS.DeterministicBridgeIntegration.hasDerivAt_actualTiltJet_direction
#print axioms KLS.DeterministicBridgeIntegration.hasDerivAt_actualTiltJet_coordinate

#print axioms KLS.DeterministicBridgeIntegration.hasDerivAt_actualAppellCoefficient_tilt_direction
