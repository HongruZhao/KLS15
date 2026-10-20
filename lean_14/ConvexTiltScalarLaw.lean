import ActualScalarCriticalObservation
import ConvexTiltScalarMoments
import KLS.ConcaveExponentialTilt
import KLS.ClassToDensity

/-! Actual fixed-support log-concave probability laws in the convex-tilt
monotonicity audit. The moments are derived from actual exponential integrals. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace KLSImprovement.ConvexTiltLaw
open KLS KLSImprovement.ProductAdmissible KLSImprovement.ActualProductCumulants
open KLSImprovement.ActualScalarCritical KLSImprovement.ConvexTiltMoments
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure (centeredProductMeasure 1) := centeredProduct_isProbability 1

def potential (b : ℝ) (x : Space 1) : ℝ := (b+1)*min (x 0) 0
def law (b : ℝ) : Measure (Space 1) := (centeredProductMeasure 1).tilted (potential b)

theorem potential_continuous (b : ℝ) : Continuous (potential b) := by
  unfold potential
  fun_prop

theorem potential_concave {b : ℝ} (hb : 0 ≤ b) :
    ConcaveOn ℝ univ (potential b) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a c ha hc _
  change a*((b+1)*min (x 0) 0)+c*((b+1)*min (y 0) 0)≤
    (b+1)*min (a*x 0+c*y 0) 0
  have hm : a*min (x 0) 0+c*min (y 0) 0 ≤ min (a*x 0+c*y 0) 0 := by
    apply le_min
    · exact add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) ha)
        (mul_le_mul_of_nonneg_left (min_le_left _ _) hc)
    · exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (min_le_right _ _))
        (mul_nonpos_of_nonneg_of_nonpos hc (min_le_right _ _))
  calc
    _=(b+1)*(a*min (x 0) 0+c*min (y 0) 0) := by ring
    _≤_ := mul_le_mul_of_nonneg_left hm (by linarith)

theorem potential_nonpositive {b : ℝ} (hb : 0 ≤ b) (x : Space 1) : potential b x ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (by linarith) (min_le_right _ _)

theorem weight_integrable {b : ℝ} (hb : 0 ≤ b) :
    Integrable (fun x => Real.exp (potential b x)) (centeredProductMeasure 1) := by
  apply (integrable_const (1:ℝ)).mono' (by unfold potential; fun_prop)
  exact .of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (potential_nonpositive hb x))

theorem law_isProbability {b : ℝ} (hb : 0 ≤ b) : IsProbabilityMeasure (law b) :=
  isProbabilityMeasure_tilted (weight_integrable hb)

theorem law_logConcave {b : ℝ} (hb : 0 ≤ b) : measureLogConcave (law b) :=
  (centeredProduct_admissible 1).hasLogConcaveDensity.measureLogConcave_tilted
    (potential_continuous b) (potential_concave hb)

theorem coordinate_power_memLp {b : ℝ} (hb : 0 ≤ b) (k : ℕ) :
    MemLp (fun x : Space 1 => x 0^k) 2 (law b) := by
  letI : IsProbabilityMeasure (law b) := law_isProbability hb
  apply ((law_logConcave hb).memLp_two_norm_pow k).mono' (by fun_prop)
  exact .of_forall (fun x => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le x 0) k)

theorem coordinate_power_integrable {b : ℝ} (hb : 0 ≤ b) (k : ℕ) :
    Integrable (fun x : Space 1 => x 0^k) (law b) := by
  letI : IsProbabilityMeasure (law b) := law_isProbability hb
  exact (coordinate_power_memLp hb k).integrable (by norm_num : (1:ℝ≥0∞)≤2)

theorem weighted_coordinate_integral {b : ℝ} (hb : 0 ≤ b) (k : ℕ) :
    (∫ x,Real.exp (potential b x)*x 0^k ∂centeredProductMeasure 1)=
      Real.exp (-1)*((k.factorial:ℝ)+(-1:ℝ)^k*
        KLSImprovement.TruncatedExponential.moment b k) := by
  rw [centered_integral]
  have he : (fun y : ℝ => Real.exp (potential b (scalarCenter y))*(scalarCenter y) 0^k)=
      (fun y : ℝ => weight b y*(y-1)^k) := by
    funext y
    have hc : (scalarCenter y) 0=y-1 := by change (-1:ℝ)+y=y-1; ring
    simp only [potential,hc,weight]
  rw [he]
  exact weighted_integral_formula hb k

theorem partition_integral {b : ℝ} (hb : 0 ≤ b) :
    (∫ x,Real.exp (potential b x) ∂centeredProductMeasure 1)=
      Real.exp (-1)*(1+KLSImprovement.TruncatedExponential.moment b 0) := by
  simpa only [pow_zero,mul_one,one_mul,Nat.factorial_zero,Nat.cast_one] using
    weighted_coordinate_integral hb 0

theorem coordinate_moment {b : ℝ} (hb : 0 ≤ b) (k : ℕ) :
    (∫ x : Space 1,x 0^k ∂law b)=
      ((k.factorial:ℝ)+(-1:ℝ)^k*KLSImprovement.TruncatedExponential.moment b k)/
        (1+KLSImprovement.TruncatedExponential.moment b 0) := by
  unfold law
  rw [integral_tilted]
  simp only [smul_eq_mul]
  have he : (fun x : Space 1 =>
      (Real.exp (potential b x)/∫ y,Real.exp (potential b y) ∂centeredProductMeasure 1)*x 0^k)=
      (fun x : Space 1 => (Real.exp (potential b x)*x 0^k)/
        (∫ y,Real.exp (potential b y) ∂centeredProductMeasure 1)) := by funext x; ring
  rw [he,integral_div,weighted_coordinate_integral hb k,partition_integral hb]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero (-1))

theorem law_nine_is_further_convex_tilt :
    (law 0).tilted (fun x : Space 1 => 9*min (x 0) 0)=law 9 := by
  unfold law
  rw [tilted_tilted (weight_integrable (by norm_num : (0:ℝ)≤0))]
  congr 1
  funext x
  simp only [Pi.add_apply,potential]
  ring

end KLSImprovement.ConvexTiltLaw
#print axioms KLSImprovement.ConvexTiltLaw.law_isProbability
#print axioms KLSImprovement.ConvexTiltLaw.law_logConcave
#print axioms KLSImprovement.ConvexTiltLaw.coordinate_power_integrable
#print axioms KLSImprovement.ConvexTiltLaw.coordinate_moment
#print axioms KLSImprovement.ConvexTiltLaw.law_nine_is_further_convex_tilt
