import TruncatedExponentialMoments
import ExponentialMoments

/-! Exact moments under a concrete bounded convex exponential tilt of Exp(1).
The original exponential probability and all moment integrals are actual. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace KLSImprovement.ConvexTiltMoments
open KLSImprovement.ExponentialMoments
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

def weight (b y : ℝ) : ℝ := Real.exp ((b+1)*min (y-1) 0)
def weightedMoment (b : ℝ) (k : ℕ) : ℝ :=
  ∫ y, weight b y*(y-1)^k ∂expMeasure 1

theorem centered_power_integrable (k : ℕ) :
    Integrable (fun y : ℝ => (y-1)^k) (expMeasure 1) := by
  simp_rw [sub_eq_add_neg,add_pow]
  apply integrable_finsetSum
  intro j _
  exact ((expMeasure_one_nat_moment j).1.mul_const ((-1:ℝ)^(k-j))).mul_const _

theorem weight_le_one {b : ℝ} (hb : 0 ≤ b) (y : ℝ) : weight b y ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (min_le_right _ _)

theorem weighted_power_integrable {b : ℝ} (hb : 0 ≤ b) (k : ℕ) :
    Integrable (fun y : ℝ => weight b y*(y-1)^k) (expMeasure 1) := by
  apply (centered_power_integrable k).bdd_mul (c:=1) (by unfold weight; fun_prop)
  exact .of_forall (fun y => by
    rw [Real.norm_eq_abs]
    change |Real.exp _|≤1
    rw [abs_of_pos (Real.exp_pos _)]
    exact weight_le_one hb y)

theorem translate_tail_integral (f : ℝ → ℝ) :
    (∫ y in Ici (1:ℝ),f y)=∫ x in Ici (0:ℝ),f (x+1) := by
  have he : (fun x : ℝ => x+1) ⁻¹' Ici (1:ℝ)=Ici (0:ℝ) := by
    ext x
    simp only [mem_preimage,mem_Ici]
    constructor <;> intro hx <;> linarith
  calc
    _ = ∫ y in Ici (1:ℝ),f y ∂Measure.map (fun x : ℝ => x+1) volume := by
      rw [map_add_right_eq_self]
    _ = ∫ x in (fun x : ℝ => x+1) ⁻¹' Ici (1:ℝ),f (x+1) := by
      exact (Homeomorph.addRight (1:ℝ)).isClosedEmbedding.setIntegral_map _
    _ = _ := by rw [he]

theorem tail_factorial (k : ℕ) :
    (∫ y in Ici (1:ℝ),Real.exp (-y)*(y-1)^k)=
      Real.exp (-1)*(k.factorial:ℝ) := by
  rw [translate_tail_integral]
  have he : (fun x : ℝ => Real.exp (-(x+1))*(x+1-1)^k)=
      (fun x : ℝ => Real.exp (-1)*(Real.exp (-x)*x^k)) := by
    funext x
    rw [show -(x+1)=(-1)+(-x) by ring,Real.exp_add]
    ring
  rw [he,integral_const_mul,←integral_expMeasure_one,(expMeasure_one_nat_moment k).2]

theorem weighted_integral_formula {b : ℝ} (hb : 0 ≤ b) (k : ℕ) :
    weightedMoment b k=Real.exp (-1)*
      ((k.factorial:ℝ)+(-1:ℝ)^k*KLSImprovement.TruncatedExponential.moment b k) := by
  let F : ℝ → ℝ := fun y => Real.exp (-y)*(weight b y*(y-1)^k)
  have hi : IntegrableOn F (Ici (0:ℝ)) :=
    (integrable_expMeasure_one_iff _).1 (weighted_power_integrable hb k)
  have hit : IntegrableOn F (Ici (1:ℝ)) := hi.mono_set (Ici_subset_Ici.mpr (by norm_num))
  have hs := intervalIntegral.integral_Ici_sub_Ici' hi hit
  have ht : (∫ y in Ici (1:ℝ),F y)=Real.exp (-1)*(k.factorial:ℝ) := by
    calc
      _ = ∫ y in Ici (1:ℝ),Real.exp (-y)*(y-1)^k := by
        apply setIntegral_congr_fun measurableSet_Ici
        intro y hy
        have hy' : 0 ≤ y-1 := by simpa only [mem_Ici] using sub_nonneg.mpr hy
        simp [F,weight,min_eq_right hy']
      _ = _ := tail_factorial k
  have hl : (∫ y in (0:ℝ)..1,F y)=Real.exp (-1)*(-1:ℝ)^k*
      KLSImprovement.TruncatedExponential.moment b k := by
    have he : (∫ y in (0:ℝ)..1,F y)=∫ y in (0:ℝ)..1,
        Real.exp (-1)*(-1:ℝ)^k*((1-y)^k*Real.exp (-b*(1-y))) := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hy1 : y ≤ 1 := by simpa using hy.2
      have hmin : min (y-1) 0=y-1 := min_eq_left (by linarith)
      dsimp [F,weight]
      rw [hmin,←mul_assoc,←Real.exp_add]
      rw [show -y+(b+1)*(y-1)=(-1)+(-b*(1-y)) by ring,Real.exp_add]
      rw [show y-1=(-1)*(1-y) by ring,mul_pow]
      ring
    rw [he,intervalIntegral.integral_const_mul]
    have hc : (∫ y in (0:ℝ)..1,(1-y)^k*Real.exp (-b*(1-y)))=
        KLSImprovement.TruncatedExponential.moment b k := by
      simpa [KLSImprovement.TruncatedExponential.moment] using
        (intervalIntegral.integral_comp_sub_left
          (fun x : ℝ => x^k*Real.exp (-b*x)) (1:ℝ) (a:=0) (b:=1))
    rw [hc]
  rw [ht,hl] at hs
  unfold weightedMoment
  rw [integral_expMeasure_one]
  change (∫ y in Ici (0:ℝ),F y)=_
  linarith

end KLSImprovement.ConvexTiltMoments
#print axioms KLSImprovement.ConvexTiltMoments.centered_power_integrable
#print axioms KLSImprovement.ConvexTiltMoments.weighted_power_integrable
#print axioms KLSImprovement.ConvexTiltMoments.tail_factorial
#print axioms KLSImprovement.ConvexTiltMoments.weighted_integral_formula
