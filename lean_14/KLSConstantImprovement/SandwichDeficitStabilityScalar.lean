import Mathlib

/-! Exact scalar payments for the proved matrix sandwich stability argument.
The averaged-response and matrix-PDE inputs are explicit here. This module
does not identify a limiting Stein kernel or a cubic tensor's Gram deficit. -/
noncomputable section
namespace KLSConstantImprovement.SandwichDeficitStabilityScalar
set_option maxHeartbeats 2000000

theorem determinant_absolute_bound {δ c z : ℝ} (hδ : 0≤δ) (hc : 0≤c)
    (hdet : z^2≤(9/2 : ℝ)*δ*c^2) : |z|≤(3/2 : ℝ)*Real.sqrt (2*δ)*c := by
  have hr := Real.sq_sqrt (show 0≤2*δ by positivity)
  have hre := congrArg (fun x : ℝ => (9/4 : ℝ)*x*c^2) hr
  have hp : 0≤(3/2 : ℝ)*Real.sqrt (2*δ)*c := by positivity
  have hs : |z|^2≤((3/2 : ℝ)*Real.sqrt (2*δ)*c)^2 := by
    rw [sq_abs]
    nlinarith [hre]
  by_contra! hn
  have ha := abs_nonneg z
  nlinarith

theorem sandwich_refined_regular_bound {δ c b2 bop m3 bc M : ℝ}
    (hδ : 0≤δ) (hc : 0≤c) (hb2 : 0≤b2) (hbop : 0≤bop)
    (hdet : (m3-3*bc)^2≤(9/2 : ℝ)*δ*c^2)
    (htrace : |bc-2*M|≤Real.sqrt (2*δ)*b2)
    (hnorm : c≤2*b2+bop*Real.sqrt (2*δ)) :
    |m3-6*M|≤6*Real.sqrt (2*δ)*b2+3*δ*bop := by
  have hz := determinant_absolute_bound hδ hc hdet
  have ht : |m3-6*M|≤|m3-3*bc|+3*|bc-2*M| := by
    calc
      _ = |(m3-3*bc)+3*(bc-2*M)| := by congr 1;ring
      _ ≤ |m3-3*bc|+|3*(bc-2*M)| := abs_add_le _ _
      _ = _ := by rw [abs_mul];norm_num
  have hn := mul_le_mul_of_nonneg_left hnorm
    (show 0≤(3/2 : ℝ)*Real.sqrt (2*δ) by positivity)
  have hr := Real.sq_sqrt (show 0≤2*δ by positivity)
  have hre := congrArg (fun x : ℝ => (3/2 : ℝ)*bop*x) hr
  nlinarith

theorem quadratic_deficit_pays_refined_bound {δ d b2 bop m3 M : ℝ}
    (hδ : 0≤δ) (hd : 4*δ≤d) (hb2 : 0≤b2) (hbop : 0≤bop)
    (hregular : m3≤6*M+6*Real.sqrt (2*δ)*b2+3*δ*bop) :
    m3≤6*M+3*Real.sqrt (2*d)*b2+(3/4 : ℝ)*d*bop := by
  have hd0 : 0≤d := by linarith
  have hr0 := Real.sqrt_nonneg (2*δ)
  have hs0 := Real.sqrt_nonneg (2*d)
  have hr := Real.sq_sqrt (show 0≤2*δ by positivity)
  have hs := Real.sq_sqrt (show 0≤2*d by positivity)
  have hroot : 2*Real.sqrt (2*δ)≤Real.sqrt (2*d) := by nlinarith
  have hp := mul_le_mul_of_nonneg_right hroot hb2
  have hq := mul_le_mul_of_nonneg_right hd hbop
  nlinarith

theorem sandwich_refined_original_upper {δ d c b2 bop m3 bc M : ℝ}
    (hδ : 0≤δ) (hd : 4*δ≤d) (hc : 0≤c) (hb2 : 0≤b2) (hbop : 0≤bop)
    (hdet : (m3-3*bc)^2≤(9/2 : ℝ)*δ*c^2)
    (htrace : |bc-2*M|≤Real.sqrt (2*δ)*b2)
    (hnorm : c≤2*b2+bop*Real.sqrt (2*δ)) :
    m3≤6*M+3*Real.sqrt (2*d)*b2+(3/4 : ℝ)*d*bop := by
  have hreg := sandwich_refined_regular_bound hδ hc hb2 hbop hdet htrace hnorm
  exact quadratic_deficit_pays_refined_bound hδ hd hb2 hbop (by linarith [le_abs_self (m3-6*M)])

theorem zero_deficit_regular_equality {δ d c b2 bop m3 bc M : ℝ}
    (hδ : 0≤δ) (hd : 4*δ≤d) (hd0 : d=0) (hc : 0≤c) (hb2 : 0≤b2) (hbop : 0≤bop)
    (hdet : (m3-3*bc)^2≤(9/2 : ℝ)*δ*c^2)
    (htrace : |bc-2*M|≤Real.sqrt (2*δ)*b2)
    (hnorm : c≤2*b2+bop*Real.sqrt (2*δ)) : m3=6*M := by
  have hδ0 : δ=0 := by linarith
  have hreg := sandwich_refined_regular_bound hδ hc hb2 hbop hdet htrace hnorm
  rw [hδ0] at hreg
  norm_num at hreg
  exact sub_eq_zero.mp hreg

theorem normalized_spectrum_free_payment {m3 M d γ scaleFactor b2 bop : ℝ}
    (hs : 0 ≤ scaleFactor) (hgamma : 0 ≤ γ) (hM : M = scaleFactor^3) (hd : d = γ*scaleFactor^2)
    (hb2 : b2 ≤ scaleFactor^2) (hbop : bop ≤ scaleFactor)
    (hupper : m3 ≤ 6*M+3*Real.sqrt (2*d)*b2+(3/4 : ℝ)*d*bop) :
    m3 ≤ M*(6+3*Real.sqrt (2*γ)+(3/4 : ℝ)*γ) :=  by
  have hroot : Real.sqrt (2*d) = Real.sqrt (2*γ)*scaleFactor :=  by
    rw [hd,show 2*(γ*scaleFactor^2) = (2*γ)*scaleFactor^2 by ring,
      Real.sqrt_mul (show 0 ≤ 2*γ by positivity),Real.sqrt_sq hs]
  have hp :=  mul_le_mul_of_nonneg_left hb2
    (show 0 ≤ 3*Real.sqrt (2*d) by positivity)
  have hq :=  mul_le_mul_of_nonneg_left hbop
    (show 0 ≤ (3/4 : ℝ)*d by rw [hd];positivity)
  rw [hroot,hd,hM] at hupper
  rw [hroot] at hp
  rw [hd] at hq
  rw [hM]
  nlinarith

end KLSConstantImprovement.SandwichDeficitStabilityScalar
#print axioms KLSConstantImprovement.SandwichDeficitStabilityScalar.determinant_absolute_bound
#print axioms KLSConstantImprovement.SandwichDeficitStabilityScalar.sandwich_refined_regular_bound
#print axioms KLSConstantImprovement.SandwichDeficitStabilityScalar.quadratic_deficit_pays_refined_bound
#print axioms KLSConstantImprovement.SandwichDeficitStabilityScalar.sandwich_refined_original_upper
#print axioms KLSConstantImprovement.SandwichDeficitStabilityScalar.zero_deficit_regular_equality
#print axioms KLSConstantImprovement.SandwichDeficitStabilityScalar.normalized_spectrum_free_payment
