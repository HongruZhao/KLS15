import GenericFiniteRankCriterion
import ActualVariableCoefficientInduction

/-! Exact factorial normalization and the genuine variable-alpha induction
barrier constructors. These definitions take only proved scalar branch data;
no coefficient estimate, maximizer or evolution property is assumed. -/
noncomputable section
open Set
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

structure ScalarVariableBarrierShape where
  phi : ℝ → ℝ
  alpha : ℝ → ℝ
  continuous : ContinuousOn phi (Icc 0 1)
  positive : ∀ u ∈ Icc (0 : ℝ) 1, 0<phi u
  antitone : AntitoneOn phi (Icc (0 : ℝ) 1)
  concave : ConcaveOn ℝ (Icc 0 1) phi
  hasDeriv : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt phi (deriv phi u) u
  derivative_negative : ∀ u ∈ Icc (0 : ℝ) 1, deriv phi u<0
  zero : phi 0=1
  alpha_unit : ∀ u ∈ Icc (0 : ℝ) 1, alpha u∈Ioo (0 : ℝ) 1

 theorem actualLowerConvolution_factorialScheme (s : FactorialScheme) (d : ℕ) :
    actualLowerConvolution s.coefficientH d=s.coefficientD d := rfl

 theorem factorial_common_criterion (s : FactorialScheme) {k : ℕ} (hk : 3≤k)
    {u z q alpha : ℝ} (hu : u∈Icc 0 1) (hz : 0<z) (hq : 0<q)
    (ha : alpha∈Ioo (0 : ℝ) 1) (hdelta : s.delta<1/2)
    (hm : 0<q*(alpha*s.K*z-(4/(1-alpha)-2)*u-s.r*Real.sqrt u)-2-s.r/Real.sqrt z) :
    q*(alpha*s.coefficientH (k+1)/s.coefficientH k*z-
      ((4/(1-alpha)-2)*(k:ℝ)^2+((4/(1-alpha)-2)-3)*k+2)*u-
      2*actualLowerConvolution s.coefficientH k/Real.sqrt (s.coefficientH k)*Real.sqrt u) >
      2*(k+1:ℝ)^2-(k+1:ℝ)+2+
        2*actualLowerConvolution s.coefficientH (k+1)/Real.sqrt (s.coefficientH (k+1)*z) := by
  have hA : 0<4/(1-alpha)-2 := by
    have hn : 0<1-alpha := by linarith [ha.2]
    have hd : 2<4/(1-alpha) := (lt_div_iff₀ hn).mpr (by nlinarith [ha.1])
    linarith
  have hdk := FactorialScheme.coefficientD_div_sqrt_bound (s:=s) hk
  have hdj := FactorialScheme.coefficientD_div_sqrt_bound (s:=s) (by omega : 3≤k+1)
  have hdj' : s.coefficientD (k+1)/Real.sqrt (s.coefficientH (k+1))≤
      s.r*genericConvolutionWeight s.delta ((k:ℝ)+1) := by
    simpa only [FactorialScheme.convolutionWeight,genericConvolutionWeight,Nat.cast_add,Nat.cast_one] using hdj
  have hcrit := generic_finite_rank_criterion (by exact_mod_cast hk) hu hz hq s.r_positive hA hdelta hm
    (by simpa only [FactorialScheme.convolutionWeight,genericConvolutionWeight] using hdk) hdj'
  have hratio : alpha*s.coefficientH (k+1)/s.coefficientH k=alpha*(s.K*(k+1:ℝ)^2) := by
    rw [show alpha*s.coefficientH (k+1)/s.coefficientH k=alpha*(s.coefficientH (k+1)/s.coefficientH k) by ring,
      FactorialScheme.coefficientH_ratio hk]
  rw [hratio,Real.sqrt_mul (FactorialScheme.coefficientH_positive (s:=s) (k+1)).le]
  simp only [actualLowerConvolution_factorialScheme]
  convert hcrit using 1 <;> push_cast <;> ring

 theorem factorial_seed_criterion (s : FactorialScheme) {u z q alpha : ℝ}
    (hm : q*(alpha*(9*s.B/2)*z-(6*(4/(1-alpha)-2)-4)*u)>17+8/Real.sqrt (s.B*z)) :
    q*(alpha*s.coefficientH 3/s.coefficientH 2*z-
      ((4/(1-alpha)-2)*(2:ℝ)^2+((4/(1-alpha)-2)-3)*2+2)*u-
      2*actualLowerConvolution s.coefficientH 2/Real.sqrt (s.coefficientH 2)*Real.sqrt u) >
      2*(3:ℝ)^2-3+2+
        2*actualLowerConvolution s.coefficientH 3/Real.sqrt (s.coefficientH 3*z) := by
  have h3 : s.coefficientH 3=36*s.B := by
    rw [FactorialScheme.coefficientH_ge_three (by norm_num : 3≤3)]
    norm_num
    ring
  have hd2 : actualLowerConvolution s.coefficientH 2=0 := by
    norm_num [actualLowerConvolution]
  have hd3 : actualLowerConvolution s.coefficientH 3=24 := by
    norm_num [actualLowerConvolution,FactorialScheme.coefficientH_two]
  have hs : Real.sqrt (s.coefficientH 3*z)=6*Real.sqrt (s.B*z) := by
    rw [h3,show 36*s.B*z=36*(s.B*z) by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤36)]
    norm_num
  rw [hs,h3,FactorialScheme.coefficientH_two,hd2,hd3]
  convert hm using 1 <;> ring

 def ScalarVariableBarrierShape.common (b : ScalarVariableBarrierShape) (s : FactorialScheme)
    (k : ℕ) (hk : 3≤k) (hdelta : s.delta<1/2)
    (hmargin : ∀ u∈Icc (0:ℝ) 1,
      0<(-deriv b.phi u/b.phi u)*(b.alpha u*s.K*b.phi u-
        (4/(1-b.alpha u)-2)*u-s.r*Real.sqrt u)-2-s.r/Real.sqrt (b.phi u)) :
    VariableCoefficientInductionBarrier k s.coefficientH where
  phi := b.phi
  alpha := b.alpha
  continuous := b.continuous
  positive := b.positive
  antitone := b.antitone
  concave := b.concave
  hasDeriv := b.hasDeriv
  derivative_negative := b.derivative_negative
  zero := b.zero
  alpha_unit := b.alpha_unit
  criterion := fun u hu => factorial_common_criterion s hk hu (b.positive u hu)
    (div_pos (neg_pos.mpr (b.derivative_negative u hu)) (b.positive u hu))
    (b.alpha_unit u hu) hdelta (hmargin u hu)

 def ScalarVariableBarrierShape.seed (b : ScalarVariableBarrierShape) (s : FactorialScheme)
    (hmargin : ∀ u∈Icc (0:ℝ) 1,
      (-deriv b.phi u/b.phi u)*(b.alpha u*(9*s.B/2)*b.phi u-
        (6*(4/(1-b.alpha u)-2)-4)*u)>17+8/Real.sqrt (s.B*b.phi u)) :
    VariableCoefficientInductionBarrier 2 s.coefficientH where
  phi := b.phi
  alpha := b.alpha
  continuous := b.continuous
  positive := b.positive
  antitone := b.antitone
  concave := b.concave
  hasDeriv := b.hasDeriv
  derivative_negative := b.derivative_negative
  zero := b.zero
  alpha_unit := b.alpha_unit
  criterion := by
    intro u hu
    convert factorial_seed_criterion s (hmargin u hu) using 1 <;> norm_num

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.factorial_common_criterion
#print axioms KLS.DeterministicBridgeNext.factorial_seed_criterion
#print axioms KLS.DeterministicBridgeNext.ScalarVariableBarrierShape.common
#print axioms KLS.DeterministicBridgeNext.ScalarVariableBarrierShape.seed
