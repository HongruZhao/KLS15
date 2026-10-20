import TwoDimensionalExponentialMoments
import KLS.SuspensionIsotropy

/-! Actual probability measure and exact moments for the two-cone
counterexample. Log-concavity and the whitening map are established in
separate modules. No moment identity is an assumption. -/
noncomputable section
open MeasureTheory MvPolynomial
open ProbabilityTheory hiding moment
open scoped BigOperators ENNReal
namespace KLSImprovement.SingleSlotCounterexample
open KLS KLSImprovement.ProductPolynomial
open KLSImprovement.TwoDimensionalExponential
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

abbrev Poly := MvPolynomial (Fin 2) ℝ

def leftPoly : Fin 2 → Poly :=
  ![C (4/5:ℝ)*X 0, C (1/5:ℝ)*X 0+X 1]
def rightPoly : Fin 2 → Poly :=
  ![C (4/5:ℝ)*X 0+C (1/6:ℝ)*X 1, C (1/5:ℝ)*X 0]

def polynomialMap (q:Fin 2→Poly) (y:Fin 2→ℝ):Space 2 :=
  WithLp.toLp 2 (fun i=>MvPolynomial.eval y (q i))

@[fun_prop] theorem polynomialMap_measurable (q:Fin 2→Poly):
    Measurable (polynomialMap q) := by
  unfold polynomialMap
  exact (MeasurableEquiv.toLp 2 (Fin 2→ℝ)).measurable.comp
    (Measurable.of_eval (fun i=>(MvPolynomial.continuous_eval (p:=q i)).measurable))

def component (q:Fin 2→Poly):Measure (Space 2) :=
  (product 2).map (polynomialMap q)

def rawMeasure :Measure (Space 2) :=
  ENNReal.ofReal (24/25:ℝ) • component leftPoly+
    ENNReal.ofReal (1/25:ℝ) • component rightPoly

def polyEval (p:Poly) (x:Space 2):ℝ := MvPolynomial.eval (fun i=>x i) p

@[fun_prop] theorem polyEval_measurable (p:Poly):Measurable (polyEval p) := by
  exact (MvPolynomial.continuous_eval (p:=p)).measurable.comp (by fun_prop)

theorem polyEval_polynomialMap (p:Poly) (q:Fin 2→Poly) (y:Fin 2→ℝ):
    polyEval p (polynomialMap q y)=MvPolynomial.eval y (MvPolynomial.eval₂ C q p) := by
  exact MvPolynomial.eval_assoc q y p

theorem integrable_component (q:Fin 2→Poly) (p:Poly):
    Integrable (polyEval p) (component q) := by
  apply (integrable_map_measure (polyEval_measurable p).aestronglyMeasurable
    (polynomialMap_measurable q).aemeasurable).mpr
  have he : (polyEval p ∘ polynomialMap q)=
      (fun y=>MvPolynomial.eval y (MvPolynomial.eval₂ C q p)) := by
    funext y
    exact polyEval_polynomialMap p q y
  rw [he]
  exact integrable_polynomial _

theorem integral_component (q:Fin 2→Poly) (p:Poly):
    (∫x,polyEval p x ∂component q)=moment (MvPolynomial.eval₂ C q p) := by
  rw [component,integral_map (polynomialMap_measurable q).aemeasurable
    (polyEval_measurable p).aestronglyMeasurable]
  unfold moment
  apply integral_congr_ae
  exact .of_forall (polyEval_polynomialMap p q)

theorem integrable_raw_polynomial (p:Poly):Integrable (polyEval p) rawMeasure :=
  ((integrable_component leftPoly p).smul_measure (by simp)).add_measure
    ((integrable_component rightPoly p).smul_measure (by simp))

theorem memLp_raw_polynomial (p:Poly):MemLp (polyEval p) 2 rawMeasure := by
  apply (memLp_two_iff_integrable_sq (polyEval_measurable p).aestronglyMeasurable).mpr
  apply (integrable_raw_polynomial (p*p)).congr
  apply Filter.Eventually.of_forall
  intro x
  change MvPolynomial.eval (fun i=>x i) (p*p)=(MvPolynomial.eval (fun i=>x i) p)^2
  rw [MvPolynomial.eval_mul,pow_two]

def rawMoment (p:Poly):ℝ := ∫x,polyEval p x ∂rawMeasure

theorem rawMoment_formula (p:Poly):rawMoment p=
    (24/25:ℝ)*moment (MvPolynomial.eval₂ C leftPoly p)+
      (1/25:ℝ)*moment (MvPolynomial.eval₂ C rightPoly p) := by
  unfold rawMoment rawMeasure
  rw [integral_add_measure
    ((integrable_component leftPoly p).smul_measure (by simp))
    ((integrable_component rightPoly p).smul_measure (by simp)),
    integral_smul_measure,integral_smul_measure,integral_component,integral_component]
  norm_num [smul_eq_mul]

theorem raw_isProbability :IsProbabilityMeasure rawMeasure := by
  have hcomp (q:Fin 2→Poly):IsProbabilityMeasure (component q) :=
    (Measure.isProbabilityMeasure_map_iff (polynomialMap_measurable q).aemeasurable).mpr
      inferInstance
  haveI := hcomp leftPoly
  haveI := hcomp rightPoly
  constructor
  simp only [rawMeasure,Measure.add_apply,Measure.smul_apply,measure_univ,
    smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

def sPoly :Poly := X 0+X 1-C (59/30:ℝ)
def wPoly :Poly := X 1-C (29/25:ℝ)-C (5364/8945:ℝ)*sPoly

theorem raw_s_mean :rawMoment sPoly=0 := by
  rw [rawMoment_formula]
  simp only [sPoly,leftPoly,rightPoly,eval₂_sub,eval₂_add,eval₂_C,eval₂_X,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  conv_lhs => enter [1,2,1];ring_nf
  conv_lhs => enter [2,2,1];ring_nf
  norm_num only [←map_pow,←map_mul,mul_assoc,moment_add,moment_sub,moment_neg,
    moment_C,moment_C_mul,moment_mul_C,moment_C_middle,moment_C_deep,moment_C_right,
    moment_ofNat,moment_mul_ofNat,moment_ofNat_right,
    moment_two,moment_three,moment_mul_two,moment_mul_three,moment_mul_four,moment_mul_six,moment_mul_eight,
    moment_two_right,moment_three_right,moment_four_right,moment_six_right,moment_eight_right,
    moment_Xpow_Xpow,moment_X0pow,moment_X1pow,moment_X0pow_mulX1,
    moment_X0_mulX1pow,moment_X0mulX1,moment_X0,moment_X1]

theorem raw_w_mean :rawMoment wPoly=0 := by
  rw [rawMoment_formula]
  simp only [wPoly,sPoly,leftPoly,rightPoly,eval₂_sub,eval₂_add,eval₂_mul,eval₂_C,eval₂_X,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  conv_lhs => enter [1,2,1];ring_nf
  conv_lhs => enter [2,2,1];ring_nf
  norm_num only [←map_pow,←map_mul,mul_assoc,moment_add,moment_sub,moment_neg,
    moment_C,moment_C_mul,moment_mul_C,moment_C_middle,moment_C_deep,moment_C_right,
    moment_ofNat,moment_mul_ofNat,moment_ofNat_right,
    moment_two,moment_three,moment_mul_two,moment_mul_three,moment_mul_four,moment_mul_six,moment_mul_eight,
    moment_two_right,moment_three_right,moment_four_right,moment_six_right,moment_eight_right,
    moment_Xpow_Xpow,moment_X0pow,moment_X1pow,moment_X0pow_mulX1,
    moment_X0_mulX1pow,moment_X0mulX1,moment_X0,moment_X1]

theorem raw_s_second :rawMoment (sPoly^2)=(1789/900:ℝ) := by
  rw [rawMoment_formula]
  simp only [sPoly,leftPoly,rightPoly,eval₂_pow,eval₂_sub,eval₂_add,eval₂_C,eval₂_X,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  conv_lhs => enter [1,2,1];ring_nf
  conv_lhs => enter [2,2,1];ring_nf
  norm_num only [←map_pow,←map_mul,mul_assoc,moment_add,moment_sub,moment_neg,
    moment_C,moment_C_mul,moment_mul_C,moment_C_middle,moment_C_deep,moment_C_right,
    moment_ofNat,moment_mul_ofNat,moment_ofNat_right,
    moment_two,moment_three,moment_mul_two,moment_mul_three,moment_mul_four,moment_mul_six,moment_mul_eight,
    moment_two_right,moment_three_right,moment_four_right,moment_six_right,moment_eight_right,
    moment_Xpow_Xpow,moment_X0pow,moment_X1pow,moment_X0pow_mulX1,
    moment_X0_mulX1pow,moment_X0mulX1,moment_X0,moment_X1]

theorem raw_sw_second :rawMoment (sPoly*wPoly)=0 := by
  rw [rawMoment_formula]
  simp only [wPoly,sPoly,leftPoly,rightPoly,eval₂_sub,eval₂_add,eval₂_mul,eval₂_C,eval₂_X,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  conv_lhs => enter [1,2,1];ring_nf
  conv_lhs => enter [2,2,1];ring_nf
  norm_num only [←map_pow,←map_mul,mul_assoc,moment_add,moment_sub,moment_neg,
    moment_C,moment_C_mul,moment_mul_C,moment_C_middle,moment_C_deep,moment_C_right,
    moment_ofNat,moment_mul_ofNat,moment_ofNat_right,
    moment_two,moment_three,moment_mul_two,moment_mul_three,moment_mul_four,moment_mul_six,moment_mul_eight,
    moment_two_right,moment_three_right,moment_four_right,moment_six_right,moment_eight_right,
    moment_Xpow_Xpow,moment_X0pow,moment_X1pow,moment_X0pow_mulX1,
    moment_X0_mulX1pow,moment_X0mulX1,moment_X0,moment_X1]

theorem raw_w_second :rawMoment (wPoly^2)=(14473/44725:ℝ) := by
  rw [rawMoment_formula]
  simp only [wPoly,sPoly,leftPoly,rightPoly,eval₂_pow,eval₂_sub,eval₂_add,eval₂_mul,eval₂_C,eval₂_X,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  conv_lhs => enter [1,2,1];ring_nf
  conv_lhs => enter [2,2,1];ring_nf
  norm_num only [←map_pow,←map_mul,mul_assoc,moment_add,moment_sub,moment_neg,
    moment_C,moment_C_mul,moment_mul_C,moment_C_middle,moment_C_deep,moment_C_right,
    moment_ofNat,moment_mul_ofNat,moment_ofNat_right,
    moment_two,moment_three,moment_mul_two,moment_mul_three,moment_mul_four,moment_mul_six,moment_mul_eight,
    moment_two_right,moment_three_right,moment_four_right,moment_six_right,moment_eight_right,
    moment_Xpow_Xpow,moment_X0pow,moment_X1pow,moment_X0pow_mulX1,
    moment_X0_mulX1pow,moment_X0mulX1,moment_X0,moment_X1]

theorem raw_s_third :rawMoment (sPoly^3)=(53909/13500:ℝ) := by
  rw [rawMoment_formula]
  simp only [sPoly,leftPoly,rightPoly,eval₂_pow,eval₂_sub,eval₂_add,eval₂_C,eval₂_X,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  conv_lhs => enter [1,2,1];ring_nf
  conv_lhs => enter [2,2,1];ring_nf
  norm_num only [←map_pow,←map_mul,mul_assoc,moment_add,moment_sub,moment_neg,
    moment_C,moment_C_mul,moment_mul_C,moment_C_middle,moment_C_deep,moment_C_right,
    moment_ofNat,moment_mul_ofNat,moment_ofNat_right,
    moment_two,moment_three,moment_mul_two,moment_mul_three,moment_mul_four,moment_mul_six,moment_mul_eight,
    moment_two_right,moment_three_right,moment_four_right,moment_six_right,moment_eight_right,
    moment_Xpow_Xpow,moment_X0pow,moment_X1pow,moment_X0pow_mulX1,
    moment_X0_mulX1pow,moment_X0mulX1,moment_X0,moment_X1]

theorem raw_ssw_third :rawMoment (sPoly^2*wPoly)=(293/134175:ℝ) := by
  rw [rawMoment_formula]
  simp only [wPoly,sPoly,leftPoly,rightPoly,eval₂_pow,eval₂_sub,eval₂_add,eval₂_mul,eval₂_C,eval₂_X,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  conv_lhs => enter [1,2,1];ring_nf
  conv_lhs => enter [2,2,1];ring_nf
  norm_num only [←map_pow,←map_mul,mul_assoc,moment_add,moment_sub,moment_neg,
    moment_C,moment_C_mul,moment_mul_C,moment_C_middle,moment_C_deep,moment_C_right,
    moment_ofNat,moment_mul_ofNat,moment_ofNat_right,
    moment_two,moment_three,moment_mul_two,moment_mul_three,moment_mul_four,moment_mul_six,moment_mul_eight,
    moment_two_right,moment_three_right,moment_four_right,moment_six_right,moment_eight_right,
    moment_Xpow_Xpow,moment_X0pow,moment_X1pow,moment_X0pow_mulX1,
    moment_X0_mulX1pow,moment_X0mulX1,moment_X0,moment_X1]

theorem raw_sww_third :rawMoment (sPoly*wPoly^2)=(51270294/80013025:ℝ) := by
  rw [rawMoment_formula]
  simp only [wPoly,sPoly,leftPoly,rightPoly,eval₂_pow,eval₂_sub,eval₂_add,eval₂_mul,eval₂_C,eval₂_X,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  conv_lhs => enter [1,2,1];ring_nf
  conv_lhs => enter [2,2,1];ring_nf
  norm_num only [←map_pow,←map_mul,mul_assoc,moment_add,moment_sub,moment_neg,
    moment_C,moment_C_mul,moment_mul_C,moment_C_middle,moment_C_deep,moment_C_right,
    moment_ofNat,moment_mul_ofNat,moment_ofNat_right,
    moment_two,moment_three,moment_mul_two,moment_mul_three,moment_mul_four,moment_mul_six,moment_mul_eight,
    moment_two_right,moment_three_right,moment_four_right,moment_six_right,moment_eight_right,
    moment_Xpow_Xpow,moment_X0pow,moment_X1pow,moment_X0pow_mulX1,
    moment_X0_mulX1pow,moment_X0mulX1,moment_X0,moment_X1]

end KLSImprovement.SingleSlotCounterexample
#print axioms KLSImprovement.SingleSlotCounterexample.raw_isProbability
#print axioms KLSImprovement.SingleSlotCounterexample.raw_s_second
#print axioms KLSImprovement.SingleSlotCounterexample.raw_w_second
#print axioms KLSImprovement.SingleSlotCounterexample.raw_s_third
#print axioms KLSImprovement.SingleSlotCounterexample.raw_ssw_third
#print axioms KLSImprovement.SingleSlotCounterexample.raw_sww_third
