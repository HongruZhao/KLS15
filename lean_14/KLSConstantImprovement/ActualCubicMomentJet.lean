import KLSConstantImprovement.LocalWordLinear
import KLSConstantImprovement.ActualTiltCubicMoment
import KLSConstantImprovement.ActualCubicRepresenter
import FullClassAppellStationarity

/-! Exact mixed degree-three jet of a literal cubic Appell polynomial. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped BigOperators ContDiff Topology
namespace KLSConstantImprovement.ActualCubicMomentJet
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25
open ActualFixedTensorDeficit ActualTiltCubicMoment ActualCubicRepresenter LocalWordLinear
variable {n : ℕ}
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

theorem meanJet_zero {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (i : Fin n) :
    cumulantJet μ [i] 0=0 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨r,hr,h1⟩:=hμ.logConcave.exists_localNormExponentialDomain_one
  rw [←actualTiltMean_eq_jet h1 (by simpa using hr)]
  exact actualTiltMean_zero_of_isotropic hμ.isotropic i
theorem pairJet_zero {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (i j : Fin n) :
    cumulantJet μ [i,j] 0=δ i j := covarianceJet_zero hμ i j
theorem wordJet_one (μ : Measure (Space n)) (ws : List (Fin n)) (θ : Space n) (i : Fin n) :
    directionalWordDerivative (cumulantJet μ ws) [e i] θ=cumulantJet μ (i::ws) θ := rfl
theorem wordJet_two (μ : Measure (Space n)) (ws : List (Fin n)) (θ : Space n) (i j : Fin n) :
    directionalWordDerivative (cumulantJet μ ws) [e i,e j] θ=cumulantJet μ (i::j::ws) θ := rfl
theorem wordJet_three (μ : Measure (Space n)) (ws : List (Fin n)) (θ : Space n) (i j k : Fin n) :
    directionalWordDerivative (cumulantJet μ ws) [e i,e j,e k] θ=
      cumulantJet μ (i::j::k::ws) θ := rfl

def rawProductKernel (μ : Measure (Space n)) (i j k a b c : Fin n) : ℝ :=
  actualFourthCumulantArray μ i j a b*δ k c+
  actualFourthCumulantArray μ i k a b*δ j c+
  actualThirdCubicArray μ i a b*actualThirdCubicArray μ j k c+
  actualFourthCumulantArray μ j k a b*δ i c+
  actualThirdCubicArray μ j a b*actualThirdCubicArray μ i k c+
  actualThirdCubicArray μ k a b*actualThirdCubicArray μ i j c+
  δ a b*actualFourthCumulantArray μ i j k c
def tripleMeanKernel (i j k a b c : Fin n) : ℝ :=
  δ i a*δ j b*δ k c+δ j a*δ i b*δ k c+
  δ i a*δ k b*δ j c+δ k a*δ i b*δ j c+
  δ j a*δ k b*δ i c+δ k a*δ j b*δ i c
def cubicGramKernel (μ : Measure (Space n)) (i j k a b c : Fin n) : ℝ :=
  cumulantJet μ [i,j,k,a,b,c] 0+
  rawProductKernel μ i j k a b c+rawProductKernel μ i j k a c b+
  rawProductKernel μ i j k b c a+tripleMeanKernel i j k a b c-
  δ b c*actualFourthCumulantArray μ i j k a-
  δ a c*actualFourthCumulantArray μ i j k b-
  δ a b*actualFourthCumulantArray μ i j k c

theorem product_moment_jet {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (i j k a b c : Fin n) :
    directionalWordDerivative (fun z=>cumulantJet μ [a,b] z*cumulantJet μ [c] z)
      [e i,e j,e k] 0=rawProductKernel μ i j k a b c := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨r,hr,h1⟩:=hμ.logConcave.exists_localNormExponentialDomain_one
  have h0:(0 : Space n)∈ball 0 r := by simpa using hr
  have hp:=local_word_product_three isOpen_ball (cumulantJet_contDiffOn h1 [a,b])
    (cumulantJet_contDiffOn h1 [c]) h0 (e i) (e j) (e k)
  simp only [wordJet_one,wordJet_two,wordJet_three,meanJet_zero hμ,pairJet_zero hμ,
    cumulantJet_three_zero hμ,cumulantJet_four_zero hμ,mul_zero,zero_add] at hp
  exact hp

theorem triple_mean_jet {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (i j k a b c : Fin n) :
    directionalWordDerivative (fun z=>cumulantJet μ [a] z*cumulantJet μ [b] z*cumulantJet μ [c] z)
      [e i,e j,e k] 0=tripleMeanKernel i j k a b c := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨r,hr,h1⟩:=hμ.logConcave.exists_localNormExponentialDomain_one
  have hp:=word_triple_product_zero (cumulantJet_contDiffOn h1 [a])
    (cumulantJet_contDiffOn h1 [b]) (cumulantJet_contDiffOn h1 [c]) hr
    (meanJet_zero hμ a) (meanJet_zero hμ b) (meanJet_zero hμ c) i j k
  simp only [derivative_cumulantJet,pairJet_zero hμ] at hp
  exact hp

theorem raw_cubic_coefficient {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (i j k a b c : Fin n) :
    actualAppellCoefficient μ (fun x=>x a*(x b*x c)) 3 ![i,j,k]=
      cumulantJet μ [i,j,k,a,b,c] 0+
      rawProductKernel μ i j k a b c+rawProductKernel μ i j k a c b+
      rawProductKernel μ i j k b c a+tripleMeanKernel i j k a b c := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨r,hr,h1⟩:=hμ.logConcave.exists_localNormExponentialDomain_one
  have h0:(0 : Space n)∈ball 0 r := by simpa using hr
  have hD:LocalNormExponentialDomain μ (fun x : Space n=>x a*(x b*x c)) r := by
    simpa only [one_mul,mul_assoc,mul_comm,mul_left_comm] using
      ((h1.mul_coordinate a).mul_coordinate b).mul_coordinate c
  have hj (ws : List (Fin n)) := cumulantJet_contDiffOn h1 ws
  have he:actualDampedAverage μ (fun x=>x a*(x b*x c)) 0 =ᶠ[𝓝 (0 : Space n)]
      (fun z=>cumulantJet μ [a,b,c] z+cumulantJet μ [a,b] z*cumulantJet μ [c] z+
        cumulantJet μ [a,c] z*cumulantJet μ [b] z+
        cumulantJet μ [b,c] z*cumulantJet μ [a] z+
        cumulantJet μ [a] z*cumulantJet μ [b] z*cumulantJet μ [c] z) := by
    filter_upwards [isOpen_ball.mem_nhds h0] with z hz
    exact actualTiltCubic_eq_jet h1 (by simpa using hz) a b c
  have hw:=directionalWordDerivative_eventuallyEq he [e i,e j,e k]
  rw [word_add isOpen_ball (((hj [a,b,c]).add ((hj [a,b]).mul (hj [c]))).add
      ((hj [a,c]).mul (hj [b])) |>.add ((hj [b,c]).mul (hj [a])))
      (((hj [a]).mul (hj [b])).mul (hj [c])) h0,
    word_add isOpen_ball (((hj [a,b,c]).add ((hj [a,b]).mul (hj [c]))).add
      ((hj [a,c]).mul (hj [b]))) ((hj [b,c]).mul (hj [a])) h0,
    word_add isOpen_ball ((hj [a,b,c]).add ((hj [a,b]).mul (hj [c])))
      ((hj [a,c]).mul (hj [b])) h0,
    word_add isOpen_ball (hj [a,b,c]) ((hj [a,b]).mul (hj [c])) h0,
    wordJet_three,product_moment_jet hμ,product_moment_jet hμ,product_moment_jet hμ,
    triple_mean_jet hμ] at hw
  have hl:=local_word_ofFn isOpen_ball
    (contDiffOn_actualDampedAverage hD h1 (show (0 : ℝ)≤0 by rfl)) ![e i,e j,e k] h0
  simp only [List.ofFn_succ,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Fin.tail_cons,List.ofFn_zero,List.cons_append,List.nil_append] at hl
  rw [actualDampedAverage_zero_eq_tilt_average] at hl
  have ht:(fun q : Fin 3=>EuclideanSpace.single (![i,j,k] q) (1:ℝ))=![e i,e j,e k] := by
    funext q;fin_cases q <;>rfl
  unfold actualAppellCoefficient
  rw [ht,←hl]
  rw [←actualDampedAverage_zero_eq_tilt_average]
  exact hw

theorem coordinate_cubic_coefficient {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (i j k a b c : Fin n) :
    actualAppellCoefficient μ (coordinateCubic μ a b c) 3 ![i,j,k]=
      cubicGramKernel μ i j k a b c := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hx (u : Fin n) : MemLp (fun x : Space n=>x u) 2 μ := hμ.isotropic.memLp_coordinate u
  have hxxx:MemLp (fun x : Space n=>x a*(x b*x c)) 2 μ := by
    have he:polynomialEval (MvPolynomial.X a*(MvPolynomial.X b*MvPolynomial.X c))=
        fun x : Space n=>x a*(x b*x c) := by
      funext x;change (MvPolynomial.eval (fun j=>x j)) _=_
      simp only [map_mul,MvPolynomial.eval_X]
    rw [←he]
    exact polynomialEval_memLp_two hμ.logConcave _
  have ha:MemLp (fun x : Space n=>δ b c*x a) 2 μ := (hx a).const_mul _
  have hb:MemLp (fun x : Space n=>δ a c*x b) 2 μ := (hx b).const_mul _
  have hc:MemLp (fun x : Space n=>δ a b*x c) 2 μ := (hx c).const_mul _
  have hcoord (u : Fin n) : actualAppellCoefficient μ (fun x=>x u) 3 ![i,j,k]=
      actualFourthCumulantArray μ i j k u := by
    have hh:=actualAppellCoefficient_inner_eq_cumulant hμ.logConcave
      (EuclideanSpace.single u 1) 3 ![i,j,k]
    have ht:Fin.snoc (fun q : Fin 3=>EuclideanSpace.single (![i,j,k] q) (1:ℝ))
        (EuclideanSpace.single u 1)=
        ![EuclideanSpace.single i 1,EuclideanSpace.single j 1,
          EuclideanSpace.single k 1,EuclideanSpace.single u 1] := by
      funext q;fin_cases q <;>rfl
    simp only [EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_right,
      RCLike.conj_to_real,one_mul,ht] at hh
    exact hh
  unfold coordinateCubic
  have he1:=actualAppellCoefficient_sub hμ.logConcave hxxx ha 3 ![i,j,k]
  have he2:=actualAppellCoefficient_sub hμ.logConcave (hxxx.sub ha) hb 3 ![i,j,k]
  have he3:=actualAppellCoefficient_sub hμ.logConcave ((hxxx.sub ha).sub hb) hc 3 ![i,j,k]
  have he4:=actualAppellCoefficient_sub hμ.logConcave (((hxxx.sub ha).sub hb).sub hc)
    (memLp_const (actualThirdCubicArray μ a b c)) 3 ![i,j,k]
  simp only [Pi.sub_def,Pi.sub_apply] at he1 he2 he3 he4
  rw [he4,he3,he2,he1,
    actualAppellCoefficient_const_fullClass hμ.logConcave _ (by norm_num : 3≠0),sub_zero,
    actualAppellCoefficient_const_mul hμ.logConcave (hx a),
    actualAppellCoefficient_const_mul hμ.logConcave (hx b),
    actualAppellCoefficient_const_mul hμ.logConcave (hx c),hcoord,hcoord,hcoord,
    raw_cubic_coefficient hμ]
  rfl

end KLSConstantImprovement.ActualCubicMomentJet
#print axioms KLSConstantImprovement.ActualCubicMomentJet.product_moment_jet
#print axioms KLSConstantImprovement.ActualCubicMomentJet.triple_mean_jet
#print axioms KLSConstantImprovement.ActualCubicMomentJet.raw_cubic_coefficient
#print axioms KLSConstantImprovement.ActualCubicMomentJet.coordinate_cubic_coefficient
