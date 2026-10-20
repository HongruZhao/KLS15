import ActualFourthCumulantFlatBound
import ActualAppellHeatDrift
import ActualPairAppellContraction

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter Set Metric InnerProductSpace
open scoped BigOperators ContDiff Topology
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

private theorem fin_cons_bool3 (a b c : Bool) (tail : Fin 0→Bool) :
    Fin.cons a (Fin.cons b (Fin.cons c tail))=![a,b,c] := by
  funext i
  fin_cases i <;> rfl

theorem local_word_product_three {f g : Space n→ℝ} {U : Set (Space n)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (⊤:ℕ∞) f U)
    (hg : ContDiffOn ℝ (⊤:ℕ∞) g U) {x : Space n} (hx : x∈U)
    (u v w : Space n) :
    directionalWordDerivative (fun y=>f y*g y) [u,v,w] x =
      directionalWordDerivative f [u,v,w] x*g x +
      directionalWordDerivative f [u,v] x*directionalWordDerivative g [w] x +
      directionalWordDerivative f [u,w] x*directionalWordDerivative g [v] x +
      directionalWordDerivative f [u] x*directionalWordDerivative g [v,w] x +
      directionalWordDerivative f [v,w] x*directionalWordDerivative g [u] x +
      directionalWordDerivative f [v] x*directionalWordDerivative g [u,w] x +
      directionalWordDerivative f [w] x*directionalWordDerivative g [u,v] x +
      f x*directionalWordDerivative g [u,v,w] x := by
  have h := local_word_product_masks hU hf hg ![u,v,w] hx
  simp only [sum_bool_masks] at h
  simp only [Fintype.sum_unique] at h
  simp only [fin_cons_bool3] at h
  simpa [maskedDirections,Fin.tail,add_assoc,Fin.cons_zero,Fin.cons_succ] using h

/-- Exact third normalized derivative for a centered coordinate observable. -/
theorem actualAppellCoefficient_three_coordinate {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (i j k l : Fin n) :
    actualAppellCoefficient μ (fun x=>x l) 3 ![i,j,k] =
      (∫ x, x l*(x i*x j*x k) ∂μ) -
        (if l=i then 1 else 0)*(if j=k then 1 else 0) -
        (if l=j then 1 else 0)*(if i=k then 1 else 0) -
        (if l=k then 1 else 0)*(if i=j then 1 else 0) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hf : MemLp (fun x : Space n=>x l) 2 μ := by
    simpa only [EuclideanSpace.inner_single_right,RCLike.conj_to_real,one_mul] using
      hμ.isotropic.memLp_inner (EuclideanSpace.single l 1)
  obtain ⟨r,hr,hD,h1D⟩ := exists_common_local_exponential_domains hμ.logConcave hf
  let A : Space n→ℝ := fun z=>∫ x, x l ∂exponentialTilt μ z
  let Z := tiltNumerator μ (fun _=>0) (fun _=>1)
  let N := tiltNumerator μ (fun _=>0) (fun x=>x l)
  let e : Fin n→Space n := fun a=>EuclideanSpace.single a 1
  have h0 : (0 : Space n)∈ball 0 r := by simpa using hr
  have hA : ContDiffOn ℝ (⊤:ℕ∞) A (ball 0 r) :=
    contDiffOn_normalized_tilt_average_of_domains hD h1D
  have hZ : ContDiffOn ℝ (⊤:ℕ∞) Z (ball 0 r) :=
    contDiffOn_tiltNumerator_of_localNormExponentialDomain h1D
  have hN : ContDiffOn ℝ (⊤:ℕ∞) N (ball 0 r) :=
    contDiffOn_tiltNumerator_of_localNormExponentialDomain hD
  have hAZ : (fun z=>A z*Z z)=ᶠ[𝓝 0] N := by
    filter_upwards [isOpen_ball.mem_nhds h0] with z hz
    have hz' : ‖z‖<r := by simpa only [mem_ball,dist_zero_right] using hz
    have hzne : Z z≠0 := by
      simpa only [Z,tiltNumerator,zero_add,one_mul] using
        (integral_exp_pos (by simpa only [one_mul] using h1D.integrable_tilt hz'.le)).ne'
    change tiltAverage μ (fun x=>inner ℝ z x) (fun x=>x l)*Z z=N z
    rw [tiltAverage_eq_ratio]
    simpa only [Z,N,tiltNumerator,tiltPartition,zero_add,one_mul] using
      div_mul_cancel₀ (N z) hzne
  have hword : directionalWordDerivative (fun z=>A z*Z z) [e i,e j,e k] 0 =
      directionalWordDerivative N [e i,e j,e k] 0 := by
    have hh := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 3=>Space n) ℝ =>
      T ![e i,e j,e k]) ((hAZ.iteratedFDeriv ℝ 3).eq_of_nhds)
    have hL := local_word_ofFn isOpen_ball (hA.mul hZ) ![e i,e j,e k] h0
    have hR := local_word_ofFn isOpen_ball hN ![e i,e j,e k] h0
    have hLR := hL.trans (hh.trans hR.symm)
    simpa using hLR
  have hA0 : A 0=0 := by simpa [A] using hμ.isotropic.integral_coordinate l
  have hZ0 : Z 0=1 := by simp [Z,tiltNumerator]
  have hDA (a : Fin n) : directionalWordDerivative A [e a] 0 =
      if l=a then 1 else 0 := by
    have hh := actualAppellCoefficient_one_of_isotropic hμ.logConcave hμ.isotropic hf ![a]
    simp only [cons_val_zero] at hh
    rw [hμ.isotropic.integral_coordinate_mul l a] at hh
    simpa only [actualAppellCoefficient,iteratedFDeriv_one_apply,cons_val_zero,
      directionalWordDerivative_cons,directionalWordDerivative_nil,A,e] using hh
  have hDZ (a : Fin n) : directionalWordDerivative Z [e a] 0=0 := by
    change coordinateDerivative Z a 0=0
    rw [coordinateDerivative_tiltNumerator_zero_of_local h1D hr]
    simpa using hμ.isotropic.integral_coordinate a
  have hDZZ (a b : Fin n) : directionalWordDerivative Z [e a,e b] 0=
      if a=b then 1 else 0 := by
    change coordinateHessian Z 0 a b=_
    rw [coordinateHessian_tiltNumerator_zero_of_local h1D hr]
    simpa using hμ.isotropic.integral_coordinate_mul a b
  have hDNN : directionalWordDerivative N [e i,e j,e k] 0=
      ∫ x, x l*(x i*x j*x k) ∂μ := by
    have hh := iteratedFDeriv_tiltNumerator_moment_of_local hD
      (by simpa using hr : ‖(0 : Space n)‖<r) ![e i,e j,e k]
    have hR := local_word_ofFn isOpen_ball hN ![e i,e j,e k] h0
    have hRH := hR.trans hh
    simpa [N,e,Fin.prod_univ_succ,mul_assoc,EuclideanSpace.inner_single_right] using hRH
  have hDAAA : directionalWordDerivative A [e i,e j,e k] 0=
      actualAppellCoefficient μ (fun x=>x l) 3 ![i,j,k] := by
    have hh := local_word_ofFn isOpen_ball hA ![e i,e j,e k] h0
    have he : (fun a : Fin 3=>EuclideanSpace.single (![i,j,k] a) (1:ℝ))=
        ![e i,e j,e k] := by funext a; fin_cases a <;> rfl
    simp only [actualAppellCoefficient,he]
    simpa [A,e] using hh
  have hp := local_word_product_three isOpen_ball hA hZ h0 (e i) (e j) (e k)
  rw [hword,hDNN,hA0,hZ0,hDAAA,hDZ,hDZ,hDZ,hDA,hDA,hDA,hDZZ,hDZZ,hDZZ] at hp
  linarith

/-- Actual four-coordinate cumulant, with the ordered four-slot convention. -/
def actualFourthCumulantArray (μ : Measure (Space n)) (i j k l : Fin n) : ℝ :=
  cumulantTensor μ 4 ![EuclideanSpace.single i 1,EuclideanSpace.single j 1,
    EuclideanSpace.single k 1,EuclideanSpace.single l 1]

theorem actual_fourth_cumulant_coordinate_eq {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (i j k l : Fin n) :
    actualFourthCumulantArray μ i j k l =
      covariance (fun x : Space n=>x i*x j) (fun x=>x k*x l) μ -
        (if i=k then 1 else 0)*(if j=l then 1 else 0) -
        (if i=l then 1 else 0)*(if j=k then 1 else 0) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hk := actualAppellCoefficient_inner_eq_cumulant hμ.logConcave
    (EuclideanSpace.single l 1) 3 ![i,j,k]
  have hsnoc : Fin.snoc (fun a : Fin 3=>EuclideanSpace.single (![i,j,k] a) (1:ℝ))
      (EuclideanSpace.single l 1)=
      ![EuclideanSpace.single i 1,EuclideanSpace.single j 1,
        EuclideanSpace.single k 1,EuclideanSpace.single l 1] := by
    funext a
    fin_cases a <;> rfl
  simp only [EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_right,
    RCLike.conj_to_real,one_mul,hsnoc] at hk
  change actualAppellCoefficient μ (fun x=>x l) 3 ![i,j,k]=
    actualFourthCumulantArray μ i j k l at hk
  rw [←hk,actualAppellCoefficient_three_coordinate hμ]
  rw [covariance_eq_sub (hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul i j)
    (hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul k l),
    hμ.isotropic.integral_coordinate_mul i j,hμ.isotropic.integral_coordinate_mul k l]
  have hm : (∫ x : Space n, x l*(x i*x j*x k) ∂μ)=
      ∫ x : Space n, (x i*x j)*(x k*x l) ∂μ := by
    apply integral_congr_ae
    exact .of_forall fun x=>by ring
  rw [hm]
  simp only [eq_comm (a:=l),Pi.mul_apply,mul_assoc]
  ring

/-- Coordinate-word version used by literal size-three subset contractions. -/
theorem actual_cumulant_four_snoc_coordinate {μ : Measure (Space n)}
    (_hμ : admissibleMeasure μ) (α : Fin 3→Fin n) (m : Fin n) :
    cumulantTensor μ 4
      (Fin.snoc (fun j=>EuclideanSpace.single (α j) 1) (EuclideanSpace.single m 1)) =
      actualFourthCumulantArray μ (α 0) (α 1) (α 2) m := by
  have hα : α=![α 0,α 1,α 2] := by funext i;fin_cases i <;> rfl
  rw [hα]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Permuting the three inserted slots preserves the literal actual kernel. -/
theorem actualFourthCumulant_first_three_symmetric {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (m : Fin n) :
    KLSBelow25.PairTensor.Symmetric
      (fun α : Fin 3→Fin n=>actualFourthCumulantArray μ (α 0) (α 1) (α 2) m) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hf : MemLp (fun x : Space n=>x m) 2 μ := by
    simpa only [EuclideanSpace.inner_single_right,RCLike.conj_to_real,one_mul] using
      hμ.isotropic.memLp_inner (EuclideanSpace.single m 1)
  have heq (α : Fin 3→Fin n) :
      actualFourthCumulantArray μ (α 0) (α 1) (α 2) m =
      actualAppellCoefficient μ (fun x=>x m) 3 α := by
    rw [←actual_cumulant_four_snoc_coordinate hμ α m]
    have hk := actualAppellCoefficient_inner_eq_cumulant hμ.logConcave
      (EuclideanSpace.single m 1) 3 α
    simpa only [EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_right,
      RCLike.conj_to_real,one_mul] using hk.symm
  intro π α
  change actualFourthCumulantArray μ ((α∘π) 0) ((α∘π) 1) ((α∘π) 2) m=
    actualFourthCumulantArray μ (α 0) (α 1) (α 2) m
  rw [heq (α∘π),heq α]
  exact actualAppellCoefficient_pair_symmetric hμ.logConcave hf π α

/-- Literal ordered contraction of the actual cumulant tensor. -/
theorem actualFourthCumulantFlat_eq_tensor_contraction {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (i j : Fin n) :
    actualFourthCumulantFlat μ H i j =
      ∑ a,∑ b,actualFourthCumulantArray μ i j a b*H a b := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hcoord := hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul
  have hp := covariance_matrixQuadratic_eq_pairing (hcoord i j) hcoord H
  have hpair : quadraticCovarianceMatrix μ (matrixQuadratic H) i j=
      ∑ a,∑ b,covariance (fun x : Space n=>x i*x j) (fun x=>x a*x b) μ*H a b := by
    rw [quadraticCovarianceMatrix,covariance_comm,hp]
    simp only [quadraticCovarianceMatrix,mul_comm]
  have hHij : H j i=H i j := by
    simpa only [Matrix.transpose_apply] using congrFun (congrFun hH i) j
  simp_rw [actual_fourth_cumulant_coordinate_eq hμ]
  simp only [sub_mul,Finset.sum_sub_distrib]
  simp [actualFourthCumulantFlat,hpair,ite_mul,hHij]
  ring

/-- The genuine fourth cumulant, flattened from two symmetric ordered slots
to two ordered slots, has operator norm at most six. -/
theorem actual_fourth_cumulant_tensor_flat_square_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    (∑ i,∑ j,(∑ a,∑ b,actualFourthCumulantArray μ i j a b*H a b)^2) ≤
      36*matrixFrobeniusSq H := by
  have h := actual_fourth_cumulant_flat_square_le hμ H hH
  simpa only [matrixFrobeniusSq,actualFourthCumulantFlat_eq_tensor_contraction hμ H hH] using h

/-- Bilinear form version of the same genuine two-slot flattening estimate. -/
theorem actual_fourth_cumulant_flat_pairing_sq_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (H J : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    (∑ i,∑ j,J i j*(∑ a,∑ b,actualFourthCumulantArray μ i j a b*H a b))^2 ≤
      36*matrixFrobeniusSq J*matrixFrobeniusSq H := by
  have h := matrix_frobenius_pairing_sq_le J (actualFourthCumulantFlat μ H)
  simp_rw [actualFourthCumulantFlat_eq_tensor_contraction hμ H hH] at h
  have hJ : 0 ≤ matrixFrobeniusSq J :=
    Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>sq_nonneg _
  have hb := mul_le_mul_of_nonneg_left (actual_fourth_cumulant_flat_square_le hμ H hH) hJ
  exact h.trans (by nlinarith)

end KLS.DeterministicBridgeIntegration

#print axioms KLS.DeterministicBridgeIntegration.actual_cumulant_four_snoc_coordinate
#print axioms KLS.DeterministicBridgeIntegration.actualFourthCumulant_first_three_symmetric
#print axioms KLS.DeterministicBridgeIntegration.actual_fourth_cumulant_coordinate_eq
#print axioms KLS.DeterministicBridgeIntegration.actual_fourth_cumulant_tensor_flat_square_le

#print axioms KLS.DeterministicBridgeIntegration.actual_fourth_cumulant_flat_pairing_sq_le
