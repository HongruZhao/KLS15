import ConvexTiltCubicAlgebra

/-! The scalar covariance-normalized cubic cap as an actual square integral.
Finite moments are required before exchanging each finite sum and integral. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace KLSImprovement.ScalarCovarianceCubic
open KLSImprovement.ConvexTiltAlgebra
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

-- Use the one-dimensional Euclidean space without assuming isotropy.
abbrev ScalarSpace := EuclideanSpace ℝ (Fin 1)
def raw (μ : Measure ScalarSpace) (k : ℕ) : ℝ := ∫ x,x 0^k ∂μ
def cubic (μ : Measure ScalarSpace) (x : ScalarSpace) : ℝ :=
  (x 0-raw μ 1)^3-3*variance (raw μ)*(x 0-raw μ 1)-centralThree (raw μ)
def actualCap (μ : Measure ScalarSpace) : ℝ :=
  (∫ x,(cubic μ x)^2 ∂μ)/(36*(variance (raw μ))^3)

private def squareCoefficients (m v a : ℝ) : Fin 7 → ℝ :=
  let c0 := -m^3+3*v*m-a
  let c1 := 3*m^2-3*v
  let c2 := -3*m
  ![c0^2,2*c0*c1,c1^2+2*c0*c2,2*c0+2*c1*c2,c2^2+2*c1,2*c2,1]

private theorem square_expansion (m v a z : ℝ) :
    ((z-m)^3-3*v*(z-m)-a)^2=
      ∑ i : Fin 7,squareCoefficients m v a i*z^i.val := by
  simp [Fin.sum_univ_succ,squareCoefficients]
  ring

theorem cubic_square_integral (μ : Measure ScalarSpace) [IsProbabilityMeasure μ]
    (hm : ∀ k ≤ 6,Integrable (fun x : ScalarSpace => x 0^k) μ) :
    (∫ x,(cubic μ x)^2 ∂μ)=
      centralSix (raw μ)-6*variance (raw μ)*centralFour (raw μ)+
        9*(variance (raw μ))^3-(centralThree (raw μ))^2 := by
  let m := raw μ 1
  let v := variance (raw μ)
  let a := centralThree (raw μ)
  have he : (fun x : ScalarSpace => (cubic μ x)^2)=
      (fun x => ∑ i : Fin 7,squareCoefficients m v a i*x 0^i.val) := by
    funext x
    exact square_expansion m v a (x 0)
  have hi (i : Fin 7) : Integrable
      (fun x : ScalarSpace => squareCoefficients m v a i*x 0^i.val) μ :=
    (hm i.val (by omega)).const_mul _
  rw [he,integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_const_mul]
  change (∑ i : Fin 7,squareCoefficients m v a i*raw μ i.val)=_
  have hr0 : raw μ 0=1 := by simp [raw]
  simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,hr0,squareCoefficients]
  dsimp [m,v,a]
  unfold variance centralThree centralFour centralSix
  ring

theorem actualCap_eq_momentCap (μ : Measure ScalarSpace) [IsProbabilityMeasure μ]
    (hm : ∀ k ≤ 6,Integrable (fun x : ScalarSpace => x 0^k) μ) :
    actualCap μ=cap (raw μ) := by
  unfold actualCap cap
  rw [cubic_square_integral μ hm]

theorem centralThree_eq_centered_integral (μ : Measure ScalarSpace) [IsProbabilityMeasure μ]
    (hm : ∀ k ≤ 3,Integrable (fun x : ScalarSpace => x 0^k) μ) :
    centralThree (raw μ)=∫ x,(x 0-raw μ 1)^3 ∂μ := by
  let m := raw μ 1
  let c : Fin 4 → ℝ := ![-m^3,3*m^2,-3*m,1]
  have he : (fun x : ScalarSpace => (x 0-raw μ 1)^3)=
      (fun x => ∑ i : Fin 4,c i*x 0^i.val) := by
    funext x
    simp [Fin.sum_univ_succ,c,m]
    ring
  have hi (i : Fin 4) : Integrable (fun x : ScalarSpace => c i*x 0^i.val) μ :=
    (hm i.val (by omega)).const_mul _
  rw [he,integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_const_mul]
  change centralThree (raw μ)=(∑ i : Fin 4,c i*raw μ i.val)
  have hr0 : raw μ 0=1 := by simp [raw]
  simp [Fin.sum_univ_succ,c,m,hr0,centralThree]
  ring

theorem variance_eq_centered_integral (μ : Measure ScalarSpace) [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ScalarSpace => x 0) μ)
    (h2 : Integrable (fun x : ScalarSpace => x 0^2) μ) :
    variance (raw μ)=∫ x,(x 0-raw μ 1)^2 ∂μ := by
  have he : (fun x : ScalarSpace => (x 0-raw μ 1)^2)=
      (fun x => x 0^2-2*raw μ 1*x 0+(raw μ 1)^2) := by funext x; ring
  rw [he,integral_add
    (f:=fun x : ScalarSpace => x 0^2-2*raw μ 1*x 0)
    (g:=fun _ : ScalarSpace => (raw μ 1)^2)
    (h2.sub (h1.const_mul (2*raw μ 1))) (integrable_const _),
    integral_sub (f:=fun x : ScalarSpace => x 0^2)
      (g:=fun x : ScalarSpace => 2*raw μ 1*x 0)
      h2 (h1.const_mul (2*raw μ 1)),integral_const_mul]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  have hr1 : (∫ x : ScalarSpace,x 0 ∂μ)=raw μ 1 := by simp [raw]
  rw [hr1]
  unfold variance raw
  ring

end KLSImprovement.ScalarCovarianceCubic
#print axioms KLSImprovement.ScalarCovarianceCubic.cubic_square_integral
#print axioms KLSImprovement.ScalarCovarianceCubic.actualCap_eq_momentCap
#print axioms KLSImprovement.ScalarCovarianceCubic.centralThree_eq_centered_integral
#print axioms KLSImprovement.ScalarCovarianceCubic.variance_eq_centered_integral
