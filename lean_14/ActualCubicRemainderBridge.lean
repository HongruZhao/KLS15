import CubicRemainderSquare
import ActualAppellTerminalSplit
import ActualAppellQuadraticSeed

noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric Matrix
open scoped ContDiff BigOperators Topology
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25.CubicRemainderImprovement
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem fullClass_cumulant_three_coordinates (hμ : admissibleMeasure μ)
    (i j k : Fin n) :
    cumulantTensor μ 3 ![EuclideanSpace.single i 1, EuclideanSpace.single j 1,
      EuclideanSpace.single k 1] =
      thirdCumulantMatrix μ (MomentMap.coordinateVector i) j k := by
  have hh := actualAppellCoefficient_inner_eq_cumulant hμ.logConcave
    (EuclideanSpace.single k 1) 2 ![i,j]
  have he : (Fin.snoc (fun a : Fin 2 => EuclideanSpace.single (![i,j] a) 1)
      (EuclideanSpace.single k 1) : Fin 3 → Space n) =
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1, EuclideanSpace.single k 1] := by
    funext a; fin_cases a <;> rfl
  simp only [EuclideanSpace.basisFun_apply] at hh
  rw [he] at hh
  rw [← hh, actualAppellCoefficient_two_eq_quadraticCovariance hμ
    (hμ.isotropic.memLp_inner (EuclideanSpace.single k 1))]
  rw [quadraticCovarianceMatrix]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ProbabilityTheory.covariance_eq_sub
    (hμ.isotropic.memLp_inner (EuclideanSpace.single k 1))
    (hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul i j)]
  simp only [EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul, Pi.mul_apply,
    hμ.isotropic.integral_coordinate, zero_mul, sub_zero]
  rw [thirdCumulantMatrix_coordinate_eq_cubic]
  apply integral_congr_ae (.of_forall fun x => ?_)
  ring

theorem listCumulant_three_coordinates (hμ : admissibleMeasure μ) (i j k : Fin n) :
    listCumulant μ [EuclideanSpace.single i 1, EuclideanSpace.single j 1,
      EuclideanSpace.single k 1] =
      thirdCumulantMatrix μ (MomentMap.coordinateVector i) j k := by
  obtain ⟨r, hr, hD, h1⟩ := exists_common_local_exponential_domains hμ.logConcave
    (memLp_const (1 : ℝ))
  have h0 : (0 : Space n) ∈ ball 0 r := by simpa using hr
  rw [listCumulant_eq_local_word hμ.logConcave]
  have hh := local_word_ofFn isOpen_ball (contDiffOn_logLaplace_of_local h1)
    ![EuclideanSpace.single i 1, EuclideanSpace.single j 1, EuclideanSpace.single k 1] h0
  have hh' : directionalWordDerivative (tiltLogLaplace μ)
      [EuclideanSpace.single i 1, EuclideanSpace.single j 1, EuclideanSpace.single k 1] 0 =
      cumulantTensor μ 3 ![EuclideanSpace.single i 1, EuclideanSpace.single j 1,
        EuclideanSpace.single k 1] := by
    simpa [List.ofFn_succ, Fin.tail, cumulantTensor] using hh
  rw [hh', fullClass_cumulant_three_coordinates hμ]

theorem actual_word_two_coordinates (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (i j : Fin n) :
    directionalWordDerivative (actualDampedAverage μ f 0)
      [EuclideanSpace.single i 1, EuclideanSpace.single j 1] 0 =
      actualAppellCoefficient μ f 2 ![i,j] := by
  obtain ⟨r, hr, hD, h1⟩ := exists_common_local_exponential_domains hμ.logConcave hf
  have h0 : (0 : Space n) ∈ ball 0 r := by simpa using hr
  have hh := local_word_ofFn isOpen_ball
    (contDiffOn_actualDampedAverage hD h1 (show (0 : ℝ) ≤ 0 from le_rfl))
    ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] h0
  rw [actualDampedAverage_zero_eq_tilt_average] at hh ⊢
  have he : (fun a : Fin 2 => (EuclideanSpace.single (![i,j] a) 1 : Space n)) =
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] := by
    funext a; fin_cases a <;> rfl
  unfold actualAppellCoefficient
  rw [he]
  simpa [List.ofFn_succ, Fin.tail] using hh

theorem actualAppellProperRemainder_three_coordinates (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (i j k : Fin n) :
    actualAppellProperRemainder μ f 3 ![i,j,k] =
      remainder (actualCubicSlotArray μ f) i j k := by
  classical
  have henum : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0,1}, {0,2}, {1,2}, {0,1,2}} := by decide
  change (∑ S : Finset (Fin 3), if 2 ≤ S.card ∧ S.card ≤ 3-1 then
    actualSubsetAppellContraction μ f 3 S ![i,j,k] else 0) = _
  rw [henum]
  norm_num [Finset.ext_iff, Fin.forall_fin_succ, actualSubsetAppellContraction, maskedDirections, List.ofFn_succ, Fin.tail]
  have hwd (a b : Fin n) :
      (fderiv ℝ (directionalWordDerivative (actualDampedAverage μ f 0)
        [EuclideanSpace.single b 1]) 0) (EuclideanSpace.single a 1) =
      actualAppellCoefficient μ f 2 ![b,a] := by
    change directionalWordDerivative (actualDampedAverage μ f 0)
      [EuclideanSpace.single a 1, EuclideanSpace.single b 1] 0 = _
    rw [actual_word_two_coordinates hμ hf, actualAppell_two_swap hμ.logConcave hf a b]
  simp_rw [listCumulant_three_coordinates hμ, hwd]
  unfold remainder actualCubicSlotArray
  ring

theorem actualAppellProperRemainder_three_square_le_retained (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    (∑ γ : Fin 3 → Fin n, (actualAppellProperRemainder μ f 3 γ)^2) ≤
      48*actualAppellEnergy μ f 2 := by
  rw [sum_fin_three_coordinates]
  simp_rw [actualAppellProperRemainder_three_coordinates hμ hf]
  exact actualCubicRemainder_square_le hμ hf

def actualCubicRemainderGram (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  3*KLSBelow25.CubicSymmetricNoise.square (actualCubicSlotArray μ f)+
    6*KLSBelow25.CubicSymmetricNoise.cross (actualCubicSlotArray μ f)

theorem actualAppellProperRemainder_three_square_eq_gram (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    (∑ γ : Fin 3 → Fin n, (actualAppellProperRemainder μ f 3 γ)^2) =
      actualCubicRemainderGram μ f := by
  rw [sum_fin_three_coordinates]
  simp_rw [actualAppellProperRemainder_three_coordinates hμ hf]
  exact remainder_square _ (actualCubicSlotArray_first_symmetry μ f)

theorem actualCubicRemainderGram_nonneg (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    0 ≤ actualCubicRemainderGram μ f := by
  rw [← actualAppellProperRemainder_three_square_eq_gram hμ hf]
  positivity

theorem actualCubicRemainderGram_defect_identity (f : Space n → ℝ) :
    actualCubicRemainderGram μ f =
      48*actualAppellEnergy μ f 2-
      3*(8*actualAppellEnergy μ f 2-
        KLSBelow25.CubicSymmetricNoise.square (actualCubicSlotArray μ f))-
      6*(4*actualAppellEnergy μ f 2-
        KLSBelow25.CubicSymmetricNoise.cross (actualCubicSlotArray μ f)) := by
  unfold actualCubicRemainderGram
  ring

theorem actualCubicRemainderGram_le (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualCubicRemainderGram μ f ≤ 48*actualAppellEnergy μ f 2 := by
  rw [← actualAppellProperRemainder_three_square_eq_gram hμ hf]
  exact actualAppellProperRemainder_three_square_le_retained hμ hf

theorem actualAppellProperRemainder_three_norm_eq_gram (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    ‖(WithLp.toLp 2 (actualAppellProperRemainder μ f 3) :
      EuclideanSpace ℝ (Fin 3 → Fin n))‖ = Real.sqrt (actualCubicRemainderGram μ f) := by
  have hn := EuclideanSpace.real_norm_sq_eq
    (WithLp.toLp 2 (actualAppellProperRemainder μ f 3) :
      EuclideanSpace ℝ (Fin 3 → Fin n))
  rw [actualAppellProperRemainder_three_square_eq_gram hμ hf] at hn
  rw [← hn, Real.sqrt_sq (norm_nonneg _)]

theorem actualAppellProperRemainder_three_pairing_le_gram (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3 ≤
      Real.sqrt (actualAppellEnergy μ f 3)*Real.sqrt (actualCubicRemainderGram μ f) := by
  have hh := real_inner_le_norm
    (WithLp.toLp 2 (actualAppellCoefficient μ f 3) : EuclideanSpace ℝ (Fin 3 → Fin n))
    (WithLp.toLp 2 (actualAppellProperRemainder μ f 3) : EuclideanSpace ℝ (Fin 3 → Fin n))
  have hn : ‖(WithLp.toLp 2 (actualAppellCoefficient μ f 3) :
      EuclideanSpace ℝ (Fin 3 → Fin n))‖ = Real.sqrt (actualAppellEnergy μ f 3) := by
    have hs : ‖(WithLp.toLp 2 (actualAppellCoefficient μ f 3) :
        EuclideanSpace ℝ (Fin 3 → Fin n))‖^2 = actualAppellEnergy μ f 3 :=
      EuclideanSpace.real_norm_sq_eq _
    rw [← hs, Real.sqrt_sq (norm_nonneg _)]
  rw [hn, actualAppellProperRemainder_three_norm_eq_gram hμ hf] at hh
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm] using hh

theorem actualAppellProperRemainder_three_norm_le (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    ‖(WithLp.toLp 2 (actualAppellProperRemainder μ f 3) :
      EuclideanSpace ℝ (Fin 3 → Fin n))‖ ≤ Real.sqrt (48*actualAppellEnergy μ f 2) := by
  have hn := EuclideanSpace.real_norm_sq_eq
    (WithLp.toLp 2 (actualAppellProperRemainder μ f 3) :
      EuclideanSpace ℝ (Fin 3 → Fin n))
  have hb := actualAppellProperRemainder_three_square_le_retained hμ hf
  have hs := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤48)
    (actualAppellEnergy_nonneg μ f 2))
  have hp := Real.sqrt_nonneg (48*actualAppellEnergy μ f 2)
  have hnorm := norm_nonneg (WithLp.toLp 2 (actualAppellProperRemainder μ f 3) :
    EuclideanSpace ℝ (Fin 3 → Fin n))
  nlinarith

theorem actualAppellProperRemainder_three_pairing_le_retained (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3 ≤
      Real.sqrt (actualAppellEnergy μ f 3)*Real.sqrt (48*actualAppellEnergy μ f 2) := by
  have hh := real_inner_le_norm
    (WithLp.toLp 2 (actualAppellCoefficient μ f 3) : EuclideanSpace ℝ (Fin 3 → Fin n))
    (WithLp.toLp 2 (actualAppellProperRemainder μ f 3) : EuclideanSpace ℝ (Fin 3 → Fin n))
  have hn : ‖(WithLp.toLp 2 (actualAppellCoefficient μ f 3) :
      EuclideanSpace ℝ (Fin 3 → Fin n))‖ = Real.sqrt (actualAppellEnergy μ f 3) := by
    have hs : ‖(WithLp.toLp 2 (actualAppellCoefficient μ f 3) :
        EuclideanSpace ℝ (Fin 3 → Fin n))‖^2 = actualAppellEnergy μ f 3 :=
      EuclideanSpace.real_norm_sq_eq _
    rw [← hs, Real.sqrt_sq (norm_nonneg _)]
  rw [hn] at hh
  have hb := mul_le_mul_of_nonneg_left (actualAppellProperRemainder_three_norm_le hμ hf)
    (Real.sqrt_nonneg (actualAppellEnergy μ f 3))
  have hh' : actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3 ≤
      Real.sqrt (actualAppellEnergy μ f 3)*
      ‖(WithLp.toLp 2 (actualAppellProperRemainder μ f 3) :
        EuclideanSpace ℝ (Fin 3 → Fin n))‖ := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm] using hh
  exact hh'.trans hb

end KLS.DeterministicBridgeIntegration

#print axioms KLS.DeterministicBridgeIntegration.actualAppellProperRemainder_three_coordinates
#print axioms KLS.DeterministicBridgeIntegration.actualAppellProperRemainder_three_square_le_retained
#print axioms KLS.DeterministicBridgeIntegration.actualAppellProperRemainder_three_pairing_le_retained
#print axioms KLS.DeterministicBridgeIntegration.actualAppellProperRemainder_three_square_eq_gram
#print axioms KLS.DeterministicBridgeIntegration.actualCubicRemainderGram_defect_identity
#print axioms KLS.DeterministicBridgeIntegration.actualAppellProperRemainder_three_pairing_le_gram
