import ActualCubicCreationBound
import ActualAppellTerminalSplit
import ActualAppellQuadraticSeed

/-! The proper degree-three Appell remainder is the literal cubic creation
operator. Its norm retains the actual degree-two energy. -/
noncomputable section
open MeasureTheory Matrix Set Metric
open scoped BigOperators ContDiff Topology
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLS.TensorEnergy
open KLSBelow25.CubicCreation KLSBelow25.CubicSymmetricNoise
variable {n : ℕ}
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem actual_list_cumulant_three_coordinate {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (i j k : Fin n) :
    listCumulant μ [EuclideanSpace.single i 1, EuclideanSpace.single j 1,
      EuclideanSpace.single k 1] = actualThirdCubicArray μ i j k := by
  let : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨r,hr,h1⟩ := hμ.logConcave.exists_localNormExponentialDomain_one
  rw [listCumulant_eq_local_word hμ.logConcave]
  have hh := local_word_ofFn isOpen_ball (contDiffOn_logLaplace_of_local h1)
    ![EuclideanSpace.single i 1,EuclideanSpace.single j 1,EuclideanSpace.single k 1]
    (show (0 : Space n)∈ball 0 r by simpa using hr)
  have he : List.ofFn (![EuclideanSpace.single i 1,EuclideanSpace.single j 1,
      EuclideanSpace.single k 1] : Fin 3 → Space n) = [EuclideanSpace.single i 1,EuclideanSpace.single j 1,
      EuclideanSpace.single k 1] := by simp [List.ofFn_succ]
  rw [he] at hh
  rw [hh]
  change cumulantTensor μ 3 _ = _
  have hk := actualAppellCoefficient_inner_eq_cumulant hμ.logConcave
    (EuclideanSpace.single k 1) 2 ![i,j]
  have htuple : Fin.snoc (fun a : Fin 2 => EuclideanSpace.basisFun (Fin n) ℝ (![i,j] a))
      (EuclideanSpace.single k 1) =
      ![EuclideanSpace.single i 1,EuclideanSpace.single j 1,EuclideanSpace.single k 1] := by
    funext a; fin_cases a <;> simp [Fin.snoc,EuclideanSpace.basisFun_apply]
  rw [htuple] at hk
  rw [←hk,actualAppellCoefficient_two_eq_quadraticCovariance hμ
    (hμ.isotropic.memLp_inner _)]
  change ProbabilityTheory.covariance (fun x => inner ℝ x (EuclideanSpace.single k 1))
    (fun x => x i*x j) μ = thirdCumulantMatrix μ (MomentMap.coordinateVector i) j k
  rw [ProbabilityTheory.covariance_eq_sub (hμ.isotropic.memLp_inner _)
    (hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul i j),
    hμ.isotropic.integral_inner,zero_mul,sub_zero,
    thirdCumulantMatrix_coordinate_eq_cubic]
  apply integral_congr_ae
  exact .of_forall fun x => by simp [EuclideanSpace.inner_single_right]; ring

theorem actual_damped_word_two_coordinate {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f : Space n→ℝ} (hf : MemLp f 2 μ) (i j : Fin n) :
    directionalWordDerivative (actualDampedAverage μ f 0)
      [EuclideanSpace.single i 1,EuclideanSpace.single j 1] 0 =
      actualAppellCoefficient μ f 2 ![i,j] := by
  obtain ⟨r,hr,hD,h1⟩ := exists_common_local_exponential_domains hLC hf
  have hh := local_word_ofFn isOpen_ball
    (contDiffOn_actualDampedAverage hD h1 (show (0:ℝ)≤0 by rfl))
    ![EuclideanSpace.single i 1,EuclideanSpace.single j 1]
    (show (0 : Space n)∈ball 0 r by simpa using hr)
  have he : List.ofFn (![EuclideanSpace.single i 1,EuclideanSpace.single j 1] : Fin 2 → Space n) =
      [EuclideanSpace.single i 1,EuclideanSpace.single j 1] := by simp [List.ofFn_succ]
  rw [he] at hh
  rw [hh,actualDampedAverage_zero_eq_tilt_average]
  have ht : (![EuclideanSpace.single i 1,EuclideanSpace.single j 1] : Fin 2→Space n) =
      fun a => EuclideanSpace.single (![i,j] a) 1 := by
    funext a; fin_cases a <;> rfl
  rw [ht]
  rfl

theorem actualAppellProperRemainder_three_creation {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ)
    (i j k : Fin n) :
    actualAppellProperRemainder μ f 3 ![i,j,k] =
      creation (actualThirdCubicArray μ) (fun l m => actualAppellCoefficient μ f 2 ![l,m]) i j k := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProb
  have he : (Finset.univ : Finset (Finset (Fin 3))).filter
      (fun S => 2≤S.card ∧ S.card≤3-1) = {{0,1},{0,2},{1,2}} := by decide
  change (∑ S : Finset (Fin 3), if 2≤S.card ∧ S.card≤3-1 then
    actualSubsetAppellContraction μ f 3 S ![i,j,k] else 0) = _
  rw [←Finset.sum_filter,he]
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton]
  simp [actualSubsetAppellContraction,maskedDirections,Fin.tail]
  simp only [←directionalWordDerivative_cons]
  simp_rw [actual_list_cumulant_three_coordinate hμ,
    actual_damped_word_two_coordinate hμ.logConcave hf]
  have hswap (a b c : Fin n) :
      (∑ x,actualThirdCubicArray μ a b x*actualAppellCoefficient μ f 2 ![c,x]) =
      ∑ x,actualThirdCubicArray μ a b x*actualAppellCoefficient μ f 2 ![x,c] := by
    apply Finset.sum_congr rfl
    intro x _
    rw [actualAppell_two_swap hμ.logConcave hf c x]
  rw [hswap i j k,hswap i k j,hswap j k i]
  unfold creation
  ring

theorem actualAppellProperRemainder_three_square_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    (∑ a : Fin 3→Fin n,(actualAppellProperRemainder μ f 3 a)^2) ≤
      48*actualAppellEnergy μ f 2 := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hh := actual_cubic_creation_square_le hμ
    (fun i j => actualAppellCoefficient μ f 2 ![i,j])
    (actualAppell_two_swap hμ.logConcave hf)
  simp only [sum_fin_three_coordinates,actualAppellProperRemainder_three_creation hμ hf]
  simpa only [square,tripleSum,matrixSquare,actualAppellEnergy,sum_fin_two_coordinates] using hh

theorem actualAppellProperRemainder_three_pairing_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3) ≤
      Real.sqrt (actualAppellEnergy μ f 3)*Real.sqrt (48*actualAppellEnergy μ f 2) := by
  have hs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin 3→Fin n)) (actualAppellCoefficient μ f 3)
    (actualAppellProperRemainder μ f 3)
  have hb := mul_le_mul_of_nonneg_left
    (actualAppellProperRemainder_three_square_le hμ hf) (actualAppellEnergy_nonneg μ f 3)
  change (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)^2 ≤
    actualAppellEnergy μ f 3*(∑ a : Fin 3→Fin n,(actualAppellProperRemainder μ f 3 a)^2) at hs
  have hsqX := Real.sq_sqrt (actualAppellEnergy_nonneg μ f 3)
  have hsqY := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤48) (actualAppellEnergy_nonneg μ f 2))
  have hnon : 0≤Real.sqrt (actualAppellEnergy μ f 3)*Real.sqrt (48*actualAppellEnergy μ f 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [hs.trans hb,sq_nonneg
    (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3+
      Real.sqrt (actualAppellEnergy μ f 3)*Real.sqrt (48*actualAppellEnergy μ f 2))]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualAppellProperRemainder_three_creation
#print axioms KLS.DeterministicBridgeIntegration.actualAppellProperRemainder_three_square_le
#print axioms KLS.DeterministicBridgeIntegration.actualAppellProperRemainder_three_pairing_le
