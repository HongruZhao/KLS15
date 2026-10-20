import ActualAppellObservationOperators
import ActualAppellLowerContraction
import ActualAppellLinearDirection
import KLS.WeightedSuccessorDomain

/-!
# Actual Appell observation restricted to linear functions

The linear tests used in cumulant contractions form an isometric copy of the
physical Euclidean space in L² of an isotropic law. Restricting the genuine
Appell observation to this space retains its actual norm instead of paying the
full L² observation norm. No sharper universal numerical constant is assumed.
-/

noncomputable section
open MeasureTheory InnerProductSpace ContinuousLinearMap
open scoped BigOperators ContDiff
namespace KLSImprovement.LinearAppell
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def actualLinearEmbeddingMap (hiso : IsIsotropic μ) : Space n →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := isotropicLinearObservable hiso
  map_add' b c := by
    change (∑ i : Fin n, (b i + c i) • isotropicAffineCoordinate hiso (some i)) = _
    simp only [add_smul, Finset.sum_add_distrib, isotropicLinearObservable]
  map_smul' a b := by
    change (∑ i : Fin n, (a * b i) • isotropicAffineCoordinate hiso (some i)) = _
    simp only [isotropicLinearObservable, Finset.smul_sum, smul_smul, RingHom.id_apply]

def actualLinearEmbedding (hiso : IsIsotropic μ) : Space n →L[ℝ] Lp ℝ 2 μ :=
  ⟨actualLinearEmbeddingMap hiso, LinearMap.continuous_of_finiteDimensional _⟩

theorem actualLinearEmbedding_coe (hiso : IsIsotropic μ) (b : Space n) :
    (actualLinearEmbedding hiso b : Space n → ℝ) =ᵐ[μ] (fun x => inner ℝ x b) :=
  isotropicLinearObservable_coe hiso b

theorem actualLinearEmbedding_norm_sq (hiso : IsIsotropic μ) (b : Space n) :
    ‖actualLinearEmbedding hiso b‖ ^ 2 = ‖b‖ ^ 2 := by
  rw [realLp_norm_sq_eq_integral_sq_of_ae (actualLinearEmbedding_coe hiso b),
    hiso.integral_inner_sq]

theorem actualLinearEmbedding_norm (hiso : IsIsotropic μ) (b : Space n) :
    ‖actualLinearEmbedding hiso b‖ = ‖b‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (actualLinearEmbedding_norm_sq hiso b)

def actualLinearAppellObservation (hμ : admissibleMeasure μ) (d : ℕ) :
    Space n →L[ℝ] EuclideanSpace ℝ (Fin d → Fin n) :=
  (actualAppellObservation hμ d).comp (actualLinearEmbedding hμ.isotropic)

/-- The restriction always has norm no greater than the original actual
Appell observation. This structural improvement is valid for every admissible law. -/
theorem actualLinearAppellObservation_norm_le_full (hμ : admissibleMeasure μ) (d : ℕ) :
    ‖actualLinearAppellObservation hμ d‖ ≤ ‖actualAppellObservation hμ d‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro b
  change ‖actualAppellObservation hμ d (actualLinearEmbedding hμ.isotropic b)‖ ≤ _
  simpa only [actualLinearEmbedding_norm] using
    (actualAppellObservation hμ d).le_opNorm (actualLinearEmbedding hμ.isotropic b)

/-- The actual restricted observation is exactly the cumulant tensor with
its last slot fixed to the physical vector b. -/
theorem actualLinearAppellObservation_apply (hμ : admissibleMeasure μ) (d : ℕ)
    (b : Space n) (α : Fin d → Fin n) :
    actualLinearAppellObservation hμ d b α =
      cumulantTensor μ (d + 1)
        (Fin.snoc (fun j => EuclideanSpace.single (α j) 1) b) := by
  change actualAppellObservation hμ d (actualLinearEmbedding hμ.isotropic b) α = _
  rw [actualAppellObservation_apply]
  change actualAppellCoefficient μ (actualLinearEmbedding hμ.isotropic b) d α = _
  rw [actualAppellCoefficient_congr_ae (actualLinearEmbedding_coe hμ.isotropic b),
    actualAppellCoefficient_inner_eq_cumulant hμ.logConcave]
  simp only [EuclideanSpace.basisFun_apply]

theorem actualLinearAppellObservation_norm_sq (hμ : admissibleMeasure μ) (d : ℕ)
    (b : Space n) :
    ‖actualLinearAppellObservation hμ d b‖ ^ 2 =
      actualAppellEnergy μ (fun x => inner ℝ x b) d := by
  change ‖actualAppellObservation hμ d (actualLinearEmbedding hμ.isotropic b)‖ ^ 2 = _
  rw [actualAppellObservation_norm_sq]
  unfold actualAppellEnergy
  apply Finset.sum_congr rfl
  intro α _
  rw [actualAppellCoefficient_congr_ae (actualLinearEmbedding_coe hμ.isotropic b)]

theorem actual_linear_appell_energy_le (hμ : admissibleMeasure μ) (d : ℕ)
    (b : Space n) :
    actualAppellEnergy μ (fun x => inner ℝ x b) d ≤
      ‖actualLinearAppellObservation hμ d‖ ^ 2 * ‖b‖ ^ 2 := by
  rw [←actualLinearAppellObservation_norm_sq]
  simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      ((actualLinearAppellObservation hμ d).le_opNorm b)

/-- Replace the full Appell cap in the canonical cumulant contraction by the
actual norm of its restriction to linear tests, preserving every original
measure, coefficient, ordered index, and factorial normalization. -/
theorem actualCanonicalAppellContraction_square_le_restricted
    (hμ : admissibleMeasure μ) (f : Space n → ℝ) (a b : ℕ) :
    (∑ α : Fin a → Fin n, ∑ β : Fin b → Fin n,
      (actualCanonicalAppellContraction μ f a b α β) ^ 2) ≤
      ‖actualLinearAppellObservation hμ a‖ ^ 2 * actualAppellEnergy μ f (b + 1) := by
  rw [Finset.sum_comm]
  have hp (β : Fin b → Fin n) :
      (∑ α : Fin a → Fin n, (actualCanonicalAppellContraction μ f a b α β) ^ 2) ≤
        ‖actualLinearAppellObservation hμ a‖ ^ 2 *
          (∑ i : Fin n, (actualAppellCoefficient μ f (b + 1) (Fin.cons i β)) ^ 2) := by
    let v : Space n := WithLp.toLp 2
      (fun i => actualAppellCoefficient μ f (b + 1) (Fin.cons i β))
    have hh := actual_linear_appell_energy_le hμ a v
    rw [EuclideanSpace.real_norm_sq_eq] at hh
    simpa only [actualAppellEnergy,
      actualCanonicalAppellContraction_eq_linear_coefficient hμ.logConcave, v] using hh
  calc
    _ ≤ ∑ β : Fin b → Fin n, ‖actualLinearAppellObservation hμ a‖ ^ 2 *
        (∑ i : Fin n, (actualAppellCoefficient μ f (b + 1) (Fin.cons i β)) ^ 2) :=
      Finset.sum_le_sum fun β _ => hp β
    _ = _ := by
      rw [←Finset.mul_sum, Finset.sum_comm]
      congr 1
      simpa only [dotProduct, pow_two] using actualAppell_next_slices_square μ f b

end KLSImprovement.LinearAppell

#print axioms KLSImprovement.LinearAppell.actualLinearEmbedding_norm
#print axioms KLSImprovement.LinearAppell.actualLinearAppellObservation_norm_le_full
#print axioms KLSImprovement.LinearAppell.actualLinearAppellObservation_apply
#print axioms KLSImprovement.LinearAppell.actualCanonicalAppellContraction_square_le_restricted
