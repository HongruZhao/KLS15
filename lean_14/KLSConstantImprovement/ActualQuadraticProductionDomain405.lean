import KLSConstantImprovement.ActualQuadraticHessianFactorDomain405
import KLSConstantImprovement.ActualResponseTargetDomain405
import KLSConstantImprovement.ActualSourceNaturalTargetCurvatureDomain405

/-! Global entry domains of the actual whole-row production and forcing.
Unweighted fluxes are not assumed globally L2. The actual ordinary
Poisson gradients pay all target and quadratic-forcing contractions. -/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualQuadraticProductionDomain405
open KLS ActualBoundedCanonicalSource ActualQuadraticGramProduction405 ActualQuadraticHessianFactorDomain405
open ActualQuadraticResponseField405 ActualQuadraticHilbertMatrix405 ActualQuadraticRowCurvature405
open ActualQuadraticRowEquation405 ActualSourceNaturalTargetCurvatureDomain405 ActualSourceCurvatureDomains405
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem quadratic_gradient_flux_pair (H B : Matrix (Fin n) (Fin n) ℝ) (X u : Fin n → ℝ)
    (hH : H.IsSymm) :
    (∑ a, (∑ b, ∑ c, (B b c / 2) * (H a b * X c + X b * H a c)) * u a) =
      ∑ b, ∑ c, (B b c / 2) * ((H *ᵥ u) b * X c + X b * (H *ᵥ u) c) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ b, ∑ c, ∑ a, ((B b c / 2) * (H a b * X c + X b * H a c)) * u a :=
      Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by
        rw [hH.apply a b, hH.apply a c]
        ring

theorem actual_quadratic_times_hessian_memLp (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i a : Fin n) :
    MemLp (fun x => (actualQuadraticFluxMatrix d T x * coordinateHessian d.potential x) i a)
      2 (potentialMeasure d.potential) := by
  apply (memLp_congr_ae ?_).mp (naturalCanonicalRawGradient_memLp d (quadraticSourceDatum d (T i)) a)
  filter_upwards [d.hessian_ae_source, hessian_mul_naturalCanonicalFlux_ae d (quadraticSourceDatum d (T i))] with x hx hp
  symm
  have he := congrFun hp a
  change (∑ b, quadraticRowFlux d T i b x * coordinateHessian d.potential x b a) = _
  rw [← he]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun b _ => by
    rw [hx.1.isHermitian.isSymm.apply a b]
    unfold quadraticRowFlux
    ring

theorem actual_quadratic_target_entry_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Integrable (fun x => (actualQuadraticFluxMatrix d T x * sourceTargetCurvature d x *
      (actualQuadraticFluxMatrix d T x).transpose) i j) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hV2 : ContDiff ℝ 2 d.targetPotential := d.target_smooth.of_le (by simp)
  have hV (a b : Fin n) : MemLp
      (fun x => coordinateHessian d.targetPotential (gradient d.potential x) a b) ∞
      (potentialMeasure d.potential) := d.continuous_comp_gradient_memLp
        (contDiff_coordinateHessian hV2 (m := 0) (by norm_num) a b).continuous ∞
  have hfirst (a b : Fin n) : MemLp (fun x => ((actualQuadraticFluxMatrix d T x *
      coordinateHessian d.potential x) * coordinateHessian d.targetPotential (gradient d.potential x)) a b)
      2 (potentialMeasure d.potential) := memLp_matrix_mul_entries (p := 2) (q := ∞) (r := 2)
        (actual_quadratic_times_hessian_memLp d T) hV a b
  have hlast (a b : Fin n) : MemLp (fun x => (actualQuadraticFluxMatrix d T x *
      coordinateHessian d.potential x).transpose a b) 2 (potentialMeasure d.potential) :=
    actual_quadratic_times_hessian_memLp d T b a
  have hm : MemLp (fun x => ((actualQuadraticFluxMatrix d T x * coordinateHessian d.potential x) *
      coordinateHessian d.targetPotential (gradient d.potential x) *
        (actualQuadraticFluxMatrix d T x * coordinateHessian d.potential x).transpose) i j)
      1 (potentialMeasure d.potential) := memLp_matrix_mul_entries (p := 2) (q := 2) (r := 1) hfirst hlast i j
  apply (hm.integrable le_rfl).congr
  filter_upwards [d.hessian_ae_source] with x hx
  simp only [sourceTargetCurvature, Matrix.transpose_mul, hx.1.isHermitian.isSymm.eq, Matrix.mul_assoc]

theorem actual_quadratic_raw_forcing_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Integrable (actualQuadraticRawForcing d T i j) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let p (i a : Fin n) := naturalCanonicalRawGradient d (quadraticSourceDatum d (T i)) a
  let q (i j : Fin n) : Space n → ℝ := fun x => ∑ b, ∑ c, (T i b c / 2) *
    (p j b x * gradient d.potential x c + gradient d.potential x b * p j c x)
  have hp (i a : Fin n) : MemLp (p i a) 2 (potentialMeasure d.potential) := naturalCanonicalRawGradient_memLp d _ a
  have hX (a : Fin n) : MemLp (fun x => gradient d.potential x a) ∞ (potentialMeasure d.potential) :=
    d.continuous_comp_gradient_memLp (EuclideanSpace.proj a).continuous ∞
  have hq (i j : Fin n) : Integrable (q i j) (potentialMeasure d.potential) := by
    apply integrable_finsetSum Finset.univ
    intro b _
    apply integrable_finsetSum Finset.univ
    intro c _
    have hm : MemLp (fun x => p j b x * gradient d.potential x c + gradient d.potential x b * p j c x)
        2 (potentialMeasure d.potential) := ((hp j b).mul (hX c)).add ((hX b).mul (hp j c))
    exact (hm.integrable (by norm_num)).const_mul _
  apply ((hq i j).add (hq j i)).congr
  filter_upwards [d.hessian_ae_source, ae_all_iff.mpr (fun b => hessian_mul_naturalCanonicalFlux_ae d (quadraticSourceDatum d (T b)))] with x hx hgrad
  have he (a b : Fin n) : (q a b) x = ∑ r, quadraticDatumRawDerivative d (T a) r x * quadraticRowFlux d T b r x := by
    symm
    change (∑ r, (∑ s, ∑ t, (T a s t / 2) * (coordinateHessian d.potential x r s * gradient d.potential x t +
      gradient d.potential x s * coordinateHessian d.potential x r t)) * quadraticRowFlux d T b r x) = _
    rw [quadratic_gradient_flux_pair _ _ _ _ hx.1.isHermitian.isSymm]
    have hgb : coordinateHessian d.potential x *ᵥ (fun r => quadraticRowFlux d T b r x) =
        (fun r => p b r x) := hgrad b
    rw [hgb]
  change q i j x + q j i x = _
  rw [he i j, he j i]
  simp only [actualQuadraticRawForcing, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem actualQuadraticProduction_entry_integrable (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i j : Fin n) : Integrable (fun x => actualQuadraticProduction d hn hμ T x i j) (potentialMeasure d.potential) :=
  ((actual_quadratic_target_entry_integrable d T i j).add
    (actual_quadratic_hessian_gram_entry_integrable d hn hμ T hC hM i j)).add
      (actual_quadratic_jacobian_gram_entry_integrable d hn hμ T i j)

theorem actualQuadraticProductionRHS_integrable (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i j : Fin n) : Integrable (actualQuadraticProductionRHS d hn hμ T i j) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  exact ((actual_quadratic_raw_forcing_integrable d T i j).sub
    ((actualQuadraticGram_top_of_mass_bound d T hM i j).integrable (by simp))).sub
      (actualQuadraticProduction_entry_integrable d hn hμ T hC hM i j)

end KLSConstantImprovement.ActualQuadraticProductionDomain405

#print axioms KLSConstantImprovement.ActualQuadraticProductionDomain405.actual_quadratic_raw_forcing_integrable
#print axioms KLSConstantImprovement.ActualQuadraticProductionDomain405.actualQuadraticProduction_entry_integrable
#print axioms KLSConstantImprovement.ActualQuadraticProductionDomain405.actualQuadraticProductionRHS_integrable
