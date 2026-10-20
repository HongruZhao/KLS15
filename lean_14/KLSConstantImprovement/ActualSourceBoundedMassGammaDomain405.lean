import KLSConstantImprovement.ActualSourceCompactConnectionAbsorption405
import KLSConstantImprovement.ActualUniformIntegralFatou405
import KLS.RawTraceEnergyPassage

/-! Positive Fatou pays the global actual Gamma(u,u) domain under an
explicit bounded natural mass. No connection integrability is assumed,
and every cutoff error comes from the actual conservative metric cutoffs. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualSourceBoundedMassGammaDomain405
open KLS ActualBoundedCanonicalSource ActualSourceConnectionFields405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceBoundedMassCutoffs405
open ActualSourceCompactConnectionDomains405 ActualSourceCompactConnectionAbsorption405
open ActualUniformIntegralFatou405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem integral_cutoff_square_tendsto {ν : Measure (Space n)}
    {χ : ℕ → Space n → ℝ} (hχ : ∀ k, Continuous (χ k))
    (hb : ∀ k x, χ k x ∈ Icc (0 : ℝ) 1)
    (hlim : ∀ x, Tendsto (fun k => χ k x) atTop (𝓝 1))
    {f : Space n → ℝ} (hf : Integrable f ν) :
    (∀ k, Integrable (fun x => χ k x ^ 2 * f x) ν) ∧
      Tendsto (fun k => ∫ x, χ k x ^ 2 * f x ∂ν) atTop (𝓝 (∫ x, f x ∂ν)) := by
  apply integral_mul_tendsto_of_ae_bounded_cutoffs hf (fun k => ((hχ k).pow 2).aestronglyMeasurable)
  · intro k
    exact Eventually.of_forall fun x => by
      change ‖χ k x ^ 2‖ ≤ 1
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      obtain ⟨hlo, hhi⟩ := hb k x
      nlinarith
  · exact Eventually.of_forall fun x => by
      change Tendsto (fun k => χ k x ^ 2) atTop (𝓝 1)
      simpa only [one_pow] using (hlim x).pow 2

theorem integral_cutoff_square_le {ν : Measure (Space n)} {χ f : Space n → ℝ}
    (hχ : Continuous χ) (hb : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hf : Integrable f ν) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x) :
    (∫ x, χ x ^ 2 * f x ∂ν) ≤ ∫ x, f x ∂ν := by
  have hn : ∀ᵐ x ∂ν, ‖χ x ^ 2‖ ≤ 1 := Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    obtain ⟨hlo, hhi⟩ := hb x
    nlinarith
  have hi : Integrable (fun x => χ x ^ 2 * f x) ν := hf.bdd_mul (hχ.pow 2).aestronglyMeasurable hn
  apply integral_mono_ae hi hf
  filter_upwards [hpos] with x hx
  have hc : χ x ^ 2 ≤ 1 := by obtain ⟨hlo, hhi⟩ := hb x; nlinarith
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hx

theorem actual_Gamma_integrable_of_bounded_natural_mass (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x)).IsSymm)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (hQi : Integrable (sourceVectorJacobianEnergy Du) (potentialMeasure d.potential)) :
    Integrable (sourceConnectionGamma d (naturalCanonicalFlux d g)) (potentialMeasure d.potential) ∧
      (∫ x, sourceConnectionGamma d (naturalCanonicalFlux d g) x ∂potentialMeasure d.potential) ≤
        2 * (∫ x, sourceVectorMass d.potential (naturalCanonicalFlux d g) x ∂potentialMeasure d.potential) +
        8 * (∫ x, sourceVectorJacobianEnergy Du x ∂potentialMeasure d.potential) := by
  let u := naturalCanonicalFlux d g
  let ν := potentialMeasure d.potential
  obtain ⟨χ, hχ, hlim, hEi, hElim⟩ := exists_actual_mass_weighted_energy_cutoffs d g hC hM
  have hMn : ∀ᵐ x ∂ν, 0 ≤ sourceVectorMass d.potential u x := sourceVectorMass_nonnegative_ae d u
  have hQn : ∀ᵐ x ∂ν, 0 ≤ sourceVectorJacobianEnergy Du x :=
    sourceVectorJacobianEnergy_nonnegative_ae d Du hcomp
  have hGn : ∀ᵐ x ∂ν, 0 ≤ sourceConnectionGamma d u x := sourceConnectionGamma_nonnegative_ae d u
  have hGi (k : ℕ) : Integrable (fun x => χ k x ^ 2 * sourceConnectionGamma d u x) ν :=
    (compact_connection_fields_integrable d g hC hM Du hu hDu hw (hχ k).1 (hχ k).2.1).2.2.2.2
  have hGlim (x : Space n) : Tendsto (fun k => χ k x ^ 2 * sourceConnectionGamma d u x) atTop
      (𝓝 (sourceConnectionGamma d u x)) := by
    simpa only [one_pow, one_mul] using ((hlim x).pow 2).mul_const (sourceConnectionGamma d u x)
  have hGm : AEStronglyMeasurable (sourceConnectionGamma d u) ν :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hGi k).aestronglyMeasurable)
      (Eventually.of_forall hGlim)
  have hMle (k : ℕ) : (∫ x, χ k x ^ 2 * sourceVectorMass d.potential u x ∂ν) ≤
      ∫ x, sourceVectorMass d.potential u x ∂ν :=
    integral_cutoff_square_le (hχ k).1.continuous (hχ k).2.2 hMi hMn
  have hQle (k : ℕ) : (∫ x, χ k x ^ 2 * sourceVectorJacobianEnergy Du x ∂ν) ≤
      ∫ x, sourceVectorJacobianEnergy Du x ∂ν :=
    integral_cutoff_square_le (hχ k).1.continuous (hχ k).2.2 hQi hQn
  have hAbs (k : ℕ) : (∫ x, χ k x ^ 2 * sourceConnectionGamma d u x ∂ν) ≤
      2 * (∫ x, χ k x ^ 2 * sourceVectorMass d.potential u x ∂ν) +
      8 * (∫ x, χ k x ^ 2 * sourceVectorJacobianEnergy Du x ∂ν) +
      8 * (∫ x, sourceVectorMass d.potential u x * inverseHessianGradientForm d.potential (χ k) x ∂ν) :=
    integral_actual_compact_connection_absorption d g hC hM Du hu hDu hw hcomp hMi hQi (hχ k).1 (hχ k).2.1
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hElim.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  let B : ℝ := 2 * (∫ x, sourceVectorMass d.potential u x ∂ν) +
    8 * (∫ x, sourceVectorJacobianEnergy Du x ∂ν) + 8
  have hB : 0 ≤ B := by
    have hm := integral_nonneg_of_ae hMn
    have hq := integral_nonneg_of_ae hQn
    dsimp only [B]
    linarith
  have hbound (k : ℕ) : (∫ x, ‖χ (k + N) x ^ 2 * sourceConnectionGamma d u x‖ ∂ν) ≤ B := by
    have he : (∫ x, ‖χ (k + N) x ^ 2 * sourceConnectionGamma d u x‖ ∂ν) =
        ∫ x, χ (k + N) x ^ 2 * sourceConnectionGamma d u x ∂ν := by
      apply integral_congr_ae
      filter_upwards [hGn] with x hx
      exact Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hx)
    rw [he]
    have hn := hN (k + N) (Nat.le_add_left N k)
    have ha := hAbs (k + N)
    have hm := hMle (k + N)
    have hq := hQle (k + N)
    dsimp only [B]
    linarith
  obtain ⟨hGlobal, _⟩ := integrable_and_integral_norm_le_of_tendsto_uniform_bound hGm
    (fun k => hGi (k + N)) (Eventually.of_forall fun x =>
      (hGlim x).comp (tendsto_add_atTop_nat N)) hB hbound
  have hGconv := (integral_cutoff_square_tendsto (fun k => (hχ k).1.continuous)
    (fun k => (hχ k).2.2) hlim hGlobal).2
  have hMconv := (integral_cutoff_square_tendsto (fun k => (hχ k).1.continuous)
    (fun k => (hχ k).2.2) hlim hMi).2
  have hQconv := (integral_cutoff_square_tendsto (fun k => (hχ k).1.continuous)
    (fun k => (hχ k).2.2) hlim hQi).2
  have hright := ((hMconv.const_mul 2).add (hQconv.const_mul 8)).add (hElim.const_mul 8)
  have hright' : Tendsto (fun k =>
      2 * (∫ x, χ k x ^ 2 * sourceVectorMass d.potential u x ∂ν) +
      8 * (∫ x, χ k x ^ 2 * sourceVectorJacobianEnergy Du x ∂ν) +
      8 * (∫ x, sourceVectorMass d.potential u x * inverseHessianGradientForm d.potential (χ k) x ∂ν))
      atTop (𝓝 (2 * (∫ x, sourceVectorMass d.potential u x ∂ν) +
        8 * (∫ x, sourceVectorJacobianEnergy Du x ∂ν))) := by
    simpa only [mul_zero, add_zero] using hright
  exact ⟨hGlobal, le_of_tendsto_of_tendsto hGconv hright' (Eventually.of_forall hAbs)⟩

/-- Only the explicit mass bound is additional here: the actual natural
inverse supplies its local weak Jacobian, compatibility and global energy. -/
theorem natural_Gamma_integrable_of_mass_bound (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C) :
    Integrable (sourceConnectionGamma d (naturalCanonicalFlux d g)) (potentialMeasure d.potential) := by
  obtain ⟨Du, hu, hDu, hw, hcomp, hMi, hQi, _, _⟩ := exists_naturalCanonicalFlux_gaffney d hn g hg
  exact (actual_Gamma_integrable_of_bounded_natural_mass d g hC hM Du hu hDu hw hcomp hMi hQi).1

end KLSConstantImprovement.ActualSourceBoundedMassGammaDomain405
#print axioms KLSConstantImprovement.ActualSourceBoundedMassGammaDomain405.integral_cutoff_square_tendsto
#print axioms KLSConstantImprovement.ActualSourceBoundedMassGammaDomain405.integral_cutoff_square_le
#print axioms KLSConstantImprovement.ActualSourceBoundedMassGammaDomain405.actual_Gamma_integrable_of_bounded_natural_mass
#print axioms KLSConstantImprovement.ActualSourceBoundedMassGammaDomain405.natural_Gamma_integrable_of_mass_bound
