import KLSConstantImprovement.ActualDensityFluxPair405
import KLSConstantImprovement.ActualDensityWeakDerivativeLimit405
import KLSConstantImprovement.ActualSourceLimitFluxPairing405

/-! The actual compact Poisson equation passes from the genuine source
family to its original-law weak inverse limit.  The final inverse is
identified by the existing maximal raw form theorem; no scalar mean limit
or stronger operator core is needed. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
namespace KLSConstantImprovement.ActualDensityPoissonLimit405
open KLS ActualBoundedCanonicalSource ActualDensityWeightedL2405 ActualDensityInverseWeakCompactness405
open ActualDensityLimitInverseIdentification405 ActualDensityFluxPair405 ActualDensityWeakDerivativeLimit405
open ActualDensityGradientCoefficient405 ActualCenteredFamilyPotentialBound405
open ActualSourceNaturalGaffney405 ActualSourceRegularizedEnergyVector405
open ActualSourceLimitFluxDomains405 ActualSourceLimitMetricRelations405 ActualSourceLimitFluxPairing405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricInverse
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem energyLimitFlux_compact_product_integrable (d : SourceData μ) (V : GaffneyEnergyAmbient d)
    {ψ : Space n → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    Integrable (fun x => energyLimitFlux d V i x * ψ x) (potentialMeasure d.potential) := by
  have hi (a : Fin n) : Integrable (fun x => V (Sum.inl a) x *
      (canonicalMetricRoot d.potential x i a * ψ x)) (potentialMeasure d.potential) :=
    (Lp.memLp _).integrable_mul (actual_root_mul_compact_memLp d hψ hc i a)
  have hs := integrable_finsetSum Finset.univ fun a _ => hi a
  convert hs using 1
  funext x
  simp only [energyLimitFlux, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem energyLimit_raw_pair_eq_flux_sum (d : SourceData μ) (V : GaffneyEnergyAmbient d)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, ∑ a : Fin n, ∑ b : Fin n, (coordinateHessian d.potential x)⁻¹ a b *
      energyLimitScalarGradient d V a x * coordinateDerivative ψ b x ∂potentialMeasure d.potential) =
      ∑ b : Fin n, ∫ x, energyLimitFlux d V b x * coordinateDerivative ψ b x ∂potentialMeasure d.potential := by
  have he : (fun x => ∑ a : Fin n, ∑ b : Fin n, (coordinateHessian d.potential x)⁻¹ a b *
      energyLimitScalarGradient d V a x * coordinateDerivative ψ b x) =ᵐ[potentialMeasure d.potential]
      fun x => ∑ b : Fin n, energyLimitFlux d V b x * coordinateDerivative ψ b x := by
    filter_upwards [d.hessian_ae_source, ae_all_iff.mpr
      (fun i => energyLimitFlux_eq_inverseGradient_ae d V i)] with x hx hf
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    calc
      _ = (∑ a : Fin n, (coordinateHessian d.potential x)⁻¹ b a *
          energyLimitScalarGradient d V a x) * coordinateDerivative ψ b x := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [hx.1.inv.isHermitian.isSymm.apply a b]
      _ = _ := by rw [hf b]
  rw [integral_congr_ae he]
  exact integral_finsetSum _ fun b _ => energyLimitFlux_compact_product_integrable d V
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) b).continuous
    (hasCompactSupport_coordinateDerivative hc b) b

theorem actual_density_limit_raw_poisson_equation
    {ν : ℕ → Measure (Space n)} (d : ∀ k, SourceData (ν k)) (d₀ : SourceData μ) (hn : 1 ≤ n)
    (g : ∀ k, Lp ℝ 2 (potentialMeasure (d k).potential))
    (hg : ∀ k, (∫ x, g k x ∂potentialMeasure (d k).potential) = 0)
    (g₀ : Lp ℝ 2 (potentialMeasure d₀.potential))
    (W : DensityInverseAmbient n) {C κ L : ℝ}
    (hκ : 0 < κ) (hk : ∀ k, κ ≤ (d k).targetConvexityConstant)
    (hV : ∀ k p, L ≤ (d k).targetPotential p)
    (hgrad0 : ∀ k, gradient (d k).potential 0 = 0)
    (hφ : ∀ x, Tendsto (fun k => (d k).potential x) atTop (𝓝 (d₀.potential x)))
    (hH : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto
      (fun k => coordinateHessian (d k).potential x) atTop (𝓝 (coordinateHessian d₀.potential x)))
    (hb : ∀ k, ‖actualDensityInverseField (d k) (g k)‖ ≤ C)
    (hw : ∀ Y : DensityInverseAmbient n,
      Tendsto (fun k => inner ℝ (actualDensityInverseField (d k) (g k)) Y)
        atTop (𝓝 (inner ℝ W Y)))
    (hrhs : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      Tendsto (fun k => ∫ x, g k x * ψ x ∂potentialMeasure (d k).potential) atTop
        (𝓝 (∫ x, g₀ x * ψ x ∂potentialMeasure d₀.potential))) :
    ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ x, ∑ a, ∑ b, (coordinateHessian d₀.potential x)⁻¹ a b *
        densityLimitRawGradient d₀ W a x * coordinateDerivative ψ b x ∂potentialMeasure d₀.potential) =
        ∫ x, g₀ x * ψ x ∂potentialMeasure d₀.potential := by
  intro ψ hψ hc
  obtain ⟨P, hP⟩ := actual_centered_family_compact_potential_upper
    d hκ hk hgrad0 (hφ 0) hc.isBounded
  obtain ⟨A, hA⟩ := actual_centered_family_global_potential_lower d hgrad0 (hφ 0)
  have hpair (b : Fin n) := actual_natural_flux_pair_tendsto d d₀ g W hκ hk hV hA hφ hH hb hw
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) b).continuous
    (hasCompactSupport_coordinateDerivative hc b)
    (fun k x hx => hP k x (tsupport_coordinateDerivative_subset ψ b hx)) b
  have hleft := tendsto_finsetSum Finset.univ fun b _ => hpair b
  have heq (k : ℕ) : (∑ b : Fin n, ∫ x, naturalCanonicalFlux (d k) (g k) b x *
      coordinateDerivative ψ b x ∂potentialMeasure (d k).potential) =
      ∫ x, g k x * ψ x ∂potentialMeasure (d k).potential := by
    obtain ⟨Du, _, _, _, _, _, _, _, he⟩ := exists_naturalCanonicalFlux_gaffney (d k) hn (g k) (hg k)
    exact he ψ hψ hc
  have hlim : (∑ b : Fin n, ∫ x, energyLimitFlux d₀ (densityLimitMetricBlock d₀ W) b x *
      coordinateDerivative ψ b x ∂potentialMeasure d₀.potential) =
      ∫ x, g₀ x * ψ x ∂potentialMeasure d₀.potential :=
    tendsto_nhds_unique hleft ((hrhs ψ hψ hc).congr fun k => (heq k).symm)
  exact (energyLimit_raw_pair_eq_flux_sum d₀ (densityLimitMetricBlock d₀ W)
    (hψ.of_le (by norm_num)) hc).trans hlim

theorem actual_density_limit_metric_gradient_identification
    {ν : ℕ → Measure (Space n)} (d : ∀ k, SourceData (ν k)) (d₀ : SourceData μ) (hn : 1 ≤ n)
    (g : ∀ k, Lp ℝ 2 (potentialMeasure (d k).potential))
    (hg : ∀ k, (∫ x, g k x ∂potentialMeasure (d k).potential) = 0)
    (g₀ : Lp ℝ 2 (potentialMeasure d₀.potential))
    (hg₀ : (∫ x, g₀ x ∂potentialMeasure d₀.potential) = 0)
    (W : DensityInverseAmbient n) {C κ L : ℝ}
    (hκ : 0 < κ) (hk : ∀ k, κ ≤ (d k).targetConvexityConstant)
    (hV : ∀ k p, L ≤ (d k).targetPotential p)
    (hgrad0 : ∀ k, gradient (d k).potential 0 = 0)
    (hφ : ∀ x, Tendsto (fun k => (d k).potential x) atTop (𝓝 (d₀.potential x)))
    (hH : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto
      (fun k => coordinateHessian (d k).potential x) atTop (𝓝 (coordinateHessian d₀.potential x)))
    (hb : ∀ k, ‖actualDensityInverseField (d k) (g k)‖ ≤ C)
    (hw : ∀ Y : DensityInverseAmbient n,
      Tendsto (fun k => inner ℝ (actualDensityInverseField (d k) (g k)) Y)
        atTop (𝓝 (inner ℝ W Y)))
    (hrhs : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      Tendsto (fun k => ∫ x, g k x * ψ x ∂potentialMeasure (d k).potential) atTop
        (𝓝 (∫ x, g₀ x * ψ x ∂potentialMeasure d₀.potential))) :
    ∀ i, (canonicalMetricGradient d₀.potential i (sourceMetricInverseH1 d₀ g₀) : Space n → ℝ)
      =ᵐ[potentialMeasure d₀.potential]
        (fromVolumeL2 d₀.source_C1.continuous (W i.succ) : Space n → ℝ) := by
  exact (density_limit_inverse_of_raw_equations d₀ g₀ hg₀ W
    (actual_density_limit_raw_weak_derivatives d d₀ g W hκ hk hgrad0 hφ hH hb hw)
    (actual_density_limit_raw_poisson_equation d d₀ hn g hg g₀ W hκ hk hV hgrad0 hφ hH hb hw hrhs)).2

end KLSConstantImprovement.ActualDensityPoissonLimit405
#print axioms KLSConstantImprovement.ActualDensityPoissonLimit405.energyLimitFlux_compact_product_integrable
#print axioms KLSConstantImprovement.ActualDensityPoissonLimit405.energyLimit_raw_pair_eq_flux_sum
#print axioms KLSConstantImprovement.ActualDensityPoissonLimit405.actual_density_limit_raw_poisson_equation
#print axioms KLSConstantImprovement.ActualDensityPoissonLimit405.actual_density_limit_metric_gradient_identification
