import KLSConstantImprovement.ActualStrongTargetExhaustion405
import KLSConstantImprovement.ActualCenteredSourceTransport405
import KLSConstantImprovement.ActualC11SourceCompactness405
import KLSConstantImprovement.ActualMomentMapLimit405
import KLSConstantImprovement.ActualWhitenedCutoffConfinement405

/-! A genuine C1,1 moment source for a smooth strongly convex full-support
isotropic law, constructed by actual bounded-target exhaustion. Probability,
gradient pushforward and properness are proved. This is deliberately NOT the
bounded-target SourceData package: no limiting MA/weak-third/natural-domain
upgrade is asserted by this theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Metric
open scoped Topology NNReal ContDiff
namespace KLSConstantImprovement.ActualFullSupportC11MomentSource405
open KLS ActualBoundedCanonicalSource ActualStrongTargetExhaustion405
open ActualSourceCentering405 ActualCenteredSourceTransport405 ActualC11SourceCompactness405
open ActualMomentMapLimit405 ActualDualCapCoercivity405 ActualSuperlinearGradientProper405
open ActualWhitenedCutoffConfinement405 ActualTargetWeakApproximation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_fullsupport_C11_moment_source (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    {κ : ℝ} (hκ : 0 < κ) (hsV : StrongConvexOn univ κ V)
    (heq : μ = potentialMeasure V) :
    ∃ φ : Space n → ℝ,
      ContDiff ℝ 1 φ ∧ ConvexOn ℝ univ φ ∧
      LipschitzWith (⟨16 / (κ / 9), div_nonneg (by norm_num) (div_pos hκ (by norm_num)).le⟩ : ℝ≥0)
        (gradient φ) ∧
      IsProbabilityMeasure (potentialMeasure φ) ∧
      (potentialMeasure φ).map (gradient φ) = μ ∧
      ∀ E : Set (Space n), IsCompact E → IsCompact ((gradient φ) ⁻¹' E) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨R, hR, hm, _⟩ := hμ.exists_whitened_compact_cutoffs
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_exists_sourceData_uniform_convexity hμ hV hκ hsV heq hR hm)
  choose d hd using fun k : ℕ => hN (N + k) (Nat.le_add_right N k)
  let f : ℕ → Space n → ℝ := fun k => centeredSourcePotential (d k)
  let L : ℝ≥0 := ⟨16 / (κ / 9), div_nonneg (by norm_num) (div_pos hκ (by norm_num)).le⟩
  have hL (k : ℕ) : LipschitzWith L (gradient (f k)) := by
    apply (centeredSourcePotential_gradient_lipschitz (d k)).weaken
    change 16 / (d k).targetConvexityConstant ≤ 16 / (κ / 9)
    exact div_le_div_of_nonneg_left (by norm_num) (div_pos hκ (by norm_num)) (hd k)
  obtain ⟨ψ, s, hs, hψ, hcψ, hψ0, hgψ0, hgψ, hflim, hglim⟩ :=
    exists_subseq_centered_C11_potentials L f
      (fun k => centeredSourcePotential_C1 (d k))
      (fun k => centeredSourcePotential_convex (d k))
      (fun k => centeredSourcePotential_zero (d k))
      (fun k => centeredSourcePotential_gradient_zero (d k)) hL
  let idx : ℕ → ℕ := fun k => N + s k
  have hidx : StrictMono idx := fun i j hij => Nat.add_lt_add_left (hs hij) N
  let ρ : ℕ → Measure (Space n) := fun k => whitenedBallCutoffMeasure μ R (idx k)
  letI : ∀ k, IsProbabilityMeasure (ballCutoffMeasure μ R (idx k)) :=
    fun k => isProbabilityMeasure_ballCutoffMeasure hm (idx k)
  letI : ∀ k, IsProbabilityMeasure (ρ k) := fun k =>
    inferInstanceAs (IsProbabilityMeasure (whitenedMeasure (ballCutoffMeasure μ R (idx k))))
  have hE (k : ℕ) : momentDualEnergy (ρ k) (f (s k)) ≤ ENNReal.ofReal n :=
    centeredSourcePotential_dualEnergy (d (s k))
  have hweak (v : BoundedContinuousFunction (Space n) ℝ) :
      Tendsto (fun k => ∫ y, v y ∂ρ k) atTop (𝓝 (∫ y, v y ∂μ)) :=
    (tendsto_integral_bounded_whitened_cutoff hμ hm v.continuous v.norm_coe_le_norm).comp hidx.tendsto_atTop
  have hcompact (v : Space n → ℝ) (hv : Continuous v) (hvc : HasCompactSupport v) :
      Tendsto (fun k => ∫ y, v y ∂ρ k) atTop (𝓝 (∫ y, v y ∂μ)) :=
    (hμ.tendsto_integral_whitenedBallCutoffMeasure_compact hm hv hvc).comp hidx.tendsto_atTop
  have hcones : ∀ a : ℝ, 0 ≤ a → ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ k in atTop, ∀ x, a * ‖x‖ - B ≤ f (s k) x := by
    intro a ha
    exact uniform_cones_of_fullsupport_target_limit hn (by positivity : 0 ≤ (n : ℝ)) hE
      (potential_density_ball_positive hV.continuous heq) hcompact ha
  have hψcones := cones_of_eventual_cones hcones hflim
  obtain ⟨B, hB, hcone⟩ := hcones 1 (by norm_num)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hcone
  let F : ℕ → Space n → ℝ := fun k => f (s (K + k))
  let ρF : ℕ → Measure (Space n) := fun k => ρ (K + k)
  have ht : StrictMono (fun k : ℕ => K + k) := fun i j hij => Nat.add_lt_add_left hij K
  have hFc (k : ℕ) (x : Space n) : (1 : ℝ) * ‖x‖ - B ≤ F k x :=
    hK (K + k) (Nat.le_add_right K k) x
  have hFp (x : Space n) : Tendsto (fun k => F k x) atTop (𝓝 (ψ x)) :=
    (hflim x).comp ht.tendsto_atTop
  have hGp (x : Space n) : Tendsto (fun k => gradient (F k) x) atTop (𝓝 (gradient ψ x)) :=
    (hglim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ x)).comp ht.tendsto_atTop
  have hmap (k : ℕ) : (potentialMeasure (normalizedMomentPotential (F k))).map
      (gradient (normalizedMomentPotential (F k))) = ρF k :=
    centeredSourcePotential_pushforward (d (s (K + k)))
  have htarget := gradient_pushforward_normalized_limit
    (fun k => centeredSourcePotential_C1 (d (s (K + k)))) hψ
    (by norm_num : (0 : ℝ) < 1) hFc hFp hGp hmap
    (fun v => (hweak v).comp ht.tendsto_atTop)
  have hiψ := integrable_exp_neg_of_linear_coercivity hψ.continuous.aestronglyMeasurable
    (by norm_num : (0 : ℝ) < 1) (limit_linear_cone hFc hFp)
  have hnorm : ContDiff ℝ 1 (normalizedMomentPotential ψ) := by
    unfold normalizedMomentPotential
    exact hψ.add contDiff_const
  have hconv : ConvexOn ℝ univ (normalizedMomentPotential ψ) := by
    change ConvexOn ℝ univ (fun x => ψ x + Real.log (momentPartitionFunction ψ))
    exact hcψ.add_const _
  refine ⟨normalizedMomentPotential ψ, hnorm, hconv, ?_,
    isProbabilityMeasure_normalizedMomentPotential hiψ, htarget, ?_⟩
  · rw [gradient_normalizedMomentPotential]
    exact hgψ
  · intro E hEcomp
    rw [gradient_normalizedMomentPotential]
    exact gradient_preimage_compact hψ hcψ hψcones hEcomp

end KLSConstantImprovement.ActualFullSupportC11MomentSource405
#print axioms KLSConstantImprovement.ActualFullSupportC11MomentSource405.exists_fullsupport_C11_moment_source
