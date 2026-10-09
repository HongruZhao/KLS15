import WeakMomentMapTwoSlot

/-! The full actual-law two-slot third-cumulant estimate. The weak moment
map is constructed for the bounded strongly convex approximants. Every
passage to the original class uses actual finite third-moment convergence. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Set Filter Metric
open scoped ContDiff BigOperators ENNReal NNReal Topology Matrix.Norms.Elementwise
namespace KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def ThirdCumulantTwoSlotFour (μ : Measure (Space n)) : Prop :=
  ∀ H : Matrix (Fin n) (Fin n) ℝ, H.IsSymm →
    (∑ k, (H*thirdCumulantMatrix μ (MomentMap.coordinateVector k)*
      H*thirdCumulantMatrix μ (MomentMap.coordinateVector k)).trace) ≤ 4*matrixFrobeniusSq H

theorem thirdCumulantMatrix_coordinate_eq_cubic (μ : Measure (Space n)) (i j k : Fin n) :
    thirdCumulantMatrix μ (MomentMap.coordinateVector k) i j =
      ∫ x, x i*x j*x k ∂μ := by
  unfold thirdCumulantMatrix
  apply integral_congr_ae
  exact .of_forall fun x => by
    simp only [MomentMap.coordinateVector,EuclideanSpace.inner_single_right,RCLike.conj_to_real]
    ring

theorem twoSlotFour_of_thirdMomentLimit {μ : Measure (Space n)}
    {ν : ℕ → Measure (Space n)}
    (hlim : ∀ i j k : Fin n,
      Tendsto (fun m => ∫ x, x i*x j*x k ∂ν m) atTop (𝓝 (∫ x, x i*x j*x k ∂μ)))
    (hbound : ∀ᶠ m in atTop, ThirdCumulantTwoSlotFour (ν m)) :
    ThirdCumulantTwoSlotFour μ := by
  intro H hH
  have hmat : Tendsto
      (fun m k => thirdCumulantMatrix (ν m) (MomentMap.coordinateVector k))
      atTop (𝓝 (fun k => thirdCumulantMatrix μ (MomentMap.coordinateVector k))) := by
    apply tendsto_pi_nhds.mpr
    intro k
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [thirdCumulantMatrix_coordinate_eq_cubic] using hlim i j k
  have hcont : Continuous (fun S : Fin n → Matrix (Fin n) (Fin n) ℝ =>
      ∑ k, (H*S k*H*S k).trace) := by fun_prop
  apply le_of_tendsto ((hcont.tendsto _).comp hmat)
  filter_upwards [hbound] with m hm
  exact hm H hH

theorem twoSlotFour_of_actual_strongDensity
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (hreg : HasSmoothBoundedStronglyConvexDensity μ) : ThirdCumulantTwoSlotFour μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨K,V,κ,hKo,hKc,hKb,_hn,hV,hκ,hstrong,htarget⟩ := hreg
  obtain ⟨R,hR,hbound⟩ := hKb.exists_pos_norm_le
  let L : ℝ≥0 := ⟨R,hR.le⟩
  have hbounded : ∀ᵐ y ∂μ, ‖y‖ ≤ L := by
    rw [htarget]
    exact (ae_restrict_mem hKo.measurableSet).mono fun y hy => hbound y hy
  obtain ⟨u,hLip,hc,hprob,hmap⟩ := hμ.isotropic.exists_bounded_momentMap L hbounded
  let : IsProbabilityMeasure (potentialMeasure u) := hprob
  have hpush : MomentMap.gradientPushforward u = μ := hmap
  have hclosedTarget : μ = (potentialMeasure V).restrict (closure K) :=
    htarget.trans (potentialMeasure_restrict_closure_of_convex V hKc).symm
  have hVc := convexOn_of_strongConvexOn_nonneg hκ.le hstrong
  rw [strongConvexOn_iff_convex] at hstrong
  have hiso : IsIsotropic (MomentMap.gradientPushforward u) := by
    simpa only [hpush] using hμ.isotropic
  intro H hH
  simpa only [hpush] using thirdCumulant_two_slot_bound_weak_uniform_momentMap
    hLip hc (hV.of_le (by simp)) hVc hκ hstrong isClosed_closure hKc.closure
    (hpush.trans hclosedTarget) hiso H hH

theorem twoSlotFour_of_regular
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (hreg : HasSmoothBoundedConvexDensity μ) : ThirdCumulantTwoSlotFour μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  let ν := fun m => quadraticDamping μ (cutoffScale m)
  let : ∀ m, IsProbabilityMeasure (ν m) :=
    fun m => isProbabilityMeasure_quadraticDamping hreg.isCompact_support _
  have hν : ∀ m, measureLogConcave (ν m) :=
    fun m => hreg.quadraticDamping_logConcave (cutoffScale_pos m).le
  have hlim (f : Space n → ℝ) (hf : Continuous f) :
      Tendsto (fun m => ∫ x, f x ∂ν m) atTop (𝓝 (∫ x, f x ∂μ)) :=
    (tendsto_integral_quadraticDamping hreg.isCompact_support
      (integrable_of_continuous_compact_support_measure hreg.isCompact_support hf)).comp
        cutoffScale_tendsto_zero
  apply twoSlotFour_of_thirdMomentLimit (ν := fun m => whitenedMeasure (ν m))
  · intro i j k
    simpa [Fin.prod_univ_succ,mul_assoc] using
      tendsto_coordinate_moment_whitenedMeasure_of_continuous_moments hμ hν hlim ![i,j,k]
  · filter_upwards [hμ.eventually_strongDensity_whitened_quadraticDamping hreg] with m hm
    exact twoSlotFour_of_actual_strongDensity hm.1 hm.2

theorem twoSlotFour_of_smooth
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hc : ConvexOn ℝ univ V) (heq : μ = potentialMeasure V) : ThirdCumulantTwoSlotFour μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨R,hR,hm,ha⟩ := hμ.exists_whitened_compact_cutoffs
  apply twoSlotFour_of_thirdMomentLimit (ν := fun m => whitenedBallCutoffMeasure μ R m)
  · intro i j k
    simpa [Fin.prod_univ_succ,mul_assoc] using
      hμ.tendsto_coordinate_moment_whitenedBallCutoffMeasure hm ![i,j,k]
  · filter_upwards [ha,hμ.eventually_smoothBoundedDensity_whitenedBallCutoff hV hc heq hR hm]
      with m ham hrm
    exact twoSlotFour_of_regular ham.1 hrm

theorem twoSlotFour_of_compact
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (hcompact : IsCompact μ.support) : ThirdCumulantTwoSlotFour μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  apply twoSlotFour_of_thirdMomentLimit
    (ν := fun m => KLS.isotropicGaussianSmoothing μ (cutoffScale m))
  · intro i j k
    simpa [Fin.prod_univ_succ,mul_assoc,Function.comp_def] using
      (hμ.tendsto_coordinate_moment_isotropicGaussianSmoothing ![i,j,k]).comp cutoffScale_tendsto_zero
  · apply Eventually.of_forall
    intro m
    have hr := (cutoffScale_pos m).ne'
    exact twoSlotFour_of_smooth (hμ.isotropicGaussianSmoothing hr)
      (isotropicGaussianPotential_contDiff hcompact hr)
      (hμ.isotropicGaussianPotential_convex hcompact hr)
      (hμ.isotropicGaussianSmoothing_eq_exp_potential hcompact hr)

/-- The genuine full original admissible class, with no moment-map,
Hessian, third-moment-bound, or approximation premises left over. -/
theorem thirdCumulant_two_slot_four_universal
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) : ThirdCumulantTwoSlotFour μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨R,_hR,hm,hevent⟩ := hμ.exists_whitened_compact_cutoffs
  apply twoSlotFour_of_thirdMomentLimit (ν := fun m => whitenedBallCutoffMeasure μ R m)
  · intro i j k
    simpa [Fin.prod_univ_succ,mul_assoc] using
      hμ.tendsto_coordinate_moment_whitenedBallCutoffMeasure hm ![i,j,k]
  · filter_upwards [hevent] with m hm
    exact twoSlotFour_of_compact hm.1 hm.2

#print axioms twoSlotFour_of_actual_strongDensity
#print axioms twoSlotFour_of_thirdMomentLimit
#print axioms thirdCumulant_two_slot_four_universal
end KLS.DeterministicBridgeIntegration
