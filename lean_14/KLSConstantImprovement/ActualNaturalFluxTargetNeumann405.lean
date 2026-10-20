import KLSConstantImprovement.ActualNaturalFluxJacobianBoundary405
import KLSConstantImprovement.ActualNaturalFluxRowEquation405
import KLSConstantImprovement.ActualGlobalRawFormTest405
import KLSConstantImprovement.ActualSourceNaturalTargetCurvatureDomain405

/-! Genuine global target-row Neumann identities for the actual natural
inverse.  The same constructed Gaffney Jacobian is retained throughout.
Its compatible energy pays the spatial cutoff boundary; no bounded natural
mass, connection domain, or compact strong generator core is assumed. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualNaturalFluxTargetNeumann405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405
open ActualNaturalFluxJacobianBoundary405 ActualNaturalFluxRowEquation405
open ActualSourceRadialConnectionBoundary405 ActualSourceNaturalTargetCurvatureDomain405
open ActualSourcePullbackMetricGradient405 ActualGlobalRawFormTest405
open ActualPotentialWeakTests405 ActualBoundedRawTestAlgebra405
open ActualSourceLocalizedGaffney405 ActualSourceBoundedMassGammaDomain405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
variable {n : ℕ} {μ : Measure (Space n)}

theorem hessian_column_flux_eq_rawGradient_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (j : Fin n) :
    (fun x => ∑ i : Fin n, coordinateHessian d.potential x i j * naturalCanonicalFlux d g i x)
      =ᵐ[potentialMeasure d.potential] naturalCanonicalRawGradient d g j := by
  filter_upwards [d.hessian_ae_source, hessian_mul_naturalCanonicalFlux_ae d g] with x hx hu
  calc
    _ = (coordinateHessian d.potential x *ᵥ (fun i => naturalCanonicalFlux d g i x)) j := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      rw [hx.1.isHermitian.isSymm.apply j i]
    _ = _ := congrFun hu j

theorem natural_row_compact_rawH1_test (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i j) j)
    {Dg : Space n → ℝ} {j : Fin n}
    (hgw : HasLocalWeakCoordinateDerivative (g : Space n → ℝ) Dg j)
    (hDg : MemLp Dg 2 (potentialMeasure d.potential))
    {f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E))
    (hc : HasCompactSupport f) {B : ℝ} (hb : ∀ᵐ x ∂volume, ‖f x‖ ≤ B)
    (hF : ∀ a E, IsCompact E → MemLp (F a) 2 (volume.restrict E))
    (hFw : ∀ a, HasLocalWeakCoordinateDerivative f (F a) a) :
    (∀ i, Integrable (fun x => Du i j x * F i x) (potentialMeasure d.potential)) ∧
      Integrable (fun x => (Dg x - naturalCanonicalRawGradient d g j x) * f x)
        (potentialMeasure d.potential) ∧
      (∑ i : Fin n, ∫ x, Du i j x * F i x ∂potentialMeasure d.potential) =
        ∫ x, (Dg x - naturalCanonicalRawGradient d g j x) * f x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hp := naturalCanonicalRawGradient_memLp d g j
  have hDr : MemLp (fun x => Dg x - naturalCanonicalRawGradient d g j x) 2
      (potentialMeasure d.potential) := hDg.sub hp
  apply potential_divergence_bounded_compact_H1_test d
    (fun i E hE => hDu i j E hE)
    (fun E hE => KLS.MemLp.restrict_volume_of_potentialMeasure hDr d.source_C1.continuous hE)
    (fun ψ hψ hψc => ?_) hf hc hb hF hFw
  have he := natural_flux_differentiated_compact_equation d hn g hg Du hu hDu hw hgw
    (hψ.of_le (by norm_num)) hψc
  have hHi (i : Fin n) : Integrable (fun x => coordinateHessian d.potential x i j *
      naturalCanonicalFlux d g i x * ψ x) (potentialMeasure d.potential) :=
    integrable_raw_mul_compact_potential d.source_C1.continuous
      (locallyIntegrable_of_memLp_two_on_compacts fun E hE =>
        (KLS.MemLp.restrict_volume_of_potentialMeasure (d.hessian_entry_memLp i j ∞)
          d.source_C1.continuous hE).mul (hu i E hE)) hψ.continuous hψc
  have hψ2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hψ.continuous hψc
  have hDi : Integrable (fun x => Dg x * ψ x) (potentialMeasure d.potential) := hDg.integrable_mul hψ2
  have hpi : Integrable (fun x => naturalCanonicalRawGradient d g j x * ψ x)
      (potentialMeasure d.potential) := hp.integrable_mul hψ2
  have hmass : (∑ i : Fin n, ∫ x, coordinateHessian d.potential x i j * naturalCanonicalFlux d g i x * ψ x
      ∂potentialMeasure d.potential) =
      ∫ x, naturalCanonicalRawGradient d g j x * ψ x ∂potentialMeasure d.potential := by
    rw [← integral_finsetSum Finset.univ (fun i _ => hHi i)]
    apply integral_congr_ae
    filter_upwards [hessian_column_flux_eq_rawGradient_ae d g j] with x hx
    rw [← Finset.sum_mul, hx]
  have hsplit : (∫ x, (Dg x - naturalCanonicalRawGradient d g j x) * ψ x ∂potentialMeasure d.potential) =
      (∫ x, Dg x * ψ x ∂potentialMeasure d.potential) -
        ∫ x, naturalCanonicalRawGradient d g j x * ψ x ∂potentialMeasure d.potential := by
    rw [← integral_sub hDi hpi]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [hmass] at he
  rw [hsplit]
  linarith

theorem compatible_target_pullback_pair_ae (d : SourceData μ)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x)).IsSymm)
    (f : Space n → ℝ) (j : Fin n) :
    (fun x => ∑ i : Fin n, Du i j x * pullbackRawGradient d f i x)
      =ᵐ[potentialMeasure d.potential] fun x =>
        ∑ a : Fin n, compatibleTargetFlux d Du j a x * coordinateDerivative f a (gradient d.potential x) := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, hcomp.filter_mono hac.ae_le] with x hp hc
  let H := coordinateHessian d.potential x
  let B : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i k => Du i k x)
  let v := gradient f (gradient d.potential x)
  have hF : (fun i => pullbackRawGradient d f i x) = H *ᵥ (fun i => v i) := by
    funext i
    have he := inner_matrixAction_transpose H v (EuclideanSpace.single i 1)
    rw [hp.1.isHermitian.isSymm.eq] at he
    change inner ℝ v (matrixAction H (EuclideanSpace.single i 1)) = _
    rw [← he, EuclideanSpace.inner_single_right]
    simp [matrixAction_apply, Matrix.mulVec, dotProduct]
  have hBH : B.transpose * H = H * B := by
    have he := hc.eq
    simpa only [Matrix.transpose_mul, hp.1.isHermitian.isSymm.eq] using he
  have he : B.transpose *ᵥ (H *ᵥ (fun i => v i)) = (H * B) *ᵥ (fun i => v i) := by
    rw [Matrix.mulVec_mulVec, hBH]
  have he' := congrFun he j
  rw [← hF] at he'
  simpa only [B, H, v, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
    compatibleTargetFlux, coordinateDerivative_eq_gradient] using he'

theorem actual_global_target_row_equation (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i j) j)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x)).IsSymm)
    (hQi : Integrable (sourceVectorJacobianEnergy Du) (potentialMeasure d.potential))
    {Dg : Space n → ℝ} {j : Fin n}
    (hgw : HasLocalWeakCoordinateDerivative (g : Space n → ℝ) Dg j)
    (hDg : MemLp Dg 2 (potentialMeasure d.potential))
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) :
    (∫ x, ∑ a : Fin n, compatibleTargetFlux d Du j a x *
      coordinateDerivative f a (gradient d.potential x) ∂potentialMeasure d.potential) +
      (∫ x, naturalCanonicalRawGradient d g j x * f (gradient d.potential x) ∂potentialMeasure d.potential) =
      ∫ x, Dg x * f (gradient d.potential x) ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let ν := potentialMeasure d.potential
  let T := pullbackTest d f hf
  let V : Space n → ℝ := fun x => ∑ a : Fin n, compatibleTargetFlux d Du j a x *
    coordinateDerivative f a (gradient d.potential x)
  let R : Space n → ℝ := fun x => (Dg x - naturalCanonicalRawGradient d g j x) * T.value x
  have hV : Integrable V ν := by
    apply integrable_finsetSum Finset.univ
    intro a _
    have htop := d.continuous_comp_gradient_memLp
      (contDiff_coordinateDerivative hf (m := 0) (by norm_num) a).continuous ∞
    have hm : MemLp (fun x => compatibleTargetFlux d Du j a x *
        coordinateDerivative f a (gradient d.potential x)) 2 ν :=
      (compatibleTargetFlux_memLp d Du hDu hcomp hQi j a).mul htop
    exact hm.integrable (by norm_num)
  have hR : Integrable R ν := by
    have hm : MemLp R 2 ν := (hDg.sub (naturalCanonicalRawGradient_memLp d g j)).mul T.value_top
    exact hm.integrable (by norm_num)
  obtain ⟨χ, hc, hlim, hBi, _, hBlim⟩ :=
    exists_compatible_column_target_boundary_cutoffs d Du hDu hcomp hQi hf.continuous j
  have hχnorm (k : ℕ) : ∀ᵐ x ∂ν, ‖χ k x‖ ≤ 1 :=
    Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((hc k).2.2 x).1]
      exact ((hc k).2.2 x).2
  have hVi (k : ℕ) : Integrable (fun x => χ k x * V x) ν :=
    hV.bdd_mul (hc k).1.continuous.aestronglyMeasurable (hχnorm k)
  have hRi (k : ℕ) : Integrable (fun x => χ k x * R x) ν :=
    hR.bdd_mul (hc k).1.continuous.aestronglyMeasurable (hχnorm k)
  have hpair (k : ℕ) : (∫ x, χ k x * V x ∂ν) +
      (∫ x, f (gradient d.potential x) * (∑ i : Fin n, Du i j x * coordinateDerivative (χ k) i x) ∂ν) =
        ∫ x, χ k x * R x ∂ν := by
    let F : Fin n → Space n → ℝ := fun i x => coordinateDerivative (χ k) i x * T.value x + χ k x * T.derivative i x
    have hχloc (E : Set (Space n)) (hE : IsCompact E) : MemLp (χ k) 2 (volume.restrict E) :=
      memLp_continuous_on_compact (hc k).1.continuous hE
    have hDχloc (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
        MemLp (coordinateDerivative (χ k) i) 2 (volume.restrict E) :=
      memLp_continuous_on_compact
        (contDiff_coordinateDerivative (hc k).1 (m := 0) (by norm_num) i).continuous hE
    have hfloc (E : Set (Space n)) (hE : IsCompact E) :
        MemLp (fun x => χ k x * T.value x) 2 (volume.restrict E) :=
      memLp_continuous_mul_on_compact hE (T.value_local E hE) (hc k).1.continuous
    have hFloc (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (F i) 2 (volume.restrict E) := by
      have hfirst : MemLp (fun x => coordinateDerivative (χ k) i x * T.value x) 2 (volume.restrict E) :=
        memLp_continuous_mul_on_compact hE (T.value_local E hE)
          (contDiff_coordinateDerivative (hc k).1 (m := 0) (by norm_num) i).continuous
      exact hfirst.add (memLp_continuous_mul_on_compact hE (T.derivative_local i E hE) (hc k).1.continuous)
    have hFw (i : Fin n) : HasLocalWeakCoordinateDerivative (fun x => χ k x * T.value x) (F i) i :=
      (hasLocalWeakCoordinateDerivative_of_contDiff (hc k).1 i).mul (T.weak_derivative i)
        hχloc T.value_local (hDχloc i) (T.derivative_local i)
    obtain ⟨B, hb⟩ := T.bounded
    have hbound : ∀ᵐ x ∂(volume : Measure (Space n)), ‖χ k x * T.value x‖ ≤ B :=
      Eventually.of_forall fun x => by
        rw [norm_mul]
        have hχb : ‖χ k x‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg ((hc k).2.2 x).1]
          exact ((hc k).2.2 x).2
        exact (mul_le_mul_of_nonneg_right hχb (norm_nonneg _)).trans (by simpa only [one_mul] using hb x)
    have ht := natural_row_compact_rawH1_test d hn g hg Du hu hDu hw hgw hDg
      hfloc (hc k).2.1.mul_right hbound hFloc hFw
    have hleft : (∑ i : Fin n, ∫ x, Du i j x * F i x ∂ν) =
        (∫ x, χ k x * V x ∂ν) +
          ∫ x, f (gradient d.potential x) * (∑ i : Fin n, Du i j x * coordinateDerivative (χ k) i x) ∂ν := by
      rw [← integral_finsetSum Finset.univ (fun i _ => ht.1 i), ← integral_add (hVi k) (hBi k)]
      apply integral_congr_ae
      filter_upwards [compatible_target_pullback_pair_ae d Du hcomp f j] with x hx
      change (∑ i : Fin n, Du i j x * (coordinateDerivative (χ k) i x * f (gradient d.potential x) +
        χ k x * pullbackRawGradient d f i x)) = χ k x * V x +
          f (gradient d.potential x) * (∑ i : Fin n, Du i j x * coordinateDerivative (χ k) i x)
      calc
        _ = χ k x * (∑ i : Fin n, Du i j x * pullbackRawGradient d f i x) +
            f (gradient d.potential x) * (∑ i : Fin n, Du i j x * coordinateDerivative (χ k) i x) := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          rw [add_comm]
          congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
        _ = _ := by rw [hx]
    have hright : (∫ x, (Dg x - naturalCanonicalRawGradient d g j x) * (χ k x * T.value x) ∂ν) =
        ∫ x, χ k x * R x ∂ν := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only [R]; ring
    rw [hleft, hright] at ht
    exact ht.2.2
  have hVlim := (integral_mul_tendsto_of_ae_bounded_cutoffs hV
    (fun k => (hc k).1.continuous.aestronglyMeasurable) hχnorm (Eventually.of_forall hlim)).2
  have hRlim := (integral_mul_tendsto_of_ae_bounded_cutoffs hR
    (fun k => (hc k).1.continuous.aestronglyMeasurable) hχnorm (Eventually.of_forall hlim)).2
  have hsumlim := hVlim.add hBlim
  have he : (∫ x, V x ∂ν) = ∫ x, R x ∂ν := by
    have hl : Tendsto (fun k => ∫ x, χ k x * R x ∂ν) atTop (𝓝 (∫ x, V x ∂ν)) := by
      simpa only [add_zero] using hsumlim.congr (fun k => hpair k)
    exact tendsto_nhds_unique hl hRlim
  have hDfi : Integrable (fun x => Dg x * f (gradient d.potential x)) ν := by
    have hm : MemLp (fun x => Dg x * f (gradient d.potential x)) 2 ν := hDg.mul T.value_top
    exact hm.integrable (by norm_num)
  have hpfi : Integrable (fun x => naturalCanonicalRawGradient d g j x * f (gradient d.potential x)) ν := by
    have hm : MemLp (fun x => naturalCanonicalRawGradient d g j x * f (gradient d.potential x)) 2 ν :=
      (naturalCanonicalRawGradient_memLp d g j).mul T.value_top
    exact hm.integrable (by norm_num)
  have hsplit : (∫ x, R x ∂ν) = (∫ x, Dg x * f (gradient d.potential x) ∂ν) -
      ∫ x, naturalCanonicalRawGradient d g j x * f (gradient d.potential x) ∂ν := by
    rw [← integral_sub hDfi hpfi]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (Dg x - naturalCanonicalRawGradient d g j x) * f (gradient d.potential x) =
        Dg x * f (gradient d.potential x) - naturalCanonicalRawGradient d g j x * f (gradient d.potential x)
      ring
  rw [hsplit] at he
  change (∫ x, V x ∂ν) + _ = _
  linarith

/-- For an actual centered C1 target datum the natural inverse constructs
the same raw Jacobian, its global target flux and every global target-row
identity.  No derivative, PDE, connection or mass witness is supplied. -/
theorem exists_actual_target_Neumann_of_pullback (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    {b : Space n → ℝ} (hb : ContDiff ℝ 1 b)
    (hgb : (g : Space n → ℝ) =ᵐ[potentialMeasure d.potential] fun x => b (gradient d.potential x)) :
    ∃ Du : Fin n → Fin n → Space n → ℝ,
      (∀ i j, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i j) j) ∧
      (∀ᵐ x ∂(volume : Measure (Space n)),
        (coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x)).IsSymm) ∧
      Integrable (sourceVectorJacobianEnergy Du) (potentialMeasure d.potential) ∧
      (∀ j a, MemLp (compatibleTargetFlux d Du j a) 2 (potentialMeasure d.potential)) ∧
      ∀ (f : Space n → ℝ), ContDiff ℝ 1 f → ∀ j : Fin n,
        (∫ x, ∑ a : Fin n, compatibleTargetFlux d Du j a x *
          coordinateDerivative f a (gradient d.potential x) ∂potentialMeasure d.potential) +
          (∫ x, naturalCanonicalRawGradient d g j x * f (gradient d.potential x) ∂potentialMeasure d.potential) =
          ∫ x, pullbackRawGradient d b j x * f (gradient d.potential x) ∂potentialMeasure d.potential := by
  obtain ⟨Du, hu, hDu, hw, hcomp, _, hQi, _, _⟩ := exists_naturalCanonicalFlux_gaffney d hn g hg
  refine ⟨Du, hw, hcomp, hQi, compatibleTargetFlux_memLp d Du hDu hcomp hQi, ?_⟩
  intro f hf j
  have hvol := (volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous).ae_eq hgb
  have hgw : HasLocalWeakCoordinateDerivative (g : Space n → ℝ) (pullbackRawGradient d b j) j :=
    (d.pullback_hasLocalWeakCoordinateDerivative hb j).congr_ae hvol.symm EventuallyEq.rfl
  exact actual_global_target_row_equation d hn g hg Du hu hDu hw hcomp hQi hgw
    (d.pullback_weak_derivative_memLp hb j 2) hf

end KLSConstantImprovement.ActualNaturalFluxTargetNeumann405
#print axioms KLSConstantImprovement.ActualNaturalFluxTargetNeumann405.natural_row_compact_rawH1_test
#print axioms KLSConstantImprovement.ActualNaturalFluxTargetNeumann405.compatible_target_pullback_pair_ae
#print axioms KLSConstantImprovement.ActualNaturalFluxTargetNeumann405.actual_global_target_row_equation
#print axioms KLSConstantImprovement.ActualNaturalFluxTargetNeumann405.exists_actual_target_Neumann_of_pullback
