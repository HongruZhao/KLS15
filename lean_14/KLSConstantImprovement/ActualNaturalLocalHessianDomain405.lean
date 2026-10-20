import KLSConstantImprovement.ActualNaturalLocalConnectionDomain405
import KLSConstantImprovement.ActualSourceNaturalHessian405
import KLSConstantImprovement.ActualSourceThirdUniformEnergy405

/-! Actual local second-order domains of every natural inverse. The raw
product rule first pays its genuine weak Hessian in L1; the newly paid local
connection contraction then upgrades the literal Hessian to local L2.
No bounded natural mass or classical source Hessian derivative is assumed. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualNaturalLocalHessianDomain405
open KLS ActualBoundedCanonicalSource ActualSourceHessianEvolution405 ActualSourceConnectionFields405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceNaturalHessian405
open ActualSourceNaturalTargetCurvatureDomain405 ActualSourceConnectionPointwise405
open ActualNaturalLocalConnectionDomain405 ActualSourceThirdUniformEnergy405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem naturalRawGradient_weakHessian_without_mass (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    (i j : Fin n) :
    HasLocalWeakCoordinateDerivative (naturalCanonicalRawGradient d g i)
      (fun x => naturalCanonicalHessian d g Du x i j) j := by
  let u := naturalCanonicalFlux d g
  let f (a : Fin n) (x : Space n) := coordinateHessian d.potential x i a * u a x
  let F (a : Fin n) (x : Space n) := d.third x j i a * u a x + coordinateHessian d.potential x i a * Du a j x
  have hH (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => coordinateHessian d.potential x i a) ∞ (volume.restrict E) :=
    memLp_top_actual_hessian_of_locallyLipschitz_gradient d.gradient_lipschitz.locallyLipschitz i a hE
  have hH2 (a : Fin n) : ∀ E, IsCompact E →
      MemLp (fun x => coordinateHessian d.potential x i a) 2 (volume.restrict E) :=
    memLp_two_on_compacts_of_top (hH a)
  have hfloc (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (f a) 2 (volume.restrict E) :=
    (hH a E hE).mul (hu a E hE)
  have hFloc (a : Fin n) : LocallyIntegrable (F a) volume := by
    apply locallyIntegrable_iff.mpr
    intro E hE
    exact ((d.third_local_L2 j i a E hE).integrable_mul (hu a E hE)).add
      ((hH2 a E hE).integrable_mul (hDu a j E hE))
  have hfw (a : Fin n) : HasLocalWeakCoordinateDerivative (f a) (F a) j :=
    (d.third_weak_derivative j i a).mul (hw a j) (hH2 a) (hu a)
      (d.third_local_L2 j i a) (hDu a j)
  have hsum := hasLocalWeakCoordinateDerivative_finset_sum Finset.univ (fun a _ => hfw a)
    (fun a _ => locallyIntegrable_of_memLp_two_on_compacts (hfloc a)) (fun a _ => hFloc a)
  have hp : (fun x => ∑ a : Fin n, f a x) =ᵐ[(volume : Measure (Space n))]
      naturalCanonicalRawGradient d g i := by
    have he := (volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous).ae_eq
      (hessian_mul_naturalCanonicalFlux_ae d g)
    filter_upwards [he] with x hx
    exact congrFun hx i
  have hF : (fun x => ∑ a : Fin n, F a x) =ᵐ[(volume : Measure (Space n))]
      fun x => naturalCanonicalHessian d g Du x i j := by
    filter_upwards [d.third_symmetric_ae] with x hx
    have hn (a : Fin n) : d.third x j i a = d.third x a i j := by
      calc
        _ = d.third x i j a := (hx j i a).1
        _ = d.third x i a j := (hx i j a).2
        _ = _ := (hx i a j).1
    simp only [F, naturalCanonicalHessian, sourceThirdAlong, sourceThirdMatrix,
      Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun a _ => by rw [hn a, mul_comm]
  exact hsum.congr_ae hp hF

theorem naturalThirdAlong_local_L2_of_local_Gamma (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hΓ : ∀ E, IsCompact E → Integrable (sourceConnectionGamma d (naturalCanonicalFlux d g)) (volume.restrict E))
    (i j : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (fun x => sourceThirdAlong d (naturalCanonicalFlux d g) x i j) 2 (volume.restrict E) := by
  let u := naturalCanonicalFlux d g
  let B : ℝ := 16 / d.targetConvexityConstant
  have hBn : 0 ≤ B := by have hκ := d.target_convexity_pos; dsimp only [B]; positivity
  have hm : AEStronglyMeasurable (fun x => sourceThirdAlong d u x i j) (volume.restrict E) := by
    simp only [sourceThirdAlong, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.aestronglyMeasurable_fun_sum Finset.univ fun a _ =>
      (hu a E hE).aestronglyMeasurable.mul (d.third_local_L2 a i j E hE).aestronglyMeasurable
  have hvol : (volume : Measure (Space n)) ≪ potentialMeasure d.potential :=
    volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous
  have hNs := (sourceThirdAlong_isSymm_ae d u).filter_mono hvol.ae_le
  have hΓn := (sourceConnectionGamma_nonnegative_ae d u).filter_mono hvol.ae_le
  have hb : ∀ᵐ x ∂volume.restrict E, sourceThirdAlong d u x i j ^ 2 ≤
      B ^ 2 * sourceConnectionGamma d u x := by
    filter_upwards [ae_restrict_of_ae d.hessian_ae, ae_restrict_of_ae hNs,
      ae_restrict_of_ae hΓn] with x hp hN hG
    have he := symmetric_entry_square_le_inverse_trace (coordinateHessian d.potential x)
      (sourceThirdAlong d u x) hp.1 hN i j
    rw [sourceThirdAlong_trace_square] at he
    have hi : coordinateHessian d.potential x i i ≤ B := by
      have ha := coordinateHessian_entry_bound_of_gradient_lipschitz d.gradient_lipschitz x i i
      change |coordinateHessian d.potential x i i| ≤ B at ha
      exact (le_abs_self _).trans ha
    have hj : coordinateHessian d.potential x j j ≤ B := by
      have ha := coordinateHessian_entry_bound_of_gradient_lipschitz d.gradient_lipschitz x j j
      change |coordinateHessian d.potential x j j| ≤ B at ha
      exact (le_abs_self _).trans ha
    have hprod : coordinateHessian d.potential x i i * coordinateHessian d.potential x j j ≤ B ^ 2 := by
      simpa only [pow_two] using mul_le_mul hi hj hp.1.posSemidef.diag_nonneg hBn
    exact he.trans (mul_le_mul_of_nonneg_right hprod hG)
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply ((hΓ E hE).const_mul (B ^ 2)).mono' (hm.pow 2)
  filter_upwards [hb] with x hx
  change ‖sourceThirdAlong d u x i j ^ 2‖ ≤ B ^ 2 * sourceConnectionGamma d u x
  rwa [Real.norm_of_nonneg (sq_nonneg _)]

theorem naturalHessian_local_L2_of_local_Gamma (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hΓ : ∀ E, IsCompact E → Integrable (sourceConnectionGamma d (naturalCanonicalFlux d g)) (volume.restrict E))
    (i j : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (fun x => naturalCanonicalHessian d g Du x i j) 2 (volume.restrict E) := by
  have hH (a : Fin n) : MemLp (fun x => coordinateHessian d.potential x i a) ∞ (volume.restrict E) :=
    memLp_top_actual_hessian_of_locallyLipschitz_gradient d.gradient_lipschitz.locallyLipschitz i a hE
  have hp : MemLp (fun x => (coordinateHessian d.potential x * Matrix.of (fun a b => Du a b x)) i j)
      2 (volume.restrict E) := by
    have hm (a : Fin n) : MemLp (fun x => coordinateHessian d.potential x i a * Du a j x)
        2 (volume.restrict E) := (hH a).mul (hDu a j E hE)
    have hs : MemLp (fun x => ∑ a : Fin n, coordinateHessian d.potential x i a * Du a j x)
        2 (volume.restrict E) := memLp_finsetSum Finset.univ fun a _ => hm a
    simpa only [Matrix.mul_apply, Matrix.of_apply] using hs
  have hn := naturalThirdAlong_local_L2_of_local_Gamma d g hu hΓ i j E hE
  have hs := hp.add hn
  change MemLp (fun x => (coordinateHessian d.potential x * Matrix.of (fun a b => Du a b x)) i j +
    sourceThirdAlong d (naturalCanonicalFlux d g) x i j) 2 (volume.restrict E) at hs
  simpa only [naturalCanonicalHessian, Matrix.add_apply] using hs

theorem exists_natural_local_H2_without_mass (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0) :
    ∃ Du : Fin n → Fin n → Space n → ℝ,
      (∀ i j E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i j) 2 (volume.restrict E)) ∧
      (∀ i j, HasLocalWeakCoordinateDerivative (naturalCanonicalRawGradient d g i)
        (fun x => naturalCanonicalHessian d g Du x i j) j) ∧
      (∀ i j E, IsCompact E → MemLp (fun x => sourceThirdAlong d (naturalCanonicalFlux d g) x i j)
        2 (volume.restrict E)) := by
  obtain ⟨Du, hu, hDu, hw, hcomp, hMi, hQi, _hEnergy, _hdiv⟩ :=
    exists_naturalCanonicalFlux_gaffney d hn g hg
  have hΓ (E : Set (Space n)) (hE : IsCompact E) :=
    (actual_connectionGamma_local_domains d g Du hDu hw hcomp hMi hQi E hE).2
  exact ⟨Du, naturalHessian_local_L2_of_local_Gamma d g Du hu hDu hΓ,
    naturalRawGradient_weakHessian_without_mass d g Du hu hDu hw,
    naturalThirdAlong_local_L2_of_local_Gamma d g hu hΓ⟩

end KLSConstantImprovement.ActualNaturalLocalHessianDomain405
#print axioms KLSConstantImprovement.ActualNaturalLocalHessianDomain405.naturalRawGradient_weakHessian_without_mass
#print axioms KLSConstantImprovement.ActualNaturalLocalHessianDomain405.naturalThirdAlong_local_L2_of_local_Gamma
#print axioms KLSConstantImprovement.ActualNaturalLocalHessianDomain405.naturalHessian_local_L2_of_local_Gamma
#print axioms KLSConstantImprovement.ActualNaturalLocalHessianDomain405.exists_natural_local_H2_without_mass
