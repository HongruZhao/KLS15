import KLSConstantImprovement.ActualJointBochnerContractions405

/-! The actual weak Bochner identity for one common compact C1 joint
multiplier of (u,H). Both original weak equations are genuinely tested and
summed. The joint truncation is retained; no nonlinear renormalization or
unbounded mass test is postulated. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualJointWeakBochner405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405
open ActualIntrinsicJointWeakTests405 ActualJointMultiplierWeakTests405 ActualJointMultiplierRowTest405
open ActualJointBochnerContractions405 ActualSourceConnectionFields405 ActualSourceHessianEvolution405
open ActualSourceLocalizedGaffney405 ActualSourceNaturalTargetCurvatureDomain405 ActualBoundedRawMetricDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

def sourceBochnerDensity (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (Du : Fin n → Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  sourceVectorJacobianEnergy Du x + sourceConnectionCross d u Du x / 2 +
    sourceConnectionGamma d u x / 2 +
      (sourceVectorMass d.potential u x + sourceConnectionTarget d u x) / 2

def sourceHalfMassFlux (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (Du : Fin n → Fin n → Space n → ℝ) (a : Fin n) (x : Space n) : ℝ :=
  rowMassFlux u Du a x +
    ((coordinateHessian d.potential x)⁻¹ *ᵥ (sourceThirdAlong d u x *ᵥ (fun i => u i x))) a / 2

def jointBochnerIntegrand (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (Du : Fin n → Fin n → Space n → ℝ) (η : (JointIndex n → ℝ) → ℝ)
    (ψ : Space n → ℝ) (x : Space n) : ℝ :=
  ψ x * jointSource d u η x * sourceBochnerDensity d u Du x +
    ∑ a : Fin n, sourceHalfMassFlux d u Du a x * jointEffectiveDerivative d u Du η ψ a x

theorem actual_joint_weak_Bochner (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i b E, IsCompact E → MemLp (Du i b) 2 (volume.restrict E))
    (hw : ∀ i b, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i b) b)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (Dg : Fin n → Space n → ℝ)
    (hgw : ∀ j, HasLocalWeakCoordinateDerivative (g : Space n → ℝ) (Dg j) j)
    (hDg : ∀ j, MemLp (Dg j) 2 (potentialMeasure d.potential))
    {η : (JointIndex n → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    Integrable (jointBochnerIntegrand d (naturalCanonicalFlux d g) Du η ψ) (potentialMeasure d.potential) ∧
      Integrable (fun x => ψ x * jointSource d (naturalCanonicalFlux d g) η x *
        (∑ j : Fin n, Dg j x * naturalCanonicalFlux d g j x)) (potentialMeasure d.potential) ∧
      (∫ x, jointBochnerIntegrand d (naturalCanonicalFlux d g) Du η ψ x ∂potentialMeasure d.potential) =
        ∫ x, ψ x * jointSource d (naturalCanonicalFlux d g) η x *
          (∑ j : Fin n, Dg j x * naturalCanonicalFlux d g j x) ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let ν := potentialMeasure d.potential
  let u := naturalCanonicalFlux d g
  let w := jointSource d u η
  let R (j a : Fin n) (x : Space n) := Du a j x *
    rawCutoffDerivative ψ (jointSource d u (jointRow η j))
      (jointSourceDerivative d u Du (jointRow η j)) a x
  let RR (j : Fin n) (x : Space n) := (Dg j x - naturalCanonicalRawGradient d g j x) *
    (ψ x * jointSource d u (jointRow η j) x)
  let T (i j a : Fin n) (x : Space n) :=
    ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
      rawCutoffDerivative ψ (jointSource d u (jointMatrix η i j))
        (jointSourceDerivative d u Du (jointMatrix η i j)) a x
  let TT (i j : Fin n) (x : Space n) :=
    (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) *
      (ψ x * jointSource d u (jointMatrix η i j) x)
  let A (x : Space n) := ∑ j : Fin n, ∑ a : Fin n, R j a x
  let AR (x : Space n) := ∑ j : Fin n, RR j x
  let B (x : Space n) := ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, T i j a x
  let BR (x : Space n) := ∑ i : Fin n, ∑ j : Fin n, TT i j x
  let M (x : Space n) := ψ x * w x * sourceVectorMass d.potential u x
  have hr (j : Fin n) := actual_joint_row_equation d hn g hg Du hu hDu hw
    (hgw j) (hDg j) hη hcη hψ hc
  have ht (i j : Fin n) := actual_joint_matrix_hessian_evolution d hu hDu hw hη hcη hψ hc i j
  have hA : Integrable A ν := integrable_finsetSum Finset.univ fun j _ =>
    integrable_finsetSum Finset.univ fun a _ => (hr j).1 a
  have hAR : Integrable AR ν := integrable_finsetSum Finset.univ fun j _ => (hr j).2.1
  have hB : Integrable B ν := integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => integrable_finsetSum Finset.univ fun a _ => (ht i j).1 a
  have hBR : Integrable BR ν := integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => (ht i j).2.1
  obtain ⟨⟨C, hC⟩, hwl, _hwD, _hwW⟩ := actual_compact_joint_domains d hu hDu hw hη hcη
  have hwm : AEStronglyMeasurable w ν :=
    (locallyIntegrable_of_memLp_two_on_compacts hwl).aestronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hwtop : MemLp w ∞ ν := memLp_top_of_bound hwm C (Eventually.of_forall hC)
  have hψtop : MemLp ψ ∞ ν := hψ.continuous.memLp_of_hasCompactSupport hc
  have hmul : MemLp (fun x => ψ x * w x) ∞ ν := hψtop.mul hwtop
  have hM : Integrable M ν := hMi.mul_of_top_right hmul
  have hRa (j : Fin n) : (∫ x, ∑ a : Fin n, R j a x ∂ν) =
      ∑ a : Fin n, ∫ x, R j a x ∂ν := integral_finsetSum Finset.univ fun a _ => (hr j).1 a
  have hAI : (∫ x, A x ∂ν) = ∫ x, AR x ∂ν := by
    change (∫ x, ∑ j : Fin n, ∑ a : Fin n, R j a x ∂ν) =
      ∫ x, ∑ j : Fin n, RR j x ∂ν
    rw [integral_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ fun a _ => (hr j).1 a),
      integral_finsetSum Finset.univ (fun j _ => (hr j).2.1)]
    exact Finset.sum_congr rfl fun j _ => (hRa j).trans (hr j).2.2
  have hTa (i j : Fin n) : (∫ x, ∑ a : Fin n, T i j a x ∂ν) =
      ∑ a : Fin n, ∫ x, T i j a x ∂ν := integral_finsetSum Finset.univ fun a _ => (ht i j).1 a
  have hTj (i : Fin n) : (∫ x, ∑ j : Fin n, ∑ a : Fin n, T i j a x ∂ν) =
      ∑ j : Fin n, ∑ a : Fin n, ∫ x, T i j a x ∂ν := by
    rw [integral_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ fun a _ => (ht i j).1 a)]
    exact Finset.sum_congr rfl fun j _ => hTa i j
  have hBI : (∫ x, B x ∂ν) = -(∫ x, BR x ∂ν) := by
    have hleft : (∫ x, B x ∂ν) = ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∫ x, T i j a x ∂ν := by
      rw [show B = (fun x => ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, T i j a x) from rfl,
        integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ fun j _ =>
          integrable_finsetSum Finset.univ fun a _ => (ht i j).1 a)]
      exact Finset.sum_congr rfl fun i _ => hTj i
    have hright : (∫ x, BR x ∂ν) = ∑ i : Fin n, ∑ j : Fin n, ∫ x, TT i j x ∂ν := by
      rw [show BR = (fun x => ∑ i : Fin n, ∑ j : Fin n, TT i j x) from rfl,
        integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ fun j _ => (ht i j).2.1)]
      exact Finset.sum_congr rfl fun i _ => integral_finsetSum Finset.univ fun j _ => (ht i j).2.1
    rw [hleft, hright, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by linarith [(ht i j).2.2]
  have hpoint (x : Space n) : jointBochnerIntegrand d u Du η ψ x =
      ((A x + B x / 2) + BR x / 2) + M x := by
    have ha := joint_row_test_contraction d u Du hη ψ x
    have hb := joint_matrix_test_contraction d u Du hη ψ x
    have hc' := joint_matrix_rhs_contraction d u η ψ x
    change A x = _ at ha
    change B x = _ at hb
    change BR x = _ at hc'
    rw [ha, hb, hc']
    have hpair : (∑ a : Fin n, sourceHalfMassFlux d u Du a x *
        jointEffectiveDerivative d u Du η ψ a x) =
        (∑ a : Fin n, rowMassFlux u Du a x * jointEffectiveDerivative d u Du η ψ a x) +
          ((fun a => jointEffectiveDerivative d u Du η ψ a x) ⬝ᵥ
            ((coordinateHessian d.potential x)⁻¹ *ᵥ (sourceThirdAlong d u x *ᵥ (fun i => u i x)))) / 2 := by
      simp only [sourceHalfMassFlux, dotProduct, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    dsimp only [jointBochnerIntegrand]
    rw [hpair]
    dsimp only [sourceBochnerDensity, M, w]
    ring
  have hComb : Integrable (fun x => ((A x + B x / 2) + BR x / 2) + M x) ν :=
    ((hA.add (hB.div_const 2)).add (hBR.div_const 2)).add hM
  have hJ : Integrable (jointBochnerIntegrand d u Du η ψ) ν :=
    hComb.congr (Eventually.of_forall fun x => (hpoint x).symm)
  have hforce : (fun x => AR x + M x) =ᵐ[ν]
      (fun x => ψ x * w x * (∑ j : Fin n, Dg j x * u j x)) := by
    filter_upwards [joint_row_rhs_contraction_ae d g Dg η ψ] with x hx
    change AR x = _ at hx
    rw [hx]
    dsimp only [M, w]
    ring
  have hF : Integrable (fun x => ψ x * w x * (∑ j : Fin n, Dg j x * u j x)) ν :=
    (hAR.add hM).congr hforce
  refine ⟨hJ, hF, ?_⟩
  calc
    _ = ∫ x, ((A x + B x / 2) + BR x / 2) + M x ∂ν :=
      integral_congr_ae (Eventually.of_forall hpoint)
    _ = ((∫ x, A x ∂ν) + (∫ x, B x ∂ν) / 2) + (∫ x, BR x ∂ν) / 2 + (∫ x, M x ∂ν) := by
      have hAB : Integrable (fun x => A x + B x / 2) ν := hA.add (hB.div_const 2)
      have hABR : Integrable (fun x => (A x + B x / 2) + BR x / 2) ν := hAB.add (hBR.div_const 2)
      rw [integral_add hABR hM, integral_add hAB (hBR.div_const 2), integral_add hA (hB.div_const 2),
        integral_div, integral_div]
    _ = (∫ x, AR x ∂ν) + (∫ x, M x ∂ν) := by rw [hAI, hBI]; ring
    _ = _ := by rw [← integral_add hAR hM]; exact integral_congr_ae hforce

end KLSConstantImprovement.ActualJointWeakBochner405
#print axioms KLSConstantImprovement.ActualJointWeakBochner405.actual_joint_weak_Bochner
