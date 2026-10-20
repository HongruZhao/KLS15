import ActualJointTangentMaximum

/-! The fixed concavity tangent supports every actual L² test, including
zero tests. This is an actual operator quadratic bound at the joint optimum. -/
noncomputable section
open MeasureTheory Set InnerProductSpace
open scoped ContDiff Topology
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

 theorem actual_joint_all_L2_tangent_bound {n k : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) {h : ℝ} (hh : 0 < h)
    (hunit : ‖f‖=1) {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ (Icc 0 1) φ)
    (hφpos : ∀ u ∈ Icc (0 : ℝ) 1, 0 < φ u)
    (hprevious : ∀ (ν : Measure (Space n)), admissibleMeasure ν → ∀ g : Space n → ℝ,
      MemLp g 2 ν → actualAppellEnergy ν g k ≤ h*(∫ x, (g x)^2 ∂ν))
    {d : ℝ} (hd : HasDerivAt φ d (‖fullClassAppellTensor k f‖^2/h))
    (hmax : ∀ g : Lp ℝ 2 μ,
      coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
        (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ g ≤
      coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
        (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ f) :
    let X := ‖fullClassAppellTensor (k+1) f‖^2
    let u := ‖fullClassAppellTensor k f‖^2/h
    let w := -(X/φ u)*(d/h)
    let lam := (X/φ u)*(φ u-u*d)
    ∀ g : Lp ℝ 2 μ,
      ‖fullClassAppellTensor (k+1) g‖^2+w*‖fullClassAppellTensor k g‖^2 ≤ lam*‖g‖^2 := by
  dsimp only
  let X := ‖fullClassAppellTensor (k+1) f‖^2
  let u := ‖fullClassAppellTensor k f‖^2/h
  let w := -(X/φ u)*(d/h)
  let lam := (X/φ u)*(φ u-u*d)
  have hf : f ≠ 0 := by
    intro he
    simp only [he,norm_zero] at hunit
    norm_num at hunit
  have hu : u ∈ Icc (0 : ℝ) 1 := by
    simpa only [hunit,one_pow,mul_one] using actualAppell_ratio_mem_Icc hμ hh hprevious f hf
  intro g
  by_cases hg : g=0
  · have hzj : fullClassAppellTensor (k+1) (0 : Lp ℝ 2 μ)=0 :=
      (fullClassAppellLinearMap hμ.logConcave (k+1)).map_zero
    have hzk : fullClassAppellTensor k (0 : Lp ℝ 2 μ)=0 :=
      (fullClassAppellLinearMap hμ.logConcave k).map_zero
    simp only [hg,hzj,hzk,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,add_zero,le_refl]
  have hratio := actualAppell_ratio_mem_Icc hμ hh hprevious g hg
  have hm := hmax g
  unfold coefficientQuotient at hm
  change ‖fullClassAppellTensor (k+1) g‖^2/
    (‖g‖^2*φ (‖fullClassAppellTensor k g‖^2/(h*‖g‖^2))) ≤
    X/(‖f‖^2*φ (‖fullClassAppellTensor k f‖^2/(h*‖f‖^2))) at hm
  rw [hunit,one_pow,mul_one,one_mul] at hm
  have hb := concave_quotient_tangent_bound hφ hφpos hu hratio hd hh
    (sq_pos_of_pos (norm_pos_iff.mpr hg)) (sq_nonneg ‖fullClassAppellTensor (k+1) f‖) hm
  change ‖fullClassAppellTensor (k+1) g‖^2+w*‖fullClassAppellTensor k g‖^2 ≤ lam*‖g‖^2
  dsimp only [w,lam] at ⊢
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_joint_all_L2_tangent_bound
