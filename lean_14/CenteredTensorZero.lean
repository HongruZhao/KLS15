import PoweredCutoffFatou
import CenteredProjectedDivergence
import KLS.WeakDistributionConstant

/-! The zero-gradient and centering endpoint of the density argument. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators ENNReal
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n r : ℕ} {φ : Space n → ℝ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

section Probability
variable [IsProbabilityMeasure (potentialMeasure φ)]

lemma centeredLp_eq_zero_of_zero_distributional_gradient
    (hφ : Continuous φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hmean : (∫ x, u x ∂potentialMeasure φ)=0)
    (hd : ∀ i (ψ : Space n → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, u x*coordinateDerivative ψ i x)=0) : u=0 := by
  have hloc := KLS.MemLp.locallyIntegrable_volume_of_potentialMeasure (Lp.memLp u) hφ
  obtain ⟨c,hc⟩ := ae_eq_const_of_zero_distributional_gradient hloc hd
  have hcw : (u : Space n → ℝ) =ᵐ[potentialMeasure φ] fun _ => c :=
    (withDensity_absolutelyContinuous _ _).ae_eq hc
  have hc0 : c=0 := by
    have he := integral_congr_ae hcw
    simpa only [hmean,integral_const,probReal_univ,one_smul] using he.symm
  apply Lp.ext
  filter_upwards [hcw,Lp.coeFn_zero ℝ 2 (potentialMeasure φ)] with x hx hz
  exact hx.trans (hc0.trans hz.symm)

theorem centeredTensor_eq_zero_of_zero_distributional_gradient
    (hφ : ContDiff ℝ 1 φ) (U : OrderedTensorField φ r)
    (hU : U ∈ centeredCompatibleTensorSubspace hφ r)
    (hd : ∀ I i (ψ : Space n → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, U I x*coordinateDerivative ψ i x)=0) : U=0 := by
  have hmeans := (mem_centeredCompatibleTensorSubspace_iff hφ U).mp hU
  apply PiLp.ext
  intro I
  exact centeredLp_eq_zero_of_zero_distributional_gradient hφ.continuous (U I)
    (hmeans.2 I) (hd I)

/-- This consumes the literal weak chain and the top derivative supplied
by the Fatou theorem; no H¹ graph membership for U is assumed. -/
theorem centeredTensor_eq_zero_of_weak_top_ae_zero
    (hφ : ContDiff ℝ 1 φ) (U : OrderedTensorField φ r)
    (hU : U ∈ centeredCompatibleTensorSubspace hφ r)
    (W : OrderedTensorIndex n r → Fin n → Space n → ℝ)
    (hweak : ∀ I i (ψ : Space n → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, U I x*coordinateDerivative ψ i x)= -(∫ x, W I i x*ψ x))
    (hW : ∀ I i, W I i =ᵐ[potentialMeasure φ] 0) : U=0 := by
  apply centeredTensor_eq_zero_of_zero_distributional_gradient hφ U hU
  intro I i ψ hψ hc
  rw [hweak I i ψ hψ hc]
  have hz : (∫ x, W I i x*ψ x)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [(volume_absolutelyContinuous_potentialMeasure hφ.continuous).ae_eq (hW I i)]
      with x hx
    change W I i x*ψ x=0
    rw [hx]
    simp
  rw [hz,neg_zero]

end Probability
end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.centeredTensor_eq_zero_of_weak_top_ae_zero
