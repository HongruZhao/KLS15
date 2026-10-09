import ProjectedDivergenceWeakEquation

/-! Once the actual next local weak jet is constructed, original
orthogonality gives its genuine homogeneous q-th order weighted weak form. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration
variable {n r : ℕ} {φ : Space n → ℝ}
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable [IsProbabilityMeasure (potentialMeasure φ)]

theorem orthogonal_tensor_top_weak_form
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (U : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r)
    (horth : ∀ (ψ : Space n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
      (hc : HasCompactSupport ψ), inner ℝ U (compactPotentialDivergenceHilbert hφ hψ hc r)=0)
    (J : List (Fin n) → Space n → ℝ)
    (hJ : ∀ I : Fin r → Fin n, J (List.ofFn I)=ᵐ[volume] (U.val I : Space n → ℝ))
    (hweak : ∀ (I : Fin r → Fin n) (j : Fin n),
      HasLocalWeakCoordinateDerivative (J (List.ofFn I)) (J (j::List.ofFn I)) j)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    (∑ I : Fin (r+1) → Fin n, ∫ x,
      J (List.ofFn I) x*coordinatePotentialTensor ψ (r+1) I x ∂potentialMeasure φ)=0 := by
  have hw := compact_potential_orthogonality_weak_equation hφ U horth hψ hc
  have hi (I : Fin r → Fin n) (j : Fin n) :
      (∫ x, U.val I x*coordinateDerivative
        (fun y => Real.exp (-φ y)*coordinatePotentialTensor ψ (r+1) (Fin.cons j I) y) j x) =
      -(∫ x, J (j::List.ofFn I) x*
        coordinatePotentialTensor ψ (r+1) (Fin.cons j I) x ∂potentialMeasure φ) := by
    have hF := coordinatePotentialTensor_contDiff hψ (r+1) (Fin.cons j I)
    have hFc := coordinatePotentialTensor_hasCompactSupport hc (r+1) (Fin.cons j I)
    have ht : ContDiff ℝ 1 (fun y => Real.exp (-φ y)*
        coordinatePotentialTensor ψ (r+1) (Fin.cons j I) y) :=
      (hφ.neg.exp.mul hF).of_le (by simp)
    have he := hweak I j _ ht hFc.mul_left
    have hl : (∫ x, U.val I x*coordinateDerivative
        (fun y => Real.exp (-φ y)*coordinatePotentialTensor ψ (r+1) (Fin.cons j I) y) j x) =
      ∫ x, J (List.ofFn I) x*coordinateDerivative
        (fun y => Real.exp (-φ y)*coordinatePotentialTensor ψ (r+1) (Fin.cons j I) y) j x := by
      apply integral_congr_ae
      filter_upwards [hJ I] with x hx
      rw [hx]
    rw [hl,he,integral_potentialMeasure hφ.continuous.measurable]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    ring
  simp_rw [hi] at hw
  simp_rw [Finset.sum_neg_distrib] at hw
  have hz : (∑ I : Fin r → Fin n, ∑ j : Fin n, ∫ x,
      J (j::List.ofFn I) x*coordinatePotentialTensor ψ (r+1) (Fin.cons j I) x
        ∂potentialMeasure φ)=0 := neg_eq_zero.mp hw
  convert hz using 1
  symm
  rw [Finset.sum_comm]
  calc
    _ = ∑ p : Fin n × (Fin r → Fin n), ∫ x,
        J (p.1::List.ofFn p.2) x*coordinatePotentialTensor ψ (r+1) (Fin.cons p.1 p.2) x
          ∂potentialMeasure φ := (Fintype.sum_prod_type _).symm
    _ = _ := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (r+1) => Fin n))
      _ _ (fun p => by
        change (∫ x, J (p.1::List.ofFn p.2) x*
          coordinatePotentialTensor ψ (r+1) (Fin.cons p.1 p.2) x ∂potentialMeasure φ) =
          ∫ x, J (List.ofFn (Fin.cons p.1 p.2)) x*
            coordinatePotentialTensor ψ (r+1) (Fin.cons p.1 p.2) x ∂potentialMeasure φ
        rw [List.ofFn_cons])

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.orthogonal_tensor_top_weak_form
