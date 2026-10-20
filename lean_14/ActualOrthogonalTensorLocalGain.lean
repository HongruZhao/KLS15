import ActualOrthogonalTensorLocalRegularity

/-! Orthogonality itself, for the actual compatible tensor Hilbert space,
now supplies the one-order local elliptic gain of its constructed primitive. -/
noncomputable section
open MeasureTheory TemperedDistribution Set Filter Matrix
open scoped ContDiff SchwartzMap LineDeriv Topology BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
open KLS KLSBelow25 KLS.DeterministicBridgeNext
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
variable {n r : ℕ} {φ : Space n → ℝ}
variable [IsProbabilityMeasure (potentialMeasure φ)]

 theorem compact_orthogonal_tensor_primitive_local_gain
     (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
     (F : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r)
     (horth : ∀ (ψ : Space n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
       (hc : HasCompactSupport ψ), inner ℝ F (compactPotentialDivergenceHilbert hφ hψ hc r)=0)
     (U : (k : ℕ) → OrderedTensorField φ k) (htop : U r=F.val)
     (hgraph : ∀ k, k < r → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
       finitePrimitiveValue (OrderedTensorIndex n k) V=U k ∧
         ∀ I i, weightedH1Derivative φ i (V I)=U (k+1) (Fin.cons i I))
     {ζ : Space n → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hcζ : HasCompactSupport ζ) :
     MemSobolev ((r+1 : ℕ) : ℝ) 2
       (compactWeightedTempered hφ.continuous hζ.continuous hcζ (tensorWordLp U [])) := by
   exact compact_tower_real_weak_equation_local_gain hφ U hgraph
     (fun η hη hcη => by
       rw [htop]
       exact compact_potential_orthogonality_weak_equation hφ F horth hη hcη) hζ hcζ

 theorem exists_orthogonal_tensor_primitive_local_gain
     (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {κ : ℝ} (hκ : 0 < κ)
     (hlower : ∀ x (a : Fin n → ℝ),
       κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
     (F : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r)
     (horth : ∀ (ψ : Space n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
       (hc : HasCompactSupport ψ), inner ℝ F (compactPotentialDivergenceHilbert hφ hψ hc r)=0) :
     ∃ U : (k : ℕ) → OrderedTensorField φ k,
       U r=F.val ∧
       (∀ k, k < r → U k ∈ centeredCompatibleTensorSubspace (hφ.of_le (by simp)) k) ∧
       (∀ k, k < r → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
         finitePrimitiveValue (OrderedTensorIndex n k) V=U k ∧
           ∀ I i, weightedH1Derivative φ i (V I)=U (k+1) (Fin.cons i I)) ∧
       ∀ (ζ : Space n → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hcζ : HasCompactSupport ζ),
         MemSobolev ((r+1 : ℕ) : ℝ) 2
           (compactWeightedTempered hφ.continuous hζ.continuous hcζ (tensorWordLp U [])) := by
   obtain ⟨U,htop,_,hcenter,hgraph,_⟩ := exists_iterated_compatibleTensorPrimitive hφ hκ hlower r
     (centeredCompatibleTensorInclusion (hφ.of_le (by simp)) r F)
   have htop' : U r=F.val := htop
   refine ⟨U,htop',hcenter,hgraph,?_⟩
   intro ζ hζ hcζ
   exact compact_orthogonal_tensor_primitive_local_gain hφ F horth U htop' hgraph hζ hcζ

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.compact_orthogonal_tensor_primitive_local_gain
#print axioms KLS.DeterministicBridgeIntegration.exists_orthogonal_tensor_primitive_local_gain
