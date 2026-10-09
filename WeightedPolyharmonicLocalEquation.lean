import WeightedPolyharmonicTestEvaluation

/-! The genuine lower weak-jet tower and literal compact-test equation
supply the localized weighted PDE and its local Sobolev gain. -/
noncomputable section
open MeasureTheory TemperedDistribution Set Filter
open scoped ContDiff SchwartzMap LineDeriv Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLSBelow25
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
variable {n r : ℕ} {φ : Space n → ℝ}

 theorem compact_tower_weighted_polyharmonic_local_zero
     (hφ : ContDiff ℝ 1 φ) (U : (k : ℕ) → OrderedTensorField φ k)
     (hgraph : ∀ k, k < r → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
       finitePrimitiveValue (OrderedTensorIndex n k) V=U k ∧
         ∀ I i, weightedH1Derivative φ i (V I)=U (k+1) (Fin.cons i I))
     {χ : Space n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
     (a w : 𝓢(Space n,ℂ))
     (hcut : ∀ x ∈ tsupport a, χ =ᶠ[𝓝 x] fun _ => (1 : ℝ))
     (hweak : ∀ ψ : 𝓢(Space n,ℂ), tsupport ψ ⊆ tsupport a →
       (∑ i : Fin n, ∑ I : Fin r → Fin n,
         ∫ x, weightedPolyharmonicAdjointTest w i (List.ofFn I) ψ x*
           (tensorWordLp U (List.ofFn I) x : ℂ))=0) :
     TemperedDistribution.smulLeftCLM ℂ a (weightedOrderedPolyharmonic (r+1) w
       (compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U [])))=0 := by
   ext ψ
   rw [TemperedDistribution.smulLeftCLM_apply_apply]
   have hs : tsupport (SchwartzMap.smulLeftCLM ℂ a ψ) ⊆ tsupport a :=
     (SchwartzMap.tsupport_smulLeftCLM_subset _ _).trans inter_subset_right
   rw [weightedOrderedPolyharmonic_compact_tower_apply hφ U hgraph le_rfl hχ hc w _
     (fun x hx => hcut x (hs hx)),hweak _ hs,mul_zero]
   rfl

 theorem compact_tower_weighted_polyharmonic_local_gain
     (hφ : ContDiff ℝ 1 φ) (U : (k : ℕ) → OrderedTensorField φ k)
     (hgraph : ∀ k, k < r → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
       finitePrimitiveValue (OrderedTensorIndex n k) V=U k ∧
         ∀ I i, weightedH1Derivative φ i (V I)=U (k+1) (Fin.cons i I))
     {χ : Space n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
     (a w : 𝓢(Space n,ℂ))
     (hcut : ∀ x ∈ tsupport a, χ =ᶠ[𝓝 x] fun _ => (1 : ℝ))
     (hweak : ∀ ψ : 𝓢(Space n,ℂ), tsupport ψ ⊆ tsupport a →
       (∑ i : Fin n, ∑ I : Fin r → Fin n,
         ∫ x, weightedPolyharmonicAdjointTest w i (List.ofFn I) ψ x*
           (tensorWordLp U (List.ofFn I) x : ℂ))=0) :
     MemSobolev ((r+1 : ℕ) : ℝ) 2
       (TemperedDistribution.smulLeftCLM ℂ (schwartzProduct a w)
         (compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U []))) := by
   have hpde := compact_tower_weighted_polyharmonic_local_zero hφ U hgraph hχ hc a w hcut hweak
   have hu := compactTensorPrimitive_memSobolev hφ U hgraph hχ hc
   exact weighted_polyharmonic_local_lift_of_zero (by omega : 1 ≤ r+1)
     (by simpa only [Nat.add_sub_cancel] using hu) a w hpde

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.compact_tower_weighted_polyharmonic_local_zero
#print axioms KLS.DeterministicBridgeIntegration.compact_tower_weighted_polyharmonic_local_gain
