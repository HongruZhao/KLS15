import RealWeightedPolyharmonicTests

/-! Genuine local elliptic gain for the primitive of an orthogonal
compatible tensor. The only equation used is the original compact real
weak equation, not an assumed Sobolev or distributional PDE. -/
noncomputable section
open MeasureTheory TemperedDistribution Set Filter Metric
open scoped ContDiff SchwartzMap LineDeriv Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLSBelow25 KLS.DeterministicBridgeNext
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
variable {n r : ℕ} {φ : Space n → ℝ}

 theorem compact_tower_real_weak_equation_local_gain
     (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (U : (k : ℕ) → OrderedTensorField φ k)
     (hgraph : ∀ k, k < r → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
       finitePrimitiveValue (OrderedTensorIndex n k) V=U k ∧
         ∀ I i, weightedH1Derivative φ i (V I)=U (k+1) (Fin.cons i I))
     (hweak : ∀ (η : Space n → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
       (∑ I : Fin r → Fin n, ∑ i : Fin n, ∫ x, U r I x*coordinateDerivative
         (fun y => Real.exp (-φ y)*coordinatePotentialTensor η (r+1) (Fin.cons i I) y) i x)=0)
     {ζ : Space n → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hcζ : HasCompactSupport ζ) :
     MemSobolev ((r+1 : ℕ) : ℝ) 2
       (compactWeightedTempered hφ.continuous hζ.continuous hcζ (tensorWordLp U [])) := by
   obtain ⟨R,hR,hKR⟩ := hcζ.isBounded.subset_ball_lt 0 (0 : Space n)
   let χ : ContDiffBump (0 : Space n) := ⟨R,R+1,hR,by linarith⟩
   have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := χ.contDiff
   have hχone (x : Space n) (hx : x ∈ tsupport ζ) : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
     χ.eventuallyEq_one_of_mem_ball (hKR hx)
   have hA : ContDiff ℝ (⊤ : ℕ∞) (fun x => ζ x*Real.exp (φ x)) := hζ.mul hφ.exp
   have hcA : HasCompactSupport (fun x => ζ x*Real.exp (φ x)) := hcζ.mul_right
   have hAc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((ζ x*Real.exp (φ x) : ℝ) : ℂ)) :=
     Complex.ofRealCLM.contDiff.comp hA
   have hcAc : HasCompactSupport (fun x => ((ζ x*Real.exp (φ x) : ℝ) : ℂ)) := hcA.comp_left (g := fun t : ℝ => (t : ℂ)) rfl
   let a : 𝓢(Space n,ℂ) := hcAc.toSchwartzMap hAc
   have hW : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x*Real.exp (-φ x)) := hχ.mul hφ.neg.exp
   have hcW : HasCompactSupport (fun x => χ x*Real.exp (-φ x)) := χ.hasCompactSupport.mul_right
   have hWc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((χ x*Real.exp (-φ x) : ℝ) : ℂ)) :=
     Complex.ofRealCLM.contDiff.comp hW
   have hcWc : HasCompactSupport (fun x => ((χ x*Real.exp (-φ x) : ℝ) : ℂ)) := hcW.comp_left (g := fun t : ℝ => (t : ℂ)) rfl
   let w : 𝓢(Space n,ℂ) := hcWc.toSchwartzMap hWc
   have has : tsupport a ⊆ tsupport ζ :=
     (tsupport_comp_subset (g := fun t : ℝ => (t : ℂ)) rfl (fun x => ζ x*Real.exp (φ x))).trans tsupport_mul_subset_left
   have hcut : ∀ x ∈ tsupport a, χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
     fun x hx => hχone x (has hx)
   have hweakC (ψ : 𝓢(Space n,ℂ)) (hs : tsupport ψ ⊆ tsupport a) :
       (∑ i : Fin n, ∑ I : Fin r → Fin n,
         ∫ x, weightedPolyharmonicAdjointTest w i (List.ofFn I) ψ x*
           (tensorWordLp U (List.ofFn I) x : ℂ))=0 := by
     simp only [tensorWordLp_ofFn]
     apply real_weighted_weak_equation_complexifies hφ (U r) hweak w ψ
       (hcAc.of_isClosed_subset (isClosed_tsupport _) hs)
     intro x hx
     filter_upwards [hcut x (hs hx)] with y hy
     change ((χ y*Real.exp (-φ y) : ℝ) : ℂ)=(Real.exp (-φ y) : ℂ)
     rw [hy,one_mul]
   have hg := compact_tower_weighted_polyharmonic_local_gain (hφ.of_le (by simp))
     U hgraph hχ χ.hasCompactSupport a w hcut hweakC
   have he : TemperedDistribution.smulLeftCLM ℂ (schwartzProduct a w)
       (compactWeightedTempered hφ.continuous hχ.continuous χ.hasCompactSupport (tensorWordLp U []))=
       compactWeightedTempered hφ.continuous hζ.continuous hcζ (tensorWordLp U []) := by
     ext ψ
     rw [TemperedDistribution.smulLeftCLM_apply_apply,compactWeightedTempered_apply_integral,
       compactWeightedTempered_apply_integral]
     apply integral_congr_ae
     filter_upwards with x
     rw [SchwartzMap.smulLeftCLM_apply_apply (schwartzProduct a w).hasTemperateGrowth]
     simp only [schwartzProduct_coe,Pi.mul_apply,smul_eq_mul]
     change (((χ x*Real.exp (-φ x) : ℝ) : ℂ)*((ζ x*Real.exp (φ x) : ℝ) : ℂ))*ψ x*
       ((χ x*tensorWordLp U [] x : ℝ) : ℂ) = ψ x*((ζ x*tensorWordLp U [] x : ℝ) : ℂ)
     by_cases hx : ζ x=0
     · simp [hx]
     · have hxs : x ∈ tsupport ζ := subset_closure hx
       rw [(hχone x hxs).eq_of_nhds]
       simp only [one_mul,Real.exp_neg,Complex.ofReal_mul,Complex.ofReal_inv]
       have hne : (Real.exp (φ x) : ℂ)≠0 := by exact_mod_cast Real.exp_ne_zero (φ x)
       field_simp
   rw [he] at hg
   exact hg

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.compact_tower_real_weak_equation_local_gain
