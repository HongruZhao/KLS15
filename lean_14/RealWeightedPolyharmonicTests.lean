import WeightedPolyharmonicLocalEquation
import ProjectedDivergenceWeakEquation
import GlobalTensorCutoffLimit

/-! Literal real/imaginary conversion of the original real compact weak
equation to the local complex tempered operator equation. -/
noncomputable section
open MeasureTheory TemperedDistribution Set Filter
open scoped ContDiff SchwartzMap LineDeriv Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLSBelow25 KLS.DeterministicBridgeNext
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
variable {n r : ℕ} {φ : Space n → ℝ}

 theorem schwartz_lineDeriv_real_projection (L : ℂ →L[ℝ] ℝ) (ψ : 𝓢(Space n,ℂ))
     (i : Fin n) (x : Space n) :
     L ((∂_{EuclideanSpace.single i (1 : ℝ)} ψ : 𝓢(Space n,ℂ)) x)=
       coordinateDerivative (fun y => L (ψ y)) i x := by
   rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
   unfold coordinateDerivative
   change L (fderiv ℝ (ψ : Space n → ℂ) x (EuclideanSpace.single i 1)) =
     fderiv ℝ (L ∘ (ψ : Space n → ℂ)) x (EuclideanSpace.single i 1)
   rw [(L.hasFDerivAt.comp x ψ.differentiableAt.hasFDerivAt).fderiv]
   rfl

 theorem schwartzCoordinateWord_real_projection (L : ℂ →L[ℝ] ℝ)
     (I : List (Fin n)) (ψ : 𝓢(Space n,ℂ)) (x : Space n) :
     L (schwartzCoordinateWord I ψ x)=
       directionalWordDerivative (fun y => L (ψ y)) (I.map (fun i => EuclideanSpace.single i 1)) x := by
   induction I generalizing x with
   | nil => rfl
   | cons i I ih =>
     rw [schwartzCoordinateWord,schwartz_lineDeriv_real_projection]
     have he : (fun y => L (schwartzCoordinateWord I ψ y))=
         directionalWordDerivative (fun y => L (ψ y)) (I.map (fun i => EuclideanSpace.single i 1)) := funext ih
     rw [he]
     rfl

 theorem coordinatePotentialTensor_tsupport_subset (f : Space n → ℝ) (d : ℕ)
     (I : OrderedTensorIndex n d) : tsupport (coordinatePotentialTensor f d I) ⊆ tsupport f := by
   induction d with
   | zero => exact subset_rfl
   | succ d ih =>
     rw [←Fin.cons_self_tail I,coordinatePotentialTensor_cons]
     exact (tsupport_coordinateDerivative_subset _ _).trans (ih (Fin.tail I))

 theorem weightedPolyharmonicAdjointTest_real_projection
     (L : ℂ →L[ℝ] ℝ) (w : 𝓢(Space n,ℂ)) (ψ : 𝓢(Space n,ℂ))
     (hw : ∀ x ∈ tsupport ψ, (w : Space n → ℂ) =ᶠ[𝓝 x]
       fun y => (Real.exp (-φ y) : ℂ)) (i : Fin n) (I : Fin r → Fin n) (x : Space n) :
     L (weightedPolyharmonicAdjointTest w i (List.ofFn I) ψ x)=
       coordinateDerivative
         (fun y => Real.exp (-φ y)*coordinatePotentialTensor (fun z => L (ψ z)) (r+1) (Fin.cons i I) y) i x := by
   by_cases hx : x ∈ tsupport ψ
   · rw [weightedPolyharmonicAdjointTest,schwartz_lineDeriv_real_projection]
     have he : (fun y => L ((SchwartzMap.smulLeftCLM ℂ w
         (∂_{EuclideanSpace.single i (1 : ℝ)} (schwartzCoordinateWord (List.ofFn I) ψ))) y)) =ᶠ[𝓝 x]
         fun y => Real.exp (-φ y)*coordinatePotentialTensor (fun z => L (ψ z)) (r+1) (Fin.cons i I) y := by
       filter_upwards [hw x hx] with y hy
       rw [SchwartzMap.smulLeftCLM_apply_apply w.hasTemperateGrowth,hy]
       change L ((Real.exp (-φ y)) • ((∂_{EuclideanSpace.single i (1 : ℝ)}
         (schwartzCoordinateWord (List.ofFn I) ψ) : 𝓢(Space n,ℂ)) y))=_
       rw [map_smul,smul_eq_mul,schwartz_lineDeriv_real_projection,coordinatePotentialTensor_cons]
       have hword : (fun z => L (schwartzCoordinateWord (List.ofFn I) ψ z))=
           coordinatePotentialTensor (fun z => L (ψ z)) r I :=
         funext (schwartzCoordinateWord_real_projection L (List.ofFn I) ψ)
       rw [hword]
     exact congrArg (fun D : Space n →L[ℝ] ℝ => D (EuclideanSpace.single i 1)) he.fderiv_eq
   · have hz : weightedPolyharmonicAdjointTest w i (List.ofFn I) ψ x=0 :=
       image_eq_zero_of_notMem_tsupport (fun h => hx (weightedPolyharmonicAdjointTest_tsupport w i _ ψ h))
     rw [hz,map_zero]
     have hsupport : tsupport (coordinateDerivative
         (fun y => Real.exp (-φ y)*coordinatePotentialTensor (fun z => L (ψ z)) (r+1) (Fin.cons i I) y) i)
         ⊆ tsupport ψ :=
       (tsupport_coordinateDerivative_subset _ _).trans
         (tsupport_mul_subset_right.trans ((coordinatePotentialTensor_tsupport_subset _ _ _).trans
           (tsupport_comp_subset (map_zero L) ψ)))
     exact (image_eq_zero_of_notMem_tsupport (fun h => hx (hsupport h))).symm

 theorem integrable_schwartz_mul_weightedLp_compact (hφ : Continuous φ)
     (u : Lp ℝ 2 (potentialMeasure φ)) (ψ : 𝓢(Space n,ℂ)) (hc : HasCompactSupport ψ) :
     Integrable (fun x => ψ x*(u x : ℂ)) volume := by
   have hu : MemLp ((tsupport ψ).indicator (u : Space n → ℝ)) 2 volume :=
     (memLp_indicator_iff_restrict hc.measurableSet.nullMeasurableSet).mpr
       (KLS.MemLp.restrict_volume_of_potentialMeasure (Lp.memLp u) hφ hc)
   have hi := (ψ.memLp 2 volume).integrable_mul hu.ofReal
   apply hi.congr
   filter_upwards with x
   change ψ x * (((tsupport ψ).indicator (u : Space n → ℝ) x : ℝ) : ℂ) = ψ x * (u x : ℂ)
   by_cases hx : x ∈ tsupport ψ
   · rw [indicator_of_mem hx]
   · simp [image_eq_zero_of_notMem_tsupport hx]

 theorem real_weighted_weak_equation_complexifies
     (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (U : OrderedTensorField φ r)
     (hweak : ∀ (η : Space n → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
       (∑ I : Fin r → Fin n, ∑ i : Fin n, ∫ x, U I x*coordinateDerivative
         (fun y => Real.exp (-φ y)*coordinatePotentialTensor η (r+1) (Fin.cons i I) y) i x)=0)
     (w : 𝓢(Space n,ℂ)) (ψ : 𝓢(Space n,ℂ)) (hc : HasCompactSupport ψ)
     (hw : ∀ x ∈ tsupport ψ, (w : Space n → ℂ) =ᶠ[𝓝 x]
       fun y => (Real.exp (-φ y) : ℂ)) :
     (∑ i : Fin n, ∑ I : Fin r → Fin n,
       ∫ x, weightedPolyharmonicAdjointTest w i (List.ofFn I) ψ x*(U I x : ℂ))=0 := by
   have hproj (L : ℂ →L[ℝ] ℝ) : L
       (∑ i : Fin n, ∑ I : Fin r → Fin n,
         ∫ x, weightedPolyharmonicAdjointTest w i (List.ofFn I) ψ x*(U I x : ℂ))=0 := by
     have hη : ContDiff ℝ (⊤ : ℕ∞) (fun y => L (ψ y)) := L.contDiff.comp (ψ.smooth (⊤ : ℕ∞))
     have hcη : HasCompactSupport (fun y => L (ψ y)) := hc.comp_left (map_zero L)
     have hz := hweak _ hη hcη
     rw [Finset.sum_comm] at hz
     rw [map_sum]
     simp only [map_sum]
     convert hz using 1
     apply Finset.sum_congr rfl
     intro i hi
     apply Finset.sum_congr rfl
     intro I hI
     rw [←L.integral_comp_comm (integrable_schwartz_mul_weightedLp_compact hφ.continuous (U I)
       (weightedPolyharmonicAdjointTest w i (List.ofFn I) ψ)
       (hc.of_isClosed_subset (isClosed_tsupport _) (weightedPolyharmonicAdjointTest_tsupport w i _ ψ)))]
     apply integral_congr_ae
     filter_upwards with x
     rw [mul_comm (weightedPolyharmonicAdjointTest w i (List.ofFn I) ψ x)]
     change L ((U I x) • weightedPolyharmonicAdjointTest w i (List.ofFn I) ψ x)=_
     rw [map_smul,smul_eq_mul,weightedPolyharmonicAdjointTest_real_projection L w ψ hw i I x]
   apply Complex.ext
   · exact hproj Complex.reCLM
   · exact hproj Complex.imCLM

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.weightedPolyharmonicAdjointTest_real_projection
#print axioms KLS.DeterministicBridgeIntegration.real_weighted_weak_equation_complexifies
