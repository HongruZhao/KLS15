import WeightedPolyharmonicLocalization

/-! Test evaluation and locality for the actual ordered weighted
polyharmonic distribution operator and the genuine lower weak-jet tower. -/
noncomputable section
open MeasureTheory TemperedDistribution Set Filter
open scoped ContDiff SchwartzMap LineDeriv Laplacian Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLSBelow25
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
variable {n s : ℕ} {φ : Space n → ℝ}

 def schwartzCoordinateWord : List (Fin n) → 𝓢(Space n,ℂ) → 𝓢(Space n,ℂ)
   | [],ψ => ψ
   | i::I,ψ => ∂_{EuclideanSpace.single i (1 : ℝ)} (schwartzCoordinateWord I ψ)

 theorem schwartzCoordinateWord_lineDeriv (I : List (Fin n)) (ψ : 𝓢(Space n,ℂ)) (v : Space n) :
     schwartzCoordinateWord I (∂_{v} ψ)=∂_{v} (schwartzCoordinateWord I ψ) := by
   induction I with
   | nil => rfl
   | cons i I ih => simp only [schwartzCoordinateWord,ih]; rw [schwartz_lineDeriv_comm]

 theorem schwartzCoordinateWord_tsupport_subset (I : List (Fin n)) (ψ : 𝓢(Space n,ℂ)) :
     tsupport (schwartzCoordinateWord I ψ) ⊆ tsupport ψ := by
   induction I with
   | nil => exact subset_rfl
   | cons i I ih => exact (SchwartzMap.tsupport_lineDerivOp_subset _ _).trans ih

 theorem coordinateTemperedWord_apply (I : List (Fin n)) (u : 𝓢'(Space n,ℂ)) (ψ : 𝓢(Space n,ℂ)) :
     coordinateTemperedWord I u ψ=(-1 : ℂ)^I.length*u (schwartzCoordinateWord I ψ) := by
   induction I generalizing ψ with
   | nil => simp only [coordinateTemperedWord,temperedCoordinateWord,schwartzCoordinateWord,
       List.length_nil,pow_zero,one_mul]
   | cons i I ih =>
     rw [coordinateTemperedWord_cons,TemperedDistribution.lineDerivOp_apply_apply,map_neg,ih,
       schwartzCoordinateWord_lineDeriv]
     simp only [List.length_cons,pow_succ,schwartzCoordinateWord]
     ring

 theorem compactWeightedTempered_apply_integral (hφ : Continuous φ) {χ : Space n → ℝ}
     (hχ : Continuous χ) (hc : HasCompactSupport χ) (u : Lp ℝ 2 (potentialMeasure φ))
     (ψ : 𝓢(Space n,ℂ)) :
     compactWeightedTempered hφ hχ hc u ψ=∫ x, ψ x*(χ x*u x : ℝ) := by
   rw [compactWeightedTempered,Lp.toTemperedDistribution_apply]
   apply integral_congr_ae
   filter_upwards [realMemLpToComplex_coe (memLp_compact_mul_weighted_to_volume hφ hχ hc u)] with x hx
   simp only [hx,smul_eq_mul]

 theorem compactWeightedTempered_derivative_cutoff_test_zero
     (hφ : ContDiff ℝ 1 φ) {χ : Space n → ℝ}
     (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
     (u : Lp ℝ 2 (potentialMeasure φ)) (i : Fin n) (ψ : 𝓢(Space n,ℂ))
     (hcut : ∀ x ∈ tsupport ψ, χ =ᶠ[𝓝 x] fun _ => (1 : ℝ)) :
     compactWeightedTempered hφ.continuous
       (contDiff_coordinateDerivative hχ (m := 0) (by simp) i).continuous
       (hasCompactSupport_coordinateDerivative hc i) u ψ=0 := by
   rw [compactWeightedTempered_apply_integral]
   apply integral_eq_zero_of_ae
   filter_upwards with x
   by_cases hx : x ∈ tsupport ψ
   · have hd : coordinateDerivative χ i x=0 := by
       unfold coordinateDerivative
       rw [(hcut x hx).fderiv_eq]
       simp
     simp [hd]
   · simp [image_eq_zero_of_notMem_tsupport hx]

 theorem compactTensorWordTempered_apply_local_word
     (hφ : ContDiff ℝ 1 φ) (U : (k : ℕ) → OrderedTensorField φ k)
     (hgraph : ∀ k, k < s → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
       finitePrimitiveValue (OrderedTensorIndex n k) V=U k ∧
         ∀ I i, weightedH1Derivative φ i (V I)=U (k+1) (Fin.cons i I))
     (I L : List (Fin n)) (hIL : I.length+L.length ≤ s)
     {χ : Space n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
     (ψ : 𝓢(Space n,ℂ)) (hcut : ∀ x ∈ tsupport ψ, χ =ᶠ[𝓝 x] fun _ => (1 : ℝ)) :
     coordinateTemperedWord I
       (compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U L)) ψ=
     compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U (I++L)) ψ := by
   induction I generalizing ψ with
   | nil => rfl
   | cons i I ih =>
     rw [coordinateTemperedWord_cons,TemperedDistribution.lineDerivOp_apply_apply,map_neg]
     rw [ih (by simp only [List.length_cons] at hIL; omega) _
       (fun x hx => hcut x (SchwartzMap.tsupport_lineDerivOp_subset (EuclideanSpace.single i (1 : ℝ)) ψ hx))]
     have he := congrArg (fun T : 𝓢'(Space n,ℂ) => T ψ)
       (compactTensorWordTempered_lineDeriv hφ U hgraph (I++L)
         (by simp only [List.length_cons] at hIL; simp only [List.length_append]; omega) i
         (hχ.of_le (by simp)) hc)
     simp only [TemperedDistribution.lineDerivOp_apply_apply,map_neg,add_apply] at he
     rw [compactWeightedTempered_derivative_cutoff_test_zero hφ hχ hc _ i ψ hcut,add_zero] at he
     exact he

 theorem compactTensorWordTempered_apply_local_integral
     (hφ : ContDiff ℝ 1 φ) (U : (k : ℕ) → OrderedTensorField φ k)
     (hgraph : ∀ k, k < s → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
       finitePrimitiveValue (OrderedTensorIndex n k) V=U k ∧
         ∀ I i, weightedH1Derivative φ i (V I)=U (k+1) (Fin.cons i I))
     (I L : List (Fin n)) (hIL : I.length+L.length ≤ s)
     {χ : Space n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
     (ψ : 𝓢(Space n,ℂ)) (hcut : ∀ x ∈ tsupport ψ, χ =ᶠ[𝓝 x] fun _ => (1 : ℝ)) :
     coordinateTemperedWord I
       (compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U L)) ψ=
       ∫ x, ψ x*(tensorWordLp U (I++L) x : ℂ) := by
   rw [compactTensorWordTempered_apply_local_word hφ U hgraph I L hIL hχ hc ψ hcut,
     compactWeightedTempered_apply_integral]
   apply integral_congr_ae
   filter_upwards with x
   by_cases hx : x ∈ tsupport ψ
   · rw [(hcut x hx).eq_of_nhds,one_mul]
   · simp [image_eq_zero_of_notMem_tsupport hx]

 def weightedPolyharmonicAdjointTest (w : 𝓢(Space n,ℂ)) (i : Fin n)
     (I : List (Fin n)) (ψ : 𝓢(Space n,ℂ)) : 𝓢(Space n,ℂ) :=
   ∂_{EuclideanSpace.single i (1 : ℝ)}
     (SchwartzMap.smulLeftCLM ℂ w (∂_{EuclideanSpace.single i (1 : ℝ)} (schwartzCoordinateWord I ψ)))

 theorem weightedPolyharmonicAdjointTest_tsupport (w : 𝓢(Space n,ℂ)) (i : Fin n)
     (I : List (Fin n)) (ψ : 𝓢(Space n,ℂ)) :
     tsupport (weightedPolyharmonicAdjointTest w i I ψ) ⊆ tsupport ψ := by
   exact (SchwartzMap.tsupport_lineDerivOp_subset _ _).trans
     ((SchwartzMap.tsupport_smulLeftCLM_subset _ _).trans inter_subset_left |>.trans
       ((SchwartzMap.tsupport_lineDerivOp_subset _ _).trans (schwartzCoordinateWord_tsupport_subset I ψ)))

 theorem weightedOrderedPolyharmonic_apply (r : ℕ) (w : 𝓢(Space n,ℂ))
     (u : 𝓢'(Space n,ℂ)) (ψ : 𝓢(Space n,ℂ)) :
     weightedOrderedPolyharmonic (r+1) w u ψ=(-1 : ℂ)^(r+2)*
       ∑ i : Fin n, ∑ I : Fin r → Fin n,
         coordinateTemperedWord (List.ofFn I) u
           (weightedPolyharmonicAdjointTest w i (List.ofFn I) ψ) := by
   have houter (I : Fin (r+1) → Fin n) :
       coordinateTemperedWord (List.ofFn I)
         (TemperedDistribution.smulLeftCLM ℂ w (coordinateTemperedWord (List.ofFn I) u)) ψ=
       (-1 : ℂ)^(r+1)*coordinateTemperedWord (List.ofFn I) u
         (SchwartzMap.smulLeftCLM ℂ w (schwartzCoordinateWord (List.ofFn I) ψ)) := by
     rw [coordinateTemperedWord_apply]
     simp only [List.length_ofFn,TemperedDistribution.smulLeftCLM_apply_apply]
   rw [weightedOrderedPolyharmonic]
   simp only [sum_apply,houter]
   rw [←(Fin.consEquiv (fun _ : Fin (r+1) => Fin n)).sum_comp
     (fun I : Fin (r+1) → Fin n =>
       (-1 : ℂ)^(r+1)*coordinateTemperedWord (List.ofFn I) u
         (SchwartzMap.smulLeftCLM ℂ w (schwartzCoordinateWord (List.ofFn I) ψ))),
       Fintype.sum_prod_type,Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro i hi
   rw [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro I hI
   simp only [Fin.consEquiv_apply,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,
     coordinateTemperedWord_cons,schwartzCoordinateWord,
     TemperedDistribution.lineDerivOp_apply_apply,map_neg,weightedPolyharmonicAdjointTest,
     show r+2=(r+1)+1 by omega,pow_succ]
   ring

 theorem weightedOrderedPolyharmonic_compact_tower_apply
     (hφ : ContDiff ℝ 1 φ) (U : (k : ℕ) → OrderedTensorField φ k)
     (hgraph : ∀ k, k < s → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
       finitePrimitiveValue (OrderedTensorIndex n k) V=U k ∧
         ∀ I i, weightedH1Derivative φ i (V I)=U (k+1) (Fin.cons i I))
     {r : ℕ} (hr : r ≤ s) {χ : Space n → ℝ}
     (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
     (w : 𝓢(Space n,ℂ)) (ψ : 𝓢(Space n,ℂ))
     (hcut : ∀ x ∈ tsupport ψ, χ =ᶠ[𝓝 x] fun _ => (1 : ℝ)) :
     weightedOrderedPolyharmonic (r+1) w
       (compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U [])) ψ=
       (-1 : ℂ)^(r+2)*∑ i : Fin n, ∑ I : Fin r → Fin n,
         ∫ x, weightedPolyharmonicAdjointTest w i (List.ofFn I) ψ x*
           (tensorWordLp U (List.ofFn I) x : ℂ) := by
   rw [weightedOrderedPolyharmonic_apply]
   congr 1
   apply Finset.sum_congr rfl
   intro i hi
   apply Finset.sum_congr rfl
   intro I hI
   have he := compactTensorWordTempered_apply_local_integral hφ U hgraph (List.ofFn I) []
     (by simpa only [List.length_ofFn,List.length_nil,add_zero] using hr) hχ hc
     (weightedPolyharmonicAdjointTest w i (List.ofFn I) ψ)
     (fun x hx => hcut x (weightedPolyharmonicAdjointTest_tsupport w i _ ψ hx))
   simpa only [List.append_nil] using he

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.coordinateTemperedWord_apply
#print axioms KLS.DeterministicBridgeIntegration.compactTensorWordTempered_apply_local_integral
#print axioms KLS.DeterministicBridgeIntegration.weightedOrderedPolyharmonic_compact_tower_apply
