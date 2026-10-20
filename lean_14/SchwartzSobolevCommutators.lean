import FiniteNegativeSobolev

/-! Local elliptic commutator estimates proved from actual multiplier
product rules and the first-derivative Sobolev characterization. Only the
original nonnegative Sobolev regularity of u is required. -/
noncomputable section
open MeasureTheory TemperedDistribution Set
open scoped ContDiff SchwartzMap LineDeriv Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLSBelow25
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 theorem tempered_coordinate_deriv_sub (i : Fin n) (u v : 𝓢'(Space n,ℂ)) :
     ∂_{EuclideanSpace.single i (1 : ℝ)} (u-v)=
       ∂_{EuclideanSpace.single i (1 : ℝ)} u-∂_{EuclideanSpace.single i (1 : ℝ)} v :=
   (LineDeriv.lineDerivOpCLM ℂ (𝓢'(Space n,ℂ)) (EuclideanSpace.single i (1 : ℝ))).map_sub u v

 theorem coordinateTemperedWord_append (I J : List (Fin n)) (u : 𝓢'(Space n,ℂ)) :
     coordinateTemperedWord (I++J) u=coordinateTemperedWord I (coordinateTemperedWord J u) :=
   temperedCoordinateWord_append _ I J u

 theorem schwartz_mul_memSobolev_nat (s : ℕ) {u : 𝓢'(Space n,ℂ)}
     (hu : MemSobolev (s : ℝ) 2 u) (g : 𝓢(Space n,ℂ)) :
     MemSobolev (s : ℝ) 2 (TemperedDistribution.smulLeftCLM ℂ g u) := by
   induction s generalizing u g with
   | zero =>
     obtain ⟨f,hf⟩ := memSobolev_zero_iff.mp (by simpa only [Nat.cast_zero] using hu)
     rw [hf]
     simpa only [Nat.cast_zero,neg_zero] using finiteL2DerivativeSpan_memSobolev
       (tempered_schwartz_mul_Lp_mem_span 0 g f)
   | succ s ih =>
     have hlow : MemSobolev (s : ℝ) 2 u := hu.mono (by push_cast; linarith)
     have hprod := ih hlow g
     have hd (i : Fin n) : MemSobolev (s : ℝ) 2
         (∂_{EuclideanSpace.basisFun (Fin n) ℝ i}
           (TemperedDistribution.smulLeftCLM ℂ g u)) := by
       rw [EuclideanSpace.basisFun_apply,tempered_lineDeriv_multiplier]
       have hdu : MemSobolev (s : ℝ) 2 (∂_{EuclideanSpace.single i (1 : ℝ)} u) := by
         convert hu.lineDerivOp (m := EuclideanSpace.single i (1 : ℝ)) using 1 <;> push_cast <;> ring
       exact (ih hdu g).add (ih hlow (∂_{EuclideanSpace.single i (1 : ℝ)} g))
     simpa only [Nat.cast_add,Nat.cast_one] using
       tempered_sobolev_first_derivatives_lift (EuclideanSpace.basisFun (Fin n) ℝ) hprod hd

 theorem schwartz_mul_coordinateWord_memSobolev (s : ℕ) {u : 𝓢'(Space n,ℂ)}
     (hu : MemSobolev (s : ℝ) 2 u) (I : List (Fin n)) (g : 𝓢(Space n,ℂ)) :
     MemSobolev ((s : ℝ)-(I.length : ℝ)) 2
       (TemperedDistribution.smulLeftCLM ℂ g (coordinateTemperedWord I u)) := by
   induction I generalizing g with
   | nil => simpa only [List.length_nil,Nat.cast_zero,sub_zero,
       coordinateTemperedWord,temperedCoordinateWord] using schwartz_mul_memSobolev_nat s hu g
   | cons i I ih =>
     have he : TemperedDistribution.smulLeftCLM ℂ g (coordinateTemperedWord (i::I) u)=
         ∂_{EuclideanSpace.single i (1 : ℝ)}
           (TemperedDistribution.smulLeftCLM ℂ g (coordinateTemperedWord I u))-
         TemperedDistribution.smulLeftCLM ℂ (∂_{EuclideanSpace.single i (1 : ℝ)} g : 𝓢(Space n,ℂ))
           (coordinateTemperedWord I u) := by
       rw [tempered_lineDeriv_multiplier]
       change _=_
       abel
     rw [he]
     have hd := (ih g).lineDerivOp (m := EuclideanSpace.single i (1 : ℝ))
     have hlo := (ih (∂_{EuclideanSpace.single i (1 : ℝ)} g)).mono
       (by linarith : (s : ℝ)-(I.length : ℝ)-1 ≤ (s : ℝ)-(I.length : ℝ))
     convert hd.sub hlo using 1 <;> simp only [List.length_cons,Nat.cast_add,Nat.cast_one] <;> ring

 def wordMultiplierCommutator (I J : List (Fin n)) (g : 𝓢(Space n,ℂ))
     (u : 𝓢'(Space n,ℂ)) : 𝓢'(Space n,ℂ) :=
   coordinateTemperedWord I (TemperedDistribution.smulLeftCLM ℂ g (coordinateTemperedWord J u))-
     TemperedDistribution.smulLeftCLM ℂ g (coordinateTemperedWord (I++J) u)

 theorem wordMultiplierCommutator_cons (I J : List (Fin n)) (i : Fin n)
     (g : 𝓢(Space n,ℂ)) (u : 𝓢'(Space n,ℂ)) :
     wordMultiplierCommutator (i::I) J g u=
       ∂_{EuclideanSpace.single i (1 : ℝ)} (wordMultiplierCommutator I J g u)+
         TemperedDistribution.smulLeftCLM ℂ
           (∂_{EuclideanSpace.single i (1 : ℝ)} g : 𝓢(Space n,ℂ))
           (coordinateTemperedWord (I++J) u) := by
   unfold wordMultiplierCommutator
   simp only [List.cons_append,coordinateTemperedWord,temperedCoordinateWord]
   rw [tempered_coordinate_deriv_sub,tempered_lineDeriv_multiplier]
   abel

 theorem schwartz_mul_wordCommutator_memSobolev (s : ℕ) {u : 𝓢'(Space n,ℂ)}
     (hu : MemSobolev (s : ℝ) 2 u) (I J : List (Fin n)) (a g : 𝓢(Space n,ℂ)) :
     MemSobolev ((s : ℝ)-(I.length : ℝ)-(J.length : ℝ)+1) 2
       (TemperedDistribution.smulLeftCLM ℂ a (wordMultiplierCommutator I J g u)) := by
   induction I generalizing a with
   | nil =>
     simp only [wordMultiplierCommutator,coordinateTemperedWord,temperedCoordinateWord,
       List.nil_append,sub_self,map_zero]
     exact memSobolev_fun_zero _ _ _ _
   | cons i I ih =>
     let v : Space n := EuclideanSpace.single i 1
     let dg : 𝓢(Space n,ℂ) := ∂_{v} g
     let da : 𝓢(Space n,ℂ) := ∂_{v} a
     let adg : 𝓢(Space n,ℂ) := SchwartzMap.smulLeftCLM ℂ a dg
     have hadg : (adg : Space n → ℂ)=(dg : Space n → ℂ)*(a : Space n → ℂ) := by
       funext x
       simp only [adg,SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth,Pi.mul_apply,
         smul_eq_mul]
       ring
     have he : TemperedDistribution.smulLeftCLM ℂ a (wordMultiplierCommutator (i::I) J g u)=
         ∂_{v} (TemperedDistribution.smulLeftCLM ℂ a (wordMultiplierCommutator I J g u))-
           TemperedDistribution.smulLeftCLM ℂ da (wordMultiplierCommutator I J g u)+
           TemperedDistribution.smulLeftCLM ℂ adg (coordinateTemperedWord (I++J) u) := by
       rw [wordMultiplierCommutator_cons,map_add]
       change _=_
       rw [tempered_lineDeriv_multiplier]
       rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply dg.hasTemperateGrowth a.hasTemperateGrowth,
         ←hadg]
       abel
     rw [he]
     have h1 := (ih a).lineDerivOp (m := v)
     simp only [add_sub_cancel_right] at h1
     have h2 := (ih da).mono
       (by linarith : (s : ℝ)-(I.length : ℝ)-(J.length : ℝ) ≤
         (s : ℝ)-(I.length : ℝ)-(J.length : ℝ)+1)
     have h3 := schwartz_mul_coordinateWord_memSobolev s hu (I++J) adg
     have h3' : MemSobolev ((s : ℝ)-(I.length : ℝ)-(J.length : ℝ)) 2
         (TemperedDistribution.smulLeftCLM ℂ adg (coordinateTemperedWord (I++J) u)) := by
       convert h3 using 1 <;> simp only [List.length_append,Nat.cast_add] <;> ring
     have hout := (h1.sub h2).add h3'
     convert hout using 1 <;> simp only [List.length_cons,Nat.cast_add,Nat.cast_one] <;> ring

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.schwartz_mul_memSobolev_nat
#print axioms KLS.DeterministicBridgeIntegration.schwartz_mul_coordinateWord_memSobolev
#print axioms KLS.DeterministicBridgeIntegration.schwartz_mul_wordCommutator_memSobolev
