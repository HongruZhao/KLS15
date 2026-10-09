import LocalizedTensorSobolev

/-! Explicit finite derivative representations for negative integer Sobolev
orders. Smooth multipliers are handled by their actual Leibniz expansions,
not by an assumed negative-Sobolev multiplier theorem. -/
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

 def coordinateTemperedWord (I : List (Fin n)) (u : 𝓢'(Space n,ℂ)) : 𝓢'(Space n,ℂ) :=
   temperedCoordinateWord (fun i => EuclideanSpace.single i (1 : ℝ)) I u

 def finiteL2DerivativeSpan (q : ℕ) : Submodule ℂ (𝓢'(Space n,ℂ)) :=
   Submodule.span ℂ {u | ∃ (I : List (Fin n)), I.length ≤ q ∧
     ∃ f : Lp ℂ 2 (volume : Measure (Space n)), u=coordinateTemperedWord I f}

 theorem finiteL2DerivativeSpan_mono {p q : ℕ} (hpq : p ≤ q) :
     (finiteL2DerivativeSpan (n := n) p) ≤ finiteL2DerivativeSpan q := by
   apply Submodule.span_mono
   rintro u ⟨I,hI,f,rfl⟩
   exact ⟨I,hI.trans hpq,f,rfl⟩

 theorem finiteL2DerivativeSpan_mem_Lp (q : ℕ) (f : Lp ℂ 2 (volume : Measure (Space n))) :
     (f : 𝓢'(Space n,ℂ)) ∈ finiteL2DerivativeSpan q :=
   Submodule.subset_span ⟨[],by simp,f,rfl⟩

 theorem finiteL2DerivativeSpan_lineDeriv {q : ℕ} {u : 𝓢'(Space n,ℂ)}
     (hu : u ∈ finiteL2DerivativeSpan q) (i : Fin n) :
     ∂_{EuclideanSpace.single i (1 : ℝ)} u ∈ finiteL2DerivativeSpan (q+1) := by
   have h : finiteL2DerivativeSpan (n := n) q ≤
       (finiteL2DerivativeSpan (q+1)).comap
         (LineDeriv.lineDerivOpCLM ℂ (𝓢'(Space n,ℂ)) (EuclideanSpace.single i (1 : ℝ))).toLinearMap := by
     apply Submodule.span_le.mpr
     rintro v ⟨I,hI,f,rfl⟩
     exact Submodule.subset_span ⟨i::I,by simp only [List.length_cons]; omega,f,rfl⟩
   exact h hu

 theorem coordinateTemperedWord_memSobolev {s : ℝ} {u : 𝓢'(Space n,ℂ)}
     (hu : MemSobolev s 2 u) (I : List (Fin n)) :
     MemSobolev (s-(I.length : ℝ)) 2 (coordinateTemperedWord I u) := by
   induction I with
   | nil => simpa only [coordinateTemperedWord,temperedCoordinateWord,List.length_nil,
       Nat.cast_zero,sub_zero] using hu
   | cons i I ih =>
     have hd := ih.lineDerivOp (m := EuclideanSpace.single i (1 : ℝ))
     convert hd using 1 <;> simp only [List.length_cons,Nat.cast_add,Nat.cast_one,
       coordinateTemperedWord,temperedCoordinateWord] <;> ring

 def integerSobolevSubmodule (s : ℝ) : Submodule ℂ (𝓢'(Space n,ℂ)) where
   carrier := {u | MemSobolev s 2 u}
   zero_mem' := memSobolev_fun_zero _ _ s 2
   add_mem' := fun hu hv => hu.add hv
   smul_mem' := fun c u hu => MemSobolev.smul c hu

 theorem finiteL2DerivativeSpan_memSobolev {q : ℕ} {u : 𝓢'(Space n,ℂ)}
     (hu : u ∈ finiteL2DerivativeSpan q) : MemSobolev (-(q : ℝ)) 2 u := by
   have h : finiteL2DerivativeSpan (n := n) q ≤ integerSobolevSubmodule (-(q : ℝ)) := by
     apply Submodule.span_le.mpr
     rintro v ⟨I,hI,f,rfl⟩
     have hf : MemSobolev 0 2 (f : 𝓢'(Space n,ℂ)) :=
       memSobolev_zero_iff.mpr ⟨f,rfl⟩
     have hd := coordinateTemperedWord_memSobolev hf I
     have hcast : (I.length : ℝ) ≤ q := by exact_mod_cast hI
     exact hd.mono (by linarith)
   exact h hu

 theorem schwartz_lineDeriv_multiplier (g ψ : 𝓢(Space n,ℂ)) (v : Space n) :
     ∂_{v} (SchwartzMap.smulLeftCLM ℂ g ψ) =
       SchwartzMap.smulLeftCLM ℂ (∂_{v} g : 𝓢(Space n,ℂ)) ψ+
         SchwartzMap.smulLeftCLM ℂ g (∂_{v} ψ) := by
   ext x
   rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
   rw [SchwartzMap.smulLeftCLM_apply g.hasTemperateGrowth]
   simp only [smul_eq_mul]
   rw [fderiv_fun_mul (𝕜 := ℝ) (c := (g : Space n → ℂ)) (d := (ψ : Space n → ℂ)) (x := x) g.differentiableAt ψ.differentiableAt]
   simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
     smul_eq_mul,SchwartzMap.add_apply,
     SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,
     SchwartzMap.smulLeftCLM_apply_apply (∂_{v} g : 𝓢(Space n,ℂ)).hasTemperateGrowth,
     SchwartzMap.lineDerivOp_apply_eq_fderiv]
   ring

 theorem tempered_lineDeriv_multiplier (g : 𝓢(Space n,ℂ)) (u : 𝓢'(Space n,ℂ)) (v : Space n) :
     ∂_{v} (TemperedDistribution.smulLeftCLM ℂ g u) =
       TemperedDistribution.smulLeftCLM ℂ g (∂_{v} u)+
         TemperedDistribution.smulLeftCLM ℂ (∂_{v} g : 𝓢(Space n,ℂ)) u := by
   ext ψ
   simp only [TemperedDistribution.lineDerivOp_apply_apply,
     TemperedDistribution.smulLeftCLM_apply_apply,ContinuousLinearMap.add_apply]
   rw [schwartz_lineDeriv_multiplier]
   simp only [map_add,map_neg]
   abel

 theorem tempered_schwartz_mul_Lp_mem_span (q : ℕ) (g : 𝓢(Space n,ℂ))
     (f : Lp ℂ 2 (volume : Measure (Space n))) :
     TemperedDistribution.smulLeftCLM ℂ g (f : 𝓢'(Space n,ℂ)) ∈ finiteL2DerivativeSpan q := by
   have hg : MemLp g (⊤ : ENNReal) (volume : Measure (Space n)) := g.memLp (⊤ : ENNReal) volume
   rw [←Lp.toTemperedDistribution_smul_eq (p := ⊤) (q := 2) (r := 2) g.hasTemperateGrowth hg f]
   exact finiteL2DerivativeSpan_mem_Lp q _

 theorem tempered_schwartz_mul_word_mem_span (g : 𝓢(Space n,ℂ))
     (I : List (Fin n)) (f : Lp ℂ 2 (volume : Measure (Space n))) :
     TemperedDistribution.smulLeftCLM ℂ g (coordinateTemperedWord I f) ∈
       finiteL2DerivativeSpan I.length := by
   induction I generalizing g with
   | nil => exact tempered_schwartz_mul_Lp_mem_span 0 g f
   | cons i I ih =>
     have hprod := tempered_lineDeriv_multiplier g (coordinateTemperedWord I f)
       (EuclideanSpace.single i (1 : ℝ))
     have he : TemperedDistribution.smulLeftCLM ℂ g
         (coordinateTemperedWord (i::I) f) =
       ∂_{EuclideanSpace.single i (1 : ℝ)}
           (TemperedDistribution.smulLeftCLM ℂ g (coordinateTemperedWord I f))-
         TemperedDistribution.smulLeftCLM ℂ
           (∂_{EuclideanSpace.single i (1 : ℝ)} g : 𝓢(Space n,ℂ))
           (coordinateTemperedWord I f) := by
       change _=_ at hprod
       change _=_
       rw [hprod]
       abel
     rw [he]
     exact (finiteL2DerivativeSpan _).sub_mem (finiteL2DerivativeSpan_lineDeriv (ih g) i)
       (finiteL2DerivativeSpan_mono (by simp only [List.length_cons]; omega : I.length ≤ (i::I).length)
         (ih (∂_{EuclideanSpace.single i (1 : ℝ)} g)))

 theorem finiteL2DerivativeSpan_schwartz_mul {q : ℕ} {u : 𝓢'(Space n,ℂ)}
     (hu : u ∈ finiteL2DerivativeSpan q) (g : 𝓢(Space n,ℂ)) :
     TemperedDistribution.smulLeftCLM ℂ g u ∈ finiteL2DerivativeSpan q := by
   have h : finiteL2DerivativeSpan (n := n) q ≤
       (finiteL2DerivativeSpan q).comap (TemperedDistribution.smulLeftCLM ℂ g).toLinearMap := by
     apply Submodule.span_le.mpr
     rintro v ⟨I,hI,f,rfl⟩
     exact finiteL2DerivativeSpan_mono hI (tempered_schwartz_mul_word_mem_span g I f)
   exact h hu

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.tempered_lineDeriv_multiplier
#print axioms KLS.DeterministicBridgeIntegration.finiteL2DerivativeSpan_memSobolev
#print axioms KLS.DeterministicBridgeIntegration.finiteL2DerivativeSpan_schwartz_mul
