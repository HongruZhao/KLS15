import TensorWeakDerivativeTower
import Mathlib.Analysis.Distribution.Sobolev

/-! Genuine compactly localized real weak derivatives, embedded into the
complex tempered distributions used by mathlib's Fourier Sobolev theory. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators SchwartzMap LineDeriv
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem compact_weak_identity_for_noncompact_test
    {f : Space n → ℝ} {i : Fin n} {g : Lp ℝ 2 (volume : Measure (Space n))}
    (hweak : HasWeakCoordinateDerivative f i g) {K : Set (Space n)} (hK : IsCompact K)
    (hfzero : ∀ᵐ x ∂(volume : Measure (Space n)), x ∉ K → f x = 0)
    (hgzero : ∀ᵐ x ∂(volume : Measure (Space n)), x ∉ K → g x = 0)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    (∫ x, f x*coordinateDerivative ψ i x) = -(∫ x, g x*ψ x) := by
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : Space n)
  let χ : ContDiffBump (0 : Space n) := ⟨R,R+1,hR,by linarith⟩
  have hχ : ContDiff ℝ 1 χ := χ.contDiff
  have he (x : Space n) (hx : x ∈ K) : χ =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) :=
    χ.eventuallyEq_one_of_mem_ball (hKR hx)
  have hχone (x : Space n) (hx : x ∈ K) : χ x = 1 := (he x hx).eq_of_nhds
  have hχderiv (x : Space n) (hx : x ∈ K) : coordinateDerivative χ i x = 0 := by
    unfold coordinateDerivative
    rw [(he x hx).fderiv_eq]
    simp
  have hw := hweak (fun x => χ x*ψ x) (hχ.mul hψ) χ.hasCompactSupport.mul_right
  have hl : (∫ x, f x*coordinateDerivative (fun y => χ y*ψ y) i x) =
      ∫ x, f x*coordinateDerivative ψ i x := by
    apply integral_congr_ae
    filter_upwards [hfzero] with x hx
    by_cases h : x ∈ K
    · rw [coordinateDerivative_mul (hχ.differentiable (by norm_num) x)
        (hψ.differentiable (by norm_num) x),hχone x h,hχderiv x h]
      ring
    · simp [hx h]
  have hr : (∫ x, g x*(χ x*ψ x)) = ∫ x, g x*ψ x := by
    apply integral_congr_ae
    filter_upwards [hgzero] with x hx
    by_cases h : x ∈ K
    · rw [hχone x h,one_mul]
    · simp [hx h]
  rw [hl,hr] at hw
  exact hw

 def realMemLpToComplex {f : Space n → ℝ} (hf : MemLp f 2 volume) :
    Lp ℂ 2 (volume : Measure (Space n)) :=
    (hf.ofReal : MemLp (fun x => (f x : ℂ)) 2 volume).toLp (fun x => (f x : ℂ))

 theorem realMemLpToComplex_coe {f : Space n → ℝ} (hf : MemLp f 2 volume) :
    (realMemLpToComplex hf : Space n → ℂ) =ᵐ[volume] fun x => (f x : ℂ) :=
    (hf.ofReal : MemLp (fun x => (f x : ℂ)) 2 volume).coeFn_toLp

 theorem lineDeriv_realMemLpToComplex_of_compact_weak_derivative
    {f : Space n → ℝ} (hf : MemLp f 2 volume) {i : Fin n}
    {g : Lp ℝ 2 (volume : Measure (Space n))}
    (hweak : HasWeakCoordinateDerivative f i g) {K : Set (Space n)} (hK : IsCompact K)
    (hfzero : ∀ᵐ x ∂(volume : Measure (Space n)), x ∉ K → f x = 0)
    (hgzero : ∀ᵐ x ∂(volume : Measure (Space n)), x ∉ K → g x = 0) :
    ∂_{EuclideanSpace.single i (1 : ℝ)}
      (realMemLpToComplex hf : 𝓢'(Space n,ℂ)) =
      (realMemLpToComplex (Lp.memLp g) : 𝓢'(Space n,ℂ)) := by
  ext ψ
  rw [TemperedDistribution.lineDerivOp_apply_apply,Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  have hRe : ContDiff ℝ 1 (fun x : Space n => (ψ x).re) :=
    Complex.reCLM.contDiff.comp (ψ.smooth 1)
  have hIm : ContDiff ℝ 1 (fun x : Space n => (ψ x).im) :=
    Complex.imCLM.contDiff.comp (ψ.smooth 1)
  have hr := compact_weak_identity_for_noncompact_test hweak hK hfzero hgzero hRe
  have hi := compact_weak_identity_for_noncompact_test hweak hK hfzero hgzero hIm
  have hdre (x : Space n) : coordinateDerivative (fun y => (ψ y).re) i x =
      ((∂_{EuclideanSpace.single i (1 : ℝ)} ψ : 𝓢(Space n,ℂ)) x).re := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    unfold coordinateDerivative
    change (fderiv ℝ (Complex.reCLM ∘ ψ) x) (EuclideanSpace.single i 1) = _
    rw [(Complex.reCLM.hasFDerivAt.comp x ψ.differentiableAt.hasFDerivAt).fderiv]
    rfl
  have hdim (x : Space n) : coordinateDerivative (fun y => (ψ y).im) i x =
      ((∂_{EuclideanSpace.single i (1 : ℝ)} ψ : 𝓢(Space n,ℂ)) x).im := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    unfold coordinateDerivative
    change (fderiv ℝ (Complex.imCLM ∘ ψ) x) (EuclideanSpace.single i 1) = _
    rw [(Complex.imCLM.hasFDerivAt.comp x ψ.differentiableAt.hasFDerivAt).fderiv]
    rfl
  have hleft : (∫ x : Space n,
      (-∂_{EuclideanSpace.single i (1 : ℝ)} ψ : 𝓢(Space n,ℂ)) x • realMemLpToComplex hf x) =
      -(∫ x : Space n,
        (∂_{EuclideanSpace.single i (1 : ℝ)} ψ : 𝓢(Space n,ℂ)) x*(f x : ℂ)) := by
    rw [←integral_neg]
    apply integral_congr_ae
    filter_upwards [realMemLpToComplex_coe hf] with x hx
    simp [hx]
  have hright : (∫ x : Space n, ψ x • realMemLpToComplex (Lp.memLp g) x) =
      ∫ x : Space n, ψ x*(g x : ℂ) := by
    apply integral_congr_ae
    filter_upwards [realMemLpToComplex_coe (Lp.memLp g)] with x hx
    simp [hx]
  rw [hleft,hright]
  have hLf : Integrable (fun x : Space n =>
      (∂_{EuclideanSpace.single i (1 : ℝ)} ψ : 𝓢(Space n,ℂ)) x*(f x : ℂ)) :=
    (SchwartzMap.memLp _ 2 volume).integrable_mul hf.ofReal
  have hRg : Integrable (fun x : Space n => ψ x*(g x : ℂ)) :=
    (ψ.memLp 2 volume).integrable_mul (Lp.memLp g).ofReal
  apply Complex.ext
  · rw [Complex.neg_re]
    change -RCLike.re (∫ x : Space n,
      (∂_{EuclideanSpace.single i (1 : ℝ)} ψ : 𝓢(Space n,ℂ)) x*(f x : ℂ)) =
      RCLike.re (∫ x : Space n, ψ x*(g x : ℂ))
    rw [←integral_re hLf,←integral_re hRg]
    change -(∫ x : Space n, ((∂_{EuclideanSpace.single i (1 : ℝ)} ψ : 𝓢(Space n,ℂ)) x*(f x : ℂ)).re) =
      ∫ x : Space n, (ψ x*(g x : ℂ)).re
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    simp_rw [←hdre]
    simpa only [mul_comm,neg_neg] using congrArg Neg.neg hr
  · rw [Complex.neg_im]
    change -RCLike.im (∫ x : Space n,
      (∂_{EuclideanSpace.single i (1 : ℝ)} ψ : 𝓢(Space n,ℂ)) x*(f x : ℂ)) =
      RCLike.im (∫ x : Space n, ψ x*(g x : ℂ))
    rw [←integral_im hLf,←integral_im hRg]
    change -(∫ x : Space n, ((∂_{EuclideanSpace.single i (1 : ℝ)} ψ : 𝓢(Space n,ℂ)) x*(f x : ℂ)).im) =
      ∫ x : Space n, (ψ x*(g x : ℂ)).im
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add]
    simp_rw [←hdim]
    simpa only [mul_comm,neg_neg] using congrArg Neg.neg hi

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.lineDeriv_realMemLpToComplex_of_compact_weak_derivative
