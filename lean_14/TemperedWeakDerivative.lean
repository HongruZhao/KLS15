import CompactWeakDerivativeTempered
import KLS.WeakDivergenceDifferentiation

/-! Fourier Sobolev derivatives give genuine real weak derivatives against
compact C1 tests. The smooth-test calculation and domain extension are proved. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff Topology SchwartzMap LineDeriv BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem tempered_lineDeriv_realPart_smooth_identity
    (F G : Lp ℂ 2 (volume : Measure (Space n))) (i : Fin n)
    (hderiv : ∂_{EuclideanSpace.single i (1 : ℝ)} (F : 𝓢'(Space n,ℂ)) =
      (G : 𝓢'(Space n,ℂ)))
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ x, (F x).re * coordinateDerivative ψ i x) =
      -(∫ x, (G x).re * ψ x) := by
  let γ : 𝓢(Space n,ℂ) := (hc.comp_left (show Complex.ofRealCLM 0=0 by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hψ)
  have hγ (x : Space n) : γ x = (ψ x : ℂ) := rfl
  have hdγ (x : Space n) :
      (∂_{EuclideanSpace.single i (1 : ℝ)} γ : 𝓢(Space n,ℂ)) x =
      (coordinateDerivative ψ i x : ℂ) := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change (fderiv ℝ (Complex.ofRealCLM ∘ ψ) x) (EuclideanSpace.single i 1) = _
    rw [(Complex.ofRealCLM.hasFDerivAt.comp x
      (hψ.differentiable (by simp) x).hasFDerivAt).fderiv]
    rfl
  have he := congrArg (fun T : 𝓢'(Space n,ℂ) => T γ) hderiv
  rw [TemperedDistribution.lineDerivOp_apply_apply,
    Lp.toTemperedDistribution_apply,Lp.toTemperedDistribution_apply] at he
  have hLf : Integrable (fun x : Space n =>
      (-∂_{EuclideanSpace.single i (1 : ℝ)} γ : 𝓢(Space n,ℂ)) x * F x) :=
    (SchwartzMap.memLp _ 2 volume).integrable_mul (Lp.memLp F)
  have hRg : Integrable (fun x : Space n => γ x * G x) :=
    (γ.memLp 2 volume).integrable_mul (Lp.memLp G)
  have hr := congrArg Complex.re he
  change RCLike.re (∫ x : Space n,
    (-∂_{EuclideanSpace.single i (1 : ℝ)} γ : 𝓢(Space n,ℂ)) x * F x) =
    RCLike.re (∫ x : Space n, γ x * G x) at hr
  rw [←integral_re hLf,←integral_re hRg] at hr
  change (∫ x : Space n,
    ((-∂_{EuclideanSpace.single i (1 : ℝ)} γ : 𝓢(Space n,ℂ)) x * F x).re) =
    (∫ x : Space n, (γ x * G x).re) at hr
  simp only [SchwartzMap.neg_apply,hdγ,hγ,neg_mul,Complex.neg_re,Complex.neg_im,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hr
  rw [integral_neg] at hr
  simpa only [mul_comm,neg_neg] using congrArg Neg.neg hr

theorem hasLocalWeakCoordinateDerivative_realPart_of_tempered
    (F G : Lp ℂ 2 (volume : Measure (Space n))) (i : Fin n)
    (hderiv : ∂_{EuclideanSpace.single i (1 : ℝ)} (F : 𝓢'(Space n,ℂ)) =
      (G : 𝓢'(Space n,ℂ))) :
    HasLocalWeakCoordinateDerivative (fun x => (F x).re) (fun x => (G x).re) i := by
  have hF : MemLp (fun x => (F x).re) 2 volume := (Lp.memLp F).re
  have hG : MemLp (fun x => (G x).re) 2 volume := (Lp.memLp G).re
  have hsum (η : Space n → ℝ) :
      (∑ j : Fin n, ∫ x : Space n,
        (if j=i then (F x).re else 0)*coordinateDerivative η j x) =
      ∫ x : Space n, (F x).re*coordinateDerivative η i x := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  intro ψ hψ hc
  have he := integral_divergence_of_smooth_compact_tests
    (A := fun j x => if j=i then (F x).re else 0)
    (b := fun x => -(G x).re)
    (fun j S _ => by
      by_cases hj : j=i
      · simpa [hj] using hF.restrict S
      · simp [hj])
    (hG.locallyIntegrable (by norm_num)).neg
    (fun η hη hηc => by
      rw [hsum]
      simpa only [neg_mul,integral_neg] using
        tempered_lineDeriv_realPart_smooth_identity F G i hderiv hη hηc)
    hψ hc
  rw [hsum] at he
  simpa only [neg_mul,integral_neg] using he

theorem exists_weakCoordinateDerivative_of_memSobolev_one
    {f : Space n → ℝ} (hf : MemLp f 2 volume)
    (hs : TemperedDistribution.MemSobolev 1 2
      (realMemLpToComplex hf : 𝓢'(Space n,ℂ))) (i : Fin n) :
    ∃ g : Lp ℝ 2 (volume : Measure (Space n)), HasWeakCoordinateDerivative f i g := by
  have hd : TemperedDistribution.MemSobolev 0 2
      (∂_{EuclideanSpace.single i (1 : ℝ)}
        (realMemLpToComplex hf : 𝓢'(Space n,ℂ))) := by
    simpa using hs.lineDerivOp (m := EuclideanSpace.single i (1 : ℝ))
  obtain ⟨G,hG⟩ := TemperedDistribution.memSobolev_zero_iff.mp hd
  let g := Complex.reCLM.compLp G
  have hg : (fun x => (G x).re) =ᵐ[volume] g :=
    by
      filter_upwards [Complex.reCLM.coeFn_compLp G] with x hx
      exact hx.symm
  have hfr : (fun x => (realMemLpToComplex hf x).re) =ᵐ[volume] f := by
    filter_upwards [realMemLpToComplex_coe hf] with x hx
    simp [hx]
  exact ⟨g,(hasLocalWeakCoordinateDerivative_realPart_of_tempered
    (realMemLpToComplex hf) G i hG).congr_ae hfr hg⟩

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.exists_weakCoordinateDerivative_of_memSobolev_one
