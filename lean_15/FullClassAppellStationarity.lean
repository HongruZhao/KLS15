import ActualLawTiltSmooth
import ActualAppellStationarity

/-! Actual Appell tensor linearity and test-function stationarity for
arbitrary log-concave probability laws, using local L² tilt smoothness.
Only local maximality of the indicated actual quotient is assumed. -/
noncomputable section
open MeasureTheory InnerProductSpace Filter Set Metric
open scoped ContDiff Topology BigOperators
namespace KLSBelow25
open KLS KLS.DeterministicBridgeIntegration
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
set_option maxHeartbeats 1000000

 theorem actualAppellCoefficient_congr_ae {f g : Space n → ℝ}
    (hfg : f =ᵐ[μ] g) (d : ℕ) (a : Fin d → Fin n) :
    actualAppellCoefficient μ f d a = actualAppellCoefficient μ g d a := by
  have he : (fun z => ∫ x, f x ∂exponentialTilt μ z) =
      (fun z => ∫ x, g x ∂exponentialTilt μ z) := by
    funext z
    exact integral_congr_ae
      ((tilted_absolutelyContinuous μ (fun x => inner ℝ z x)).ae_eq hfg)
  unfold actualAppellCoefficient
  rw [he]

 theorem actualAppellCoefficient_const_mul (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (c : ℝ) (d : ℕ) (a : Fin d → Fin n) :
    actualAppellCoefficient μ (fun x => c*f x) d a =
      c*actualAppellCoefficient μ f d a := by
  have hs := contDiffAt_normalized_tilt_average hLC hf
  have he : (fun z => ∫ x, c*f x ∂exponentialTilt μ z) =
      c • (fun z => ∫ x, f x ∂exponentialTilt μ z) := by
    funext z
    simp only [integral_const_mul,Pi.smul_apply,smul_eq_mul]
  unfold actualAppellCoefficient
  rw [he,iteratedFDeriv_const_smul_apply (hs.of_le (by simp))]
  simp only [_root_.smul_apply,smul_eq_mul]

 theorem actualAppellCoefficient_sub (hLC : measureLogConcave μ)
    {f g : Space n → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (d : ℕ) (a : Fin d → Fin n) :
    actualAppellCoefficient μ (fun x => f x-g x) d a =
      actualAppellCoefficient μ f d a-actualAppellCoefficient μ g d a := by
  obtain ⟨rf,hrf,hfd,h1f⟩ := exists_common_local_exponential_domains hLC hf
  obtain ⟨rg,hrg,hgd,h1g⟩ := exists_common_local_exponential_domains hLC hg
  have he : (fun z => ∫ x, f x-g x ∂exponentialTilt μ z) =ᶠ[𝓝 (0 : Space n)]
      (fun z => ∫ x, f x ∂exponentialTilt μ z)-
        (fun z => ∫ x, g x ∂exponentialTilt μ z) := by
    filter_upwards [ball_mem_nhds (0 : Space n) (lt_min hrf hrg)] with z hz
    have hz' : ‖z‖ < min rf rg := by simpa only [mem_ball,dist_zero_right] using hz
    have hif := hfd.integrable_tilt ((lt_min_iff.mp hz').1.le)
    have hig := hgd.integrable_tilt ((lt_min_iff.mp hz').2.le)
    change tiltAverage μ (fun x => inner ℝ z x) (fun x => f x-g x) =
      tiltAverage μ (fun x => inner ℝ z x) f-tiltAverage μ (fun x => inner ℝ z x) g
    simp_rw [tiltAverage_eq_ratio,sub_mul]
    rw [integral_sub hif hig]
    ring
  have hsF := contDiffAt_normalized_tilt_average hLC hf
  have hsG := contDiffAt_normalized_tilt_average hLC hg
  unfold actualAppellCoefficient
  rw [(he.iteratedFDeriv ℝ d).eq_of_nhds,
    iteratedFDeriv_sub_apply (hsF.of_le (by simp)) (hsG.of_le (by simp))]
  simp only [_root_.sub_apply]

 def fullClassAppellTensor (d : ℕ) (f : Lp ℝ 2 μ) :
    EuclideanSpace ℝ (Fin d → Fin n) :=
  WithLp.toLp 2 (fun a => actualAppellCoefficient μ f d a)

 theorem fullClassAppellTensor_sub (hLC : measureLogConcave μ)
    (d : ℕ) (f g : Lp ℝ 2 μ) :
    fullClassAppellTensor d (f-g) = fullClassAppellTensor d f-fullClassAppellTensor d g := by
  apply PiLp.ext
  intro a
  change actualAppellCoefficient μ (f-g : Lp ℝ 2 μ) d a =
    actualAppellCoefficient μ f d a-actualAppellCoefficient μ g d a
  rw [actualAppellCoefficient_congr_ae (Lp.coeFn_sub _ _) d a]
  exact actualAppellCoefficient_sub hLC (Lp.memLp f) (Lp.memLp g) d a

 theorem fullClassAppellTensor_smul (hLC : measureLogConcave μ)
    (d : ℕ) (c : ℝ) (f : Lp ℝ 2 μ) :
    fullClassAppellTensor d (c • f) = c • fullClassAppellTensor d f := by
  apply PiLp.ext
  intro a
  change actualAppellCoefficient μ (c • f : Lp ℝ 2 μ) d a =
    c*actualAppellCoefficient μ f d a
  rw [actualAppellCoefficient_congr_ae (Lp.coeFn_smul _ _) d a]
  exact actualAppellCoefficient_const_mul hLC (Lp.memLp f) c d a

 theorem fullClassAppellTensor_add (hLC : measureLogConcave μ)
    (d : ℕ) (f g : Lp ℝ 2 μ) :
    fullClassAppellTensor d (f+g) = fullClassAppellTensor d f+fullClassAppellTensor d g := by
  have he := fullClassAppellTensor_sub hLC d (f+g) g
  rw [add_sub_cancel_right] at he
  exact eq_add_of_sub_eq he.symm

 def fullClassAppellLinearMap (hLC : measureLogConcave μ) (d : ℕ) :
    Lp ℝ 2 μ →ₗ[ℝ] EuclideanSpace ℝ (Fin d → Fin n) where
  toFun := fullClassAppellTensor d
  map_add' := fullClassAppellTensor_add hLC d
  map_smul' := fullClassAppellTensor_smul hLC d

 theorem fullClass_test_function_stationarity (hLC : measureLogConcave μ) (k : ℕ)
    (f ell : Lp ℝ 2 μ) {h : ℝ} (hh : 0 < h) (hunit : ‖f‖=1)
    (phi : ℝ → ℝ) {phiPrime : ℝ}
    (hphi : HasDerivAt phi phiPrime (‖fullClassAppellTensor k f‖^2/h))
    (hphipos : 0 < phi (‖fullClassAppellTensor k f‖^2/h))
    (hmax : IsLocalMax (fun t : ℝ => coefficientQuotient
      (fullClassAppellLinearMap hLC k) (fullClassAppellLinearMap hLC (k+1))
      h phi (f+t • ell)) 0) :
    inner ℝ (fullClassAppellTensor (k+1) f) (fullClassAppellTensor (k+1) ell)+
      ‖fullClassAppellTensor (k+1) f‖^2*((-phiPrime)/phi (‖fullClassAppellTensor k f‖^2/h))/h*
        inner ℝ (fullClassAppellTensor k f) (fullClassAppellTensor k ell) =
      ‖fullClassAppellTensor (k+1) f‖^2*
        (1+(‖fullClassAppellTensor k f‖^2/h)*
          ((-phiPrime)/phi (‖fullClassAppellTensor k f‖^2/h)))*inner ℝ f ell := by
  exact coefficient_quotient_stationarity
    (fullClassAppellLinearMap hLC k) (fullClassAppellLinearMap hLC (k+1))
    f ell hh hunit phi hphi hphipos hmax

 theorem fullClassAppellTensor_potential_eq_actual {V : Space n → ℝ}
    (d : ℕ) (f : Lp ℝ 2 (potentialMeasure V)) :
    fullClassAppellTensor d f = actualAppellTensor d f := by
  apply PiLp.ext
  intro a
  exact actualAppellCoefficient_eq_factorial_taylor V f d a

#print axioms actualAppellCoefficient_sub
#print axioms fullClassAppellLinearMap
#print axioms fullClass_test_function_stationarity
#print axioms fullClassAppellTensor_potential_eq_actual
end KLSBelow25
