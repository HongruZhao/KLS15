import KLS.WeightedL2TaylorTensor
import KLS.LinearCumulantTaylor
import KLS.IsotropicFirstTaylor
import Mathlib

/-! Actual L2 Appell coefficient maps and the test-direction stationarity
identity of manuscript (3.20). Joint law-polynomial maximizer existence is
not asserted: local maximality in a test direction is an explicit premise. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped Topology BigOperators
namespace KLSBelow25

section Stationarity
variable {V W Z : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

def coefficientQuotient (B : V →ₗ[ℝ] W) (C : V →ₗ[ℝ] Z)
    (h : ℝ) (phi : ℝ → ℝ) (f : V) : ℝ :=
  ‖C f‖^2/(‖f‖^2*phi (‖B f‖^2/(h*‖f‖^2)))

theorem hasDerivAt_linear_energy (B : V →ₗ[ℝ] W) (f ell : V) :
    HasDerivAt (fun t : ℝ => ‖B (f+t • ell)‖^2)
      (2*inner ℝ (B f) (B ell)) 0 := by
  have hd : HasDerivAt (fun t : ℝ => B f+t • B ell) (B ell) 0 := by
    convert (hasDerivAt_const (0 : ℝ) (B f)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (B ell)) using 1 <;>
      first | rfl | (ext t; rfl) | simp
  simpa only [map_add,map_smul,zero_smul,add_zero] using hd.norm_sq

/-- The exact adjacent-rank coefficient identity at an actual local maximum
in one test-function direction. No continuity of the linear maps is needed. -/
theorem coefficient_quotient_stationarity (B : V →ₗ[ℝ] W) (C : V →ₗ[ℝ] Z)
    (f ell : V) {h : ℝ} (hh : 0 < h) (hunit : ‖f‖=1)
    (phi : ℝ → ℝ) {phiPrime : ℝ}
    (hphi : HasDerivAt phi phiPrime (‖B f‖^2/h))
    (hphipos : 0 < phi (‖B f‖^2/h))
    (hmax : IsLocalMax (fun t : ℝ => coefficientQuotient B C h phi (f+t • ell)) 0) :
    inner ℝ (C f) (C ell)+
      ‖C f‖^2*((-phiPrime)/phi (‖B f‖^2/h))/h*inner ℝ (B f) (B ell) =
      ‖C f‖^2*(1+(‖B f‖^2/h)*((-phiPrime)/phi (‖B f‖^2/h)))*inner ℝ f ell := by
  let x : ℝ := ‖C f‖^2
  let y : ℝ := ‖B f‖^2
  let m : ℝ := inner ℝ f ell
  let b : ℝ := inner ℝ (B f) (B ell)
  let c : ℝ := inner ℝ (C f) (C ell)
  have hg : HasDerivAt (fun t : ℝ => ‖f+t • ell‖^2) (2*m) 0 := by
    simpa [m] using hasDerivAt_linear_energy (LinearMap.id : V →ₗ[ℝ] V) f ell
  have hy := hasDerivAt_linear_energy B f ell
  have hx := hasDerivAt_linear_energy C f ell
  have hdenbase : h*‖f+(0 : ℝ) • ell‖^2 ≠ 0 := by simp [hunit,ne_of_gt hh]
  have hu : HasDerivAt (fun t : ℝ => ‖B (f+t • ell)‖^2/(h*‖f+t • ell‖^2))
      ((2*b*h-y*(h*(2*m)))/h^2) 0 := by
    convert hy.div (hg.const_mul h) hdenbase using 1 <;>
      simp [b,y,m,hunit]
  have hphi' : HasDerivAt
      (fun t : ℝ => phi (‖B (f+t • ell)‖^2/(h*‖f+t • ell‖^2)))
      (phiPrime*((2*b*h-y*(h*(2*m)))/h^2)) 0 := by
    have hp : HasDerivAt phi phiPrime (‖B (f+(0 : ℝ) • ell)‖^2/
        (h*‖f+(0 : ℝ) • ell‖^2)) := by simpa [hunit] using hphi
    exact hp.comp 0 hu
  have hd := hg.mul hphi'
  have hdne : ‖f+(0 : ℝ) • ell‖^2*
      phi (‖B (f+(0 : ℝ) • ell)‖^2/(h*‖f+(0 : ℝ) • ell‖^2)) ≠ 0 := by
    simpa [hunit] using ne_of_gt hphipos
  have hF := hx.div hd hdne
  have hzero := hmax.hasDerivAt_eq_zero hF
  have hhne := ne_of_gt hh
  have hpne := ne_of_gt hphipos
  simp only [zero_smul,add_zero,hunit,one_pow,mul_one] at hzero
  dsimp [x,y,m,b,c] at *
  simp only [zero_smul,add_zero,hunit,one_pow,mul_one] at hzero
  field_simp [hhne,hpne] at hzero ⊢
  nlinarith

end Stationarity

section ActualCoefficients
open KLS
variable {n : ℕ} {V : Space n → ℝ} {kappa : ℝ}
  [IsProbabilityMeasure (potentialMeasure V)]
  (hV : ContDiff ℝ 2 V) (hkappa : 0 < kappa)
  (hlower : ∀ x (a : Fin n → ℝ),
    kappa*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))

def actualAppellTensor (d : ℕ) (f : Lp ℝ 2 (potentialMeasure V)) :
    EuclideanSpace ℝ (Fin d → Fin n) :=
  WithLp.toLp 2 (fun a => (d.factorial : ℝ)*exponentialTiltCoordinateTaylor V f d a)

include hV hkappa hlower

theorem actualAppellTensor_sub (d : ℕ) (f g : Lp ℝ 2 (potentialMeasure V)) :
    actualAppellTensor d (f-g) = actualAppellTensor d f-actualAppellTensor d g := by
  apply PiLp.ext
  intro a
  change (d.factorial : ℝ)*exponentialTiltCoordinateTaylor V (f-g : Lp ℝ 2 _) d a =
    (d.factorial : ℝ)*exponentialTiltCoordinateTaylor V f d a-
      (d.factorial : ℝ)*exponentialTiltCoordinateTaylor V g d a
  rw [exponentialTiltCoordinateTaylor_congr_ae (Lp.coeFn_sub _ _) d a]
  have he := exponentialTiltCoordinateTaylor_sub hV hkappa hlower (Lp.memLp f) (Lp.memLp g) d a
  change (d.factorial : ℝ)*exponentialTiltCoordinateTaylor V (fun x => f x-g x) d a = _
  rw [he]
  ring

theorem actualAppellTensor_smul (d : ℕ) (c : ℝ) (f : Lp ℝ 2 (potentialMeasure V)) :
    actualAppellTensor d (c • f) = c • actualAppellTensor d f := by
  apply PiLp.ext
  intro a
  change (d.factorial : ℝ)*exponentialTiltCoordinateTaylor V (c • f : Lp ℝ 2 _) d a =
    c*((d.factorial : ℝ)*exponentialTiltCoordinateTaylor V f d a)
  rw [exponentialTiltCoordinateTaylor_congr_ae (Lp.coeFn_smul _ _) d a]
  have he := exponentialTiltCoordinateTaylor_const_mul hV hkappa hlower (Lp.memLp f) c d a
  change (d.factorial : ℝ)*exponentialTiltCoordinateTaylor V (fun x => c*f x) d a = _
  rw [he]
  ring

theorem actualAppellTensor_add (d : ℕ) (f g : Lp ℝ 2 (potentialMeasure V)) :
    actualAppellTensor d (f+g) = actualAppellTensor d f+actualAppellTensor d g := by
  have he := actualAppellTensor_sub hV hkappa hlower d (f+g) g
  rw [add_sub_cancel_right] at he
  exact eq_add_of_sub_eq he.symm

def actualAppellLinearMap (d : ℕ) : Lp ℝ 2 (potentialMeasure V) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin d → Fin n) where
  toFun := actualAppellTensor d
  map_add' := actualAppellTensor_add hV hkappa hlower d
  map_smul' := actualAppellTensor_smul hV hkappa hlower d

theorem actual_test_function_stationarity (k : ℕ)
    (f ell : Lp ℝ 2 (potentialMeasure V)) {h : ℝ} (hh : 0 < h) (hunit : ‖f‖=1)
    (phi : ℝ → ℝ) {phiPrime : ℝ}
    (hphi : HasDerivAt phi phiPrime (‖actualAppellTensor k f‖^2/h))
    (hphipos : 0 < phi (‖actualAppellTensor k f‖^2/h))
    (hmax : IsLocalMax (fun t : ℝ => coefficientQuotient
      (actualAppellLinearMap hV hkappa hlower k)
      (actualAppellLinearMap hV hkappa hlower (k+1)) h phi (f+t • ell)) 0) :
    inner ℝ (actualAppellTensor (k+1) f) (actualAppellTensor (k+1) ell)+
      ‖actualAppellTensor (k+1) f‖^2*((-phiPrime)/phi (‖actualAppellTensor k f‖^2/h))/h*
        inner ℝ (actualAppellTensor k f) (actualAppellTensor k ell) =
      ‖actualAppellTensor (k+1) f‖^2*
        (1+(‖actualAppellTensor k f‖^2/h)*((-phiPrime)/phi (‖actualAppellTensor k f‖^2/h)))*
        inner ℝ f ell := by
  exact coefficient_quotient_stationarity
    (actualAppellLinearMap hV hkappa hlower k)
    (actualAppellLinearMap hV hkappa hlower (k+1)) f ell hh hunit phi hphi hphipos hmax

end ActualCoefficients
#print axioms actualAppellLinearMap
#print axioms actual_test_function_stationarity
end KLSBelow25
