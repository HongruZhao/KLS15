import ActualAppellStationarity

/-! Actual linear test direction, cumulant substitution (3.19), and the
combined terminal estimate (3.20). Local test-function maximality remains
an explicit premise; no joint-law attainment is assumed or constructed. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix Filter
open scoped Topology BigOperators
namespace KLSBelow25
open KLS

section IsotropicLinear
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def isotropicLinearObservable (hiso : IsIsotropic μ) (b : Space n) : Lp ℝ 2 μ :=
  ∑ i : Fin n, b i • isotropicAffineCoordinate hiso (some i)

theorem isotropicLinearObservable_coe (hiso : IsIsotropic μ) (b : Space n) :
    (isotropicLinearObservable hiso b : Space n → ℝ) =ᵐ[μ]
      (fun x => inner ℝ x b) := by
  have hs : (∑ i : Fin n, ⇑(b i • isotropicAffineCoordinate hiso (some i))) =ᵐ[μ]
      (∑ i : Fin n, fun x => b i*x i) := by
    apply eventuallyEq_sum
    intro i hi
    exact (Lp.coeFn_smul _ _).trans
      ((isotropicAffineCoordinate_coe hiso (some i)).const_smul (b i))
  apply (Lp.coeFn_finsetSum _ _).trans
  filter_upwards [hs] with x hx
  rw [hx]
  simp only [Finset.sum_apply, inner_eq_coordinate_sum]

theorem inner_isotropicLinearObservable_projection
    (hiso : IsIsotropic μ) (f : Lp ℝ 2 μ) :
    inner ℝ f (isotropicLinearObservable hiso (affineProjectionVector hiso f)) =
      ‖affineProjectionVector hiso f‖^2 := by
  rw [real_inner_comm, EuclideanSpace.real_norm_sq_eq]
  simp only [isotropicLinearObservable, sum_inner, real_inner_smul_left]
  change (∑ i : Fin n, inner ℝ (isotropicAffineCoordinate hiso (some i)) f *
      inner ℝ (isotropicAffineCoordinate hiso (some i)) f) =
    ∑ i : Fin n, inner ℝ (isotropicAffineCoordinate hiso (some i)) f ^ 2
  simp only [pow_two]

theorem affineProjectionVector_norm_sq_le_full
    (hiso : IsIsotropic μ) (f : Lp ℝ 2 μ) :
    ‖affineProjectionVector hiso f‖^2 ≤ ‖f‖^2 := by
  have ha := affineProjectionVector_norm_sq_le hiso f
  have hp := finiteOrthonormalProjection_remainder_norm_sq
    (orthonormal_isotropicAffineCoordinate hiso) f
  nlinarith [sq_nonneg ‖finiteOrthonormalRemainder (isotropicAffineCoordinate hiso) f‖]

end IsotropicLinear

section RegularLaw
variable {n : ℕ} {V : Space n → ℝ} {kappa : ℝ}
  [IsProbabilityMeasure (potentialMeasure V)]
  (hV : ContDiff ℝ 2 V) (hkappa : 0 < kappa)
  (hlower : ∀ x (a : Fin n → ℝ),
    kappa*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
  (hiso : IsIsotropic (potentialMeasure V))

def actualLinearCumulantTensor (d : ℕ) (b : Space n) :
    EuclideanSpace ℝ (Fin d → Fin n) :=
  WithLp.toLp 2 (fun a => cumulantTensor (potentialMeasure V) (d+1)
    (Fin.snoc (fun j => EuclideanSpace.basisFun (Fin n) ℝ (a j)) b))

include hV hkappa hlower

theorem actualAppellTensor_linear_eq_cumulant (d : ℕ) (b : Space n) :
    actualAppellTensor d (isotropicLinearObservable hiso b) =
      actualLinearCumulantTensor (V := V) d b := by
  apply PiLp.ext
  intro a
  change (d.factorial : ℝ)*
    exponentialTiltCoordinateTaylor V (isotropicLinearObservable hiso b) d a = _
  rw [exponentialTiltCoordinateTaylor_congr_ae (isotropicLinearObservable_coe hiso b)]
  have hExp : NormExponentialDomain (potentialMeasure V) (fun _ => 1) :=
    normExponentialDomain_of_memLp_potentialMeasure hV hkappa hlower (memLp_const (1 : ℝ))
  rw [exponentialTiltCoordinateTaylor_inner_eq_cumulant hExp]
  have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast d.factorial_ne_zero
  change (d.factorial : ℝ)*(_/(d.factorial : ℝ)) =
    cumulantTensor (potentialMeasure V) (d+1)
      (Fin.snoc (fun j => EuclideanSpace.basisFun (Fin n) ℝ (a j)) b)
  field_simp

/-- The actual first Appell tensor is the coordinate projection vector,
up to the canonical singleton-index equivalence; in particular norms agree. -/
theorem actualAppellTensor_one_norm_sq (f : Lp ℝ 2 (potentialMeasure V)) :
    ‖actualAppellTensor 1 f‖^2 = ‖affineProjectionVector hiso f‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ a : Fin 1 → Fin n,
    (((1 : ℕ).factorial : ℝ)*exponentialTiltCoordinateTaylor V f 1 a) ^ 2) = _
  simp only [Nat.factorial_one,Nat.cast_one,one_mul]
  exact sum_exponentialTiltCoordinateTaylor_one_sq_eq hV hkappa hlower hiso f

/-- Literal equality in manuscript (3.20), with genuine cumulant tensors.
This preserves the cancellation between both highest-order terminal terms. -/
theorem actual_linear_test_stationarity (k : ℕ)
    (f : Lp ℝ 2 (potentialMeasure V)) {h : ℝ} (hh : 0 < h) (hunit : ‖f‖=1)
    (phi : ℝ → ℝ) {phiPrime : ℝ}
    (hphi : HasDerivAt phi phiPrime (‖actualAppellTensor k f‖^2/h))
    (hphipos : 0 < phi (‖actualAppellTensor k f‖^2/h))
    (hmax : IsLocalMax (fun t : ℝ => coefficientQuotient
      (actualAppellLinearMap hV hkappa hlower k)
      (actualAppellLinearMap hV hkappa hlower (k+1)) h phi
      (f+t • isotropicLinearObservable hiso (affineProjectionVector hiso f))) 0) :
    inner ℝ (actualAppellTensor (k+1) f)
        (actualLinearCumulantTensor (V := V) (k+1) (affineProjectionVector hiso f))+
      ‖actualAppellTensor (k+1) f‖^2*((-phiPrime)/phi (‖actualAppellTensor k f‖^2/h))/h*
        inner ℝ (actualAppellTensor k f)
          (actualLinearCumulantTensor (V := V) k (affineProjectionVector hiso f)) =
      ‖actualAppellTensor (k+1) f‖^2*
        (1+(‖actualAppellTensor k f‖^2/h)*((-phiPrime)/phi (‖actualAppellTensor k f‖^2/h)))*
        ‖actualAppellTensor 1 f‖^2 := by
  have he := actual_test_function_stationarity hV hkappa hlower k f
    (isotropicLinearObservable hiso (affineProjectionVector hiso f))
    hh hunit phi hphi hphipos hmax
  rw [actualAppellTensor_linear_eq_cumulant hV hkappa hlower hiso,
    actualAppellTensor_linear_eq_cumulant hV hkappa hlower hiso,
    inner_isotropicLinearObservable_projection,
    ← actualAppellTensor_one_norm_sq hV hkappa hlower hiso] at he
  exact he

/-- Literal inequality in (3.20), using only the sharp first-coefficient
bound and the sign of minus phi'. No next-rank cumulant bound appears. -/
theorem actual_linear_terminal_bound (k : ℕ)
    (f : Lp ℝ 2 (potentialMeasure V)) {h : ℝ} (hh : 0 < h) (hunit : ‖f‖=1)
    (phi : ℝ → ℝ) {phiPrime : ℝ}
    (hphi : HasDerivAt phi phiPrime (‖actualAppellTensor k f‖^2/h))
    (hphipos : 0 < phi (‖actualAppellTensor k f‖^2/h)) (hphiPrime : phiPrime ≤ 0)
    (hmax : IsLocalMax (fun t : ℝ => coefficientQuotient
      (actualAppellLinearMap hV hkappa hlower k)
      (actualAppellLinearMap hV hkappa hlower (k+1)) h phi
      (f+t • isotropicLinearObservable hiso (affineProjectionVector hiso f))) 0) :
    inner ℝ (actualAppellTensor (k+1) f)
        (actualLinearCumulantTensor (V := V) (k+1) (affineProjectionVector hiso f))+
      ‖actualAppellTensor (k+1) f‖^2*((-phiPrime)/phi (‖actualAppellTensor k f‖^2/h))/h*
        inner ℝ (actualAppellTensor k f)
          (actualLinearCumulantTensor (V := V) k (affineProjectionVector hiso f)) ≤
      ‖actualAppellTensor (k+1) f‖^2*
        (1+(‖actualAppellTensor k f‖^2/h)*((-phiPrime)/phi (‖actualAppellTensor k f‖^2/h))) := by
  rw [actual_linear_test_stationarity hV hkappa hlower hiso k f hh hunit phi hphi hphipos hmax]
  have hb : ‖actualAppellTensor 1 f‖^2 ≤ 1 := by
    rw [actualAppellTensor_one_norm_sq hV hkappa hlower hiso]
    simpa [hunit] using affineProjectionVector_norm_sq_le_full hiso f
  have hq : 0 ≤ (-phiPrime)/phi (‖actualAppellTensor k f‖^2/h) :=
    div_nonneg (neg_nonneg.mpr hphiPrime) hphipos.le
  have hu : 0 ≤ ‖actualAppellTensor k f‖^2/h := div_nonneg (sq_nonneg _) hh.le
  have hpos : 0 ≤ ‖actualAppellTensor (k+1) f‖^2*
      (1+(‖actualAppellTensor k f‖^2/h)*((-phiPrime)/phi (‖actualAppellTensor k f‖^2/h))) := by
    positivity
  nlinarith

end RegularLaw
#print axioms actualAppellTensor_linear_eq_cumulant
#print axioms actual_linear_test_stationarity
#print axioms actual_linear_terminal_bound
end KLSBelow25
