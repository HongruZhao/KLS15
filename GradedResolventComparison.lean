import GradedHilbertOperators
import PositiveResolventContraction

/-! Blockwise curvature comparison implies the actual graded comparison.
The inverse is constructed on the genuine Hilbert direct sum; no spectral
calculus compatibility assumption is needed. The geometric block comparison
remains an explicit premise. -/
noncomputable section
namespace KLSBelow25
namespace GradedHilbert
open ContinuousLinearMap InnerProductSpace RealHilbertComplexification
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {G E : ℕ → Type*}
  [∀ r, NormedAddCommGroup (G r)] [∀ r, InnerProductSpace ℝ (G r)]
  [∀ r, CompleteSpace (G r)]
  [∀ r, NormedAddCommGroup (E r)] [∀ r, InnerProductSpace ℝ (E r)]
  [∀ r, CompleteSpace (E r)]

def blockGram (J : ∀ r, G (r+1) →L[ℝ] G r) (L : ∀ r, E r →L[ℝ] G r) (r : ℕ) :
    G r →L[ℝ] G r := (J r).comp (J r).adjoint+(L r).comp (L r).adjoint

theorem blockGram_isPositive (J : ∀ r, G (r+1) →L[ℝ] G r)
    (L : ∀ r, E r →L[ℝ] G r) (r : ℕ) : (blockGram J L r).IsPositive :=
  (isPositive_self_comp_adjoint _).add (isPositive_self_comp_adjoint _)

def blockResolvent (J : ∀ r, G (r+1) →L[ℝ] G r) (L : ∀ r, E r →L[ℝ] G r)
    (a : ℝ) (r : ℕ) : G r →L[ℝ] G r := Ring.inverse (1+a • blockGram J L r)

theorem blockResolvent_inverse (J : ∀ r, G (r+1) →L[ℝ] G r)
    (L : ∀ r, E r →L[ℝ] G r) {a : ℝ} (ha : 0 ≤ a) (r : ℕ) :
    (1+a • blockGram J L r)*blockResolvent J L a r=1 :=
  Ring.mul_inverse_cancel _ (positive_resolvent_isUnit _ (blockGram_isPositive J L r) ha)

theorem blockResolvent_norm_le_one (J : ∀ r, G (r+1) →L[ℝ] G r)
    (L : ∀ r, E r →L[ℝ] G r) {a : ℝ} (ha : 0 ≤ a) (r : ℕ) :
    ‖blockResolvent J L a r‖ ≤ 1 :=
  positive_resolvent_norm_le_one _ _ (blockGram_isPositive J L r) ha (blockResolvent_inverse J L ha r)

variable (J : ∀ r, G (r+1) →L[ℝ] G r) (L : ∀ r, E r →L[ℝ] G r)
  {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
  (hJ : ∀ r, ‖J r‖ ≤ C) (hL : ∀ r, ‖L r‖ ≤ D)

theorem gradedGram_apply (x : lp G 2) (r : ℕ) :
    realIntegrationGram (shift J hC hJ) (diagonal L hD hL) x r=blockGram J L r (x r) := by
  simp [realIntegrationGram,blockGram,shift_adjoint_succ,diagonal_adjoint_apply]

theorem gradedResolvent_apply {a : ℝ} (ha : 0 ≤ a) (x : lp G 2) (r : ℕ) :
    realCanonicalIntegrationResolvent (shift J hC hJ) (diagonal L hD hL) a x r=
      blockResolvent J L a r (x r) := by
  let U := diagonal (blockResolvent J L a) zero_le_one (blockResolvent_norm_le_one J L ha)
  have hU : (1+a • realIntegrationGram (shift J hC hJ) (diagonal L hD hL))*U=1 := by
    apply ContinuousLinearMap.ext
    intro y
    apply lp.ext
    funext s
    change (U y) s+a • (realIntegrationGram (shift J hC hJ) (diagonal L hD hL) (U y)) s=y s
    rw [gradedGram_apply]
    change blockResolvent J L a s (y s)+a • blockGram J L s (blockResolvent J L a s (y s))=y s
    exact congrArg (fun A : G s →L[ℝ] G s => A (y s)) (blockResolvent_inverse J L ha s)
  have hu := positive_resolvent_isUnit _
    (realIntegrationGram_isPositive (shift J hC hJ) (diagonal L hD hL)) ha
  have he : U=realCanonicalIntegrationResolvent (shift J hC hJ) (diagonal L hD hL) a :=
    hu.mul_left_cancel (hU.trans (realCanonicalIntegrationResolvent_inverse _ _ ha).symm)
  rw [← he]
  rfl

/-- Exact manuscript(6.10), rank by rank, glues into(6.15) on genuine ℓ². -/
theorem gradedRationalIntegrationComparison {a : ℝ} (ha : 0 ≤ a)
    (hcomparison : ∀ r (v : G (r+1)), ‖J r v‖^2 ≤
      ⟪(a⁻¹ • (1-blockResolvent J L a (r+1))) v,v⟫_ℝ) :
    realRationalIntegrationComparison (shift J hC hJ) (diagonal L hD hL) a := by
  intro x
  let R := shift J hC hJ
  let V := a⁻¹ • (1-realCanonicalIntegrationResolvent R (diagonal L hD hL) a)
  have hV (r : ℕ) : V x r=(a⁻¹ • (1-blockResolvent J L a r)) (x r) := by
    simp [V,R,gradedResolvent_apply J L hC hD hJ hL ha]
  have hpoint (r : ℕ) : ⟪R.adjoint (R x) r,x r⟫_ℝ ≤ ⟪V x r,x r⟫_ℝ := by
    cases r with
    | zero =>
      simp only [R,shift_adjoint_zero,inner_zero_left,hV]
      exact positive_resolvent_rational_nonneg _ _ (blockGram_isPositive J L 0) ha
        (blockResolvent_inverse J L ha 0) (x 0)
    | succ r =>
      rw [show R.adjoint (R x) (r+1)=(J r).adjoint (J r (x (r+1))) by
        simp [R,shift_adjoint_succ]]
      rw [adjoint_inner_left,real_inner_self_eq_norm_sq,hV]
      exact hcomparison r (x (r+1))
  have hs := (lp.summable_inner (𝕜:=ℝ) (R.adjoint (R x)) x).tsum_le_tsum hpoint
    (lp.summable_inner (𝕜:=ℝ) (V x) x)
  change ‖R x‖^2 ≤ ⟪V x,x⟫_ℝ
  rw [apply_norm_sq_eq_inner_adjoint_left R x]
  simpa only [RCLike.re_to_real,comp_apply,lp.inner_eq_tsum] using hs

#print axioms gradedGram_apply
#print axioms gradedResolvent_apply
#print axioms gradedRationalIntegrationComparison
end GradedHilbert
end KLSBelow25
