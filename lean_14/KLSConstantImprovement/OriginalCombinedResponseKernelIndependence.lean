import Mathlib

/-! Kernel-independent characterization of the compatible combined field.
The original common-law Stein expansion, Hessian-core projection, Riesz
representation, and core-to-closed-space extension remain analytic inputs.
In the uniqueness theorem E is the compatible closed Hessian space itself.
No uniform numeric combined-energy estimate is asserted. -/
noncomputable section
namespace KLSConstantImprovement.OriginalCombinedResponseKernelIndependence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem combined_same_test_pairing (z p b s : E) (response target : ℝ)
    (hprojection : inner ℝ p s = inner ℝ z s)
    (hresponse : response = inner ℝ b s)
    (hstein : target = inner ℝ z s + 3 * response) :
    inner ℝ (p + (3 : ℝ) • b) s = target := by
  rw [inner_add_left, real_inner_smul_left, hprojection]
  linarith

theorem same_law_combined_field_unique (f g : E) (target : E → ℝ)
    (hf : ∀ s, inner ℝ f s = target s)
    (hg : ∀ s, inner ℝ g s = target s) : f = g := by
  have hp : inner ℝ f (f-g) = inner ℝ g (f-g) := by
    rw [hf, hg]
  have hs : inner ℝ (f-g) (f-g) = 0 := by
    rw [inner_sub_left]
    linarith
  rw [real_inner_self_eq_norm_sq] at hs
  have hn : ‖f-g‖ = 0 := by nlinarith [norm_nonneg (f-g)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end KLSConstantImprovement.OriginalCombinedResponseKernelIndependence
#print axioms KLSConstantImprovement.OriginalCombinedResponseKernelIndependence.combined_same_test_pairing
#print axioms KLSConstantImprovement.OriginalCombinedResponseKernelIndependence.same_law_combined_field_unique
