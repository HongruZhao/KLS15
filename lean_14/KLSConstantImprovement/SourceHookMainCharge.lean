import KLSConstantImprovement.SourceThirdAdjointResponse

/-! Constant source hook null pairing and its compatible projection charge.
Actual source IBP, scalar Hessian/core identification, curvature and finite
Gram projection inputs remain explicit. No uniform numeric response cap. -/
noncomputable section
namespace KLSConstantImprovement.SourceHookMainCharge

variable {ι : Type*} [Fintype ι]

def triplePair (C D : ι → ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, C i j k * D i j k

theorem constant_hook_third_pair_zero
    (C D : ι → ι → ι → ℝ)
    (hHook : ∀ i j k, C i j k + C j i k + C k i j = 0)
    (hfirst : ∀ i j k, D i j k = D j i k)
    (hlast : ∀ i j k, D i j k = D i k j) :
    triplePair C D = 0 := by
  have hswap : (∑ i, ∑ j, ∑ k, C j i k * D i j k) = triplePair C D := by
    calc
      (∑ i, ∑ j, ∑ k, C j i k * D i j k) =
          ∑ i, ∑ j, ∑ k, C j i k * D j i k := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        rw [hfirst i j k]
      _ = triplePair C D := by
        unfold triplePair
        rw [Finset.sum_comm]
  have hcycle : (∑ i, ∑ j, ∑ k, C k i j * D i j k) = triplePair C D := by
    calc
      (∑ i, ∑ j, ∑ k, C k i j * D i j k) =
          ∑ i, ∑ j, ∑ k, C k i j * D k i j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        rw [hlast i j k, hfirst i k j]
      _ = ∑ i, ∑ k, ∑ j, C k i j * D k i j := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_comm
      _ = triplePair C D := by
        unfold triplePair
        rw [Finset.sum_comm]
  have hz : (∑ i, ∑ j, ∑ k,
      (C i j k + C j i k + C k i j) * D i j k) = 0 := by
    simp only [hHook, zero_mul, Finset.sum_const_zero]
  have hsum : (∑ i, ∑ j, ∑ k,
      (C i j k + C j i k + C k i j) * D i j k) = 3 * triplePair C D := by
    simp only [add_mul, Finset.sum_add_distrib]
    rw [hswap, hcycle]
    unfold triplePair
    ring
  linarith

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem source_hook_corrected_coercivity (a : E) (b w : F) (r : E → F)
    (hcontract : ∀ v, ‖r v‖ ≤ ‖v‖)
    (hrep : ∀ v, inner ℝ a v = inner ℝ b (r v))
    (hnull : ∀ v, inner ℝ w (r v) = 0) :
    ‖a‖^2 ≤ ‖b-w‖^2 := by
  apply KLSConstantImprovement.SourceThirdAdjointResponse.third_adjoint_norm_coercivity
    a (b-w) r hcontract
  intro v
  rw [inner_sub_left, hnull v]
  simpa using hrep v

/-- Orthogonal projection gives a Schur charge without an inverse Gram. -/
theorem source_hook_projection_charge (a : E) (b w : F) (r : E → F)
    (hcontract : ∀ v, ‖r v‖ ≤ ‖v‖)
    (hrep : ∀ v, inner ℝ a v = inner ℝ b (r v))
    (hnull : ∀ v, inner ℝ w (r v) = 0)
    (hprojection : inner ℝ b w = ‖w‖^2) :
    ‖a‖^2 + ‖w‖^2 ≤ ‖b‖^2 := by
  have h := source_hook_corrected_coercivity a b w r hcontract hrep hnull
  rw [norm_sub_sq_real, hprojection] at h
  nlinarith

theorem source_hook_paid_variance (a f : E) (b w : F) {V : ℝ}
    (hvariance : V = 9 * ‖a+f‖^2)
    (hcharge : ‖a‖^2 + ‖w‖^2 ≤ ‖b‖^2) :
    V + 9 * ‖w‖^2 ≤
      9 * ‖b‖^2 + 18 * inner ℝ a f + 9 * ‖f‖^2 := by
  rw [norm_add_sq_real] at hvariance
  nlinarith

theorem two_exponential_full_hook_charge :
    (8:ℝ) - (15/2) = 1/2 ∧
    (15/2:ℝ) - (25/4) = 5/4 ∧
    (54/7:ℝ) > 15/2 := by
  norm_num

end KLSConstantImprovement.SourceHookMainCharge
#print axioms KLSConstantImprovement.SourceHookMainCharge.constant_hook_third_pair_zero
#print axioms KLSConstantImprovement.SourceHookMainCharge.source_hook_corrected_coercivity
#print axioms KLSConstantImprovement.SourceHookMainCharge.source_hook_projection_charge
#print axioms KLSConstantImprovement.SourceHookMainCharge.source_hook_paid_variance
#print axioms KLSConstantImprovement.SourceHookMainCharge.two_exponential_full_hook_charge
