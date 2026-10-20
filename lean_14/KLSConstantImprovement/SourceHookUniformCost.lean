import KLSConstantImprovement.SourceHookMainCharge
import KLSConstantImprovement.TensorGramThirdSandwich

/-! Last-two affine trace cost and a uniform compatible source-hook charge.
The three-marginal weighted interpolation, same original kernel sandwich,
last-two trace/slot bindings, and actual source scalar core are explicit
analytic inputs. No universal signed response estimate is asserted. -/
noncomputable section
namespace KLSConstantImprovement.SourceHookUniformCost

theorem last_two_slot_pair_charge {b W Q R p : ℝ}
    (hpair : b^2 ≤ W*((Q+R)/2))
    (hsource : Q+R=W-p) :
    2*b^2 ≤ W*(W-p) := by
  rw [hsource] at hpair
  nlinarith

theorem last_two_affine_trace_cost {W N J b p : ℝ}
    (hW : 0 ≤ W) (hN : 0 ≤ N) (hp : 0 ≤ p)
    (hbound : W ≤ (8*Real.sqrt 2)*N)
    (hidentity : J=W+2*b)
    (hcharge : 2*b^2 ≤ W*(W-p)) :
    J ≤ (16+8*Real.sqrt 2)*N := by
  exact OriginalUpperRecovery6TensorGram.affine_trace_bound_from_tensor_third
    hW hN hp hbound hidentity hcharge

theorem last_two_affine_trace_cost_twenty_eight {W N J b p : ℝ}
    (hW : 0 ≤ W) (hN : 0 ≤ N) (hp : 0 ≤ p)
    (hbound : W ≤ (8*Real.sqrt 2)*N)
    (hidentity : J=W+2*b)
    (hcharge : 2*b^2 ≤ W*(W-p)) :
    J ≤ 28*N := by
  have h := last_two_affine_trace_cost hW hN hp hbound hidentity hcharge
  have hs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  have hr : Real.sqrt (2:ℝ) ≤ 3/2 := by nlinarith
  have hm := mul_nonneg hN (sub_nonneg.mpr hr)
  nlinarith

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A scaled null correction pays a dual coefficient charge. The cost
and pairing use the SAME field; no positive Gram inverse is assumed. -/
theorem scaled_null_charge (a : E) (b v : F) (r : E → F)
    {alpha k : ℝ} (halpha : 0 ≤ alpha)
    (hcontract : ∀ z, ‖r z‖ ≤ ‖z‖)
    (hrep : ∀ z, inner ℝ a z=inner ℝ b (r z))
    (hnull : ∀ z, inner ℝ v (r z)=0)
    (hpair : inner ℝ b v=k)
    (hcost : alpha*‖v‖^2 ≤ k) :
    ‖a‖^2+alpha*k ≤ ‖b‖^2 := by
  have hz : ∀ z, inner ℝ (alpha • v) (r z)=0 := by
    intro z
    simp only [real_inner_smul_left, hnull z, mul_zero]
  have hc := SourceHookMainCharge.source_hook_corrected_coercivity
    a b (alpha • v) r hcontract hrep hz
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, hpair] at hc
  have hp := mul_nonneg halpha (sub_nonneg.mpr hcost)
  nlinarith

theorem uniform_hook_charge_twenty_eight (a : E) (b v : F) (r : E → F)
    {k : ℝ}
    (hcontract : ∀ z, ‖r z‖ ≤ ‖z‖)
    (hrep : ∀ z, inner ℝ a z=inner ℝ b (r z))
    (hnull : ∀ z, inner ℝ v (r z)=0)
    (hpair : inner ℝ b v=k)
    (hcost : ‖v‖^2 ≤ 28*k) :
    ‖a‖^2+k/28 ≤ ‖b‖^2 := by
  have hc : (1/28:ℝ)*‖v‖^2 ≤ k := by linarith
  have h := scaled_null_charge a b v r (alpha := (1/28:ℝ))
    (by norm_num) hcontract hrep hnull hpair hc
  nlinarith

theorem uniform_hook_paid_variance (a f : E) (b : F) {V k : ℝ}
    (hvariance : V=9*‖a+f‖^2)
    (hcharge : ‖a‖^2+k/28 ≤ ‖b‖^2) :
    V+(9/28:ℝ)*k ≤
      9*‖b‖^2+18*inner ℝ a f+9*‖f‖^2 := by
  rw [norm_add_sq_real] at hvariance
  nlinarith

end KLSConstantImprovement.SourceHookUniformCost
#print axioms KLSConstantImprovement.SourceHookUniformCost.last_two_slot_pair_charge
#print axioms KLSConstantImprovement.SourceHookUniformCost.last_two_affine_trace_cost
#print axioms KLSConstantImprovement.SourceHookUniformCost.last_two_affine_trace_cost_twenty_eight
#print axioms KLSConstantImprovement.SourceHookUniformCost.scaled_null_charge
#print axioms KLSConstantImprovement.SourceHookUniformCost.uniform_hook_charge_twenty_eight
#print axioms KLSConstantImprovement.SourceHookUniformCost.uniform_hook_paid_variance
