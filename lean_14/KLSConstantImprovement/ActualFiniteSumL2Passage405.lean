import KLSConstantImprovement.ActualWeightedL2PairingContinuity

/-! Finite sums of actual strong L2 limits, with a general fixed measure. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace KLSConstantImprovement.ActualFiniteSumL2Passage405
open KLS ActualWeightedL2PairingContinuity
variable {n : ℕ} {ν : Measure (Space n)} {ι : Type*} [DecidableEq ι]
set_option backward.isDefEq.respectTransparency false

theorem finite_sum_strong_L2 {f : ι → ℕ → Space n → ℝ} {u : ι → Space n → ℝ}
    (s : Finset ι) (hf : ∀ a k, MemLp (f a k) 2 ν) (hu : ∀ a, MemLp (u a) 2 ν)
    (hlim : ∀ a, Tendsto (fun k => eLpNorm (f a k - u a) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm ((∑ a ∈ s, f a k) - (∑ a ∈ s, u a)) 2 ν)
      atTop (𝓝 0) := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, sub_self, eLpNorm_zero]
      exact tendsto_const_nhds
  | @insert a s ha hs =>
      simp only [Finset.sum_insert ha]
      exact weighted_L2_add_tendsto (hf a)
        (fun k => by
          convert memLp_finsetSum s (fun b _ => hf b k) using 1
          funext x
          simp only [Finset.sum_apply]) (hu a)
        (by
          convert memLp_finsetSum s (fun b _ => hu b) using 1
          funext x
          simp only [Finset.sum_apply]) (hlim a) hs

end KLSConstantImprovement.ActualFiniteSumL2Passage405
#print axioms KLSConstantImprovement.ActualFiniteSumL2Passage405.finite_sum_strong_L2
