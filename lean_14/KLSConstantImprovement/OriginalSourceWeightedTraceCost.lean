import KLSConstantImprovement.SourceThirdAdjointResponse

/-! The original source response is bounded by its weighted trace cost.
The first lemma is the scalar BL/graph-Cauchy step. The Riesz binding
uses the SAME source/core/datum response as SourceThirdAdjointResponse;
geometry, core density, weighted field identification and integrability
remain explicit analytic inputs. No universal numerical trace-cost cap
or new Poincare endpoint is asserted. -/
noncomputable section
namespace KLSConstantImprovement.OriginalSourceWeightedTraceCost

theorem dirichlet_le_graph_energy {d v g : ℝ}
    (hd : 0 ≤ d) (hg : 0 ≤ g)
    (hBL : v ≤ d) (hCS : d^2 ≤ v*g) : d ≤ g := by
  have hp := mul_le_mul_of_nonneg_right hBL hg
  by_contra h
  have hlt : g < d := lt_of_not_ge h
  nlinarith

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- `b=Hhalf e`, `r(A eta)=H^-half grad_y eta` on the same completed
datum range. The source BL/graph lemma pays the contraction on that
range; uniqueness identifies `f` with the existing response. -/
theorem same_response_le_weighted_trace_cost (f : E) (b : F)
    (r : E → F) {C : ℝ}
    (hcontract : ∀ v, ‖r v‖ ≤ ‖v‖)
    (hrep : ∀ v, inner ℝ f v = inner ℝ b (r v))
    (hcost : ‖b‖^2 = C) : ‖f‖^2 ≤ C := by
  have h := SourceThirdAdjointResponse.third_adjoint_norm_coercivity
    f b r hcontract hrep
  simpa only [hcost] using h

theorem exponential_weighted_cost_calibration :
    (6:ℝ)-2*2+1=3 ∧ (2:ℝ)≤3 ∧
    (3:ℝ)=(3/2)*2 := by norm_num

end KLSConstantImprovement.OriginalSourceWeightedTraceCost
#print axioms KLSConstantImprovement.OriginalSourceWeightedTraceCost.dirichlet_le_graph_energy
#print axioms KLSConstantImprovement.OriginalSourceWeightedTraceCost.same_response_le_weighted_trace_cost
#print axioms KLSConstantImprovement.OriginalSourceWeightedTraceCost.exponential_weighted_cost_calibration
