import KLSConstantImprovement.ResumeRaw4047255BellmanOperator
import ActualKLS149963Endpoints

/-! Conditional original-class endpoint: the sole added premise is the
universal raw404.7255 observation bound. Every other analytic and scalar
input is proved. This does not assert original-law raw404.7255. -/
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff ENNReal NNReal
namespace KLSConstantImprovement.ResumeRaw4047255BellmanConditionalEndpoint
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.ResumeRaw4047255BellmanOperator
open KLSConstantImprovement.ResumeRaw4047255BellmanData
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def bound : ℝ := 1400840517562834548357/97656250000000000000

theorem regular_poincare
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound (809451/2000))
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hn : 0 < n) (hμ : admissibleMeasure (potentialMeasure φ)) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal bound := by
  have hnorm := operator_norm_sq_le hφ hκ hlower hμ hraw
  have hb : 1+‖gradedTensorIntegration hφ hκ hlower‖^2 ≤ bound := by
    calc
      _ ≤ 1+K*p := by linarith
      _ = bound := by norm_num [K,p,bound]
  exact (poincareConstant_le_one_add_graded_norm_sq hφ hκ hlower hn hμ.isotropic).trans
    (ENNReal.ofReal_le_ofReal hb)

theorem original_poincare_mem
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound (809451/2000)) {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (1400840517562834548357/97656250000000000000 : ℝ≥0) ∈ poincareConstants μ := by
  apply mem_poincareConstants_of_paperRegularDensity hμ (by norm_num)
  intro ν hν hregular
  obtain ⟨V,κ,hV,hκ,hstrong,hupper,hgrowth,heq⟩ := hregular
  subst ν
  let : IsProbabilityMeasure (potentialMeasure V) := hν.isProb
  let hlower := coordinateHessian_lower_of_strongConvexOn (hV.of_le (by simp)) hstrong
  have hc := regular_poincare hraw hV hκ hlower (by omega) hν
  have hfin : poincareConstant (potentialMeasure V) < ⊤ := hc.trans_lt ENNReal.ofReal_lt_top
  apply (poincareConstants_iff_optimal_le (poincareConstants_nonempty_iff.mpr hfin)
    (hν.poincareConstant_pos hn)).mpr
  convert hc using 1
  unfold bound
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 97656250000000000000)]
  norm_num

theorem original_poincare
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound (809451/2000)) {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (1400840517562834548357/97656250000000000000 : ℝ≥0∞)*energy μ f := by
  simpa using original_poincare_mem hraw hn hμ f hf

theorem universal_poincare_upper
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound (809451/2000)) :
    universalPoincareConstant ≤ (1400840517562834548357/97656250000000000000 : ℝ≥0∞) := by
  apply universal_le_iff.mpr
  intro n hn μ hμ
  simpa using poincareConstant_le_of_mem (original_poincare_mem hraw hn hμ)

theorem bound_lt_previous : bound < (14365931903 : ℝ)/1000000000 := by
  norm_num [bound]

theorem bound_lt_fourteen_point_four : bound < 72/5 := by
  norm_num [bound]

theorem bound_lt_original_bellman : bound < 1434537805407/100000000000 := by
  norm_num [bound]

theorem universal_poincare_rounded
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound (809451/2000)) :
    universalPoincareConstant ≤ (14345234772/1000000000 : ℝ≥0∞) := by
  have hh : ENNReal.ofReal bound ≤ ENNReal.ofReal (14345234772/1000000000 : ℝ) :=
    ENNReal.ofReal_le_ofReal (by norm_num [bound])
  have hleft : ENNReal.ofReal bound=(1400840517562834548357/97656250000000000000 : ℝ≥0∞) := by
    unfold bound
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 97656250000000000000)]
    norm_num
  have hright : ENNReal.ofReal (14345234772/1000000000 : ℝ)=
      (14345234772/1000000000 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 1000000000)]
    norm_num
  rw [hleft,hright] at hh
  exact (universal_poincare_upper hraw).trans hh

theorem openai_poincare
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound (809451/2000)) {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ)
      ((1400840517562834548357 : ℝ)/97656250000000000000) :=
  OpenAIBridge.poincareBound_of_mem hρ
    (original_poincare_mem hraw hn (OpenAIBridge.admissible hρ hiso))

end KLSConstantImprovement.ResumeRaw4047255BellmanConditionalEndpoint
#print axioms KLSConstantImprovement.ResumeRaw4047255BellmanConditionalEndpoint.regular_poincare
#print axioms KLSConstantImprovement.ResumeRaw4047255BellmanConditionalEndpoint.original_poincare_mem
#print axioms KLSConstantImprovement.ResumeRaw4047255BellmanConditionalEndpoint.original_poincare
#print axioms KLSConstantImprovement.ResumeRaw4047255BellmanConditionalEndpoint.universal_poincare_upper
#print axioms KLSConstantImprovement.ResumeRaw4047255BellmanConditionalEndpoint.bound_lt_previous
#print axioms KLSConstantImprovement.ResumeRaw4047255BellmanConditionalEndpoint.openai_poincare

#print axioms KLSConstantImprovement.ResumeRaw4047255BellmanConditionalEndpoint.bound_lt_fourteen_point_four

#print axioms KLSConstantImprovement.ResumeRaw4047255BellmanConditionalEndpoint.bound_lt_original_bellman
#print axioms KLSConstantImprovement.ResumeRaw4047255BellmanConditionalEndpoint.universal_poincare_rounded
