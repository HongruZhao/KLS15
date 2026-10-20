import WeightedHodgeCore
import KLS.MollificationLocalization
import KLS.WeightedEnergyGraphClosability

/-! Actual mollification equations for the weighted Hodge kernel.
Distributional curl and weighted divergence are tested against genuine C∞
compact functions. No local Sobolev regularity of the vector input is assumed. -/

open MeasureTheory Set Filter ContinuousLinearMap
open scoped BigOperators ContDiff Convolution Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ}

def DistributionallyCurlFree (F : Fin n → Space n → ℝ) : Prop :=
  ∀ (ψ : Space n → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    ∀ i j : Fin n, (∫ x, F i x * coordinateDerivative ψ j x) =
      ∫ x, F j x * coordinateDerivative ψ i x

def WeakWeightedDivergenceFree (φ : Space n → ℝ)
    (F : Fin n → Space n → ℝ) : Prop :=
  ∀ (ψ : Space n → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    (∑ i, ∫ x, F i x * coordinateDerivative ψ i x ∂potentialMeasure φ) = 0

def vectorDriftFlux (φ : Space n → ℝ)
    (F : Fin n → Space n → ℝ) (i : Fin n) : Space n → ℝ :=
  fun x => F i x * coordinateDerivative φ i x

/-- Testing actual distributional curl with a reflected compact kernel
shows that each actual mollification is classically curl free. -/
theorem DistributionallyCurlFree.scalarConvolution
    {F : Fin n → Space n → ℝ} (hcurl : DistributionallyCurlFree F)
    (hloc : ∀ i, LocallyIntegrable (F i) volume)
    {κ : Space n → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hc : HasCompactSupport κ)
    (i j : Fin n) (a : Space n) :
    coordinateDerivative (KLS.scalarConvolution (F i) κ) j a =
      coordinateDerivative (KLS.scalarConvolution (F j) κ) i a := by
  rw [coordinateDerivative_scalarConvolution (hloc i) (hκ.of_le (by simp)) hc,
    coordinateDerivative_scalarConvolution (hloc j) (hκ.of_le (by simp)) hc]
  have he := hcurl (fun y => κ (a - y))
    (hκ.comp (contDiff_const.sub contDiff_id))
    (hc.comp_homeomorph (Homeomorph.subLeft a)) i j
  have hleft (l k : Fin n) :
      (∫ y, F l y * coordinateDerivative (fun z => κ (a - z)) k y) =
      -(KLS.scalarConvolution (F l) (coordinateDerivative κ k) a) := by
    unfold KLS.scalarConvolution
    rw [convolution_def, ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      rw [coordinateDerivative_const_sub (hκ.differentiable (by simp))]
      simp
  rw [hleft, hleft] at he
  exact neg_injective he

theorem DistributionallyCurlFree.mollify
    {F : Fin n → Space n → ℝ} (hcurl : DistributionallyCurlFree F)
    (hloc : ∀ i, LocallyIntegrable (F i) volume) (k : ℕ) (i j : Fin n) (x : Space n) :
    vectorCurl (fun i => mollify k (F i)) i j x = 0 := by
  unfold vectorCurl
  exact sub_eq_zero.mpr (hcurl.scalarConvolution hloc
    (mollifierKernel_contDiff k) (mollifierKernel_hasCompactSupport k) j i x)

/-- The weighted divergence equation becomes an ordinary distributional
divergence equation with the actual drift flux. -/
theorem WeakWeightedDivergenceFree.unweighted_test {φ : Space n → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {F : Fin n → Space n → ℝ}
    (hdiv : WeakWeightedDivergenceFree φ F)
    (hloc : ∀ i, LocallyIntegrable (F i) volume)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    (∑ i, ∫ x, F i x * coordinateDerivative ψ i x) =
      -(∑ i, ∫ x, vectorDriftFlux φ F i x * ψ x) := by
  have he := hdiv (fun x => ψ x * Real.exp (φ x)) (hψ.mul hφ.exp) hc.mul_right
  have hd (i : Fin n) (x : Space n) :
      coordinateDerivative (fun y => ψ y * Real.exp (φ y)) i x =
      Real.exp (φ x) * (coordinateDerivative ψ i x + ψ x * coordinateDerivative φ i x) := by
    have hh := weightedDerivativeTest_exp_mul (hφ.of_le (by simp))
      (hψ.of_le (by simp)) i x
    dsimp only [weightedDerivativeTest] at hh
    linarith
  have hI (i : Fin n) : Integrable (fun x => F i x * coordinateDerivative ψ i x) volume := by
    simpa only [smul_eq_mul] using (hloc i).integrable_smul_right_of_hasCompactSupport
      (contDiff_coordinateDerivative hψ (m := 0) (by simp) i).continuous
      (hasCompactSupport_coordinateDerivative hc i)
  have hJ (i : Fin n) : Integrable (fun x => vectorDriftFlux φ F i x * ψ x) volume := by
    have hh := (hloc i).integrable_smul_right_of_hasCompactSupport
      (((contDiff_coordinateDerivative hφ (m := 0) (by simp) i).continuous).mul hψ.continuous)
      hc.mul_left
    convert hh using 1
    funext x
    dsimp only [vectorDriftFlux, smul_eq_mul, Pi.mul_apply]
    ring
  have hi (i : Fin n) :
      (∫ x, F i x * coordinateDerivative (fun y => ψ y * Real.exp (φ y)) i x
        ∂potentialMeasure φ) =
      (∫ x, F i x * coordinateDerivative ψ i x) +
        ∫ x, vectorDriftFlux φ F i x * ψ x := by
    rw [integral_potentialMeasure hφ.continuous.measurable, ← integral_add (hI i) (hJ i)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [hd]
      dsimp only [vectorDriftFlux]
      calc
        _ = (F i x * coordinateDerivative ψ i x +
          (F i x * coordinateDerivative φ i x) * ψ x) *
            (Real.exp (φ x) * Real.exp (-φ x)) := by ring
        _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  simp only [hi, Finset.sum_add_distrib] at he
  linarith

/-- The derivative sum of the mollified field is exactly the sum of the
mollified actual drift fluxes. -/
theorem WeakWeightedDivergenceFree.scalarConvolution {φ : Space n → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {F : Fin n → Space n → ℝ}
    (hdiv : WeakWeightedDivergenceFree φ F)
    (hloc : ∀ i, LocallyIntegrable (F i) volume)
    {κ : Space n → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hc : HasCompactSupport κ)
    (a : Space n) :
    (∑ i, coordinateDerivative (KLS.scalarConvolution (F i) κ) i a) =
      ∑ i, KLS.scalarConvolution (vectorDriftFlux φ F i) κ a := by
  have he := hdiv.unweighted_test hφ hloc
    (ψ := fun y => κ (a - y)) (hκ.comp (contDiff_const.sub contDiff_id))
    (hc.comp_homeomorph (Homeomorph.subLeft a))
  have hd (i : Fin n) :
      (∫ x, F i x * coordinateDerivative (fun y => κ (a - y)) i x) =
      -(coordinateDerivative (KLS.scalarConvolution (F i) κ) i a) := by
    rw [coordinateDerivative_scalarConvolution (hloc i) (hκ.of_le (by simp)) hc]
    unfold KLS.scalarConvolution
    rw [convolution_def, ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      rw [coordinateDerivative_const_sub (hκ.differentiable (by simp))]
      simp
  simp only [hd, Finset.sum_neg_distrib] at he
  exact neg_injective he

theorem WeakWeightedDivergenceFree.mollify {φ : Space n → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {F : Fin n → Space n → ℝ}
    (hdiv : WeakWeightedDivergenceFree φ F)
    (hloc : ∀ i, LocallyIntegrable (F i) volume) (k : ℕ) (x : Space n) :
    weightedVectorDivergence φ (fun i => mollify k (F i)) x =
      ∑ i, (mollify k (vectorDriftFlux φ F i) x -
        mollify k (F i) x * coordinateDerivative φ i x) := by
  simp only [weightedVectorDivergence, weightedDerivativeTest, KLS.mollify]
  rw [Finset.sum_sub_distrib, hdiv.scalarConvolution hφ hloc
    (mollifierKernel_contDiff k) (mollifierKernel_hasCompactSupport k)]
  rw [Finset.sum_sub_distrib]

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.DistributionallyCurlFree.scalarConvolution
#print axioms KLS.DeterministicBridgeIntegration.WeakWeightedDivergenceFree.scalarConvolution
#print axioms KLS.DeterministicBridgeIntegration.WeakWeightedDivergenceFree.mollify
