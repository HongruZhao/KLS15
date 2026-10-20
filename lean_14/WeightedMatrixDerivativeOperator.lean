import TensorMaximalHodgeCoercivity
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Genuine closed maximal weighted L² differential operators for constant
finite principal matrices, also between fixed closed tensor fibers. The
graph uses all ordinary smooth compact distributional tests. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology LinearPMap
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {φ : Space n → ℝ}
variable {ι ρ : Type*} [Fintype ι] [Fintype ρ]

/-- Density-cancelled compact test, representing an ordinary volume pairing. -/
def weightedCompactTestLp (hφ : Continuous φ) {ψ : Space n → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) : Lp ℝ 2 (potentialMeasure φ) :=
  (memLp_of_continuous_hasCompactSupport hφ (hψ.mul (Real.continuous_exp.comp hφ)) hc.mul_right).toLp
    (fun x => ψ x * Real.exp (φ x))

lemma weightedCompactTestLp_inner (hφ : Continuous φ) {ψ : Space n → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (f : Lp ℝ 2 (potentialMeasure φ)) :
    inner ℝ (weightedCompactTestLp hφ hψ hc) f = ∫ x, f x * ψ x := by
  rw [L2.inner_def]
  have hae : (weightedCompactTestLp hφ hψ hc : Space n → ℝ) =ᵐ[potentialMeasure φ]
      fun x => ψ x * Real.exp (φ x) :=
    (memLp_of_continuous_hasCompactSupport hφ (hψ.mul (Real.continuous_exp.comp hφ)) hc.mul_right).coeFn_toLp
  have he : (∫ x, inner ℝ (weightedCompactTestLp hφ hψ hc x) (f x) ∂potentialMeasure φ) =
      ∫ x, (f x * ψ x) * Real.exp (φ x) ∂potentialMeasure φ := by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial]
    ring
  rw [he, integral_potentialMeasure hφ.measurable]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    calc
      _ = (f x * ψ x) * (Real.exp (φ x) * Real.exp (-φ x)) := by ring
      _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

def weightedMatrixDerivativeTest (hφ : ContDiff ℝ 1 φ) (A : ρ → Fin n → ι → ℝ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (a : ρ) :
    (CenteredL2.Family (potentialMeasure φ) ι × CenteredL2.Family (potentialMeasure φ) ρ) →L[ℝ] ℝ :=
  ((innerSL ℝ (weightedCompactTestLp hφ.continuous hψ.continuous hc)).comp
    (PiLp.proj 2 (fun _ : ρ => Lp ℝ 2 (potentialMeasure φ)) a)).comp
      (ContinuousLinearMap.snd ℝ _ _) +
  ∑ i : Fin n, ∑ j : ι, A a i j •
    (((innerSL ℝ (weightedCurlTestLp hφ hψ hc i)).comp
      (PiLp.proj 2 (fun _ : ι => Lp ℝ 2 (potentialMeasure φ)) j)).comp
        (ContinuousLinearMap.fst ℝ _ _))

lemma weightedMatrixDerivativeTest_apply (hφ : ContDiff ℝ 1 φ)
    (A : ρ → Fin n → ι → ℝ) {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (a : ρ)
    (p : CenteredL2.Family (potentialMeasure φ) ι × CenteredL2.Family (potentialMeasure φ) ρ) :
    weightedMatrixDerivativeTest hφ A hψ hc a p =
      (∫ x, p.2 a x * ψ x) + ∑ i : Fin n, ∑ j : ι,
        A a i j * ∫ x, p.1 j x * coordinateDerivative ψ i x := by
  simp only [weightedMatrixDerivativeTest, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.snd, ContinuousLinearMap.fst,
    PiLp.proj_apply, innerSL_apply_apply, weightedCompactTestLp_inner,
    weightedCurlTestLp_inner, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rfl

def weightedMatrixDerivativeGraph (hφ : ContDiff ℝ 1 φ) (A : ρ → Fin n → ι → ℝ) :
    Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ι × CenteredL2.Family (potentialMeasure φ) ρ) :=
  ⨅ (ψ : Space n → ℝ), ⨅ (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ), ⨅ (hc : HasCompactSupport ψ),
    ⨅ a : ρ, LinearMap.ker (weightedMatrixDerivativeTest hφ A hψ hc a).toLinearMap

lemma weightedMatrixDerivativeGraph_isClosed (hφ : ContDiff ℝ 1 φ)
    (A : ρ → Fin n → ι → ℝ) :
    IsClosed (weightedMatrixDerivativeGraph hφ A :
      Set (CenteredL2.Family (potentialMeasure φ) ι × CenteredL2.Family (potentialMeasure φ) ρ)) := by
  simp only [weightedMatrixDerivativeGraph, Submodule.coe_iInf]
  exact isClosed_iInter fun ψ => isClosed_iInter fun hψ => isClosed_iInter fun hc =>
    isClosed_iInter fun a => (weightedMatrixDerivativeTest hφ A hψ hc a).isClosed_ker

lemma mem_weightedMatrixDerivativeGraph_iff (hφ : ContDiff ℝ 1 φ)
    (A : ρ → Fin n → ι → ℝ)
    (p : CenteredL2.Family (potentialMeasure φ) ι × CenteredL2.Family (potentialMeasure φ) ρ) :
    p ∈ weightedMatrixDerivativeGraph hφ A ↔
      HasWeakMatrixDerivative A (fun j x => p.1 j x) (fun a x => p.2 a x) := by
  simp only [weightedMatrixDerivativeGraph, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h ψ hψ hc a
    have he := h ψ hψ hc a
    change weightedMatrixDerivativeTest hφ A hψ hc a p = 0 at he
    rw [weightedMatrixDerivativeTest_apply] at he
    exact eq_neg_of_add_eq_zero_left he
  · intro h ψ hψ hc a
    change weightedMatrixDerivativeTest hφ A hψ hc a p = 0
    rw [weightedMatrixDerivativeTest_apply, h ψ hψ hc a]
    exact neg_add_cancel _

lemma weightedMatrixDerivativeGraph_singleValued (hφ : ContDiff ℝ 1 φ)
    (A : ρ → Fin n → ι → ℝ) (p : CenteredL2.Family (potentialMeasure φ) ι ×
      CenteredL2.Family (potentialMeasure φ) ρ)
    (hp : p ∈ weightedMatrixDerivativeGraph hφ A) (hz : p.1 = 0) : p.2 = 0 := by
  have hw := (mem_weightedMatrixDerivativeGraph_iff hφ A p).mp hp
  apply PiLp.ext
  intro a
  have hl := KLS.MemLp.locallyIntegrable_volume_of_potentialMeasure (Lp.memLp (p.2 a)) hφ.continuous
  have hzero : (p.2 a : Space n → ℝ) =ᵐ[volume] 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero hl (fun ψ hψ hc => by
      have he := hw ψ hψ hc a
      rw [hz] at he
      have hzi (i : Fin n) : (∫ x, (0 : Lp ℝ 2 (potentialMeasure φ)) x *
          coordinateDerivative ψ i x) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [(volume_absolutelyContinuous_potentialMeasure hφ.continuous).ae_eq
          (Lp.coeFn_zero ℝ 2 (potentialMeasure φ))] with x hx
        simpa only [hx, Pi.zero_apply, zero_mul]
      dsimp only at he
      simp only [PiLp.zero_apply, hzi, Finset.sum_const_zero, mul_zero, neg_zero] at he
      simpa only [smul_eq_mul, mul_comm] using he)
  apply Lp.ext
  filter_upwards [(withDensity_absolutelyContinuous _ _).ae_eq hzero,
    Lp.coeFn_zero ℝ 2 (potentialMeasure φ)] with x hx hz
  exact hx.trans hz.symm

def weightedMatrixDerivativeOperator (hφ : ContDiff ℝ 1 φ) (A : ρ → Fin n → ι → ℝ) :
    CenteredL2.Family (potentialMeasure φ) ι →ₗ.[ℝ] CenteredL2.Family (potentialMeasure φ) ρ :=
  (weightedMatrixDerivativeGraph hφ A).toLinearPMap

lemma weightedMatrixDerivativeOperator_graph (hφ : ContDiff ℝ 1 φ)
    (A : ρ → Fin n → ι → ℝ) :
    (weightedMatrixDerivativeOperator hφ A).graph = weightedMatrixDerivativeGraph hφ A :=
  Submodule.toLinearPMap_graph_eq _ (weightedMatrixDerivativeGraph_singleValued hφ A)

/-- The actual full maximal ordinary-distributional operator is closed in
weighted L². No graph-closure or domain equality is assumed. -/
theorem weightedMatrixDerivativeOperator_isClosed (hφ : ContDiff ℝ 1 φ)
    (A : ρ → Fin n → ι → ℝ) : (weightedMatrixDerivativeOperator hφ A).IsClosed := by
  rw [LinearPMap.IsClosed, weightedMatrixDerivativeOperator_graph]
  exact weightedMatrixDerivativeGraph_isClosed hφ A

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.weightedMatrixDerivativeOperator_isClosed
