import WeightedCompactFiberDensity
import WeightedMatrixGraphRepresentatives

/-! The genuine constrained exterior derivative has a dense domain,
proved using actual compact symmetric representatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology LinearPMap
namespace KLS.DeterministicBridgeIntegration
variable {n q : ℕ} {φ : Space n → ℝ}

lemma tensorOneFormConstraint_zero_iff (v : EuclideanSpace ℝ (TensorOneFormIndex n q)) :
    (∀ a, (∑ b, tensorOneFormConstraintMatrix n q a b * v b) = 0) ↔
      v ∈ tensorOneFormSymmetricFiber n q := by
  simp only [tensorOneFormConstraintMatrix_apply]
  constructor
  · intro h
    exact Submodule.starProjection_eq_self_iff.mp (PiLp.ext fun a => (sub_eq_zero.mp (h a)).symm)
  · intro h a
    exact sub_eq_zero.mpr (congrArg (fun v : EuclideanSpace ℝ (TensorOneFormIndex n q) => v a)
      (Submodule.starProjection_eq_self_iff.mpr h)).symm

lemma tensorExteriorOneDifferential_contDiff
    {f : TensorOneFormIndex n q → Space n → ℝ}
    (hf : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (f a)) (z : TensorTwoFormIndex n q) :
    ContDiff ℝ (⊤ : ℕ∞) (tensorExteriorOneDifferential f z) :=
  contDiff_const.mul ((contDiff_coordinateDerivative (hf _) (m := (⊤ : ℕ∞)) (by simp) _).sub
    (contDiff_coordinateDerivative (hf _) (m := (⊤ : ℕ∞)) (by simp) _))

lemma tensorExteriorOneDifferential_compact
    {f : TensorOneFormIndex n q → Space n → ℝ}
    (hc : ∀ a, HasCompactSupport (f a)) (z : TensorTwoFormIndex n q) :
    HasCompactSupport (tensorExteriorOneDifferential f z) :=
  ((hasCompactSupport_coordinateDerivative (hc _) _).sub
    (hasCompactSupport_coordinateDerivative (hc _) _)).mul_left

/-- Every genuine smooth compact one-form in the literal fully symmetric
fiber belongs to the actual maximal constrained d₁ domain. -/
theorem compactSmoothFiberSet_subset_exteriorOne_domain
    (hφ : ContDiff ℝ 1 φ) (q : ℕ) :
    compactSmoothFiberSet φ (tensorOneFormConstraintMatrix n q) ⊆
      ((tensorExteriorOneOperator hφ q).domain : Set (TensorOneFormL2 φ q)) := by
  rintro u ⟨f, hf, hc, hflp, hu⟩
  have hmem : finiteMatrixLp f hflp ∈ tensorOneFormL2Subspace φ q := hu ▸ u.property
  have hrows := (continuous_finiteMatrixLp_mem_constraint_iff_forall hφ.continuous
    (tensorOneFormConstraintMatrix n q) hflp (fun a => (hf a).continuous)).mp hmem
  have hpoint (x : Space n) : WithLp.toLp 2 (fun a => f a x) ∈ tensorOneFormSymmetricFiber n q :=
    (tensorOneFormConstraint_zero_iff _).mp (fun a => hrows a x)
  let df := tensorExteriorOneDifferential f
  have hdf (z : TensorTwoFormIndex n q) : MemLp (df z) 2 (potentialMeasure φ) :=
    memLp_of_continuous_hasCompactSupport hφ.continuous
      (tensorExteriorOneDifferential_contDiff hf z).continuous (tensorExteriorOneDifferential_compact hc z)
  have hdmem : finiteMatrixLp df hdf ∈ tensorTwoFormL2Subspace φ q :=
    (finiteMatrixLp_mem_twoForm_iff hdf).mpr (Eventually.of_forall
      (fun x => tensorExteriorOneDifferential_compatible hpoint x))
  have hw : HasWeakMatrixDerivative (tensorExteriorOneDerivativeMatrix n q) f df := by
    have hd := matrixDifferential_hasWeakMatrixDerivative (tensorExteriorOneDerivativeMatrix n q)
      (fun a => (hf a).of_le (by simp))
    have he : matrixDifferential (tensorExteriorOneDerivativeMatrix n q) f = df :=
      funext fun z => funext fun x => tensorExteriorOne_matrixDifferential f z x
    exact he ▸ hd
  have hgraph := finiteMatrixLp_mem_weightedMatrixFiberGraph hφ
    (tensorExteriorOneDerivativeMatrix n q) (tensorOneFormL2Subspace φ q)
    (tensorTwoFormL2Subspace φ q) hflp hdf hmem hdmem hw
  change u ∈ (weightedMatrixFiberGraph hφ (tensorExteriorOneDerivativeMatrix n q)
    (tensorOneFormL2Subspace φ q) (tensorTwoFormL2Subspace φ q)).map (LinearMap.fst ℝ _ _)
  exact ⟨(⟨finiteMatrixLp f hflp, hmem⟩, ⟨finiteMatrixLp df hdf, hdmem⟩), hgraph,
    Subtype.ext hu.symm⟩

/-- Dense domain is proved on the actual constrained weighted Hilbert
space; no domain-density hypothesis is exposed to the endpoint. -/
theorem tensorExteriorOneOperator_domain_dense (hφ : ContDiff ℝ 1 φ) (q : ℕ) :
    Dense ((tensorExteriorOneOperator hφ q).domain : Set (TensorOneFormL2 φ q)) :=
  (compactSmoothFiberSet_dense hφ.continuous (tensorOneFormConstraintMatrix n q)).mono
    (compactSmoothFiberSet_subset_exteriorOne_domain hφ q)

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorExteriorOneOperator_domain_dense
