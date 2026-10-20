import FirstOrderMatrixGraphCore

/-! Literal finite ordered-coordinate fibers for the constrained tensor
Hodge complex. Two-form coefficients use the normalized ordered-pair
coordinates ω_ij / √2, and three-form coefficients use ω_ijk / √6.
The first-order core is proved for the actual constant derivative matrices
and the actual potential-gradient drift. Curvature identities are separate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n q : ℕ} {φ : Space n → ℝ}

abbrev TensorOneFormIndex (n q : ℕ) := OrderedTensorIndex n q × Fin n
abbrev TensorTwoFormIndex (n q : ℕ) := OrderedTensorIndex n q × (Fin n × Fin n)
abbrev TensorThreeFormIndex (n q : ℕ) := OrderedTensorIndex n q × (Fin n × Fin n × Fin n)
abbrev TensorHodgeOutputIndex (n q : ℕ) := TensorThreeFormIndex n q ⊕ TensorOneFormIndex n q
abbrev TensorTwoFormConstraintIndex (n q : ℕ) :=
  (OrderedTensorIndex n q × OrderedTensorIndex n q × (Fin n × Fin n)) ⊕
    (TensorTwoFormIndex n q ⊕ TensorThreeFormIndex n q)

def tensorOneFormDifference (a b : TensorOneFormIndex n q) :
    EuclideanSpace ℝ (TensorOneFormIndex n q) →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ : TensorOneFormIndex n q => ℝ) a :
    EuclideanSpace ℝ (TensorOneFormIndex n q) →L[ℝ] ℝ) -
    PiLp.proj 2 (fun _ : TensorOneFormIndex n q => ℝ) b

/-- The genuine one-form ker b fiber, written as complete symmetry of
the auxiliary slots together with the exterior one-form slot. -/
def tensorOneFormSymmetricFiber (n q : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ (TensorOneFormIndex n q)) :=
  ⨅ a, ⨅ b, ⨅ (_ : List.Perm (List.ofFn (Fin.cons a.2 a.1))
    (List.ofFn (Fin.cons b.2 b.1))), LinearMap.ker (tensorOneFormDifference a b).toLinearMap

lemma tensorOneFormSymmetricFiber_isClosed :
    IsClosed (tensorOneFormSymmetricFiber n q : Set (EuclideanSpace ℝ (TensorOneFormIndex n q))) := by
  simp only [tensorOneFormSymmetricFiber, Submodule.coe_iInf]
  exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
    (tensorOneFormDifference a b).isClosed_ker

instance tensorOneFormSymmetricFiber_complete : CompleteSpace (↥(tensorOneFormSymmetricFiber n q)) :=
  tensorOneFormSymmetricFiber_isClosed.isComplete.completeSpace_coe

def tensorOneFormProjection (n q : ℕ) :
    EuclideanSpace ℝ (TensorOneFormIndex n q) →L[ℝ]
      EuclideanSpace ℝ (TensorOneFormIndex n q) :=
  (tensorOneFormSymmetricFiber n q).starProjection

def tensorOneFormProjectionMatrix (a b : TensorOneFormIndex n q) : ℝ :=
  tensorOneFormProjection n q (EuclideanSpace.single b 1) a

lemma finite_euclidean_coordinate_expansion {τ : Type*} [Fintype τ] [DecidableEq τ]
    (v : EuclideanSpace ℝ τ) : v = ∑ j, v j • EuclideanSpace.single j 1 := by
  apply PiLp.ext
  intro i
  change v i = (PiLp.proj 2 (fun _ : τ => ℝ) i : EuclideanSpace ℝ τ →L[ℝ] ℝ)
    (∑ j, v j • EuclideanSpace.single j 1)
  rw [map_sum]
  simp only [PiLp.proj_apply, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.single_apply, Pi.single_apply]
  simp

lemma tensorOneFormProjection_matrix_apply (v : EuclideanSpace ℝ (TensorOneFormIndex n q))
    (a : TensorOneFormIndex n q) :
    tensorOneFormProjection n q v a = ∑ b, tensorOneFormProjectionMatrix a b * v b := by
  conv_lhs => rw [finite_euclidean_coordinate_expansion v]
  rw [map_sum]
  change (PiLp.proj 2 (fun _ : TensorOneFormIndex n q => ℝ) a :
    EuclideanSpace ℝ (TensorOneFormIndex n q) →L[ℝ] ℝ)
    (∑ b, tensorOneFormProjection n q (v b • EuclideanSpace.single b 1)) = _
  rw [map_sum]
  simp only [map_smul, PiLp.proj_apply, PiLp.smul_apply, smul_eq_mul,
    tensorOneFormProjectionMatrix, mul_comm]

def tensorAuxReplaceFirst (I : OrderedTensorIndex n q) (i : Fin n) : OrderedTensorIndex n q :=
  fun k => if k.val = 0 then i else I k

/-- The rows encode auxiliary symmetry, exterior skew symmetry, and the
literal normalized Koszul equation bω=0. At auxiliary rank zero b=0. -/
def tensorTwoFormConstraintMatrix (n q : ℕ) :
    TensorTwoFormConstraintIndex n q → TensorTwoFormIndex n q → ℝ
  | Sum.inl (I, J, ij), z =>
      if List.Perm (List.ofFn I) (List.ofFn J) then
        (if z = (I, ij) then 1 else 0) - (if z = (J, ij) then 1 else 0)
      else 0
  | Sum.inr (Sum.inl (I, i, j)), z =>
      (if z = (I, i, j) then 1 else 0) + (if z = (I, j, i) then 1 else 0)
  | Sum.inr (Sum.inr (I, i, j, k)), z =>
      Real.sqrt q * ((if z = (tensorAuxReplaceFirst I i, j, k) then 1 else 0) -
        (if z = (tensorAuxReplaceFirst I j, i, k) then 1 else 0) +
        (if z = (tensorAuxReplaceFirst I k, i, j) then 1 else 0))

def tensorTwoFormConstraintFunctional (a : TensorTwoFormConstraintIndex n q) :
    EuclideanSpace ℝ (TensorTwoFormIndex n q) →L[ℝ] ℝ :=
  ∑ z, (tensorTwoFormConstraintMatrix n q a z) •
    PiLp.proj 2 (fun _ : TensorTwoFormIndex n q => ℝ) z

def tensorTwoFormFiber (n q : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ (TensorTwoFormIndex n q)) :=
  ⨅ a, LinearMap.ker (tensorTwoFormConstraintFunctional a).toLinearMap

lemma mem_tensorTwoFormFiber_iff (v : EuclideanSpace ℝ (TensorTwoFormIndex n q)) :
    v ∈ tensorTwoFormFiber n q ↔ ∀ a, (∑ z, tensorTwoFormConstraintMatrix n q a z * v z) = 0 := by
  simp only [tensorTwoFormFiber, Submodule.mem_iInf, LinearMap.mem_ker,
    tensorTwoFormConstraintFunctional, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, PiLp.proj_apply, smul_eq_mul]

lemma tensorTwoFormFiber_isClosed :
    IsClosed (tensorTwoFormFiber n q : Set (EuclideanSpace ℝ (TensorTwoFormIndex n q))) := by
  simp only [tensorTwoFormFiber, Submodule.coe_iInf]
  exact isClosed_iInter fun a => (tensorTwoFormConstraintFunctional a).isClosed_ker

/-- The actual d₂ and P₁d₁* principal matrices, in normalized ordered
exterior coordinates. The positive weighted adjoint derivative is -∂+φᵢ. -/
def tensorHodgeDerivativeMatrix (n q : ℕ) :
    TensorHodgeOutputIndex n q → Fin n → TensorTwoFormIndex n q → ℝ
  | Sum.inl (I, i, j, k), l, z =>
      (1 / Real.sqrt 3) *
        ((if l = i ∧ z = (I, j, k) then 1 else 0) -
          (if l = j ∧ z = (I, i, k) then 1 else 0) +
          (if l = k ∧ z = (I, i, j) then 1 else 0))
  | Sum.inr a, l, (I, i, j) =>
      -(Real.sqrt 2) * tensorOneFormProjectionMatrix a (I, j) * (if l = i then 1 else 0)

def tensorHodgeDriftMatrix (φ : Space n → ℝ) (q : ℕ) :
    TensorHodgeOutputIndex n q → TensorTwoFormIndex n q → Space n → ℝ
  | Sum.inl _, _, _ => 0
  | Sum.inr a, (I, i, j), x =>
      Real.sqrt 2 * tensorOneFormProjectionMatrix a (I, j) * coordinateDerivative φ i x

lemma tensorHodgeDriftMatrix_continuous (hφ : ContDiff ℝ 1 φ) (q : ℕ)
    (a : TensorHodgeOutputIndex n q) (z : TensorTwoFormIndex n q) :
    Continuous (tensorHodgeDriftMatrix φ q a z) := by
  cases a with
  | inl a => exact continuous_const
  | inr a => exact (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) z.2.1).continuous.const_mul _

/-- The literal combined maximal weak constrained Hodge domain. -/
def HasWeakConstrainedTensorHodge (φ : Space n → ℝ) (q : ℕ)
    (f : TensorTwoFormIndex n q → Space n → ℝ)
    (g : TensorHodgeOutputIndex n q → Space n → ℝ) : Prop :=
  HasWeakMatrixFirstOrder (tensorHodgeDerivativeMatrix n q) (tensorHodgeDriftMatrix φ q) f g ∧
    ∀ a, (fun x => ∑ z, tensorTwoFormConstraintMatrix n q a z * f z x) =ᵐ[volume] 0

/-- Genuine simultaneous compact approximation of d₂ and P₁d₁* on the
full actual distributional matrix domain, retaining bω=0 and all fiber
symmetries. Identification with the Hilbert adjoint domain is separate. -/
theorem constrained_tensorHodge_graph_core (hφ : ContDiff ℝ 1 φ) (q : ℕ)
    {f : TensorTwoFormIndex n q → Space n → ℝ}
    {g : TensorHodgeOutputIndex n q → Space n → ℝ}
    (h : HasWeakConstrainedTensorHodge φ q f g)
    (hf : ∀ z, MemLp (f z) 2 (potentialMeasure φ))
    (hg : ∀ a, MemLp (g a) 2 (potentialMeasure φ)) :
    (finiteMatrixLp f hf, finiteMatrixLp g hg) ∈ closure
      (compactMatrixGraphSet (φ := φ) (tensorHodgeDerivativeMatrix n q)
        (tensorHodgeDriftMatrix φ q) (tensorTwoFormConstraintMatrix n q)) :=
  matrix_maximal_graph_mem_closure_compact_graph hφ.continuous _
    (tensorHodgeDriftMatrix_continuous hφ q) _ h.1 hf hg h.2

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorOneFormProjection_matrix_apply
#print axioms KLS.DeterministicBridgeIntegration.constrained_tensorHodge_graph_core
