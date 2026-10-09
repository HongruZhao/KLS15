import ActualAppellEnergyEvolution
import KLS.SubsetLowerContraction

/-! Dimension-free contractions of actual cumulant and Appell tensors.
The only norm input is a previous actual Appell coefficient bound. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
variable {n a b : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem cumulantTensor_snoc_coordinate_sum (μ : Measure (Space n))
    (m : Fin a → Space n) (v : Space n) :
    cumulantTensor μ (a+1) (Fin.snoc m v) =
      ∑ i : Fin n, v i*cumulantTensor μ (a+1) (Fin.snoc m (EuclideanSpace.single i 1)) := by
  classical
  let T := (cumulantTensor μ (a+1)).toMultilinearMap
  let L := T.toLinearMap (Fin.snoc m 0) (Fin.last a)
  have he (u : Space n) : L u = cumulantTensor μ (a+1) (Fin.snoc m u) := by
    change T (Function.update (Fin.snoc m 0) (Fin.last a) u) = _
    rw [Fin.update_snoc_last]
    rfl
  calc
    _ = L v := (he v).symm
    _ = L (∑ i : Fin n, v i • EuclideanSpace.single i 1) :=
      congrArg L (euclidean_sum_coordinate_single v).symm
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul,he]
      rfl

 def actualCanonicalAppellContraction (μ : Measure (Space n)) (f : Space n → ℝ)
    (a b : ℕ) (α : Fin a → Fin n) (β : Fin b → Fin n) : ℝ :=
  ∑ i : Fin n,
    cumulantTensor μ (a+1)
      (Fin.snoc (fun j => EuclideanSpace.single (α j) 1) (EuclideanSpace.single i 1))*
    actualAppellCoefficient μ f (b+1) (Fin.cons i β)

 theorem actualCanonicalAppellContraction_eq_linear_coefficient
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (f : Space n → ℝ) (a b : ℕ) (α : Fin a → Fin n) (β : Fin b → Fin n) :
    actualCanonicalAppellContraction μ f a b α β =
      actualAppellCoefficient μ
        (fun x => inner ℝ x
          (WithLp.toLp 2 (fun i => actualAppellCoefficient μ f (b+1) (Fin.cons i β)) : Space n)) a α := by
  rw [actualAppellCoefficient_inner_eq_cumulant hLC,
    cumulantTensor_snoc_coordinate_sum]
  unfold actualCanonicalAppellContraction
  apply Finset.sum_congr rfl
  intro i hi
  change _ = actualAppellCoefficient μ f (b+1) (Fin.cons i β)*_
  simp only [EuclideanSpace.basisFun_apply]
  ring

 /-- The canonical one-slot contraction obeys (3.21) without a dimension
 factor. Fixed remaining Appell indices form a genuine Euclidean vector. -/
 theorem actualCanonicalAppellContraction_square_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (f : Space n → ℝ) (a b : ℕ) {h : ℝ}
    (hA : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualAppellEnergy μ g a ≤ h*(∫ x, (g x)^2 ∂μ)) :
    (∑ α : Fin a → Fin n, ∑ β : Fin b → Fin n,
      (actualCanonicalAppellContraction μ f a b α β)^2) ≤ h*actualAppellEnergy μ f (b+1) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  rw [Finset.sum_comm]
  have hp (β : Fin b → Fin n) :
      (∑ α : Fin a → Fin n, (actualCanonicalAppellContraction μ f a b α β)^2) ≤
        h*(∑ i : Fin n, (actualAppellCoefficient μ f (b+1) (Fin.cons i β))^2) := by
    let v : Space n := WithLp.toLp 2 (fun i => actualAppellCoefficient μ f (b+1) (Fin.cons i β))
    have hv : (∫ x, (inner ℝ x v)^2 ∂μ) =
        ∑ i : Fin n, (actualAppellCoefficient μ f (b+1) (Fin.cons i β))^2 := by
      rw [hμ.isotropic.integral_inner_sq,EuclideanSpace.real_norm_sq_eq]
    have hh := hA (fun x => inner ℝ x v) (hμ.isotropic.memLp_inner v)
    rw [hv] at hh
    simpa only [actualAppellEnergy,actualCanonicalAppellContraction_eq_linear_coefficient hμ.logConcave,
      v] using hh
  calc
    _ ≤ ∑ β : Fin b → Fin n, h*(∑ i : Fin n,
        (actualAppellCoefficient μ f (b+1) (Fin.cons i β))^2) :=
      Finset.sum_le_sum fun β hβ => hp β
    _ = h*actualAppellEnergy μ f (b+1) := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      congr 1
      have hh := actualAppell_next_slices_square μ f b
      simpa only [dotProduct,pow_two] using hh

 def actualSubsetAppellContraction (μ : Measure (Space n)) (f : Space n → ℝ)
    (d : ℕ) (S : Finset (Fin d)) (γ : Fin d → Fin n) : ℝ :=
  ∑ i : Fin n,
    listCumulant μ
      (maskedDirections (fun j => EuclideanSpace.single (γ j) 1)
        (fun j => decide (j ∈ S))++[EuclideanSpace.single i 1])*
    directionalWordDerivative (actualDampedAverage μ f 0)
      (maskedDirections (fun j => EuclideanSpace.single (γ j) 1)
        (fun j => !(decide (j ∈ S)))++[EuclideanSpace.single i 1]) 0

 theorem actualSubsetAppellContraction_reindex
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {d : ℕ} (S : Finset (Fin d))
    (α : Fin S.card → Fin n) (β : Fin Sᶜ.card → Fin n) :
    actualSubsetAppellContraction μ f d S (subsetCoordinateEquiv S (α,β)) =
      actualCanonicalAppellContraction μ f S.card Sᶜ.card α β := by
  obtain ⟨r,hr,hD,h1⟩ := exists_common_local_exponential_domains hLC hf
  have hA := contDiffOn_actualDampedAverage hD h1 (show (0 : ℝ) ≤ 0 from le_rfl)
  have hC := contDiffOn_logLaplace_of_local h1
  have h0 : (0 : Space n) ∈ ball 0 r := by simpa using hr
  let γ := subsetCoordinateEquiv S (α,β)
  let m : Fin d → Space n := fun j => EuclideanSpace.single (γ j) 1
  have hp : (maskedDirections m (fun j => decide (j ∈ S))).Perm
      (List.ofFn (fun j => EuclideanSpace.single (α j) 1)) := by
    simpa only [m,γ,subsetCoordinateEquiv_left] using maskedDirections_perm_orderEmb m S
  have hq : (maskedDirections m (fun j => !(decide (j ∈ S)))).Perm
      (List.ofFn (fun j => EuclideanSpace.single (β j) 1)) := by
    have hc : (fun j : Fin d => !(decide (j ∈ S))) = fun j => decide (j ∈ Sᶜ) := by
      funext j
      simp
    rw [hc]
    simpa only [m,γ,subsetCoordinateEquiv_right] using maskedDirections_perm_orderEmb m Sᶜ
  unfold actualSubsetAppellContraction actualCanonicalAppellContraction
  apply Finset.sum_congr rfl
  intro i hi
  change listCumulant μ (maskedDirections m (fun j => decide (j ∈ S))++[EuclideanSpace.single i 1])*
    directionalWordDerivative (actualDampedAverage μ f 0)
      (maskedDirections m (fun j => !(decide (j ∈ S)))++[EuclideanSpace.single i 1]) 0 = _
  have hcum : listCumulant μ
      (maskedDirections m (fun j => decide (j ∈ S))++[EuclideanSpace.single i 1]) =
      cumulantTensor μ (S.card+1)
        (Fin.snoc (fun j => EuclideanSpace.single (α j) 1) (EuclideanSpace.single i 1)) := by
    rw [listCumulant_eq_local_word hLC]
    rw [local_word_perm isOpen_ball hC (hp.append_right _) h0]
    have hh := local_word_ofFn isOpen_ball hC
      (Fin.snoc (fun j => EuclideanSpace.single (α j) 1) (EuclideanSpace.single i 1)) h0
    simpa only [List.ofFn_succ_last,Fin.snoc_castSucc,Fin.snoc_last,cumulantTensor] using hh
  have happ : directionalWordDerivative (actualDampedAverage μ f 0)
      (maskedDirections m (fun j => !(decide (j ∈ S)))++[EuclideanSpace.single i 1]) 0 =
      actualAppellCoefficient μ f (Sᶜ.card+1) (Fin.cons i β) := by
    rw [local_word_perm isOpen_ball hA List.perm_append_comm h0]
    simp only [List.singleton_append]
    rw [local_word_perm isOpen_ball hA (hq.cons (EuclideanSpace.single i 1)) h0]
    have hh := local_word_ofFn isOpen_ball hA
      (Fin.cons (EuclideanSpace.single i 1) (fun j => EuclideanSpace.single (β j) 1)) h0
    rw [actualDampedAverage_zero_eq_tilt_average]
    rw [actualDampedAverage_zero_eq_tilt_average] at hh
    have hm : (Fin.cons (EuclideanSpace.single i 1) (fun j => EuclideanSpace.single (β j) 1) :
        Fin (Sᶜ.card+1) → Space n) =
        (fun j : Fin (Sᶜ.card+1) =>
          (EuclideanSpace.single ((Fin.cons i β : Fin (Sᶜ.card+1) → Fin n) j) (1 : ℝ) : Space n)) := by
      funext j
      exact Fin.cases rfl (fun k => rfl) j
    have hh' : directionalWordDerivative (fun z => ∫ x, f x ∂exponentialTilt μ z)
        (EuclideanSpace.single i 1::List.ofFn (fun j => EuclideanSpace.single (β j) 1)) 0 =
        iteratedFDeriv ℝ (Sᶜ.card+1) (fun z => ∫ x, f x ∂exponentialTilt μ z) 0
          (Fin.cons (EuclideanSpace.single i 1) (fun j => EuclideanSpace.single (β j) 1)) := by
      simpa only [List.ofFn_cons] using hh
    simpa only [List.ofFn_cons,List.singleton_append,actualAppellCoefficient,
      Fin.cons_zero,Fin.cons_succ,EuclideanSpace.basisFun_apply,hm] using hh'
  rw [hcum,happ]

 /-- Every labeled subset has the same dimension-free canonical norm
 estimate, through an explicit equivalence of ordered coordinate assignments. -/
 theorem actualSubsetAppellContraction_square_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {d : ℕ} (S : Finset (Fin d)) {h : ℝ}
    (hA : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualAppellEnergy μ g S.card ≤ h*(∫ x, (g x)^2 ∂μ)) :
    (∑ γ : Fin d → Fin n, (actualSubsetAppellContraction μ f d S γ)^2) ≤
      h*actualAppellEnergy μ f (Sᶜ.card+1) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  rw [← (subsetCoordinateEquiv (n := n) S).sum_comp]
  simp only [Fintype.sum_prod_type,actualSubsetAppellContraction_reindex hμ.logConcave hf]
  exact actualCanonicalAppellContraction_square_le hμ f S.card Sᶜ.card hA

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualCanonicalAppellContraction_square_le
#print axioms KLS.DeterministicBridgeIntegration.actualSubsetAppellContraction_square_le
