import KLSConstantImprovement.ActualSourceResolventOrder405
import KLSConstantImprovement.ActualBoundedSourceCalculus
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.NhdsWithin

/-!
The actual scalar conservative unit resolvent acts entrywise on matrix
fields. Scalar positivity on countably many rational quadratic forms,
followed by real-vector density, proves matrix positivity AE. In
particular the actual Hessian resolvent is PSD and has bounded entries.
The further L1 curvature-forcing comparison K >= H/2 is separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Matrix Set Filter InnerProductSpace
open scoped BigOperators ContDiff Topology RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceMatrixResolvent405
open KLS ActualBoundedCanonicalSource ActualSourceConservativeResolvent405
open ActualSourceResolventOrder405
variable {n : ℕ} {μ : Measure (Space n)}

def matrixFieldValue (d : SourceData μ)
    (F : Matrix (Fin n) (Fin n) (Lp ℝ 2 (potentialMeasure d.potential))) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => F i j x

def sourceMatrixResolvent (d : SourceData μ)
    (F : Matrix (Fin n) (Fin n) (Lp ℝ 2 (potentialMeasure d.potential))) :
    Matrix (Fin n) (Fin n) (Lp ℝ 2 (potentialMeasure d.potential)) :=
  Matrix.of fun i j => sourceConservativeResolvent d (t := 1) zero_lt_one (F i j)

def matrixQuadraticLp (d : SourceData μ)
    (F : Matrix (Fin n) (Fin n) (Lp ℝ 2 (potentialMeasure d.potential))) (v : Fin n → ℝ) :
    Lp ℝ 2 (potentialMeasure d.potential) := ∑ i, ∑ j, (v i * v j) • F i j

theorem matrixQuadraticLp_ae (d : SourceData μ)
    (F : Matrix (Fin n) (Fin n) (Lp ℝ 2 (potentialMeasure d.potential))) (v : Fin n → ℝ) :
    (matrixQuadraticLp d F v : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => v ⬝ᵥ (matrixFieldValue d F x *ᵥ v) := by
  have hrow : ∀ᵐ x ∂potentialMeasure d.potential, ∀ i : Fin n,
      (∑ j, (v i * v j) • F i j) x = ∑ j, ((v i * v j) • F i j) x :=
    ae_all_iff.mpr fun i => by
      filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => (v i * v j) • F i j)] with x hx
      simpa only [Finset.sum_apply] using hx
  have hsm : ∀ᵐ x ∂potentialMeasure d.potential, ∀ i j : Fin n,
      ((v i * v j) • F i j) x = (v i * v j) * F i j x := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    filter_upwards [Lp.coeFn_smul (v i * v j) (F i j)] with x hx
    change ((v i * v j) • F i j) x = (v i * v j) * F i j x at hx
    exact hx
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i => ∑ j, (v i * v j) • F i j), hrow, hsm] with x hx hr hs
  change (∑ i, ∑ j, (v i * v j) • F i j) x = _
  have hx' : (∑ i, ∑ j, (v i * v j) • F i j) x =
      ∑ i, (∑ j, (v i * v j) • F i j) x := by
    simpa only [Finset.sum_apply] using hx
  rw [hx']
  calc
    _ = ∑ i, ∑ j, (v i * v j) * F i j x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hr i]
      exact Finset.sum_congr rfl fun j _ => hs i j
    _ = _ := by
      simp only [dotProduct, Matrix.mulVec, matrixFieldValue, Matrix.of_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem sourceMatrixResolvent_quadratic (d : SourceData μ)
    (F : Matrix (Fin n) (Fin n) (Lp ℝ 2 (potentialMeasure d.potential))) (v : Fin n → ℝ) :
    matrixQuadraticLp d (sourceMatrixResolvent d F) v =
      sourceConservativeResolvent d (t := 1) zero_lt_one (matrixQuadraticLp d F v) := by
  simp only [matrixQuadraticLp, sourceMatrixResolvent, Matrix.of_apply, map_sum, map_smul]

/-- No matrix order property is an input for the operator: it follows
from the actual scalar unit-resolvent positivity and rational density. -/
theorem sourceMatrixResolvent_posSemidef (d : SourceData μ)
    (F : Matrix (Fin n) (Fin n) (Lp ℝ 2 (potentialMeasure d.potential)))
    (hF : ∀ᵐ x ∂potentialMeasure d.potential, (matrixFieldValue d F x).PosSemidef) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (matrixFieldValue d (sourceMatrixResolvent d F) x).PosSemidef := by
  have hsym (i j : Fin n) : F i j = F j i := by
    apply Lp.ext
    filter_upwards [hF] with x hx
    exact hx.isHermitian.isSymm.apply j i
  have hRsym (x : Space n) : (matrixFieldValue d (sourceMatrixResolvent d F) x).IsSymm := by
    apply Matrix.ext
    intro i j
    change sourceConservativeResolvent d (t := 1) zero_lt_one (F j i) x =
      sourceConservativeResolvent d (t := 1) zero_lt_one (F i j) x
    rw [hsym j i]
  have hq (v : Fin n → ℝ) : ∀ᵐ x ∂potentialMeasure d.potential,
      0 ≤ v ⬝ᵥ (matrixFieldValue d (sourceMatrixResolvent d F) x *ᵥ v) := by
    have hinput : ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ matrixQuadraticLp d F v x := by
      filter_upwards [hF, matrixQuadraticLp_ae d F v] with x hx he
      rw [he]
      simpa only [star_trivial] using hx.dotProduct_mulVec_nonneg v
    have ho := sourceConservativeResolvent_nonneg d (matrixQuadraticLp d F v) hinput
    rw [← sourceMatrixResolvent_quadratic] at ho
    filter_upwards [ho, matrixQuadraticLp_ae d (sourceMatrixResolvent d F) v] with x hx he
    rwa [he] at hx
  have hrat : ∀ᵐ x ∂potentialMeasure d.potential, ∀ q : Fin n → ℚ,
      0 ≤ (fun i => (q i : ℝ)) ⬝ᵥ
        (matrixFieldValue d (sourceMatrixResolvent d F) x *ᵥ fun i => (q i : ℝ)) :=
    ae_all_iff.mpr fun q => hq (fun i => (q i : ℝ))
  have hdense : DenseRange (fun q : Fin n → ℚ => fun i => (q i : ℝ)) := by
    have hd : DenseRange (Pi.map (fun _ : Fin n => fun q : ℚ => (q : ℝ))) :=
      DenseRange.piMap (fun _ : Fin n =>
        (Rat.denseRange_cast : DenseRange (fun q : ℚ => (q : ℝ))))
    have he : Pi.map (fun _ : Fin n => fun q : ℚ => (q : ℝ)) =
        (fun q : Fin n → ℚ => fun i => (q i : ℝ)) := by
      funext q i
      rfl
    rw [he] at hd
    exact hd
  filter_upwards [hrat] with x hx
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr (hRsym x))
  intro v
  simp only [star_trivial]
  exact hdense.induction_on
    (p := fun w : Fin n → ℝ => 0 ≤ w ⬝ᵥ (matrixFieldValue d (sourceMatrixResolvent d F) x *ᵥ w))
    v (isClosed_le continuous_const (by fun_prop)) hx

theorem sourceConservativeResolvent_abs_bound (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (C : ℝ)
    (hg : ∀ᵐ x ∂potentialMeasure d.potential, ‖g x‖ ≤ C) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      ‖sourceConservativeResolvent d (t := 1) zero_lt_one g x‖ ≤ C := by
  have hgU : ∀ᵐ x ∂potentialMeasure d.potential, g x ≤ C := hg.mono fun x hx =>
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hx)
  have hgN : ∀ᵐ x ∂potentialMeasure d.potential, (-g) x ≤ C := by
    filter_upwards [hg, Lp.coeFn_neg g] with x hx hn
    rw [hn, Pi.neg_apply]
    exact (neg_le_abs _).trans (by simpa only [Real.norm_eq_abs] using hx)
  have hU := sourceConservativeResolvent_upper_bound d g C hgU
  have hN := sourceConservativeResolvent_upper_bound d (-g) C hgN
  rw [map_neg] at hN
  filter_upwards [hU, hN, Lp.coeFn_neg (sourceConservativeResolvent d (t := 1) zero_lt_one g)]
    with x hu hn he
  rw [he, Pi.neg_apply] at hn
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, hu⟩

def sourceHessianLp (d : SourceData μ) :
    Matrix (Fin n) (Fin n) (Lp ℝ 2 (potentialMeasure d.potential)) :=
  Matrix.of fun i j => (d.hessian_entry_memLp i j 2).toLp (fun x => coordinateHessian d.potential x i j)

theorem sourceHessianLp_ae (d : SourceData μ) :
    matrixFieldValue d (sourceHessianLp d) =ᵐ[potentialMeasure d.potential] coordinateHessian d.potential := by
  have he : ∀ᵐ x ∂potentialMeasure d.potential, ∀ i j : Fin n,
      sourceHessianLp d i j x = coordinateHessian d.potential x i j :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => (d.hessian_entry_memLp i j 2).coeFn_toLp
  filter_upwards [he] with x hx
  exact Matrix.ext (fun i j => hx i j)

/-- Positivity of K=R1 H uses the actual constructed Hessian; no PSD
certificate for K is assumed. -/
theorem actualHessianResolvent_posSemidef (d : SourceData μ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (matrixFieldValue d (sourceMatrixResolvent d (sourceHessianLp d)) x).PosSemidef := by
  apply sourceMatrixResolvent_posSemidef d
  filter_upwards [sourceHessianLp_ae d, d.hessian_ae_source] with x hx hp
  rw [hx]
  exact hp.1.posSemidef

/-- The actual Hessian resolvent is bounded entrywise by the law's paid
Hessian bound. This pays subsequent L1 curvature pairings. -/
theorem actualHessianResolvent_entry_bound (d : SourceData μ) (i j : Fin n) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      ‖sourceMatrixResolvent d (sourceHessianLp d) i j x‖ ≤ 16 / d.targetConvexityConstant := by
  apply sourceConservativeResolvent_abs_bound d
  filter_upwards [(d.hessian_entry_memLp i j 2).coeFn_toLp] with x hx
  change ‖((d.hessian_entry_memLp i j 2).toLp (fun x => coordinateHessian d.potential x i j)) x‖ ≤ _
  rw [hx]
  have hb := coordinateHessian_entry_bound_of_gradient_lipschitz d.gradient_lipschitz x i j
  change ‖coordinateHessian d.potential x i j‖ ≤ 16 / d.targetConvexityConstant at hb
  exact hb

end KLSConstantImprovement.ActualSourceMatrixResolvent405

#print axioms KLSConstantImprovement.ActualSourceMatrixResolvent405.sourceMatrixResolvent_quadratic
#print axioms KLSConstantImprovement.ActualSourceMatrixResolvent405.sourceMatrixResolvent_posSemidef
#print axioms KLSConstantImprovement.ActualSourceMatrixResolvent405.actualHessianResolvent_posSemidef
#print axioms KLSConstantImprovement.ActualSourceMatrixResolvent405.actualHessianResolvent_entry_bound
