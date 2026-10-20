import KLSConstantImprovement.ActualBoundedCanonicalSource
import KLS.MatrixDeterminantCompactEllipticity

/-! Uniform local ellipticity of a family of genuine canonical sources.
The hypotheses concern their actual potentials and convexity moduli; the
Hessian lower bound is derived from the actual Monge--Ampere equation. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology NNReal ContDiff Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceUniformEllipticity405
open KLS ActualBoundedCanonicalSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} {ν : ℕ → Measure (Space n)}

theorem actual_family_local_ellipticity
    (d : ∀ k, SourceData (ν k)) {κ L P : ℝ} (hκ : 0 < κ)
    (hk : ∀ k, κ ≤ (d k).targetConvexityConstant)
    (hV : ∀ k p, L ≤ (d k).targetPotential p)
    (E : Set (Space n))
    (hp : ∀ k x, x ∈ E → (d k).potential x ≤ P) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ k,
      ∀ᵐ x ∂(volume : Measure (Space n)), x ∈ E →
        (coordinateHessian (d k).potential x).PosDef ∧
        Real.exp (L - P) ≤ (coordinateHessian (d k).potential x).det ∧
        ‖coordinateHessian (d k).potential x‖ ≤ 16 / κ ∧
        ∀ v : Space n,
          α * ‖v‖ ^ 2 ≤ inner ℝ v (matrixAction (coordinateHessian (d k).potential x) v) ∧
          inner ℝ v (matrixAction (coordinateHessian (d k).potential x) v) ≤ β * ‖v‖ ^ 2 := by
  obtain ⟨α, β, hα, hβ, hb⟩ := exists_uniform_ellipticity_of_det_and_norm
    n (16 / κ) (Real.exp (L-P)) (Real.exp_pos _)
  refine ⟨α, β, hα, hβ, ?_⟩
  intro k
  filter_upwards [(d k).hessian_ae] with x hx
  intro hxE
  have hnorm : ‖coordinateHessian (d k).potential x‖ ≤ 16 / κ :=
    hx.2.2.2.trans (div_le_div_of_nonneg_left (by norm_num) hκ (hk k))
  have hdet : Real.exp (L-P) ≤ (coordinateHessian (d k).potential x).det := by
    rw [hx.2.1]
    apply Real.exp_le_exp.mpr
    have ha := hp k x hxE
    have hb := hV k (gradient (d k).potential x)
    linarith
  exact ⟨hx.1, hdet, hnorm, hb _ hx.1.posSemidef hnorm hdet⟩

end KLSConstantImprovement.ActualSourceUniformEllipticity405
#print axioms KLSConstantImprovement.ActualSourceUniformEllipticity405.actual_family_local_ellipticity
