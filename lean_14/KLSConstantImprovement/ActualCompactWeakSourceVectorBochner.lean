import KLSConstantImprovement.ActualWeakSourceCompactVectorBochner
import KLSConstantImprovement.ActualCompactWeakH1Smoothing
import KLSConstantImprovement.ActualWeightedL2PairingContinuity

/-!
Actual source-vector Bochner for compact raw H1 coordinates.

The source potential is C1 with globally Lipschitz gradient; its Hessian is
the actual measurable almost-everywhere derivative. Both vector coordinates
may be merely H1. The displayed weak derivatives and their compact supports
are genuine inputs, rather than an assumed Bochner identity or source graph.
This covers compact inverse-Hessian gradients once their actual weak product
formula has been proved. Every integral passage uses actual mollifiers and
strong weighted L2 convergence.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators ContDiff Topology NNReal ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualCompactWeakSourceVectorBochner
open KLS ActualCompactSourceVectorBochner ActualWeakSourceCompactVectorBochner
open ActualCompactWeakH1Smoothing ActualWeightedL2PairingContinuity
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def rawWeakSourceAdjoint (φ a F : Space n → ℝ) (i : Fin n) (x : Space n) : ℝ :=
  coordinateDerivative φ i x * a x - F x

theorem source_coordinate_memLp_top_of_lipschitz
    {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (μ : Measure (Space n)) (i : Fin n) :
    MemLp (coordinateDerivative φ i) ∞ μ := by
  apply memLp_top_of_bound (measurable_coordinateDerivative φ i).aestronglyMeasurable L
  exact Eventually.of_forall fun x =>
    (norm_coordinateDerivative_le φ i x).trans (norm_gradient_le_of_lipschitz hLip x)

theorem compact_rawWeak_source_vector_bochner_coordinate
    {φ a b : Space n → ℝ} {L G : ℝ≥0}
    {Fa Fb : Fin n → Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hLip : LipschitzWith L φ)
    (hG : LipschitzWith G (gradient φ))
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (ha2 : MemLp a 2 (potentialMeasure φ)) (hb2 : MemLp b 2 (potentialMeasure φ))
    (hFa2 : ∀ i, MemLp (Fa i) 2 (potentialMeasure φ))
    (hFb2 : ∀ i, MemLp (Fb i) 2 (potentialMeasure φ))
    (hFac : ∀ i, HasCompactSupport (Fa i)) (hFbc : ∀ i, HasCompactSupport (Fb i))
    (hFaw : ∀ i, HasLocalWeakCoordinateDerivative a (Fa i) i)
    (hFbw : ∀ i, HasLocalWeakCoordinateDerivative b (Fb i) i)
    (i j : Fin n) :
    (∫ x, rawWeakSourceAdjoint φ a (Fa i) i x * rawWeakSourceAdjoint φ b (Fb j) j x
      ∂potentialMeasure φ) =
      (∫ x, coordinateHessian φ x i j * a x * b x ∂potentialMeasure φ) +
        ∫ x, Fa j x * Fb i x ∂potentialMeasure φ := by
  obtain ⟨has, haV, haD⟩ :=
    compact_rawWeak_weighted_smoothing hφ.continuous hca ha2 hFa2 hFac hFaw
  obtain ⟨hbs, hbV, hbD⟩ :=
    compact_rawWeak_weighted_smoothing hφ.continuous hcb hb2 hFb2 hFbc hFbw
  have hφtop (k : Fin n) := source_coordinate_memLp_top_of_lipschitz hLip (potentialMeasure φ) k
  have hHtop := memLp_coordinateHessian_top_of_gradient_lipschitz hG (potentialMeasure φ) i j
  have hδa : MemLp (rawWeakSourceAdjoint φ a (Fa i) i) 2 (potentialMeasure φ) :=
    ((hφtop i).mul ha2).sub (hFa2 i)
  have hδb : MemLp (rawWeakSourceAdjoint φ b (Fb j) j) 2 (potentialMeasure φ) :=
    ((hφtop j).mul hb2).sub (hFb2 j)
  have hδas (k : ℕ) : MemLp (coordinateSourceAdjoint φ (mollify k a) i) 2
      (potentialMeasure φ) :=
    ((hφtop i).mul (has k).2.2.1).sub ((has k).2.2.2 i)
  have hδbs (k : ℕ) : MemLp (coordinateSourceAdjoint φ (mollify k b) j) 2
      (potentialMeasure φ) :=
    ((hφtop j).mul (hbs k).2.2.1).sub ((hbs k).2.2.2 j)
  have hδaT : Tendsto (fun k => eLpNorm
      (coordinateSourceAdjoint φ (mollify k a) i - rawWeakSourceAdjoint φ a (Fa i) i)
      2 (potentialMeasure φ)) atTop (𝓝 0) := by
    exact weighted_L2_sub_tendsto
      (fun k => (hφtop i).mul (has k).2.2.1) (fun k => (has k).2.2.2 i)
      ((hφtop i).mul ha2) (hFa2 i)
      (weighted_L2_bounded_mul_tendsto (hφtop i) (fun k => (has k).2.2.1) ha2 haV)
      (haD i)
  have hδbT : Tendsto (fun k => eLpNorm
      (coordinateSourceAdjoint φ (mollify k b) j - rawWeakSourceAdjoint φ b (Fb j) j)
      2 (potentialMeasure φ)) atTop (𝓝 0) := by
    exact weighted_L2_sub_tendsto
      (fun k => (hφtop j).mul (hbs k).2.2.1) (fun k => (hbs k).2.2.2 j)
      ((hφtop j).mul hb2) (hFb2 j)
      (weighted_L2_bounded_mul_tendsto (hφtop j) (fun k => (hbs k).2.2.1) hb2 hbV)
      (hbD j)
  have hleft := tendsto_integral_mul_of_weighted_L2 hδas hδbs hδa hδb hδaT hδbT
  have hcurv := tendsto_integral_mul_of_weighted_L2
    (fun k => hHtop.mul (has k).2.2.1) (fun k => (hbs k).2.2.1)
    (hHtop.mul ha2) hb2
    (weighted_L2_bounded_mul_tendsto hHtop (fun k => (has k).2.2.1) ha2 haV) hbV
  have hderiv := tendsto_integral_mul_of_weighted_L2
    (fun k => (has k).2.2.2 j) (fun k => (hbs k).2.2.2 i)
    (hFa2 j) (hFb2 i) (haD j) (hbD i)
  have he (k : ℕ) :
      (∫ x, coordinateSourceAdjoint φ (mollify k a) i x *
        coordinateSourceAdjoint φ (mollify k b) j x ∂potentialMeasure φ) =
      (∫ x, coordinateHessian φ x i j * mollify k a x * mollify k b x
        ∂potentialMeasure φ) +
      ∫ x, coordinateDerivative (mollify k a) j x * coordinateDerivative (mollify k b) i x
        ∂potentialMeasure φ :=
    compact_left_source_vector_bochner_coordinate_C11 hφ hG.locallyLipschitz
      ((has k).1.of_le (by norm_num)) ((hbs k).1.of_le (by norm_num)) (has k).2.1 i j
  exact tendsto_nhds_unique hleft
    ((hcurv.add hderiv).congr' (Eventually.of_forall fun k => (he k).symm))

end KLSConstantImprovement.ActualCompactWeakSourceVectorBochner
#print axioms KLSConstantImprovement.ActualCompactWeakSourceVectorBochner.source_coordinate_memLp_top_of_lipschitz
#print axioms KLSConstantImprovement.ActualCompactWeakSourceVectorBochner.compact_rawWeak_source_vector_bochner_coordinate
