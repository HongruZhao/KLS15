import ActualMixedDampingJets
import SymmetricMultilinearDiagonal
import Mathlib

/-! Scalar right derivatives of a finite dimensional multilinear family
form a genuine continuous multilinear map. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n d : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3

 theorem multilinear_euclidean_expansion
    (T : MultilinearMap ℝ (fun _ : Fin d => Space n) ℝ) (m : Fin d → Space n) :
    T m = ∑ a : Fin d → Fin n, (∏ j, (m j) (a j))*
      T (fun j => EuclideanSpace.single (a j) 1) := by
  have hrep (v : Space n) : (∑ i, v i • EuclideanSpace.single i 1) = v := by
    apply PiLp.ext
    intro i
    change (EuclideanSpace.proj i) (∑ j, v j • EuclideanSpace.single j 1) = v i
    rw [map_sum]
    simp
  calc
    T m = T (fun j => ∑ i, (m j) i • EuclideanSpace.single i 1) := by
      congr 1
      funext j
      exact (hrep (m j)).symm
    _ = ∑ a : Fin d → Fin n,
        T (fun j => (m j) (a j) • EuclideanSpace.single (a j) 1) := T.map_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [T.map_smul_univ]
      rfl

 theorem continuous_multilinear_euclidean
    (T : MultilinearMap ℝ (fun _ : Fin d => Space n) ℝ) : Continuous T := by
  have hc : Continuous (fun m : Fin d → Space n =>
      ∑ a : Fin d → Fin n, (∏ j, (m j) (a j))*
        T (fun j => EuclideanSpace.single (a j) 1)) := by fun_prop
  exact hc.congr (fun m => (multilinear_euclidean_expansion T m).symm)

 def pointwiseRightDerivativeMultilinear
    (T : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin d => Space n) ℝ)
    (hT : ∀ m : Fin d → Space n,
      DifferentiableWithinAt ℝ (fun s : ℝ => T s m) (Ici 0) 0) :
    MultilinearMap ℝ (fun _ : Fin d => Space n) ℝ where
  toFun m := derivWithin (fun s : ℝ => T s m) (Ici 0) 0
  map_update_add' m i x y := by
    have he : (fun s : ℝ => T s (Function.update m i (x+y))) =
        (fun s : ℝ => T s (Function.update m i x)+T s (Function.update m i y)) :=
      funext fun s => (T s).map_update_add m i x y
    rw [he,derivWithin_fun_add (hT _) (hT _)]
  map_update_smul' m i c x := by
    have he : (fun s : ℝ => T s (Function.update m i (c • x))) =
        (fun s : ℝ => c*T s (Function.update m i x)) := by
      funext s
      exact (T s).map_update_smul m i c x
    rw [he,derivWithin_const_mul c (hT _)]
    rfl

 def pointwiseRightDerivativeTensor
    (T : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin d => Space n) ℝ)
    (hT : ∀ m : Fin d → Space n,
      DifferentiableWithinAt ℝ (fun s : ℝ => T s m) (Ici 0) 0) :
    ContinuousMultilinearMap ℝ (fun _ : Fin d => Space n) ℝ :=
  { pointwiseRightDerivativeMultilinear T hT with
    cont := continuous_multilinear_euclidean (pointwiseRightDerivativeMultilinear T hT) }

 @[simp] theorem pointwiseRightDerivativeTensor_apply
    (T : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin d => Space n) ℝ)
    (hT : ∀ m : Fin d → Space n,
      DifferentiableWithinAt ℝ (fun s : ℝ => T s m) (Ici 0) 0) (m : Fin d → Space n) :
    pointwiseRightDerivativeTensor T hT m = derivWithin (fun s : ℝ => T s m) (Ici 0) 0 := rfl

 theorem pointwiseRightDerivativeTensor_symmetric
    (T : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin d => Space n) ℝ)
    (hT : ∀ m : Fin d → Space n,
      DifferentiableWithinAt ℝ (fun s : ℝ => T s m) (Ici 0) 0)
    (hsym : ∀ s : ℝ, 0 ≤ s → MultilinearPermutationInvariant (T s)) :
    MultilinearPermutationInvariant (pointwiseRightDerivativeTensor T hT) := by
  intro m σ
  simp only [pointwiseRightDerivativeTensor_apply]
  apply derivWithin_congr
  · intro s hs
    exact hsym s hs m σ
  · exact hsym 0 le_rfl m σ

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.pointwiseRightDerivativeTensor_symmetric
