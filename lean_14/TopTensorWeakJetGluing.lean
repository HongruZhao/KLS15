import SobolevWeakJetTower
import LocalizedTensorTempered
import GlobalTensorCutoffLimit
import KLS.LocalWeakDerivativeGluing

/-! Propagation of the genuine local extra Sobolev derivative along the
actual known tensor tower, followed by raw weak-derivative gluing. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric TemperedDistribution
open scoped ContDiff Topology BigOperators SchwartzMap LineDeriv
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n r : ℕ} {φ : Space n → ℝ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem compactTensorWord_memSobolev_of_primitive_gain
    (hφ : ContDiff ℝ 1 φ) (U : (k : ℕ) → OrderedTensorField φ k)
    (hgraph : ∀ k, k < r → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
      finitePrimitiveValue (OrderedTensorIndex n k) V=U k ∧
        ∀ I i, weightedH1Derivative φ i (V I)=U (k+1) (Fin.cons i I))
    (hgain : ∀ {χ : Space n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ),
      MemSobolev ((r : ℝ)+1) 2
        (compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U [])))
    (L : List (Fin n)) (hL : L.length ≤ r)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    MemSobolev ((r : ℝ)+1-(L.length : ℝ)) 2
      (compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U L)) := by
   induction L generalizing χ with
   | nil => simpa only [List.length_nil,Nat.cast_zero,sub_zero] using hgain hχ hc
   | cons i L ih =>
     have hLr : L.length < r := by simp only [List.length_cons] at hL; omega
     have hbase := ih hLr.le hχ hc
     have hdx : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative χ i) :=
       contDiff_coordinateDerivative hχ (m := (⊤ : ℕ∞)) (by simp) i
     have hlow := (ih hLr.le hdx (hasCompactSupport_coordinateDerivative hc i)).mono
       (by linarith : (r : ℝ)+1-(L.length : ℝ)-1 ≤ (r : ℝ)+1-(L.length : ℝ))
     have hd := hbase.lineDerivOp (m := EuclideanSpace.single i (1 : ℝ))
     have he : compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U (i::L)) =
       ∂_{EuclideanSpace.single i (1 : ℝ)}
         (compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U L))-
       compactWeightedTempered hφ.continuous hdx.continuous
         (hasCompactSupport_coordinateDerivative hc i) (tensorWordLp U L) := by
       rw [compactTensorWordTempered_lineDeriv hφ U hgraph L hLr i
         (hχ.of_le (by simp)) hc]
       abel
     rw [he]
     convert hd.sub hlow using 1 <;> simp only [List.length_cons,Nat.cast_add,Nat.cast_one] <;> ring

 theorem compactTopTensorWord_memSobolev_one
    (hφ : ContDiff ℝ 1 φ) (U : (k : ℕ) → OrderedTensorField φ k)
    (hgraph : ∀ k, k < r → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
      finitePrimitiveValue (OrderedTensorIndex n k) V=U k ∧
        ∀ I i, weightedH1Derivative φ i (V I)=U (k+1) (Fin.cons i I))
    (hgain : ∀ {χ : Space n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ),
      MemSobolev ((r : ℝ)+1) 2
        (compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U [])))
    (L : List (Fin n)) (hL : L.length=r)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    MemSobolev 1 2
      (compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U L)) := by
   simpa only [hL,add_sub_cancel_left] using
     compactTensorWord_memSobolev_of_primitive_gain hφ U hgraph hgain L hL.le hχ hc

/-- Each globally defined top tensor component has a genuine globally
raw next derivative, locally L², obtained by actual cutoff gluing. -/
theorem exists_local_top_tensor_weak_derivative
    (hφ : ContDiff ℝ 1 φ) (U : (k : ℕ) → OrderedTensorField φ k)
    (hgraph : ∀ k, k < r → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
      finitePrimitiveValue (OrderedTensorIndex n k) V=U k ∧
        ∀ I i, weightedH1Derivative φ i (V I)=U (k+1) (Fin.cons i I))
    (hgain : ∀ {χ : Space n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ),
      MemSobolev ((r : ℝ)+1) 2
        (compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U [])))
    (L : List (Fin n)) (hL : L.length=r) (i : Fin n) :
    ∃ g : Space n → ℝ,
      (∀ K : Set (Space n), IsCompact K → MemLp g 2 (volume.restrict K)) ∧
      HasLocalWeakCoordinateDerivative (tensorWordLp U L) g i := by
  apply exists_local_weakCoordinateDerivative_of_cutoffs i
  intro k
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (smoothCutoff n k) :=
    (unitCutoff n).contDiff.comp (contDiff_id.const_smul _)
  have hc := smoothCutoff_hasCompactSupport (n := n) k
  have hf := memLp_compact_mul_weighted_to_volume hφ.continuous hχ.continuous hc (tensorWordLp U L)
  have hs := compactTopTensorWord_memSobolev_one hφ U hgraph hgain L hL hχ hc
  exact exists_weakCoordinateDerivative_of_memSobolev_one hf hs i

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.compactTensorWord_memSobolev_of_primitive_gain
#print axioms KLS.DeterministicBridgeIntegration.exists_local_top_tensor_weak_derivative
