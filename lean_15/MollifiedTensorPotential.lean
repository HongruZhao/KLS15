import TensorCutoffLeibniz
import KLS.WeakDerivativeMollification
import WeightedLocalMollificationLimit

/-! Actual compact C∞ potentials approximate every compactly localized
primitive tower in all its derivative orders simultaneously. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter ContinuousLinearMap
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n r s : ℕ} {φ χ : Space n → ℝ}

lemma mollify_congr_ae {f g : Space n → ℝ} (h : f =ᵐ[volume] g) (k : ℕ) :
    mollify k f = mollify k g := by
  unfold mollify scalarConvolution
  exact convolution_congr (lsmul ℝ ℝ) h EventuallyEq.rfl

lemma tensorCutoffJet_hasCompactSupport (hc : HasCompactSupport χ)
    (U : (k : ℕ) → OrderedTensorField φ k) (r : ℕ) (I : OrderedTensorIndex n r) :
    HasCompactSupport (tensorCutoffJet U χ r I) := by
  have he := compactSupport_finsetSum (n := n) Finset.univ
    (fun b _ => (coordinateWordDerivative_hasCompactSupport hc (maskedDirections I b)).mul_right
      (f' := fun x => tensorWordLp U (maskedDirections I (fun j => !(b j))) x))
  convert he using 1
  funext x
  simp [tensorCutoffJet]

def mollifiedCutoffPotential (U : (k : ℕ) → OrderedTensorField φ k) (χ : Space n → ℝ)
    (k : ℕ) : Space n → ℝ :=
  mollify k (tensorCutoffJet U χ 0 (fun j => Fin.elim0 j))

lemma mollifiedCutoffPotential_contDiff (hφ : Continuous φ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (U : (k : ℕ) → OrderedTensorField φ k) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifiedCutoffPotential U χ k) :=
  mollify_contDiff ((tensorCutoffJet_memLp hφ hχ hc U 0 _).locallyIntegrable (by norm_num)) k

lemma mollifiedCutoffPotential_hasCompactSupport (hc : HasCompactSupport χ)
    (U : (k : ℕ) → OrderedTensorField φ k) (k : ℕ) :
    HasCompactSupport (mollifiedCutoffPotential U χ k) :=
  hasCompactSupport_mollify (tensorCutoffJet_hasCompactSupport hc U 0 _) k

/-- Every actual classical derivative of the compact C∞ mollified scalar
potential is exactly the corresponding mollified weak Leibniz jet. -/
theorem coordinatePotentialTensor_mollifiedCutoffPotential (hφ : ContDiff ℝ 1 φ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (U : (k : ℕ) → OrderedTensorField φ k)
    (hgraph : ∀ k, k < s → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
      finitePrimitiveValue (OrderedTensorIndex n k) V = U k ∧
        ∀ I i, weightedH1Derivative φ i (V I) = U (k + 1) (Fin.cons i I))
    (r : ℕ) (hr : r ≤ s) (I : OrderedTensorIndex n r) (k : ℕ) :
    coordinatePotentialTensor (mollifiedCutoffPotential U χ k) r I =
      mollify k (tensorCutoffJet U χ r I) := by
  induction r with
  | zero =>
    have he : I = (fun j => Fin.elim0 j) := Subsingleton.elim _ _
    rw [he]
    simp only [coordinatePotentialTensor, List.ofFn_zero, List.map_nil,
      directionalWordDerivative_nil, mollifiedCutoffPotential]
  | succ r ih =>
    rw [← Fin.cons_self_tail I, coordinatePotentialTensor_cons, ih (by omega)]
    have hw := tensorCutoffJet_hasWeakCoordinateDerivative hφ hχ hc U hgraph
      (show r < s by omega) (Fin.tail I) (I 0)
    rw [hw.mollify_eq (tensorCutoffJet_memLp hφ.continuous hχ hc U r (Fin.tail I)) k]
    exact mollify_congr_ae (tensorCutoffJet_memLp hφ.continuous hχ hc U (r + 1)
      (Fin.cons (I 0) (Fin.tail I))).coeFn_toLp k

theorem eLpNorm_mollify_cutoffJet_potential_tendsto_zero (hφ : Continuous φ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (U : (k : ℕ) → OrderedTensorField φ k) (r : ℕ) (I : OrderedTensorIndex n r) :
    Tendsto (fun k => eLpNorm (mollify k (tensorCutoffJet U χ r I) - tensorCutoffJet U χ r I)
      2 (potentialMeasure φ)) atTop (𝓝 0) := by
  have hV := tensorCutoffJet_memLp hφ hχ hc U r I
  have hC := tensorCutoffJet_hasCompactSupport hc U r I
  apply eLpNorm_potentialMeasure_sub_tendsto_zero_of_compact_support hφ
    (isCompact_mollifierEnlargement hC) (tsupport_mollify_subset hC)
    (subset_mollifierEnlargement _) (fun k => memLp_mollify hV k) hV
  · intro k
    exact memLp_of_continuous_hasCompactSupport hφ
      (mollify_contDiff (hV.locallyIntegrable (by norm_num)) k).continuous
      (hasCompactSupport_mollify hC k)
  · exact memLp_potentialMeasure_of_memLp_volume_compact hφ hV hC
  · exact eLpNorm_mollify_sub_tendsto_zero hV

theorem eLpNorm_mollifiedCutoffPotential_derivative_sub_tendsto_zero
    (hφ : ContDiff ℝ 1 φ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (U : (k : ℕ) → OrderedTensorField φ k)
    (hgraph : ∀ k, k < s → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
      finitePrimitiveValue (OrderedTensorIndex n k) V = U k ∧
        ∀ I i, weightedH1Derivative φ i (V I) = U (k + 1) (Fin.cons i I))
    (r : ℕ) (hr : r ≤ s) (I : OrderedTensorIndex n r) :
    Tendsto (fun k => eLpNorm
      (coordinatePotentialTensor (mollifiedCutoffPotential U χ k) r I - tensorCutoffJet U χ r I)
        2 (potentialMeasure φ)) atTop (𝓝 0) := by
  simpa only [coordinatePotentialTensor_mollifiedCutoffPotential hφ hχ hc U hgraph r hr I] using
    eLpNorm_mollify_cutoffJet_potential_tendsto_zero hφ.continuous hχ hc U r I

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.coordinatePotentialTensor_mollifiedCutoffPotential
#print axioms KLS.DeterministicBridgeIntegration.eLpNorm_mollifiedCutoffPotential_derivative_sub_tendsto_zero
