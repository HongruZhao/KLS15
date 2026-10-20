import ActualPairTensorNoiseRealization
import PairTensorRepresentatives

/-! The literal all-rank pair projection gives the improved covariance
noise on an arbitrary symmetric tensor. The remaining disjoint contraction
is precisely the lower-grade creation/adjoint quantity, not a generator
or Poincare bound. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
open KLSBelow25.PairTensor KLSBelow25.PairProjection
variable {n r : ℕ}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem actual_general_pair_noise_lower_of_disjoint {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Tensor (ι := Fin n) (r+3)) (hT : Symmetric T)
    (W : Tensor (ι := Fin n) (r+4)) (hW : Symmetric W)
    {β : ℝ} (hβ0 : 0≤β) (hβhi : β≤((r : ℝ)+2)/((r : ℝ)+4))
    (hS : pairing (kernel (actualThirdCubicArray μ) T (incidentPair (0 : Fin (r+3))))
      (kernel (actualThirdCubicArray μ) T (disjointPair r))≤
        (4+8/(3*((r : ℝ)+2)))*square T) :
    β*square W-(leadingNoiseCoefficient ((r : ℝ)+3)/(1-β)-
      positiveNoiseCoefficient ((r : ℝ)+3))*square T≤
      ∑ i : Fin n,KLS.TensorEnergy.energyNoiseCorrection T
        (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
        (fun a => W (Fin.cons i a)) := by
  let U := fun e : Pair (r+4) => toHilbert (kernel (actualThirdCubicArray μ) T e)
  let e0 := incidentPair (0 : Fin (r+3))
  let e1 := incidentPair (1 : Fin (r+3))
  let Q := pairing (kernel (actualThirdCubicArray μ) T e0)
    (kernel (actualThirdCubicArray μ) T e0)
  let R := pairing (kernel (actualThirdCubicArray μ) T e0)
    (kernel (actualThirdCubicArray μ) T e1)
  let S := pairing (kernel (actualThirdCubicArray μ) T e0)
    (kernel (actualThirdCubicArray μ) T (disjointPair r))
  have hg : Gram U Q R S := kernel_gram_of_representatives (actualThirdCubicArray μ)
    (actualThirdCumulant_swap_first μ) T hT e0 e1 (disjointPair r)
    (incident_intersection_card _ _ (by norm_num [Fin.ext_iff])) disjoint_intersection_card
  have hc : ∀ e,inner ℝ (toHilbert W) (U e)=pairing T (annihilation (actualThirdCubicArray μ) W) := by
    intro e
    rw [real_inner_comm]
    exact (toHilbert_inner _ _).trans (kernel_pairing_annihilation _ T W hW e)
  have hR : R≤4*square T := actual_pair_kernel_cross_le_four hμ T hT 0 1
    (by norm_num [Fin.ext_iff])
  have hS' : S≤(4+8/(3*(((r+4 : ℕ) : ℝ)-2)))*square T := by
    dsimp only [S,e0]
    convert hS using 1; push_cast; ring_nf
  have hb : β≤(((r+4 : ℕ) : ℝ)-2)/((r+4 : ℕ) : ℝ) := by
    convert hβhi using 1; push_cast; ring_nf
  have hh := pair_projection_noise_low U (toHilbert W) (0 : Fin (r+4))
    (by omega) hg hc hβ0 hb hR hS'
  have hQ : ∀ s : Fin (r+3),square (kernel (actualThirdCubicArray μ) T (incidentPair s))=Q := by
    intro s
    have hd := hg (incidentPair s) (incidentPair s)
    simpa only [Gram,ite_true,U,toHilbert_inner,pairing,square,pow_two] using hd
  have he := actual_pair_noise_eq μ T hT W hQ
  rw [toHilbert_norm_sq] at hh
  have hn : ((r+3 : ℕ) : ℝ)=((r+4 : ℕ) : ℝ)-1 := by push_cast;ring_nf
  rw [hn] at he
  rw [he] at hh
  convert hh using 1; push_cast; ring_nf

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_general_pair_noise_lower_of_disjoint
