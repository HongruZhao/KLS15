import CubicSymmetricNoiseAlgebra

/-! Joint completion of covariance noise and the signed cubic proper drift.
The additional Q coefficient is a retained canonical budget square; no
upper bound is subtracted from the shared budget. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.CubicSymmetricNoise
variable {ι : Type*} [Fintype ι]
set_option maxHeartbeats 1500000

 theorem joint_completion {β g t : ℝ} (hβ : β < 1) (U W : Array3 ι)
    (hU : ∀ i j k, U i j k = U j i k)
    (hW12 : ∀ i j k, W i j k = W j i k)
    (hW23 : ∀ i j k, W i j k = W i k j) :
    β*square W+(2+t-4*g^2/(3*(1-β)))*square U+
      (1-8*g^2/(3*(1-β)))*cross U ≤
    noise U W-2*(g-1)*tripleSum (fun i j k => W i j k*symPart U i j k)+t*square U := by
  have hpos : 0 < 1-β := by linarith
  have hsum : 0 ≤ tripleSum (fun i j k => ((1-β)*W i j k-g*symPart U i j k)^2) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => sq_nonneg _
  have he : tripleSum (fun i j k => ((1-β)*W i j k-g*symPart U i j k)^2) =
      (1-β)^2*square W-2*(1-β)*g*
        tripleSum (fun i j k => W i j k*symPart U i j k)+g^2*square (symPart U) := by
    unfold square
    simp only [sub_eq_add_neg,←tripleSum_neg,←tripleSum_add,←tripleSum_smul]
    congr 1
    funext i j k
    ring
  rw [he,symPart_square U hU] at hsum
  rw [noise_eq,symmetric_pairing U W hW12 hW23]
  field_simp
  nlinarith

 theorem joint_lower_of_bounds {β g t E : ℝ} (hβ : β < 1)
    (hQcoeff : 2+t-4*g^2/(3*(1-β)) ≤ 0)
    (hRcoeff : 1-8*g^2/(3*(1-β)) ≤ 0)
    (U W : Array3 ι) (hU : ∀ i j k, U i j k = U j i k)
    (hW12 : ∀ i j k, W i j k = W j i k)
    (hW23 : ∀ i j k, W i j k = W i k j)
    (hQ : square U ≤ 8*E) (hR : cross U ≤ 4*E) :
    β*square W-(64*g^2/(3*(1-β))-20-8*t)*E ≤
    noise U W-2*(g-1)*tripleSum (fun i j k => W i j k*symPart U i j k)+t*square U := by
  have hh := joint_completion (g:=g) (t:=t) hβ U W hU hW12 hW23
  have hq := mul_le_mul_of_nonpos_left hQ hQcoeff
  have hr := mul_le_mul_of_nonpos_left hR hRcoeff
  have he : (2+t-4*g^2/(3*(1-β)))*(8*E)+
      (1-8*g^2/(3*(1-β)))*(4*E) =
      -(64*g^2/(3*(1-β))-20-8*t)*E := by ring
  linarith

end KLSBelow25.CubicSymmetricNoise
#print axioms KLSBelow25.CubicSymmetricNoise.joint_completion
#print axioms KLSBelow25.CubicSymmetricNoise.joint_lower_of_bounds
