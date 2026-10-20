import ActualAppellSymmetry
import KLS.DirectionalWordLeibniz
import Mathlib

/-! Local form of the released exact labeled-subset Leibniz rule. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

 theorem local_word_product_masks {U : Set E} (hU : IsOpen U) {f g : E → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    {d : ℕ} (m : Fin d → E) {x : E} (hx : x ∈ U) :
    directionalWordDerivative (fun y => f y*g y) (List.ofFn m) x =
      ∑ s : Fin d → Bool,
        directionalWordDerivative f (maskedDirections m s) x*
          directionalWordDerivative g (maskedDirections m (fun i => !(s i))) x := by
  induction d generalizing x with
  | zero => simp [maskedDirections]
  | succ d ih =>
    have he : directionalWordDerivative (fun y => f y*g y) (List.ofFn (Fin.tail m)) =ᶠ[𝓝 x]
        (fun y => ∑ s : Fin d → Bool,
          directionalWordDerivative f (maskedDirections (Fin.tail m) s) y*
            directionalWordDerivative g (maskedDirections (Fin.tail m) (fun i => !(s i))) y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih (Fin.tail m) hy
    rw [List.ofFn_succ]
    change fderiv ℝ (directionalWordDerivative (fun y => f y*g y) (List.ofFn (Fin.tail m))) x (m 0) = _
    rw [he.fderiv_eq]
    have hd := HasFDerivAt.fun_sum (u := Finset.univ) (x := x) (fun (s : Fin d → Bool) _ =>
      (((contDiffOn_word_of_isOpen hU hf (maskedDirections (Fin.tail m) s)).contDiffAt
        (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.mul
      (((contDiffOn_word_of_isOpen hU hg
        (maskedDirections (Fin.tail m) (fun i => !(s i)))).contDiffAt
        (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt)
    change HasFDerivAt (fun y => ∑ s : Fin d → Bool,
      directionalWordDerivative f (maskedDirections (Fin.tail m) s) y*
        directionalWordDerivative g (maskedDirections (Fin.tail m) (fun i => !(s i))) y) _ x at hd
    rw [hd.fderiv,sum_bool_masks]
    simp only [_root_.sum_apply,_root_.add_apply,_root_.smul_apply,smul_eq_mul,
      maskedDirections,Fin.cons_zero,Fin.tail_cons,Bool.false_eq_true,
      ↓reduceIte,complement_fin_cons,Bool.not_true,Bool.not_false]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    change _ = fderiv ℝ (directionalWordDerivative f (maskedDirections (Fin.tail m) s)) x (m 0)*
        directionalWordDerivative g (maskedDirections (Fin.tail m) (fun i => !(s i))) x +
      directionalWordDerivative f (maskedDirections (Fin.tail m) s) x*
        fderiv ℝ (directionalWordDerivative g (maskedDirections (Fin.tail m) (fun i => !(s i)))) x (m 0)
    ring

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.local_word_product_masks
