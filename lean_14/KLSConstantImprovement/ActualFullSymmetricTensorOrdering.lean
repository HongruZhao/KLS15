import KLSConstantImprovement.FourthCubicProjectionDefect
import KLSConstantImprovement.FullSymmetricProductionCoercivity

/-! Concrete finite tensor identities needed by the raw405 production proof.
The tensor, matrix, cyclic projection, Frobenius norms and hook residuals are
defined here. No scalar ordering or norm identity is assumed. The only tensor
hypothesis is cyclic symmetry (which follows from full three-slot symmetry).
This does not construct the analytic canonical source. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.ActualFullSymmetricTensorOrdering
open MixedCubicRankSlicing FourthCubicProjectionDefect
variable {ι : Type*} [Fintype ι]
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

def firstAction (B : Matrix ι ι ℝ) (N : ι → ι → ι → ℝ) : ι → ι → ι → ℝ :=
  fun i j k => ∑ a, B i a * N a j k

def secondAction (B : Matrix ι ι ℝ) (N : ι → ι → ι → ℝ) : ι → ι → ι → ℝ :=
  fun i j k => ∑ a, B j a * N i a k

def cyclicPairing (U : ι → ι → ι → ℝ) : ℝ :=
  pairing (fun i j k => U j k i) U

def hook (U : ι → ι → ι → ℝ) : ι → ι → ι → ℝ :=
  fun i j k => U i j k - cyclicAverage U i j k

private theorem sum3_cycle (f : ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, f j k i) = ∑ i, ∑ j, ∑ k, f i j k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

private theorem sum5_exchange (f : ι → ι → ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, f i j k a b) =
      ∑ a, ∑ b, ∑ k, ∑ i, ∑ j, f i j k a b := by
  calc
    _ = ∑ i, ∑ j, ∑ a, ∑ k, ∑ b, f i j k a b :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ j, ∑ k, ∑ b, f i j k a b :=
      Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, ∑ k, ∑ b, f i j k a b := Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, ∑ b, ∑ k, f i j k a b :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ j, ∑ k, f i j k a b :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ i, ∑ j, ∑ k, f i j k a b :=
      Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ i, ∑ k, ∑ j, f i j k a b :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_comm

private theorem sum5_reverse (f : ι → ι → ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, f i j k a b) =
      ∑ b, ∑ a, ∑ k, ∑ j, ∑ i, f i j k a b := by
  calc
    _ = ∑ a, ∑ b, ∑ k, ∑ i, ∑ j, f i j k a b := sum5_exchange f
    _ = ∑ b, ∑ a, ∑ k, ∑ i, ∑ j, f i j k a b := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_comm

theorem tensor_pairing_comm (U V : ι → ι → ι → ℝ) : pairing U V = pairing V U := by
  unfold pairing
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem cyclic_pairing_reverse (U : ι → ι → ι → ℝ) :
    pairing (fun i j k => U k i j) U = cyclicPairing U := by
  unfold pairing cyclicPairing
  calc
    _ = ∑ i, ∑ j, ∑ k, U i j k * U j k i :=
      (sum3_cycle (fun i j k => U k i j * U i j k)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem cyclic_projection_energy (U : ι → ι → ι → ℝ) :
    3 * cubicEnergy (cyclicAverage U) = cubicEnergy U + 2 * cyclicPairing U := by
  have hc : ∀ i j k, cyclicAverage U i j k = cyclicAverage U j k i := by
    intro i j k
    unfold cyclicAverage
    ring
  have hp : pairing (cyclicAverage U) U = cubicEnergy (cyclicAverage U) := by
    rw [← pairing_cyclicAverage (cyclicAverage U) U hc]
    simp only [pairing, cubicEnergy, pow_two]
  have he : 3 * pairing (cyclicAverage U) U = cubicEnergy U + cyclicPairing U +
      pairing (fun i j k => U k i j) U := by
    unfold cyclicPairing
    simp only [pairing, cubicEnergy, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    unfold cyclicAverage
    ring
  rw [hp, cyclic_pairing_reverse] at he
  linarith

theorem first_action_cyclic_pairing (B : Matrix ι ι ℝ) (N : ι → ι → ι → ℝ)
    (hN : ∀ i j k, N i j k = N j k i) :
    cyclicPairing (firstAction B N) = pairing (firstAction B N) (secondAction B N) := by
  have hr : (fun i j k => firstAction B N j k i) = secondAction B N := by
    funext i j k
    unfold firstAction secondAction
    apply Finset.sum_congr rfl
    intro a _
    rw [hN a k i, hN k i a]
  unfold cyclicPairing
  rw [hr, tensor_pairing_comm]

theorem opposite_slot_transpose_pairing (B : Matrix ι ι ℝ)
    (N : ι → ι → ι → ℝ) :
    pairing (firstAction B.transpose N) (secondAction B.transpose N) =
      pairing (firstAction B N) (secondAction B N) := by
  simp only [pairing, firstAction, secondAction, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [sum5_reverse (fun (i j k b a : ι) => (B a i * N a j k) * (B b j * N i b k))]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem actual_projection_ordering (B : Matrix ι ι ℝ) (N : ι → ι → ι → ℝ)
    (hN : ∀ i j k, N i j k = N j k i) :
    3 * (cubicEnergy (cyclicAverage (firstAction B N)) -
      cubicEnergy (cyclicAverage (firstAction B.transpose N))) =
      cubicEnergy (firstAction B N) - cubicEnergy (firstAction B.transpose N) := by
  have h1 := cyclic_projection_energy (firstAction B N)
  have h2 := cyclic_projection_energy (firstAction B.transpose N)
  rw [first_action_cyclic_pairing B N hN] at h1
  rw [first_action_cyclic_pairing B.transpose N hN, opposite_slot_transpose_pairing] at h2
  linarith

theorem actual_hook_residual_split (U : ι → ι → ι → ℝ) :
    cubicEnergy (hook U) + cubicEnergy (cyclicAverage U) = cubicEnergy U := by
  change cubicEnergy (fun i j k => U i j k - cyclicAverage U i j k) +
    cubicEnergy (cyclicAverage U) = cubicEnergy U
  have hh := cyclicAverage_residual_split U (fun _ _ _ => 0)
    (by intros; rfl) 0
  simpa only [mul_zero, sub_zero] using hh

theorem actual_full_tensor_hook_ordering (B : Matrix ι ι ℝ)
    (N : ι → ι → ι → ℝ) (hN : ∀ i j k, N i j k = N j k i) :
    2 * (cubicEnergy (firstAction B N) - cubicEnergy (firstAction B.transpose N)) =
      3 * (cubicEnergy (hook (firstAction B N)) -
        cubicEnergy (hook (firstAction B.transpose N))) := by
  have hp := actual_projection_ordering B N hN
  have h1 := actual_hook_residual_split (firstAction B N)
  have h2 := actual_hook_residual_split (firstAction B.transpose N)
  linarith

end KLSConstantImprovement.ActualFullSymmetricTensorOrdering
#print axioms KLSConstantImprovement.ActualFullSymmetricTensorOrdering.cyclic_projection_energy
#print axioms KLSConstantImprovement.ActualFullSymmetricTensorOrdering.opposite_slot_transpose_pairing
#print axioms KLSConstantImprovement.ActualFullSymmetricTensorOrdering.actual_projection_ordering
#print axioms KLSConstantImprovement.ActualFullSymmetricTensorOrdering.actual_hook_residual_split
#print axioms KLSConstantImprovement.ActualFullSymmetricTensorOrdering.actual_full_tensor_hook_ordering
