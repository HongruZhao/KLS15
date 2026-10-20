import QuarticSymmetricNoiseAlgebra
import CubicCreationAdjointAlgebra

/-! The disjoint rank-three covariance-noise contraction is the literal
trace square of the cubic annihilation matrix. No symmetry hypothesis is
needed for this finite sum identity. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.QuarticSymmetricNoise
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open KLSBelow25.CubicSymmetricNoise KLSBelow25.CubicCreation
variable {ι : Type*} [Fintype ι]

theorem disjoint_creation_trace (κ T : Array3 ι) :
    disjoint (fun i j k l => ∑ m,κ i j m*T m k l)=
      ∑ m,∑ p,annihilation κ T m p*annihilation κ T p m := by
  unfold disjoint quadSum annihilation
  simp only [Finset.sum_mul,Finset.mul_sum]
  calc
    (∑ i,∑ j,∑ k,∑ l,∑ p,∑ m,(κ i j m*T m k l)*(κ k l p*T p i j))=
        ∑ i,∑ j,∑ k,∑ l,∑ m,∑ p,(κ i j m*T m k l)*(κ k l p*T p i j) := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _=
        ∑ i,∑ j,∑ k,∑ m,∑ l,∑ p,(κ i j m*T m k l)*(κ k l p*T p i j) := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _=∑ i,∑ j,∑ m,∑ k,∑ l,∑ p,(κ i j m*T m k l)*(κ k l p*T p i j) := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _=∑ i,∑ m,∑ j,∑ k,∑ l,∑ p,(κ i j m*T m k l)*(κ k l p*T p i j) := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _=∑ m,∑ i,∑ j,∑ k,∑ l,∑ p,(κ i j m*T m k l)*(κ k l p*T p i j) := Finset.sum_comm
    _=∑ m,∑ i,∑ j,∑ k,∑ p,∑ l,(κ i j m*T m k l)*(κ k l p*T p i j) := by
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _=∑ m,∑ i,∑ j,∑ p,∑ k,∑ l,(κ i j m*T m k l)*(κ k l p*T p i j) := by
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _=∑ m,∑ i,∑ p,∑ j,∑ k,∑ l,(κ i j m*T m k l)*(κ k l p*T p i j) := by
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _=∑ m,∑ p,∑ i,∑ j,∑ k,∑ l,(κ i j m*T m k l)*(κ k l p*T p i j) := by
      exact Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _=_ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring

end KLSBelow25.QuarticSymmetricNoise
#print axioms KLSBelow25.QuarticSymmetricNoise.disjoint_creation_trace
