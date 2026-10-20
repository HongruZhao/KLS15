import CubicSymmetricNoiseAlgebra

/-! Finite creation/annihilation duality. The creation bound is an explicit
input, not a bound on a raw or residual polynomial Gram matrix. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.CubicCreation
open KLSBelow25.CubicSymmetricNoise
variable {ι : Type*} [Fintype ι]

def matrixSquare (H : ι → ι → ℝ) : ℝ := ∑ i, ∑ j, H i j ^ 2
def symmetricMatrix (H : ι → ι → ℝ) : ι → ι → ℝ :=
  fun i j => (H i j + H j i)/2
def creation (κ : Array3 ι) (H : ι → ι → ℝ) : Array3 ι :=
  fun i j k => (∑ l, κ i j l * H l k) +
    (∑ l, κ i k l * H l j) + (∑ l, κ j k l * H l i)
def annihilation (κ T : Array3 ι) : ι → ι → ℝ :=
  fun l m => ∑ a, ∑ b, κ a b l * T m a b

omit [Fintype ι] in
theorem symmetricMatrix_symm (H : ι → ι → ℝ) :
    ∀ i j, symmetricMatrix H i j = symmetricMatrix H j i := by
  intro i j; unfold symmetricMatrix; ring

theorem matrixSquare_nonneg (H : ι → ι → ℝ) : 0 ≤ matrixSquare H := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem symmetric_pairing_matrix (H M : ι → ι → ℝ)
    (hH : ∀ i j, H i j=H j i) :
    (∑ i, ∑ j, H i j*M i j) = ∑ i, ∑ j, H i j*symmetricMatrix M i j := by
  have ht : (∑ i, ∑ j, H i j*M j i) = ∑ i, ∑ j, H i j*M i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hH j i]
  have he : (∑ i, ∑ j, H i j*symmetricMatrix M i j) =
      ((∑ i, ∑ j, H i j*M i j)+(∑ i, ∑ j, H i j*M j i))/2 := by
    unfold symmetricMatrix
    simp only [←mul_div_assoc, mul_add, ←Finset.sum_div, Finset.sum_add_distrib]
  rw [he,ht]; ring

theorem creation_pairing (κ T : Array3 ι) (H : ι → ι → ℝ)
    (hT12 : ∀ i j k, T i j k=T j i k)
    (hT23 : ∀ i j k, T i j k=T i k j)
    (hH : ∀ i j, H i j=H j i) :
    tripleSum (fun i j k => creation κ H i j k*T i j k) =
      3*(∑ l, ∑ m, H l m*symmetricMatrix (annihilation κ T) l m) := by
  let U : Array3 ι := fun i j k => ∑ l, κ i j l*H l k
  have h2 : tripleSum (fun i j k => U i k j*T i j k)=
      tripleSum (fun i j k => U i j k*T i j k) := by
    rw [←tripleSum_swap23 (fun i j k => U i k j*T i j k)]
    congr 1; funext i j k; rw [hT23 i k j]
  have h3 : tripleSum (fun i j k => U j k i*T i j k)=
      tripleSum (fun i j k => U i j k*T i j k) := by
    rw [←tripleSum_cycle (fun i j k => U j k i*T i j k),
      ←tripleSum_cycle (fun i j k => U k i j*T j k i)]
    congr 1; funext i j k; rw [hT12 k i j,hT23 i k j]
  have hbase : tripleSum (fun i j k => U i j k*T i j k)=
      ∑ l, ∑ m, H l m*annihilation κ T l m := by
    unfold tripleSum U annihilation
    simp only [Finset.sum_mul,Finset.mul_sum]
    calc
      (∑ i, ∑ j, ∑ k, ∑ l, κ i j l*H l k*T i j k) =
          ∑ i, ∑ j, ∑ l, ∑ k, κ i j l*H l k*T i j k := by
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ i, ∑ l, ∑ j, ∑ k, κ i j l*H l k*T i j k := by
            exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ j, ∑ k, κ i j l*H l k*T i j k := Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ k, ∑ j, κ i j l*H l k*T i j k := by
            exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ l, ∑ k, ∑ i, ∑ j, κ i j l*H l k*T i j k := by
            exact Finset.sum_congr rfl fun l _ => Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl; intro l _
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [hT12 i j k,hT23 j i k,hT12 j k i,hT23 k j i]
        ring
  change tripleSum (fun i j k => (U i j k+U i k j+U j k i)*T i j k)=_
  simp only [add_mul,tripleSum_add,h2,h3]
  rw [hbase,symmetric_pairing_matrix H (annihilation κ T) hH]
  ring

theorem triple_pairing_sq_le (A B : Array3 ι) :
    (tripleSum (fun i j k => A i j k*B i j k))^2 ≤ square A*square B := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι × ι))
    (fun a => A a.1 a.2.1 a.2.2) (fun a => B a.1 a.2.1 a.2.2)
  simpa only [Fintype.sum_prod_type,tripleSum,square] using hh

theorem symmetric_annihilation_square_le (κ T : Array3 ι)
    (hT12 : ∀ i j k, T i j k=T j i k)
    (hT23 : ∀ i j k, T i j k=T i k j)
    (hC : ∀ H : ι → ι → ℝ, (∀ i j, H i j=H j i) →
      square (creation κ H) ≤ 48*matrixSquare H) :
    matrixSquare (symmetricMatrix (annihilation κ T)) ≤ (16/3 : ℝ)*square T := by
  let H := symmetricMatrix (annihilation κ T)
  have hsym : ∀ i j, H i j=H j i := symmetricMatrix_symm _
  have hp := creation_pairing κ T H hT12 hT23 hsym
  have hc := triple_pairing_sq_le (creation κ H) T
  have hsqT : 0 ≤ square T :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => sq_nonneg _
  have hbound := mul_le_mul_of_nonneg_right (hC H hsym) hsqT
  have hpair : (∑ l, ∑ m, H l m*symmetricMatrix (annihilation κ T) l m)=matrixSquare H := by
    simp only [H,matrixSquare,pow_two]
  rw [hpair] at hp
  rw [hp] at hc
  have hH := matrixSquare_nonneg H
  by_cases hz : matrixSquare H=0
  · change matrixSquare H ≤ _; rw [hz]; positivity
  · have hpos : 0 < matrixSquare H := lt_of_le_of_ne hH (Ne.symm hz)
    change matrixSquare H ≤ _
    nlinarith

theorem trace_square_le_symmetric_square (M : ι → ι → ℝ) :
    (∑ l, ∑ m, M l m*M m l) ≤ matrixSquare (symmetricMatrix M) := by
  have hnonneg : 0 ≤ ∑ l, ∑ m, (M l m-M m l)^2 :=
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun m _ => sq_nonneg _
  have he : matrixSquare (symmetricMatrix M)-(∑ l, ∑ m, M l m*M m l)=
      (1/4 : ℝ)*(∑ l, ∑ m, (M l m-M m l)^2) := by
    unfold matrixSquare symmetricMatrix at *
    have hterm : (∑ l, ∑ m, (((M l m+M m l)/2)^2-M l m*M m l))=
        (1/4 : ℝ)*(∑ l, ∑ m, (M l m-M m l)^2) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro l _
      apply Finset.sum_congr rfl; intro m _
      ring
    simpa only [Finset.sum_sub_distrib] using hterm
  linarith

theorem annihilation_trace_square_le (κ T : Array3 ι)
    (hT12 : ∀ i j k, T i j k=T j i k)
    (hT23 : ∀ i j k, T i j k=T i k j)
    (hC : ∀ H : ι → ι → ℝ, (∀ i j, H i j=H j i) →
      square (creation κ H) ≤ 48*matrixSquare H) :
    (∑ l, ∑ m, annihilation κ T l m*annihilation κ T m l) ≤
      (16/3 : ℝ)*square T :=
  (trace_square_le_symmetric_square _).trans (symmetric_annihilation_square_le κ T hT12 hT23 hC)

end KLSBelow25.CubicCreation
#print axioms KLSBelow25.CubicCreation.annihilation_trace_square_le
