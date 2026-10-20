import Mathlib

/-! Exact rank-two square completion using full symmetry of the next
coefficient. The arrays below are finite literal coordinates. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.CubicSymmetricNoise
variable {ι : Type*} [Fintype ι]

abbrev Array3 (ι : Type*) := ι → ι → ι → ℝ

def tripleSum (F : Array3 ι) : ℝ := ∑ i, ∑ j, ∑ k, F i j k

def square (U : Array3 ι) : ℝ := tripleSum (fun i j k => U i j k ^ 2)
def cross (U : Array3 ι) : ℝ := tripleSum (fun i j k => U i j k*U i k j)
def symPart (U : Array3 ι) : Array3 ι :=
  fun i j k => (2/3 : ℝ)*(U i j k+U i k j+U j k i)
def noise (U W : Array3 ι) : ℝ := tripleSum (fun i j k =>
  W i j k^2-2*W i j k*(U i j k+U i k j)+
  (1/2 : ℝ)*(U i j k+U i k j)^2+
  (1/2 : ℝ)*(U i j k^2+U i k j^2))

theorem tripleSum_swap23 (F : Array3 ι) :
    tripleSum (fun i j k => F i k j)=tripleSum F := by
  unfold tripleSum
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

theorem tripleSum_swap12 (F : Array3 ι) :
    tripleSum (fun i j k => F j i k)=tripleSum F := by
  exact Finset.sum_comm

theorem tripleSum_cycle (F : Array3 ι) :
    tripleSum (fun i j k => F j k i)=tripleSum F := by
  unfold tripleSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

theorem tripleSum_add (F G : Array3 ι) :
    tripleSum (fun i j k => F i j k+G i j k)=tripleSum F+tripleSum G := by
  simp only [tripleSum,Finset.sum_add_distrib]

theorem tripleSum_smul (a : ℝ) (F : Array3 ι) :
    tripleSum (fun i j k => a*F i j k)=a*tripleSum F := by
  simp only [tripleSum,Finset.mul_sum]

theorem tripleSum_neg (F : Array3 ι) :
    tripleSum (fun i j k => -F i j k) = -tripleSum F := by
  simp only [tripleSum, Finset.sum_neg_distrib]

theorem permuted_square (U : Array3 ι) :
    square (fun i j k => U i k j)=square U := tripleSum_swap23 _

theorem cycle_square (U : Array3 ι) :
    square (fun i j k => U j k i)=square U := tripleSum_cycle _

theorem cross_cycle_left (U : Array3 ι)
    (hU : ∀ i j k,U i j k=U j i k) :
    tripleSum (fun i j k=>U i j k*U j k i)=cross U := by
  rw [←tripleSum_swap12 (fun i j k=>U i j k*U j k i)]
  unfold cross
  congr 1
  funext i j k
  rw [hU j i k]

theorem cross_cycle_right (U : Array3 ι)
    (hU : ∀ i j k,U i j k=U j i k) :
    tripleSum (fun i j k=>U i k j*U j k i)=cross U := by
  rw [←tripleSum_cycle (fun i j k=>U i k j*U j k i)]
  unfold cross
  congr 1
  funext i j k
  rw [hU j i k,hU k i j]

theorem symPart_square (U : Array3 ι)
    (hU : ∀ i j k,U i j k=U j i k) :
    square (symPart U)=(4/3 : ℝ)*square U+(8/3 : ℝ)*cross U := by
  have hp : square (symPart U)=
      (4/9 : ℝ)*(square U+square (fun i j k=>U i k j)+square (fun i j k=>U j k i)+
        2*cross U+2*tripleSum (fun i j k=>U i j k*U j k i)+
        2*tripleSum (fun i j k=>U i k j*U j k i)) := by
    unfold square symPart cross
    simp only [←tripleSum_add,←tripleSum_smul]
    congr 1
    funext i j k
    ring
  rw [hp,permuted_square U,cycle_square U,cross_cycle_left U hU,cross_cycle_right U hU]
  ring

theorem symmetric_pairing (U W : Array3 ι)
    (hW12 : ∀ i j k,W i j k=W j i k)
    (hW23 : ∀ i j k,W i j k=W i k j) :
    tripleSum (fun i j k=>W i j k*(U i j k+U i k j))=
      tripleSum (fun i j k=>W i j k*symPart U i j k) := by
  have h1 : tripleSum (fun i j k=>W i j k*U i k j)=
      tripleSum (fun i j k=>W i j k*U i j k) := by
    rw [←tripleSum_swap23 (fun i j k=>W i j k*U i k j)]
    congr 1
    funext i j k
    rw [hW23 i k j]
  have h2 : tripleSum (fun i j k=>W i j k*U j k i)=
      tripleSum (fun i j k=>W i j k*U i j k) := by
    rw [←tripleSum_cycle (fun i j k=>W i j k*U j k i),
      ←tripleSum_cycle (fun i j k=>W j k i*U k i j)]
    congr 1
    funext i j k
    rw [hW12 k i j,hW23 i k j]
  have ha : tripleSum (fun i j k=>W i j k*(U i j k+U i k j))=
      2*tripleSum (fun i j k=>W i j k*U i j k) := by
    simp only [mul_add,tripleSum_add,h1]
    ring
  rw [ha]
  have hb : tripleSum (fun i j k=>W i j k*symPart U i j k)=
      (2/3 : ℝ)*(tripleSum (fun i j k=>W i j k*U i j k)+
        tripleSum (fun i j k=>W i j k*U i k j)+
        tripleSum (fun i j k=>W i j k*U j k i)) := by
    unfold symPart
    simp only [mul_add,←tripleSum_add,←tripleSum_smul]
    congr 1
    funext i j k
    ring
  rw [hb,h1,h2]
  ring

theorem noise_eq (U W : Array3 ι) :
    noise U W=square W-2*tripleSum (fun i j k=>W i j k*(U i j k+U i k j))+
      2*square U+cross U := by
  have he : noise U W=square W-2*tripleSum (fun i j k=>W i j k*(U i j k+U i k j))+
      square U+square (fun i j k=>U i k j)+cross U := by
    unfold noise square cross
    simp only [sub_eq_add_neg,←tripleSum_neg,←tripleSum_add,←tripleSum_smul]
    congr 1
    funext i j k
    ring
  rw [he,permuted_square U]
  ring

theorem completion {β : ℝ} (hβ : β<1) (U W : Array3 ι)
    (hU : ∀ i j k,U i j k=U j i k)
    (hW12 : ∀ i j k,W i j k=W j i k)
    (hW23 : ∀ i j k,W i j k=W i k j) :
    β*square W+(2-4/(3*(1-β)))*square U+
      (1-8/(3*(1-β)))*cross U≤noise U W := by
  have hpos : 0<1-β := by linarith
  have hsum : 0≤tripleSum (fun i j k=>((1-β)*W i j k-symPart U i j k)^2) := by
    exact Finset.sum_nonneg fun i _=>Finset.sum_nonneg fun j _=>
      Finset.sum_nonneg fun k _=>sq_nonneg _
  have he : tripleSum (fun i j k=>((1-β)*W i j k-symPart U i j k)^2)=
      (1-β)^2*square W-2*(1-β)*
        tripleSum (fun i j k=>W i j k*symPart U i j k)+square (symPart U) := by
    unfold square
    simp only [sub_eq_add_neg,←tripleSum_neg,←tripleSum_add,←tripleSum_smul]
    congr 1
    funext i j k
    ring
  rw [he,symPart_square U hU] at hsum
  rw [noise_eq,symmetric_pairing U W hW12 hW23]
  field_simp
  nlinarith

 theorem lower_of_bounds {β E : ℝ} (hβ0 : (1 : ℝ)/3≤β) (hβ1 : β<1)
    (U W : Array3 ι) (hU : ∀ i j k,U i j k=U j i k)
    (hW12 : ∀ i j k,W i j k=W j i k)
    (hW23 : ∀ i j k,W i j k=W i k j)
    (hQ : square U≤8*E) (hR : cross U≤4*E) :
    β*square W-(64/(3*(1-β))-20)*E≤noise U W := by
  have hc := completion hβ1 U W hU hW12 hW23
  have hpos : 0<1-β := by linarith
  have ha : 2-4/(3*(1-β))≤0 := by
    apply sub_nonpos.mpr
    apply (le_div_iff₀ (by positivity : 0<3*(1-β))).mpr
    linarith
  have hb : 1-8/(3*(1-β))≤0 := by
    apply sub_nonpos.mpr
    apply (le_div_iff₀ (by positivity : 0<3*(1-β))).mpr
    linarith
  have hq := mul_le_mul_of_nonpos_left hQ ha
  have hr := mul_le_mul_of_nonpos_left hR hb
  have hid : (2-4/(3*(1-β)))*(8*E)+(1-8/(3*(1-β)))*(4*E)=
      -(64/(3*(1-β))-20)*E := by ring
  linarith

end KLSBelow25.CubicSymmetricNoise
#print axioms KLSBelow25.CubicSymmetricNoise.lower_of_bounds
