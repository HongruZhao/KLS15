import KLSConstantImprovement.TensorGramThirdSandwich

/-! Finite all-tensor calibration for explicitly diagonal product kernels.
For independent normalized scalar kernels, the second/third moments give
the repeated-slot weights below. Their actual probability and canonical
kernel identification remain analytic inputs. Gaussian, standardized
Gamma(shape >= 1), and uniform factors have moments at most 2 and 6.
Centered exponential factors have exact weights 6, 2, and 1. No dependent
original-law improvement or new Poincare endpoint follows. -/
noncomputable section
open Finset
namespace KLSConstantImprovement.ProductKernelTensorThirdSharp
open OriginalUpperRecovery6TensorGram

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def productWeight (second third : ι → ℝ) (i j k : ι) : ℝ :=
  if i = j then (if j = k then third i else second i)
  else if i = k then second i else if j = k then second j else 1

def productEnergy (T : ι → ι → ι → ℝ) (second third : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, T i j k ^ 2 * productWeight second third i j k

def diagonalMass (T : ι → ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, if i = j ∧ j = k then T i j k ^ 2 else 0

def repeatedMass (T : ι → ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k,
    if (i = j ∨ i = k ∨ j = k) ∧ ¬(i = j ∧ j = k) then T i j k ^ 2 else 0

def distinctMass (T : ι → ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, if i ≠ j ∧ i ≠ k ∧ j ≠ k then T i j k ^ 2 else 0

theorem productWeight_nonneg (second third : ι → ℝ)
    (hsecond : ∀ i, 0 ≤ second i) (hthird : ∀ i, 0 ≤ third i) (i j k : ι) :
    0 ≤ productWeight second third i j k := by
  unfold productWeight
  split_ifs <;> first | exact hthird _ | exact hsecond _ | norm_num

theorem productWeight_le_six (second third : ι → ℝ)
    (hsecond : ∀ i, second i ≤ 2) (hthird : ∀ i, third i ≤ 6) (i j k : ι) :
    productWeight second third i j k ≤ 6 := by
  unfold productWeight
  split_ifs <;> first | exact hthird _ | linarith [hsecond i, hsecond j]

theorem productEnergy_nonneg (T : ι → ι → ι → ℝ) (second third : ι → ℝ)
    (hsecond : ∀ i, 0 ≤ second i) (hthird : ∀ i, 0 ≤ third i) :
    0 ≤ productEnergy T second third := by
  unfold productEnergy
  exact sum_nonneg fun i _ => sum_nonneg fun j _ => sum_nonneg fun k _ =>
    mul_nonneg (sq_nonneg _) (productWeight_nonneg second third hsecond hthird i j k)

theorem productEnergy_le_six (T : ι → ι → ι → ℝ) (second third : ι → ℝ)
    (hsecond : ∀ i, second i ≤ 2) (hthird : ∀ i, third i ≤ 6) :
    productEnergy T second third ≤ 6 * tensorNormSq T := by
  simp only [productEnergy, tensorNormSq, mul_sum]
  apply sum_le_sum
  intro i hi
  apply sum_le_sum
  intro j hj
  apply sum_le_sum
  intro k hk
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (productWeight_le_six second third hsecond hthird i j k)
      (sq_nonneg (T i j k))

theorem mass_partition (T : ι → ι → ι → ℝ) :
    tensorNormSq T = diagonalMass T + repeatedMass T + distinctMass T := by
  simp only [tensorNormSq, diagonalMass, repeatedMass, distinctMass,
    ←sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro k hk
  by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hjk : j = k
  all_goals simp_all

theorem mass_nonneg (T : ι → ι → ι → ℝ) :
    0 ≤ diagonalMass T ∧ 0 ≤ repeatedMass T ∧ 0 ≤ distinctMass T := by
  unfold diagonalMass repeatedMass distinctMass
  constructor
  · exact sum_nonneg fun i _ => sum_nonneg fun j _ => sum_nonneg fun k _ => by
      split_ifs <;> positivity
  constructor
  · exact sum_nonneg fun i _ => sum_nonneg fun j _ => sum_nonneg fun k _ => by
      split_ifs <;> positivity
  · exact sum_nonneg fun i _ => sum_nonneg fun j _ => sum_nonneg fun k _ => by
      split_ifs <;> positivity

theorem exponential_energy_decomposition (T : ι → ι → ι → ℝ) :
    productEnergy T (fun _ => 2) (fun _ => 6) =
      6 * diagonalMass T + 2 * repeatedMass T + distinctMass T := by
  simp only [productEnergy, diagonalMass, repeatedMass, distinctMass,
    mul_sum, ←sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro k hk
  by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hjk : j = k
  all_goals simp_all [productWeight] <;> ring

theorem exponential_six_gap (T : ι → ι → ι → ℝ) :
    6 * tensorNormSq T - productEnergy T (fun _ => 2) (fun _ => 6) =
      4 * repeatedMass T + 5 * distinctMass T := by
  rw [mass_partition, exponential_energy_decomposition]
  ring

theorem exponential_six_equality_iff (T : ι → ι → ι → ℝ) :
    productEnergy T (fun _ => 2) (fun _ => 6) = 6 * tensorNormSq T ↔
      repeatedMass T = 0 ∧ distinctMass T = 0 := by
  have h := exponential_six_gap T
  have hn := mass_nonneg T
  constructor
  · intro he
    rw [he] at h
    constructor <;> nlinarith [hn.2.1, hn.2.2]
  · rintro ⟨hr, hd⟩
    rw [hr, hd] at h
    linarith

theorem literal_single_exponential_sharp :
    tensorNormSq (fun (_ _ _ : Fin 1) => (1 : ℝ)) = 1 ∧
    productEnergy (fun (_ _ _ : Fin 1) => (1 : ℝ))
      (fun _ => 2) (fun _ => 6) = 6 := by
  norm_num [tensorNormSq, productEnergy, productWeight, Fin.sum_univ_succ]

theorem same_product_kernel_transfer (T : ι → ι → ι → ℝ)
    (second third : ι → ℝ) {actualW : ℝ}
    (hcanonical : actualW = productEnergy T second third)
    (hsecond : ∀ i, second i ≤ 2) (hthird : ∀ i, third i ≤ 6) :
    actualW ≤ 6 * tensorNormSq T := by
  rw [hcanonical]
  exact productEnergy_le_six T second third hsecond hthird

end KLSConstantImprovement.ProductKernelTensorThirdSharp
#print axioms KLSConstantImprovement.ProductKernelTensorThirdSharp.productWeight_nonneg
#print axioms KLSConstantImprovement.ProductKernelTensorThirdSharp.productWeight_le_six
#print axioms KLSConstantImprovement.ProductKernelTensorThirdSharp.productEnergy_nonneg
#print axioms KLSConstantImprovement.ProductKernelTensorThirdSharp.productEnergy_le_six
#print axioms KLSConstantImprovement.ProductKernelTensorThirdSharp.mass_partition
#print axioms KLSConstantImprovement.ProductKernelTensorThirdSharp.mass_nonneg
#print axioms KLSConstantImprovement.ProductKernelTensorThirdSharp.exponential_energy_decomposition
#print axioms KLSConstantImprovement.ProductKernelTensorThirdSharp.exponential_six_gap
#print axioms KLSConstantImprovement.ProductKernelTensorThirdSharp.exponential_six_equality_iff
#print axioms KLSConstantImprovement.ProductKernelTensorThirdSharp.literal_single_exponential_sharp
#print axioms KLSConstantImprovement.ProductKernelTensorThirdSharp.same_product_kernel_transfer
