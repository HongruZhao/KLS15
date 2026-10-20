import KLSConstantImprovement.ActualQuarticWhiteFrame405
import KLS.MatrixTracePositive

/-! Literal congruence formulas for the quartic Gram field. The finite
row family is arbitrary. The row index is never transformed. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualQuarticCongruence405
open ActualQuarticCompression405 ActualQuarticWhiteFrame405
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
set_option maxHeartbeats 1200000

def rawGram (H : Matrix ι ι ℝ) (T : κ → Matrix ι ι ℝ) : Matrix κ κ ℝ :=
  fun i j => (T i * H * T j * H).trace

def rawGramDerivative (H : Matrix ι ι ℝ) (T : κ → Matrix ι ι ℝ)
    (C : Matrix ι ι ℝ) : Matrix κ κ ℝ := fun i j =>
  (T i * C * T j * H).trace + (T i * H * T j * C).trace

def rawGramSecond (T : κ → Matrix ι ι ℝ)
    (C D : Matrix ι ι ℝ) : Matrix κ κ ℝ := fun i j =>
  (T i * C * T j * D).trace + (T i * D * T j * C).trace

def rowWhitening (Q : Matrix ι ι ℝ) (T : κ → Matrix ι ι ℝ) :
    κ → Matrix ι ι ℝ := fun i => Q * T i * Q

def rawQuarticGradient (H : Matrix ι ι ℝ) (T : κ → Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (2 : ℝ) • ∑ i, ∑ j, rawGram H T i j • (T i * H * T j)

theorem rowWhitening_symmetric (Q : Matrix ι ι ℝ) (hQ : Q.IsSymm)
    (T : κ → Matrix ι ι ℝ) (hT : ∀ i, (T i).IsSymm) (i : κ) :
    (rowWhitening Q T i).IsSymm := by
  change (Q * T i * Q).transpose = Q * T i * Q
  simp only [Matrix.transpose_mul, hQ.eq, (hT i).eq, Matrix.mul_assoc]

private theorem trace_rotate_congruence (Q A B : Matrix ι ι ℝ) :
    (Q * A * Q * B).trace = (A * Q * B * Q).trace := by
  calc
    _ = (Q * (A * Q * B)).trace := by simp only [Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_comm _ _

theorem rawGram_eq_white (Q : Matrix ι ι ℝ) (T : κ → Matrix ι ι ℝ) :
    rawGram (Q * Q) T = whiteGram (rowWhitening Q T) := by
  ext i j
  symm
  change ((Q * T i * Q) * (Q * T j * Q)).trace = _
  calc
    _ = (Q * T i * Q * (Q * T j * Q)).trace := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [trace_rotate_congruence]
      simp only [rawGram, Matrix.mul_assoc]

theorem rawGramDerivative_eq_white (Q : Matrix ι ι ℝ)
    (T : κ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ) :
    rawGramDerivative (Q * Q) T (Q * M * Q) =
      whiteGramDerivative (rowWhitening Q T) M := by
  ext i j
  unfold rawGramDerivative whiteGramDerivative rowWhitening
  have h₁ : ((Q * T i * Q) * M * (Q * T j * Q)).trace =
      (T i * (Q * M * Q) * T j * (Q * Q)).trace := by
    calc
      _ = (Q * T i * Q * (M * Q * T j * Q)).trace := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [trace_rotate_congruence]; simp only [Matrix.mul_assoc]
  have h₂ : ((Q * T i * Q) * (Q * T j * Q) * M).trace =
      (T i * (Q * Q) * T j * (Q * M * Q)).trace := by
    calc
      _ = (Q * T i * Q * (Q * T j * Q * M)).trace := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [trace_rotate_congruence]; simp only [Matrix.mul_assoc]
  rw [h₁, h₂]

theorem rawGramSecond_eq_white (Q : Matrix ι ι ℝ)
    (T : κ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ) :
    rawGramSecond T (Q * M * Q) (Q * M * Q) =
      fun i j => 2 * (rowWhitening Q T i * M * rowWhitening Q T j * M).trace := by
  ext i j
  have h : ((Q * T i * Q) * M * (Q * T j * Q) * M).trace =
      (T i * (Q * M * Q) * T j * (Q * M * Q)).trace := by
    calc
      _ = (Q * T i * Q * (M * Q * T j * Q * M)).trace := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [trace_rotate_congruence]; simp only [Matrix.mul_assoc]
  simp only [rawGramSecond, rowWhitening]
  rw [h]
  ring

theorem rawQuartic_hessian_eq_white (Q : Matrix ι ι ℝ)
    (T : κ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ) :
    entryPair (rawGram (Q * Q) T) (rawGramSecond T (Q * M * Q) (Q * M * Q)) =
      whiteHessian (rowWhitening Q T) M := by
  rw [rawGram_eq_white, rawGramSecond_eq_white]
  unfold entryPair whiteHessian
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem whiteCurvature_eq_double (S : κ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ) :
    whiteCurvature S M = 2 * ∑ i, ∑ j,
      whiteGram S i j * (S i * S j * (M * M)).trace := by
  have hs : (∑ i, ∑ j, whiteGram S i j * (S i * (M * M) * S j).trace) =
      ∑ i, ∑ j, whiteGram S i j * (S i * S j * (M * M)).trace := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.trace_mul_cycle (S j) (M * M) (S i)]
    unfold whiteGram
    rw [Matrix.trace_mul_comm (S j) (S i)]
  unfold whiteCurvature
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hs]
  ring

theorem rawQuartic_curvature_eq_white (Q : Matrix ι ι ℝ)
    (T : κ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ) :
    (rawQuarticGradient (Q * Q) T * (Q * (M * M) * Q)).trace =
      whiteCurvature (rowWhitening Q T) M := by
  rw [whiteCurvature_eq_double]
  unfold rawQuarticGradient
  simp only [Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul, Matrix.trace_sum,
    rawGram_eq_white, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h : (rowWhitening Q T i * rowWhitening Q T j * (M * M)).trace =
      ((T i * (Q * Q) * T j) * (Q * (M * M) * Q)).trace := by
    unfold rowWhitening
    calc
      _ = (Q * T i * Q * (Q * T j * Q * (M * M))).trace := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [trace_rotate_congruence]; simp only [Matrix.mul_assoc]
  rw [h]

theorem raw_quartic_family_gap {τ : Type*} [Fintype τ]
    (Q : Matrix ι ι ℝ) (hQ : Q.IsSymm)
    (T : κ → Matrix ι ι ℝ) (hT : ∀ i, (T i).IsSymm)
    (M : τ → Matrix ι ι ℝ) (hM : ∀ l, (M l).IsSymm) :
    (rawQuarticGradient (Q * Q) T * (Q * (∑ l, M l * M l) * Q)).trace +
      (∑ l, entryPair (rawGram (Q * Q) T)
        (rawGramSecond T (Q * M l * Q) (Q * M l * Q))) -
      (∑ l, entrySquare (rawGramDerivative (Q * Q) T (Q * M l * Q))) =
      (1 / 2 : ℝ) * ∑ l, entrySquare
        (ambientGram (rowColumns (rowWhitening Q T)) * doubleSlot (M l) -
          doubleSlot (M l) * ambientGram (rowColumns (rowWhitening Q T))) := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum,
    rawQuartic_curvature_eq_white, rawQuartic_hessian_eq_white,
    rawGramDerivative_eq_white]
  rw [← Finset.sum_add_distrib]
  exact white_quartic_family_commutator_square (rowWhitening Q T)
    (rowWhitening_symmetric Q hQ T hT) M hM

end KLSConstantImprovement.ActualQuarticCongruence405

#print axioms KLSConstantImprovement.ActualQuarticCongruence405.rawGramDerivative_eq_white
#print axioms KLSConstantImprovement.ActualQuarticCongruence405.rawQuartic_hessian_eq_white
#print axioms KLSConstantImprovement.ActualQuarticCongruence405.rawQuartic_curvature_eq_white
#print axioms KLSConstantImprovement.ActualQuarticCongruence405.raw_quartic_family_gap
