import KLSConstantImprovement.ActualQuarticCompression405
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.Abel

/-!
The literal ordered matrix-coordinate white frame for quartic Gram
production. Only the two matrix slots are whitened; the row family is
unchanged. All derivative and second-variation contractions are bound to
actual finite sums before invoking the commutator square.
-/
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace KLSConstantImprovement.ActualQuarticWhiteFrame405
open ActualQuarticCompression405
variable {ι κ τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype τ]

def rowColumns (S : κ → Matrix ι ι ℝ) : Matrix (ι × ι) κ ℝ := fun p i => Matrix.vec (S i) p

def doubleSlot (M : Matrix ι ι ℝ) : Matrix (ι × ι) (ι × ι) ℝ :=
  M ⊗ₖ (1 : Matrix ι ι ℝ) + (1 : Matrix ι ι ℝ) ⊗ₖ M

def whiteGram (S : κ → Matrix ι ι ℝ) : Matrix κ κ ℝ := fun i j => (S i * S j).trace

def whiteGramDerivative (S : κ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ) : Matrix κ κ ℝ :=
  fun i j => (S i * M * S j).trace + (S i * S j * M).trace

def whiteGramSecond (S : κ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ) : Matrix κ κ ℝ :=
  fun i j => (S i * (M * M) * S j).trace +
    2 * (S i * M * S j * M).trace + (S i * S j * (M * M)).trace

def whiteCurvature (S : κ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j, whiteGram S i j *
    ((S i * (M * M) * S j).trace + (S i * S j * (M * M)).trace)

def whiteHessian (S : κ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ) : ℝ :=
  2 * ∑ i, ∑ j, whiteGram S i j * (S i * M * S j * M).trace

theorem doubleSlot_symmetric (M : Matrix ι ι ℝ) (hM : M.IsSymm) : (doubleSlot M).IsSymm := by
  change (M ⊗ₖ (1 : Matrix ι ι ℝ) + (1 : Matrix ι ι ℝ) ⊗ₖ M).transpose = _
  simp only [Matrix.transpose_add, ← Matrix.kroneckerMap_transpose, Matrix.transpose_one, hM.eq]
  rfl

theorem doubleSlot_mulVec (M S : Matrix ι ι ℝ) (hM : M.IsSymm) :
    doubleSlot M *ᵥ Matrix.vec S = Matrix.vec (M * S + S * M) := by
  rw [doubleSlot, Matrix.add_mulVec, Matrix.kronecker_mulVec_vec, Matrix.kronecker_mulVec_vec,
    Matrix.transpose_one, hM.eq, Matrix.one_mul, Matrix.mul_one, ← Matrix.vec_add]
  exact congrArg Matrix.vec (add_comm _ _)

theorem rowColumns_gram (S : κ → Matrix ι ι ℝ) (hS : ∀ i, (S i).IsSymm) :
    compressionGram (rowColumns S) = whiteGram S := by
  ext i j
  change Matrix.vec (S i) ⬝ᵥ Matrix.vec (S j) = (S i * S j).trace
  rw [Matrix.vec_dotProduct_vec, (hS i).eq]

theorem rowColumns_derivative (S : κ → Matrix ι ι ℝ) (hS : ∀ i, (S i).IsSymm)
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    compressedAction (rowColumns S) (doubleSlot M) = whiteGramDerivative S M := by
  ext i j
  unfold compressedAction
  rw [Matrix.mul_assoc]
  change Matrix.vec (S i) ⬝ᵥ (doubleSlot M *ᵥ Matrix.vec (S j)) = _
  rw [doubleSlot_mulVec M (S j) hM, Matrix.vec_dotProduct_vec, (hS i).eq,
    Matrix.mul_add, Matrix.trace_add]
  simp only [whiteGramDerivative, Matrix.mul_assoc]

theorem doubleSlot_square_mulVec (M S : Matrix ι ι ℝ) (hM : M.IsSymm) :
    (doubleSlot M * doubleSlot M) *ᵥ Matrix.vec S =
      Matrix.vec ((M * M) * S + (M * S * M + M * S * M) + S * (M * M)) := by
  rw [← Matrix.mulVec_mulVec, doubleSlot_mulVec M S hM,
    doubleSlot_mulVec M (M * S + S * M) hM]
  congr 1
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

theorem rowColumns_second (S : κ → Matrix ι ι ℝ) (hS : ∀ i, (S i).IsSymm)
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    compressedAction (rowColumns S) (doubleSlot M * doubleSlot M) = whiteGramSecond S M := by
  ext i j
  unfold compressedAction
  rw [Matrix.mul_assoc]
  change Matrix.vec (S i) ⬝ᵥ ((doubleSlot M * doubleSlot M) *ᵥ Matrix.vec (S j)) = _
  rw [doubleSlot_square_mulVec M (S j) hM, Matrix.vec_dotProduct_vec, (hS i).eq]
  simp only [Matrix.mul_add, Matrix.trace_add, whiteGramSecond, Matrix.mul_assoc]
  ring

theorem white_second_contraction (S : κ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ) :
    entryPair (whiteGram S) (whiteGramSecond S M) = whiteCurvature S M + whiteHessian S M := by
  unfold entryPair whiteCurvature whiteHessian
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold whiteGramSecond
  ring

/-- The literal white derivative energy and curvature/Hessian contraction
have the exact finite commutator difference. -/
theorem white_quartic_commutator_square (S : κ → Matrix ι ι ℝ)
    (hS : ∀ i, (S i).IsSymm) (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    whiteCurvature S M + whiteHessian S M - entrySquare (whiteGramDerivative S M) =
      (1 / 2 : ℝ) * entrySquare
        (ambientGram (rowColumns S) * doubleSlot M - doubleSlot M * ambientGram (rowColumns S)) := by
  have he := compression_energy_gap (rowColumns S) (doubleSlot M) (doubleSlot_symmetric M hM)
  rw [rowColumns_gram S hS, rowColumns_derivative S hS M hM,
    rowColumns_second S hS M hM, white_second_contraction] at he
  exact he

theorem white_quartic_family_commutator_square (S : κ → Matrix ι ι ℝ)
    (hS : ∀ i, (S i).IsSymm) (M : τ → Matrix ι ι ℝ) (hM : ∀ l, (M l).IsSymm) :
    (∑ l, (whiteCurvature S (M l) + whiteHessian S (M l))) -
      (∑ l, entrySquare (whiteGramDerivative S (M l))) =
      (1 / 2 : ℝ) * ∑ l, entrySquare
        (ambientGram (rowColumns S) * doubleSlot (M l) -
          doubleSlot (M l) * ambientGram (rowColumns S)) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => white_quartic_commutator_square S hS (M l) (hM l)

theorem white_quartic_energy_le (S : κ → Matrix ι ι ℝ)
    (hS : ∀ i, (S i).IsSymm) (M : τ → Matrix ι ι ℝ) (hM : ∀ l, (M l).IsSymm) :
    (∑ l, entrySquare (whiteGramDerivative S (M l))) ≤
      ∑ l, (whiteCurvature S (M l) + whiteHessian S (M l)) := by
  have he := white_quartic_family_commutator_square S hS M hM
  have hn : 0 ≤ ∑ l, entrySquare
      (ambientGram (rowColumns S) * doubleSlot (M l) -
        doubleSlot (M l) * ambientGram (rowColumns S)) :=
    Finset.sum_nonneg fun _ _ => entrySquare_nonneg _
  linarith

end KLSConstantImprovement.ActualQuarticWhiteFrame405

#print axioms KLSConstantImprovement.ActualQuarticWhiteFrame405.rowColumns_gram
#print axioms KLSConstantImprovement.ActualQuarticWhiteFrame405.rowColumns_derivative
#print axioms KLSConstantImprovement.ActualQuarticWhiteFrame405.rowColumns_second
#print axioms KLSConstantImprovement.ActualQuarticWhiteFrame405.white_quartic_family_commutator_square
#print axioms KLSConstantImprovement.ActualQuarticWhiteFrame405.white_quartic_energy_le
