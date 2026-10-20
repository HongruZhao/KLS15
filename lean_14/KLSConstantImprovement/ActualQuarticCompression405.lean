import KLS.TensorCommutatorComparison
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Literal finite matrix compressions for the quartic Gram square. The row
space is left unchanged. The ambient matrix-coordinate space may be an
ordered product index; no Euclidean norm is transported through a
nonorthogonal congruence.
-/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualQuarticCompression405
variable {p q : Type*} [Fintype p] [Fintype q]

def entryPair (A B : Matrix p q ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

def entrySquare (A : Matrix p q ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

theorem entrySquare_nonneg (A : Matrix p q ℝ) : 0 ≤ entrySquare A := by
  unfold entrySquare
  positivity

theorem entryPair_eq_trace (A B : Matrix p q ℝ) :
    entryPair A B = (A.transpose * B).trace := by
  rw [← Matrix.vec_dotProduct_vec]
  simp only [entryPair, dotProduct, Matrix.vec, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

theorem entrySquare_eq_trace (A : Matrix p q ℝ) :
    entrySquare A = (A * A.transpose).trace := by
  simp only [entrySquare, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply, pow_two]

theorem entrySquare_eq_trace_sq (A : Matrix p p ℝ) (hA : A.IsSymm) :
    entrySquare A = (A * A).trace := by rw [entrySquare_eq_trace, hA.eq]

private theorem trace_abba (A B : Matrix p p ℝ) :
    ((A * B) * (B * A)).trace = ((A * A) * (B * B)).trace := by
  calc
    _ = (A * (B * B) * A).trace := by simp only [Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_cycle _ _ _

private theorem trace_baba (A B : Matrix p p ℝ) :
    ((B * A) * (B * A)).trace = ((A * B) * (A * B)).trace := by
  calc
    _ = (B * (A * B * A)).trace := by simp only [Matrix.mul_assoc]
    _ = ((A * B * A) * B).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The exact finite commutator remainder, for arbitrary finite ambient
indices. This applies directly to the ordered matrix-coordinate space. -/
theorem quartic_commutator_square (B K : Matrix p p ℝ)
    (hB : B.IsSymm) (hK : K.IsSymm) :
    (B * B * K * K).trace - (B * K * B * K).trace =
      (1 / 2 : ℝ) * entrySquare (B * K - K * B) := by
  rw [entrySquare_eq_trace, Matrix.transpose_sub, Matrix.transpose_mul,
    Matrix.transpose_mul, hB.eq, hK.eq, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub]
  have ha := trace_abba B K
  have hb := trace_abba K B
  have hc := trace_baba B K
  have hd := Matrix.trace_mul_comm (K * K) (B * B)
  simp only [Matrix.mul_assoc] at ha hb hc hd ⊢
  rw [ha, hb, hc, hd]
  ring

def compressionGram (V : Matrix p q ℝ) : Matrix q q ℝ := V.transpose * V

def ambientGram (V : Matrix p q ℝ) : Matrix p p ℝ := V * V.transpose

def compressedAction (V : Matrix p q ℝ) (K : Matrix p p ℝ) : Matrix q q ℝ :=
  V.transpose * K * V

theorem ambientGram_symmetric (V : Matrix p q ℝ) : (ambientGram V).IsSymm := by
  change (V * V.transpose).transpose = V * V.transpose
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]

theorem compressionGram_symmetric (V : Matrix p q ℝ) : (compressionGram V).IsSymm := by
  change (V.transpose * V).transpose = V.transpose * V
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]

theorem compressedAction_symmetric (V : Matrix p q ℝ) (K : Matrix p p ℝ)
    (hK : K.IsSymm) : (compressedAction V K).IsSymm := by
  change (V.transpose * K * V).transpose = V.transpose * K * V
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hK.eq, Matrix.mul_assoc]

/-- E4 is the squared literal derivative compression, hence tr(BKBK). -/
theorem compressedAction_energy_trace (V : Matrix p q ℝ) (K : Matrix p p ℝ)
    (hK : K.IsSymm) :
    entrySquare (compressedAction V K) =
      (ambientGram V * K * ambientGram V * K).trace := by
  rw [entrySquare_eq_trace_sq _ (compressedAction_symmetric V K hK)]
  change ((V.transpose * K * V) * (V.transpose * K * V)).trace = _
  calc
    _ = (V.transpose * (K * V * V.transpose * K * V)).trace := by simp only [Matrix.mul_assoc]
    _ = ((K * V * V.transpose * K * V) * V.transpose).trace := Matrix.trace_mul_comm _ _
    _ = (K * (ambientGram V * K * ambientGram V)).trace := by
      simp only [ambientGram, Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_comm _ _

/-- The curvature plus Hessian-of-G contraction is tr(B²K²). -/
theorem compressedAction_second_trace (V : Matrix p q ℝ) (K : Matrix p p ℝ) :
    entryPair (compressionGram V) (compressedAction V (K * K)) =
      (ambientGram V * ambientGram V * K * K).trace := by
  rw [entryPair_eq_trace, (compressionGram_symmetric V).eq]
  change ((V.transpose * V) * (V.transpose * (K * K) * V)).trace = _
  calc
    _ = (V.transpose * (V * V.transpose * (K * K) * V)).trace := by simp only [Matrix.mul_assoc]
    _ = ((V * V.transpose * (K * K) * V) * V.transpose).trace := Matrix.trace_mul_comm _ _
    _ = ((ambientGram V * (K * K)) * ambientGram V).trace := by
      simp only [ambientGram, Matrix.mul_assoc]
    _ = (ambientGram V * (ambientGram V * (K * K))).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The finite quartic energy gap is an actual commutator square. -/
theorem compression_energy_gap (V : Matrix p q ℝ) (K : Matrix p p ℝ) (hK : K.IsSymm) :
    entryPair (compressionGram V) (compressedAction V (K * K)) -
      entrySquare (compressedAction V K) =
        (1 / 2 : ℝ) * entrySquare (ambientGram V * K - K * ambientGram V) := by
  rw [compressedAction_second_trace, compressedAction_energy_trace V K hK]
  exact quartic_commutator_square _ _ (ambientGram_symmetric V) hK

theorem compression_energy_le (V : Matrix p q ℝ) (K : Matrix p p ℝ) (hK : K.IsSymm) :
    entrySquare (compressedAction V K) ≤
      entryPair (compressionGram V) (compressedAction V (K * K)) := by
  have he := compression_energy_gap V K hK
  have hn := entrySquare_nonneg (ambientGram V * K - K * ambientGram V)
  linarith

end KLSConstantImprovement.ActualQuarticCompression405

#print axioms KLSConstantImprovement.ActualQuarticCompression405.quartic_commutator_square
#print axioms KLSConstantImprovement.ActualQuarticCompression405.compressedAction_energy_trace
#print axioms KLSConstantImprovement.ActualQuarticCompression405.compressedAction_second_trace
#print axioms KLSConstantImprovement.ActualQuarticCompression405.compression_energy_gap
#print axioms KLSConstantImprovement.ActualQuarticCompression405.compression_energy_le
