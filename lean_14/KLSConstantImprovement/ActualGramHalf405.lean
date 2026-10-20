import KLSConstantImprovement.ActualKroneckerGram405
import KLS.SmoothCutoffSequence
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
The actual finite Gram square-root inequality, including singular Gram.
An epsilon identity slice is added before the nonsingular block-Gram
comparison. Only a numerical finite matrix inequality passes to the
limit; no inverse or support certificate on a singular Gram is assumed.
The final symmetric test matrix may have either sign.
-/
noncomputable section
open Matrix Set Filter
open scoped BigOperators Kronecker Topology MatrixOrder Matrix.Norms.L2Operator
namespace KLSConstantImprovement.ActualGramHalf405
open KLS ActualKroneckerGram405
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def regularizedSlices (T : κ → Matrix ι ι ℝ) (ε : ℝ) : Option κ → Matrix ι ι ℝ
  | none => ε • 1
  | some i => T i

theorem regularizedSlices_symmetric (T : κ → Matrix ι ι ℝ)
    (hT : ∀ i, (T i).IsSymm) (ε : ℝ) (i : Option κ) : (regularizedSlices T ε i).IsSymm := by
  cases i with
  | none => change (ε • (1 : Matrix ι ι ℝ)).transpose = ε • 1; simp
  | some i => exact hT i

theorem regularizedSlices_gram (T : κ → Matrix ι ι ℝ) (ε : ℝ) :
    sliceGram (regularizedSlices T ε) = ε ^ 2 • (1 : Matrix ι ι ℝ) + sliceGram T := by
  simp only [sliceGram, Fintype.sum_option, regularizedSlices,
    smul_mul_smul_comm, Matrix.one_mul, pow_two]

theorem regularizedSlices_kronecker (T : κ → Matrix ι ι ℝ) (ε : ℝ) :
    sliceKronecker (regularizedSlices T ε) =
      ε ^ 2 • (1 : Matrix (ι × ι) (ι × ι) ℝ) + sliceKronecker T := by
  simp only [sliceKronecker, Fintype.sum_option, regularizedSlices,
    Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
    Matrix.one_kronecker_one, pow_two]

/-- Singular Gram matrices are covered by a concrete positive
regularization and operator-square-root continuity. -/
theorem sliceKronecker_le_sqrtGram (T : κ → Matrix ι ι ℝ)
    (hT : ∀ i, (T i).IsSymm) :
    sliceKronecker T ≤ CFC.sqrt (sliceGram T) ⊗ₖ CFC.sqrt (sliceGram T) := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    letI : IsEmpty ι := hι
    exact le_of_eq (Subsingleton.elim _ _)
  | inr hι =>
    letI : Nonempty ι := hι
    let Gk (k : ℕ) := sliceGram (regularizedSlices T (cutoffScale k))
    have hG : (sliceGram T).PosSemidef := sliceGram_posSemidef T hT
    have hGk (k : ℕ) : (Gk k).PosDef := by
      rw [show Gk k = cutoffScale k ^ 2 • (1 : Matrix ι ι ℝ) + sliceGram T from
        regularizedSlices_gram T (cutoffScale k)]
      exact (Matrix.PosDef.one.smul (sq_pos_of_pos (cutoffScale_pos k))).add_posSemidef hG
    have hupper (k : ℕ) : sliceKronecker T ≤ CFC.sqrt (Gk k) ⊗ₖ CFC.sqrt (Gk k) := by
      have hp := sliceKronecker_le_sqrtGram_of_posDef (regularizedSlices T (cutoffScale k))
        (regularizedSlices_symmetric T hT (cutoffScale k)) (hGk k)
      apply le_trans ?_ hp
      rw [regularizedSlices_kronecker]
      exact le_add_of_nonneg_left (Matrix.PosSemidef.one.smul (sq_nonneg (cutoffScale k))).nonneg
    have hconv : Tendsto Gk atTop (𝓝 (sliceGram T)) := by
      have he : Gk = fun k => cutoffScale k ^ 2 • (1 : Matrix ι ι ℝ) + sliceGram T := by
        funext k
        exact regularizedSlices_gram T (cutoffScale k)
      rw [he]
      simpa using ((cutoffScale_tendsto_zero.pow 2).smul_const (1 : Matrix ι ι ℝ)).add_const
        (sliceGram T)
    have hwithin : Tendsto Gk atTop (𝓝[{M : Matrix ι ι ℝ | 0 ≤ M}] (sliceGram T)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hconv, Eventually.of_forall fun k => (hGk k).posSemidef.nonneg⟩
    have hroot : Tendsto (fun k => CFC.sqrt (Gk k)) atTop (𝓝 (CFC.sqrt (sliceGram T))) :=
      (CFC.continuousOn_sqrt (A := Matrix ι ι ℝ) (sliceGram T) hG.nonneg).tendsto.comp hwithin
    have hc : Continuous (fun M : Matrix ι ι ℝ => M ⊗ₖ M) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      change Continuous (fun M : Matrix ι ι ℝ => M i.1 j.1 * M i.2 j.2)
      fun_prop
    exact ge_of_tendsto (hc.continuousAt.tendsto.comp hroot) (Eventually.of_forall hupper)

theorem vec_kronecker_trace (A H : Matrix ι ι ℝ) (hA : A.IsSymm) (hH : H.IsSymm) :
    Matrix.vec H ⬝ᵥ ((A ⊗ₖ A) *ᵥ Matrix.vec H) = (A * H * A * H).trace := by
  rw [Matrix.kronecker_mulVec_vec, hA.eq, Matrix.vec_dotProduct_vec, hH.eq]
  exact Matrix.trace_mul_comm H (A * H * A)

/-- Arbitrary symmetric slice families satisfy the literal Gram-half
trace inequality. The Gram may be singular and H need not be positive. -/
theorem gram_half_trace_inequality (T : κ → Matrix ι ι ℝ)
    (hT : ∀ i, (T i).IsSymm) (H : Matrix ι ι ℝ) (hH : H.IsSymm) :
    (∑ i, (T i * H * T i * H).trace) ≤
      (CFC.sqrt (sliceGram T) * H * CFC.sqrt (sliceGram T) * H).trace := by
  have hp := (Matrix.le_iff.mp (sliceKronecker_le_sqrtGram T hT)).dotProduct_mulVec_nonneg
    (Matrix.vec H)
  have hA : (CFC.sqrt (sliceGram T)).IsSymm :=
    (CFC.sqrt_nonneg (sliceGram T)).posSemidef.isHermitian.isSymm
  simp only [Pi.star_apply, star_trivial, Matrix.sub_mulVec, dotProduct_sub,
    sliceKronecker, Matrix.sum_mulVec, dotProduct_sum] at hp
  rw [vec_kronecker_trace _ H hA hH] at hp
  have he : (∑ i, Matrix.vec H ⬝ᵥ ((T i ⊗ₖ T i) *ᵥ Matrix.vec H)) =
      ∑ i, (T i * H * T i * H).trace :=
    Finset.sum_congr rfl fun i _ => vec_kronecker_trace (T i) H (hT i) hH
  rw [he] at hp
  exact sub_nonneg.mp hp

theorem gram_half_gap_nonneg (T : κ → Matrix ι ι ℝ)
    (hT : ∀ i, (T i).IsSymm) (H : Matrix ι ι ℝ) (hH : H.IsSymm) :
    0 ≤ (CFC.sqrt (sliceGram T) * H * CFC.sqrt (sliceGram T) * H).trace -
      ∑ i, (T i * H * T i * H).trace :=
  sub_nonneg.mpr (gram_half_trace_inequality T hT H hH)

end KLSConstantImprovement.ActualGramHalf405

#print axioms KLSConstantImprovement.ActualGramHalf405.sliceKronecker_le_sqrtGram
#print axioms KLSConstantImprovement.ActualGramHalf405.gram_half_trace_inequality
#print axioms KLSConstantImprovement.ActualGramHalf405.gram_half_gap_nonneg
