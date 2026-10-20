import KLSConstantImprovement.ActualDirectCubicCoefficients405

/-! Exact finite affine score and Hessian-test expansions. E1 remains
signed. The inverse-metric cancellation uses the literal identity JH=I. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualAffineFiniteExpansion405
open ActualQuarticCongruence405 ActualQuarticThirdWhitening405
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def affineCross (H A : Matrix (Fin n) (Fin n) ℝ)
    (T N : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ a, (T a * N a * A * H).trace

def affineScoreDifferential (H A : Matrix (Fin n) (Fin n) ℝ)
    (T N : Fin n → Matrix (Fin n) (Fin n) ℝ) (a : Fin n) : ℝ :=
  (T a * N a * A * H + T a * H * mixFamily H T a * H + T a * H * A * N a).trace

def affineHessianDifferential (H A : Matrix (Fin n) (Fin n) ℝ)
    (T N : Fin n → Matrix (Fin n) (Fin n) ℝ) (a : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  mixFamily H T a * H * A + A * N a * A + A * H * mixFamily H T a

def affineSignedConnection (J A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ a, ∑ b, J a b * (A * N a * A * N b).trace

theorem trace_four_reverse (A B C D : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hB : B.IsSymm) (hC : C.IsSymm) (hD : D.IsSymm) :
    (A * B * C * D).trace = (A * D * C * B).trace := by
  calc
    _ = ((A * B * C * D).transpose).trace := (Matrix.trace_transpose _).symm
    _ = (D * C * B * A).trace := by
      simp only [Matrix.transpose_mul, hA.eq, hB.eq, hC.eq, hD.eq, Matrix.mul_assoc]
    _ = _ := by simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (D * C * B) A

theorem rawGram_symmetric (H : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : (rawGram H T).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simpa only [rawGram, Matrix.mul_assoc] using Matrix.trace_mul_comm (T j * H) (T i * H)

theorem affine_omega_score (H : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ a, (T a * H * mixFamily H T a * H).trace) = (H * rawGram H T).trace := by
  simp only [mixFamily, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  change (∑ a, ∑ i, H a i * rawGram H T a i) = _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by
    rw [(rawGram_symmetric H T).apply a i]

theorem affine_score_expansion (H A : Matrix (Fin n) (Fin n) ℝ)
    (T N : Fin n → Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (hA : A.IsSymm)
    (hT : ∀ a, (T a).IsSymm) (hN : ∀ a, (N a).IsSymm) :
    (∑ a, affineScoreDifferential H A T N a) =
      (H * rawGram H T).trace + 2 * affineCross H A T N := by
  have ht (a : Fin n) : (T a * H * A * N a).trace = (T a * N a * A * H).trace :=
    trace_four_reverse _ _ _ _ (hT a) hH hA (hN a)
  simp only [affineScoreDifferential, Matrix.trace_add, ht, Finset.sum_add_distrib,
    affine_omega_score, affineCross]
  ring

theorem contract_affine_omega (J H : Matrix (Fin n) (Fin n) ℝ)
    (hJH : J * H = 1) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (a : Fin n) :
    (∑ b, J a b • mixFamily H T b) = T a := by
  ext i j
  calc
    _ = ∑ c, (J * H) a c * T c i j := by
      simp only [mixFamily, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    _ = ∑ c, (1 : Matrix (Fin n) (Fin n) ℝ) a c * T c i j :=
      congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => ∑ c, M a c * T c i j) hJH
    _ = _ := by
      change (∑ c, (if a = c then (1 : ℝ) else 0) * T c i j) = T a i j
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem contract_affine_omega_trace_middle (J H : Matrix (Fin n) (Fin n) ℝ)
    (hJH : J * H = 1) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (a : Fin n)
    (C D E : Matrix (Fin n) (Fin n) ℝ) :
    (∑ b, J a b * (C * mixFamily H T b * D * E).trace) = (C * T a * D * E).trace := by
  rw [← contract_affine_omega J H hJH T a]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]

theorem contract_affine_omega_trace_right (J H : Matrix (Fin n) (Fin n) ℝ)
    (hJH : J * H = 1) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (a : Fin n)
    (C D E : Matrix (Fin n) (Fin n) ℝ) :
    (∑ b, J a b * (C * D * E * mixFamily H T b).trace) = (C * D * E * T a).trace := by
  rw [← contract_affine_omega J H hJH T a]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]

theorem affine_hessian_metric_expansion (J H A : Matrix (Fin n) (Fin n) ℝ)
    (hJH : J * H = 1) (T N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsSymm) (hA : A.IsSymm)
    (hT : ∀ a, (T a).IsSymm) (hN : ∀ a, (N a).IsSymm) :
    (∑ a, ∑ b, J a b * (N a * affineHessianDifferential H A T N b).trace) =
      affineSignedConnection J A N + 2 * affineCross H A T N := by
  have hleft (a : Fin n) : (N a * T a * H * A).trace = (T a * N a * A * H).trace := by
    calc
      _ = (T a * H * A * N a).trace := by
        simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (N a) (T a * H * A)
      _ = _ := trace_four_reverse _ _ _ _ (hT a) hH hA (hN a)
  have hright (a : Fin n) : (N a * A * H * T a).trace = (T a * N a * A * H).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (N a * A * H) (T a)
  have hmiddle (a b : Fin n) : (N a * A * N b * A).trace = (A * N a * A * N b).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (N a * A * N b) A
  simp only [affineHessianDifferential, Matrix.mul_add, Matrix.trace_add, mul_add,
    Finset.sum_add_distrib, ← Matrix.mul_assoc, hmiddle,
    contract_affine_omega_trace_middle J H hJH T,
    contract_affine_omega_trace_right J H hJH T, hleft, hright,
    affineSignedConnection, affineCross]
  ring

end KLSConstantImprovement.ActualAffineFiniteExpansion405

#print axioms KLSConstantImprovement.ActualAffineFiniteExpansion405.affine_score_expansion
#print axioms KLSConstantImprovement.ActualAffineFiniteExpansion405.contract_affine_omega
#print axioms KLSConstantImprovement.ActualAffineFiniteExpansion405.affine_hessian_metric_expansion
