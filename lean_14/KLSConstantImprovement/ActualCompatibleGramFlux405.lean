import KLS.MatrixTracePositive

/-! Literal finite metric flux of a Gram entry for compatible weak
Jacobian values. Only first-slot source-tensor symmetry is needed for
the connection term; no derivative of that tensor is taken. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualCompatibleGramFlux405
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def gramRawDifferential (H : Matrix ι ι ℝ) (N : ι → Matrix ι ι ℝ)
    (u v : ι → ℝ) (Du Dv : Matrix ι ι ℝ) (r : ι) : ℝ :=
  ∑ b, ∑ a, ((Du a r * H a b + u a * N r a b) * v b + (u a * H a b) * Dv b r)

def thirdAlong (N : ι → Matrix ι ι ℝ) (u : ι → ℝ) : Matrix ι ι ℝ := ∑ a, u a • N a

theorem gramRawDifferential_vector (H : Matrix ι ι ℝ) (N : ι → Matrix ι ι ℝ)
    (hH : H.IsSymm) (hN : ∀ r a b, N r a b = N a r b)
    (u v : ι → ℝ) (Du Dv : Matrix ι ι ℝ) :
    gramRawDifferential H N u v Du Dv =
      Du.transpose *ᵥ (H *ᵥ v) + Dv.transpose *ᵥ (H *ᵥ u) + thirdAlong N u *ᵥ v := by
  funext r
  have hfirst : (∑ b, ∑ a, Du a r * H a b * v b) = (Du.transpose *ᵥ (H *ᵥ v)) r := by
    rw [Finset.sum_comm]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hsecond : (∑ b, ∑ a, u a * N r a b * v b) = (thirdAlong N u *ᵥ v) r := by
    simp only [thirdAlong, Matrix.mulVec, dotProduct, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by rw [hN r a b]
  have hthird : (∑ b, ∑ a, (u a * H a b) * Dv b r) = (Dv.transpose *ᵥ (H *ᵥ u)) r := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by rw [hH.apply a b]; ring
  change gramRawDifferential H N u v Du Dv r =
    (Du.transpose *ᵥ (H *ᵥ v)) r + (Dv.transpose *ᵥ (H *ᵥ u)) r + (thirdAlong N u *ᵥ v) r
  rw [← hfirst, ← hsecond, ← hthird]
  simp only [gramRawDifferential, add_mul, Finset.sum_add_distrib]
  ring

theorem compatible_gram_metric_flux (H J : Matrix ι ι ℝ) (N : ι → Matrix ι ι ℝ)
    (hH : H.IsSymm) (hJH : J * H = 1) (hN : ∀ r a b, N r a b = N a r b)
    (u v : ι → ℝ) (Du Dv : Matrix ι ι ℝ)
    (hDu : (H * Du).IsSymm) (hDv : (H * Dv).IsSymm) :
    J *ᵥ gramRawDifferential H N u v Du Dv =
      Du *ᵥ v + Dv *ᵥ u + (J * thirdAlong N u) *ᵥ v := by
  have hcomp (D : Matrix ι ι ℝ) (hc : (H * D).IsSymm) : J * (D.transpose * H) = D := by
    have he : D.transpose * H = H * D := by
      calc
        _ = (H * D).transpose := by rw [Matrix.transpose_mul, hH.eq]
        _ = _ := hc.eq
    rw [he, ← Matrix.mul_assoc, hJH, Matrix.one_mul]
  rw [gramRawDifferential_vector H N hH hN u v Du Dv]
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  rw [show J * (Du.transpose * H) = Du from hcomp Du hDu,
    show J * (Dv.transpose * H) = Dv from hcomp Dv hDv]

end KLSConstantImprovement.ActualCompatibleGramFlux405

#print axioms KLSConstantImprovement.ActualCompatibleGramFlux405.gramRawDifferential_vector
#print axioms KLSConstantImprovement.ActualCompatibleGramFlux405.compatible_gram_metric_flux
