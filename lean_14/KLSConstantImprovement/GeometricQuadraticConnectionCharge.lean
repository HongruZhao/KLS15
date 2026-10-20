import KLSConstantImprovement.SourceThirdAdjointResponse

/-! Same geometric quadratic Poisson rows and their two endpoint
Bochner records. All actual source, graph-domain, datum and cross-term
identifications are explicit inputs. This does not prove the open
response metric excess or a new Poincare endpoint. -/
noncomputable section
namespace KLSConstantImprovement.GeometricQuadraticConnectionCharge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem endpoint_connection_pair (R K : E) {B p j : ℝ}
    (hTarget : B = ‖R‖^2+p)
    (hSource : B = ‖R-K‖^2+j) :
    2*inner ℝ R K = ‖K‖^2+j-p := by
  rw [norm_sub_sq_real] at hSource
  linarith

theorem quadratic_projection_loss (C R : E) {B p : ℝ}
    (hTarget : B = ‖R‖^2+p)
    (hPair : inner ℝ C R = B) :
    ‖C-R‖^2+p = ‖C‖^2-B := by
  rw [norm_sub_sq_real]
  linarith

theorem matched_connection_budget (C R K : E) {B p j Jq : ℝ}
    (hTarget : B = ‖R‖^2+p)
    (hSource : B = ‖R-K‖^2+j)
    (hPair : inner ℝ C R = B)
    (hConnection : inner ℝ C K = 2*B-Jq) :
    2*‖C‖^2-Jq = ‖K‖^2/2+2*‖C-R‖^2+
      3*p/2+j/2+inner ℝ (C-R) K := by
  have hEndpoint := endpoint_connection_pair R K hTarget hSource
  have hLoss := quadratic_projection_loss C R hTarget hPair
  rw [inner_sub_left]
  linarith

theorem signed_connection_square (D K : E) :
    2*‖D‖^2+inner ℝ D K+‖K‖^2/8 =
      (1/2:ℝ)*‖(2:ℝ) • D+(1/2:ℝ) • K‖^2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul,
    real_inner_smul_left, real_inner_smul_right]
  norm_num
  ring

theorem exact_connection_square_budget (C R K : E) {B p j Jq : ℝ}
    (hTarget : B = ‖R‖^2+p)
    (hSource : B = ‖R-K‖^2+j)
    (hPair : inner ℝ C R = B)
    (hConnection : inner ℝ C K = 2*B-Jq) :
    2*‖C‖^2-Jq = 3*‖K‖^2/8+3*p/2+j/2+
      (1/2:ℝ)*‖(2:ℝ) • (C-R)+(1/2:ℝ) • K‖^2 := by
  have hBudget := matched_connection_budget C R K hTarget hSource hPair hConnection
  have hSquare := signed_connection_square (C-R) K
  linarith

theorem retained_geometric_connection_charge (C R K : E) {B p j Jq : ℝ}
    (hTarget : B = ‖R‖^2+p)
    (hSource : B = ‖R-K‖^2+j)
    (hPair : inner ℝ C R = B)
    (hConnection : inner ℝ C K = 2*B-Jq) :
    3*‖K‖^2/8+3*p/2+j/2 ≤ 2*‖C‖^2-Jq := by
  have h := exact_connection_square_budget C R K hTarget hSource hPair hConnection
  have hs := sq_nonneg (‖(2:ℝ) • (C-R)+(1/2:ℝ) • K‖)
  linarith

theorem geometric_connection_eight_thirds {gamma p j k : ℝ}
    (hp : 0 ≤ p) (hj : 0 ≤ j)
    (hBudget : 3*gamma/8+3*p/2+j/2 ≤ k) :
    gamma ≤ (8/3:ℝ)*k := by
  linarith

theorem geometric_connection_four_N {gamma p j k N : ℝ}
    (hp : 0 ≤ p) (hj : 0 ≤ j)
    (hBudget : 3*gamma/8+3*p/2+j/2 ≤ k)
    (hForcing : k ≤ 4*N) :
    gamma ≤ (32/3:ℝ)*N := by
  have h := geometric_connection_eight_thirds hp hj hBudget
  linarith

theorem exponential_geometric_connection_calibration :
    (1:ℝ) = 3*(1/2)/8+(3/2)/2+1/16 ∧
    (2:ℝ) = (1/2)+(3/2) := by
  norm_num

end KLSConstantImprovement.GeometricQuadraticConnectionCharge
#print axioms KLSConstantImprovement.GeometricQuadraticConnectionCharge.endpoint_connection_pair
#print axioms KLSConstantImprovement.GeometricQuadraticConnectionCharge.quadratic_projection_loss
#print axioms KLSConstantImprovement.GeometricQuadraticConnectionCharge.matched_connection_budget
#print axioms KLSConstantImprovement.GeometricQuadraticConnectionCharge.signed_connection_square
#print axioms KLSConstantImprovement.GeometricQuadraticConnectionCharge.exact_connection_square_budget
#print axioms KLSConstantImprovement.GeometricQuadraticConnectionCharge.retained_geometric_connection_charge
#print axioms KLSConstantImprovement.GeometricQuadraticConnectionCharge.geometric_connection_eight_thirds
#print axioms KLSConstantImprovement.GeometricQuadraticConnectionCharge.geometric_connection_four_N
#print axioms KLSConstantImprovement.GeometricQuadraticConnectionCharge.exponential_geometric_connection_calibration
