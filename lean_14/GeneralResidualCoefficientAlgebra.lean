import PairNoiseSquareCompletion

/-! Exact scalar normalization of the general pair-projection noise.
The covariance generator adds the released drift term -d times the energy. -/
noncomputable section
namespace KLS.DeterministicBridgeIntegration
open KLSBelow25.PairProjection

def generalResidualA (β : ℝ) (d : ℕ) : ℝ :=
  4/(1-β)-2-4*β/(3*((d : ℝ)-1)*(1-β))
def generalResidualGeneratorLoss (β : ℝ) (d : ℕ) : ℝ :=
  generalResidualA β d*(d : ℝ)^2+(generalResidualA β d-3)*(d : ℝ)

theorem generalResidualGeneratorLoss_eq (d : ℕ) (hd : 3≤d) {β : ℝ} (hβ : β<1) :
    generalResidualGeneratorLoss β d=
      leadingNoiseCoefficient (d : ℝ)/(1-β)-positiveNoiseCoefficient (d : ℝ)+(d : ℝ) := by
  have hdr : (3 : ℝ)≤d := by exact_mod_cast hd
  have hdm : (d : ℝ)-1≠0 := by linarith
  have hb : 1-β≠0 := by linarith
  unfold generalResidualGeneratorLoss generalResidualA leadingNoiseCoefficient positiveNoiseCoefficient
  field_simp
  ring

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.generalResidualGeneratorLoss_eq
