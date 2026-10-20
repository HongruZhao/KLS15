import KLSConstantImprovement.ActualSourceLimitFluxPairing405
import KLSConstantImprovement.ActualSourceRegularizedRootMultipliers405
import KLSConstantImprovement.ActualWhitenedJacobianSymmetry405

/-! Literal ordered Jacobian reconstruction and compact pairings of
the regularized and actual root-sandwich fields. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceJacobianCompactPairing405
open KLS ActualBoundedCanonicalSource ActualSourceRegularizedEnergyVector405
open ActualSourceRegularizedFluxH1405 ActualSourceRegularizedFluxCompatibility405
open ActualSourceRegularizedEnergyForm405 ActualSourceMetricRegularization405
open ActualSourceRegularizedRootPassage405 ActualSourceRegularizedRootMultipliers405
open ActualWhitenedJacobianEnergy405 ActualWhitenedJacobianSymmetry405
open ActualSourceLimitFluxDomains405 ActualSourceLimitFluxPairing405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem root_sandwich_entry (R Z S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (R * Z * S) i j = ∑ a : Fin n, ∑ b : Fin n, (R i a * S b j) * Z a b := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_congr rfl fun b _ => by ring

theorem regularizedFluxDerivative_eq_energy_sandwich_ae (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (D : Fin n → Fin n → Space n → ℝ)
    (W : GaffneyEnergyAmbient d)
    (hW : ∀ a, (W a : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      regularizedGaffneyEnergyField d hn k (cutoffScale_pos k) g D a) (i j : Fin n) :
    regularizedFluxDerivative d hn k (cutoffScale_pos k) g D i j =ᵐ[potentialMeasure d.potential]
      fun x => ∑ a : Fin n, ∑ b : Fin n,
        (regularizedMetricRoot d k (cutoffScale k) x i a * regularizedMetricUnroot d k (cutoffScale k) x b j) *
          W (Sum.inr (a, b)) x := by
  filter_upwards [ae_all_iff.mpr hW] with x hx
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j)
    (whitenedJacobian_reconstruct (regularizedMetricHessian d k (cutoffScale k) x)
      (regularizedFluxJacobian d hn k (cutoffScale_pos k) g D x)
      (regularizedMetricHessian_posDef d k (cutoffScale_pos k) x))
  rw [root_sandwich_entry] at he
  calc
    _ = ∑ a : Fin n, ∑ b : Fin n,
        (regularizedMetricRoot d k (cutoffScale k) x i a * regularizedMetricUnroot d k (cutoffScale k) x b j) *
          whitenedJacobian (regularizedMetricHessian d k (cutoffScale k) x)
            (regularizedFluxJacobian d hn k (cutoffScale_pos k) g D x) a b := he.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [hx (Sum.inr (a, b))]
      rfl

theorem regularized_jacobian_compact_pair_eq_inner_sum (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (D : Fin n → Fin n → Space n → ℝ)
    (W : GaffneyEnergyAmbient d)
    (hW : ∀ a, (W a : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      regularizedGaffneyEnergyField d hn k (cutoffScale_pos k) g D a)
    {ψ : Space n → ℝ} (hc : HasCompactSupport ψ) (i j : Fin n)
    (hQ : ∀ a b, MemLp (fun x => compactRegularizedRootProduct d (tsupport ψ) i a b j k x * ψ x)
      2 (potentialMeasure d.potential)) :
    (∫ x, regularizedFluxDerivative d hn k (cutoffScale_pos k) g D i j x * ψ x ∂potentialMeasure d.potential) =
      ∑ a : Fin n, ∑ b : Fin n, inner ℝ (W (Sum.inr (a, b)))
        ((hQ a b).toLp (fun x => compactRegularizedRootProduct d (tsupport ψ) i a b j k x * ψ x)) := by
  have hi (a b : Fin n) : Integrable (fun x => W (Sum.inr (a, b)) x *
      (compactRegularizedRootProduct d (tsupport ψ) i a b j k x * ψ x)) (potentialMeasure d.potential) :=
    (Lp.memLp _).integrable_mul (hQ a b)
  calc
    _ = ∫ x, ∑ a : Fin n, ∑ b : Fin n, W (Sum.inr (a, b)) x *
        (compactRegularizedRootProduct d (tsupport ψ) i a b j k x * ψ x) ∂potentialMeasure d.potential := by
      apply integral_congr_ae
      filter_upwards [regularizedFluxDerivative_eq_energy_sandwich_ae d hn k g D W hW i j] with x hx
      rw [hx]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hxψ : x ∈ tsupport ψ
      · rw [compactRegularizedRootProduct, indicator_of_mem hxψ]
        ring
      · simp only [image_eq_zero_of_notMem_tsupport hxψ, mul_zero]
    _ = ∑ a : Fin n, ∑ b : Fin n, ∫ x, W (Sum.inr (a, b)) x *
        (compactRegularizedRootProduct d (tsupport ψ) i a b j k x * ψ x) ∂potentialMeasure d.potential := by
      rw [integral_finsetSum Finset.univ (fun a _ => integrable_finsetSum Finset.univ (fun b _ => hi a b))]
      exact Finset.sum_congr rfl fun a _ => integral_finsetSum Finset.univ (fun b _ => hi a b)
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => integral_lp_mul_eq_inner_toLp _ _

theorem limit_jacobian_compact_pair_eq_inner_sum (d : SourceData μ) (V : GaffneyEnergyAmbient d)
    {ψ : Space n → ℝ} (hc : HasCompactSupport ψ) (i j : Fin n)
    (hQ : ∀ a b, MemLp (fun x => compactActualRootProduct d (tsupport ψ) i a b j x * ψ x)
      2 (potentialMeasure d.potential)) :
    (∫ x, energyLimitJacobian d V i j x * ψ x ∂potentialMeasure d.potential) =
      ∑ a : Fin n, ∑ b : Fin n, inner ℝ (V (Sum.inr (a, b)))
        ((hQ a b).toLp (fun x => compactActualRootProduct d (tsupport ψ) i a b j x * ψ x)) := by
  have hi (a b : Fin n) : Integrable (fun x => V (Sum.inr (a, b)) x *
      (compactActualRootProduct d (tsupport ψ) i a b j x * ψ x)) (potentialMeasure d.potential) :=
    (Lp.memLp _).integrable_mul (hQ a b)
  calc
    _ = ∫ x, ∑ a : Fin n, ∑ b : Fin n, V (Sum.inr (a, b)) x *
        (compactActualRootProduct d (tsupport ψ) i a b j x * ψ x) ∂potentialMeasure d.potential := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [energyLimitJacobian, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        by_cases hxψ : x ∈ tsupport ψ
        · rw [compactActualRootProduct, indicator_of_mem hxψ]
          ring
        · simp only [image_eq_zero_of_notMem_tsupport hxψ, mul_zero]
    _ = ∑ a : Fin n, ∑ b : Fin n, ∫ x, V (Sum.inr (a, b)) x *
        (compactActualRootProduct d (tsupport ψ) i a b j x * ψ x) ∂potentialMeasure d.potential := by
      rw [integral_finsetSum Finset.univ (fun a _ => integrable_finsetSum Finset.univ (fun b _ => hi a b))]
      exact Finset.sum_congr rfl fun a _ => integral_finsetSum Finset.univ (fun b _ => hi a b)
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => integral_lp_mul_eq_inner_toLp _ _

end KLSConstantImprovement.ActualSourceJacobianCompactPairing405
#print axioms KLSConstantImprovement.ActualSourceJacobianCompactPairing405.root_sandwich_entry
#print axioms KLSConstantImprovement.ActualSourceJacobianCompactPairing405.regularizedFluxDerivative_eq_energy_sandwich_ae
#print axioms KLSConstantImprovement.ActualSourceJacobianCompactPairing405.regularized_jacobian_compact_pair_eq_inner_sum
#print axioms KLSConstantImprovement.ActualSourceJacobianCompactPairing405.limit_jacobian_compact_pair_eq_inner_sum
