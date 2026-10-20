import KLSConstantImprovement.ActualSourceRegularizedEnergyForm405
import KLS.WeightedEnergyGraphClosability
import KLS.WeakMomentLocalEssentialBounds
import EllipticPdes.Regularity.Local.WeakSolution

/-!
The constructed regularized inverse satisfies the literal local volume
weak equation with principal coefficient exp(-phi) J[k,epsilon]. The
source is only C1,1; its density is C1 and the matrix inverse is smooth.
All local L2 value, gradient and forcing domains are proved below.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceRegularizedLocalEquation405
open KLS ActualBoundedCanonicalSource ActualSourceMetricRegularization405
open ActualSourceInverseMetricRegularization405 ActualSourceRegularizedEnergyForm405
open EllipticPdes.Sobolev EllipticPdes.Embedding EllipticPdes.Regularity
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem regularizedOrdinaryInverse_compact_test (d : SourceData μ) (hn : 1 ≤ n)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∑ j : Fin n, ∫ x, regularizedMetricInverse d k ε x i j *
      weightedH1Derivative d.potential i (regularizedOrdinaryInverse d hn k hε g) x *
        coordinateDerivative ψ j x ∂potentialMeasure d.potential) =
      ∫ x, g x * (ψ x - ∫ y, ψ y ∂potentialMeasure d.potential)
        ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨V, hV, hDV⟩ := exists_weightedH1_of_smoothCompact d.source_C1.continuous hψ hc
  have he := regularizedOrdinaryInverse_variational d hn k hε g V
  rw [regularizedOrdinaryEnergyForm_eq_sum_integral] at he
  have hl : (∑ i : Fin n, ∑ j : Fin n, ∫ x, regularizedMetricInverse d k ε x i j *
      weightedH1Derivative d.potential i (regularizedOrdinaryInverse d hn k hε g) x *
        weightedH1Derivative d.potential j V x ∂potentialMeasure d.potential) =
      ∑ i : Fin n, ∑ j : Fin n, ∫ x, regularizedMetricInverse d k ε x i j *
        weightedH1Derivative d.potential i (regularizedOrdinaryInverse d hn k hε g) x *
          coordinateDerivative ψ j x ∂potentialMeasure d.potential := by
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      integral_congr_ae (EventuallyEq.rfl.fun_mul (hDV j))
  have hr : inner ℝ g (weightedH1Value d.potential V) =
      ∫ x, g x * (ψ x - ∫ y, ψ y ∂potentialMeasure d.potential)
        ∂potentialMeasure d.potential := by
    rw [L2.real_inner_eq_integral]
    exact integral_congr_ae (EventuallyEq.rfl.fun_mul hV)
  rwa [hl, hr] at he

theorem regularizedOrdinaryInverse_compact_test_mean_zero (d : SourceData μ) (hn : 1 ≤ n)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∑ j : Fin n, ∫ x, regularizedMetricInverse d k ε x i j *
      weightedH1Derivative d.potential i (regularizedOrdinaryInverse d hn k hε g) x *
        coordinateDerivative ψ j x ∂potentialMeasure d.potential) =
      ∫ x, g x * ψ x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  rw [regularizedOrdinaryInverse_compact_test d hn k hε g hψ hc]
  have hψ2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hψ.continuous hc
  have hi : Integrable (fun x => g x * ψ x) (potentialMeasure d.potential) :=
    (Lp.memLp g).integrable_mul hψ2
  have hC := ((Lp.memLp g).integrable (by norm_num)).mul_const (∫ y, ψ y ∂potentialMeasure d.potential)
  calc
    _ = ∫ x, (g x * ψ x - g x * ∫ y, ψ y ∂potentialMeasure d.potential)
        ∂potentialMeasure d.potential := by
      apply integral_congr_ae
      exact Eventually.of_forall fun _ => by ring
    _ = _ := by rw [integral_sub hi hC, integral_mul_const, hg, zero_mul, sub_zero]

def regularizedDensityCoefficient (d : SourceData μ) (k : ℕ) (ε : ℝ) (x : Space n)
    (i j : Fin n) : ℝ := Real.exp (-d.potential x) * regularizedMetricInverse d k ε x i j

theorem regularizedDensityCoefficient_contDiff (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (i j : Fin n) :
    ContDiff ℝ 1 (fun x => regularizedDensityCoefficient d k ε x i j) :=
  d.source_C1.neg.exp.mul
    ((contDiff_pi.mp (contDiff_pi.mp (regularizedMetricInverse_contDiff d k hε) i) j).of_le (by simp))

theorem regularizedDensityForcing_local_L2 (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {E : Set (Space n)} (hE : IsCompact E) :
    MemLp (fun x => Real.exp (-d.potential x) * g x) 2 (volume.restrict E) := by
  have hg := KLS.MemLp.restrict_volume_of_potentialMeasure (Lp.memLp g) d.source_C1.continuous hE
  have hρ := memLp_continuous_top_on_compact (Real.continuous_exp.comp d.source_C1.continuous.neg) hE
  exact hρ.mul hg

/-- The ordinary graph coordinates are genuine local volume weak derivatives. -/
theorem regularizedOrdinaryInverse_hasWeakGradOn (d : SourceData μ) (hn : 1 ≤ n)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    HasWeakGradOn univ
      (weightedH1Value d.potential (regularizedOrdinaryInverse d hn k hε g))
      (fun i => weightedH1Derivative d.potential i (regularizedOrdinaryInverse d hn k hε g)) := by
  intro ψ hψ hc _ i
  simpa only [Measure.restrict_univ, partialD, coordinateDerivative] using
    weightedH1_unweighted_weak_identity d.source_C1
      (regularizedOrdinaryInverse d hn k hε g) (hψ.of_le (by simp)) hc i

/-- The coefficient is the original density times the actual regularized
inverse; no change of the probability law or classical solution is used. -/
theorem regularizedOrdinaryInverse_localWeakSol (d : SourceData μ) (hn : 1 ≤ n)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0) :
    LocalWeakSol univ (regularizedDensityCoefficient d k ε)
      (fun _ _ => 0) (fun _ => 0) (fun x => Real.exp (-d.potential x) * g x)
      (weightedH1Value d.potential (regularizedOrdinaryInverse d hn k hε g))
      (fun i => weightedH1Derivative d.potential i (regularizedOrdinaryInverse d hn k hε g)) := by
  intro ψ hψ hc _
  have ht := regularizedOrdinaryInverse_compact_test_mean_zero d hn k hε g hg
    (hψ.of_le (by simp)) hc
  simp_rw [integral_potentialMeasure d.source_C1.continuous.measurable] at ht
  simp only [Measure.restrict_univ, zero_mul, integral_zero, Finset.sum_const_zero, add_zero]
  have hl (i j : Fin n) : (∫ x, regularizedDensityCoefficient d k ε x i j *
      weightedH1Derivative d.potential i (regularizedOrdinaryInverse d hn k hε g) x * partialD j ψ x) =
      ∫ x, (regularizedMetricInverse d k ε x i j *
        weightedH1Derivative d.potential i (regularizedOrdinaryInverse d hn k hε g) x *
          coordinateDerivative ψ j x) * Real.exp (-d.potential x) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only [regularizedDensityCoefficient, partialD, coordinateDerivative]
      ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hl i j]
  convert ht using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

end KLSConstantImprovement.ActualSourceRegularizedLocalEquation405
#print axioms KLSConstantImprovement.ActualSourceRegularizedLocalEquation405.regularizedOrdinaryInverse_compact_test
#print axioms KLSConstantImprovement.ActualSourceRegularizedLocalEquation405.regularizedOrdinaryInverse_compact_test_mean_zero
#print axioms KLSConstantImprovement.ActualSourceRegularizedLocalEquation405.regularizedDensityCoefficient_contDiff
#print axioms KLSConstantImprovement.ActualSourceRegularizedLocalEquation405.regularizedDensityForcing_local_L2
#print axioms KLSConstantImprovement.ActualSourceRegularizedLocalEquation405.regularizedOrdinaryInverse_hasWeakGradOn
#print axioms KLSConstantImprovement.ActualSourceRegularizedLocalEquation405.regularizedOrdinaryInverse_localWeakSol
