import WeightedHodgeKernelEstimate
import KLS.WeightedWeakLiouville
import KLS.WeightedBochnerDomain

/-! No weighted-L² harmonic one-forms under positive curvature. The proof
uses actual mollified compact fields and expanding cutoffs, without assuming
the input belongs to a compact-core closure or has any weak derivative. -/
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ}

lemma finite_lagrange_identity (a b : Fin n → ℝ) :
    (∑ i, a i * b i) ^ 2 + (1 / 2 : ℝ) *
      (∑ i, ∑ j, (a i * b j - a j * b i) ^ 2) =
      (∑ i, (a i) ^ 2) * (∑ i, (b i) ^ 2) := by
  have h1 : (∑ i, ∑ j, (a i * b j) ^ 2) =
      (∑ i, (a i) ^ 2) * (∑ i, (b i) ^ 2) := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum, mul_pow]
  have h2 : (∑ i, ∑ j, (a j * b i) ^ 2) =
      (∑ i, (a i) ^ 2) * (∑ i, (b i) ^ 2) := by
    rw [Finset.sum_comm]
    exact h1
  have h3 : (∑ i, ∑ j, a i * b j * (a j * b i)) = (∑ i, a i * b i) ^ 2 := by
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [sub_sq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hcross : (∑ i, ∑ j, 2 * (a i * b j) * (a j * b i)) =
      2 * (∑ i, ∑ j, a i * b j * (a j * b i)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h1, h2, hcross, h3]
  ring

/-- The true distributional weighted Hodge kernel is zero. No regularity or
core-density assumption on the actual weighted-L² field is a premise. -/
theorem weightedHodge_kernel_eq_zero {φ : Space n → ℝ}
    {F : Fin n → Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hF : ∀ i, MemLp (F i) 2 (potentialMeasure φ))
    (hcurl : DistributionallyCurlFree F) (hdiv : WeakWeightedDivergenceFree φ F) :
    ∀ i, F i =ᵐ[potentialMeasure φ] fun _ => 0 := by
  have hFlocal (i : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (F i) 2 (volume.restrict K) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure (hF i) hφ.continuous hK
  obtain ⟨K, hK, hbound⟩ := smoothCutoff_gradient_bound (n := n)
  let E : ℝ := ∑ i, ∫ x, (F i x) ^ 2 ∂potentialMeasure φ
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hestimate (k : ℕ) :
      κ * (∑ i, ∫ x, (smoothCutoff n k x * F i x) ^ 2 ∂potentialMeasure φ) ≤
        (cutoffScale k * K) ^ 2 * E := by
    let χ := smoothCutoff n k
    have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := smoothCutoff_contDiff_top k
    have hc : HasCompactSupport χ := smoothCutoff_hasCompactSupport k
    have hdχ (i : Fin n) : Continuous (coordinateDerivative χ i) :=
      (contDiff_coordinateDerivative hχ (m := 0) (by simp) i).continuous
    have hP (i j : Fin n) : MemLp (fun x => coordinateDerivative χ i x * F j x)
        2 (potentialMeasure φ) := memLp_compact_mul_local_potential hφ.continuous
      (hdχ i) (hasCompactSupport_coordinateDerivative hc i) (hFlocal j)
    have hD : Integrable (fun x => (∑ i, coordinateDerivative χ i x * F i x) ^ 2)
        (potentialMeasure φ) :=
      (memLp_finsetSum Finset.univ (fun i _ => hP i i)).integrable_sq
    have hB (i j : Fin n) : Integrable (fun x =>
        (coordinateDerivative χ i x * F j x - coordinateDerivative χ j x * F i x) ^ 2)
        (potentialMeasure φ) := ((hP i j).sub (hP j i)).integrable_sq
    have hBI := integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hB i j))
    have hBsum : (∑ i, ∑ j, ∫ x,
        (coordinateDerivative χ i x * F j x - coordinateDerivative χ j x * F i x) ^ 2
          ∂potentialMeasure φ) =
        ∫ x, ∑ i, ∑ j,
          (coordinateDerivative χ i x * F j x - coordinateDerivative χ j x * F i x) ^ 2
            ∂potentialMeasure φ := by
      rw [integral_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun j _ => hB i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hB i j)]
    have hsum : (∫ x, (∑ i, coordinateDerivative χ i x * F i x) ^ 2
        ∂potentialMeasure φ) +
        (1 / 2 : ℝ) * (∑ i, ∑ j, ∫ x,
          (coordinateDerivative χ i x * F j x - coordinateDerivative χ j x * F i x) ^ 2
            ∂potentialMeasure φ) =
        ∫ x, (∑ i, (coordinateDerivative χ i x) ^ 2) * (∑ i, (F i x) ^ 2)
          ∂potentialMeasure φ := by
      rw [hBsum, ← integral_const_mul]
      have hs := integral_add hD (hBI.const_mul (1 / 2 : ℝ))
      rw [← hs]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => finite_lagrange_identity
        (fun i => coordinateDerivative χ i x) (fun i => F i x)
    have hgrad (x : Space n) : (∑ i, (coordinateDerivative χ i x) ^ 2) ≤
        (cutoffScale k * K) ^ 2 := by
      have he : (∑ i, (coordinateDerivative χ i x) ^ 2) = ‖gradient χ x‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp only [coordinateDerivative_eq_gradient]
      rw [he]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound k x) 2
    have hrightI : Integrable (fun x => (cutoffScale k * K) ^ 2 *
        (∑ i, (F i x) ^ 2)) (potentialMeasure φ) :=
      (integrable_finsetSum Finset.univ (fun i _ => (hF i).integrable_sq)).const_mul _
    have hleftI : Integrable (fun x => (∑ i, (coordinateDerivative χ i x) ^ 2) *
        (∑ i, (F i x) ^ 2)) (potentialMeasure φ) := by
      have hh := hD.add (hBI.const_mul (1 / 2 : ℝ))
      convert hh using 1
      funext x
      exact (finite_lagrange_identity
        (fun i => coordinateDerivative χ i x) (fun i => F i x)).symm
    have hupper := integral_mono hleftI hrightI (fun x =>
      mul_le_mul_of_nonneg_right (hgrad x) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    rw [integral_const_mul, integral_finsetSum Finset.univ
      (fun i _ => (hF i).integrable_sq)] at hupper
    have he := weightedHodge_kernel_cutoff_estimate hφ hlower hFlocal hcurl hdiv hχ hc
    rw [hsum] at he
    exact he.trans hupper
  have hlimleft : Tendsto (fun k =>
      κ * (∑ i, ∫ x, (smoothCutoff n k x * F i x) ^ 2 ∂potentialMeasure φ))
      atTop (𝓝 (κ * E)) := by
    apply Tendsto.const_mul κ
    apply tendsto_finsetSum Finset.univ
    intro i _
    have ht := integral_smoothCutoff_sq_tendsto (hF i).integrable_sq (fun x => sq_nonneg (F i x))
    simpa only [mul_pow] using ht
  have hlimright : Tendsto (fun k => (cutoffScale k * K) ^ 2 * E) atTop (𝓝 0) := by
    simpa using ((cutoffScale_tendsto_zero.mul_const K).pow 2).mul_const E
  have hzero : κ * E ≤ 0 := le_of_tendsto_of_tendsto hlimleft hlimright
    (Eventually.of_forall hestimate)
  have hEz : E = 0 := by nlinarith
  intro i
  have hi : (∫ x, (F i x) ^ 2 ∂potentialMeasure φ) = 0 := by
    have hs : (∫ x, (F i x) ^ 2 ∂potentialMeasure φ) ≤ E :=
      Finset.single_le_sum (f := fun j => ∫ x, (F j x) ^ 2 ∂potentialMeasure φ)
        (fun _ _ => integral_nonneg fun _ => sq_nonneg _) (Finset.mem_univ i)
    exact le_antisymm (by simpa only [hEz] using hs) (integral_nonneg fun _ => sq_nonneg _)
  have hnorm : (hF i).toLp (F i) = 0 := by
    have hn := integral_sq_eq_norm_toLp_sq (hF i)
    rw [hi] at hn
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg ((hF i).toLp (F i))])
  have hae := (hF i).coeFn_toLp
  rw [hnorm] at hae
  filter_upwards [hae, Lp.coeFn_zero ℝ 2 (potentialMeasure φ)] with x hx hz
  exact hx.symm.trans hz

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.finite_lagrange_identity
#print axioms KLS.DeterministicBridgeIntegration.weightedHodge_kernel_eq_zero
