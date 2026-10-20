import KLSConstantImprovement.ActualSourceGlobalJacobianDomain405
import KLS.RawTraceEnergyPassage
import KLS.WeakWeightedMean

/-!
Actual radius limits after the global raw Jacobian domain has been paid.
The measure is the original source measure throughout. Both boundary
terms vanish by dominated convergence of genuine L1 products.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceGaffneyBoundary405
open KLS ActualBoundedCanonicalSource ActualSourceLocalizedGaffney405
open ActualSourceGaffneyAbsorption405 ActualSourceGlobalJacobianDomain405
open ActualCompactWeakSourceVectorSquare
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem integral_cutoff_mul_derivative_tendsto_zero {ν : Measure (Space n)}
    {f : Space n → ℝ} (hf : Integrable f ν) (i : Fin n) :
    (∀ r, Integrable (fun x => smoothCutoff n r x * f x *
      coordinateDerivative (smoothCutoff n r) i x) ν) ∧
      Tendsto (fun r => ∫ x, smoothCutoff n r x * f x *
        coordinateDerivative (smoothCutoff n r) i x ∂ν) atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ := smoothCutoff_gradient_bound (n := n)
  have hχnorm (r : ℕ) (x : Space n) : ‖smoothCutoff n r x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (faithfulCutoff_bounds r x).1]
    exact (faithfulCutoff_bounds r x).2
  have hDnorm (r : ℕ) (x : Space n) : ‖coordinateDerivative (smoothCutoff n r) i x‖ ≤ K := by
    have hs : cutoffScale r ≤ 1 := by
      unfold cutoffScale
      apply inv_le_one_of_one_le₀
      linarith [Nat.cast_nonneg (α := ℝ) r]
    exact ((norm_coordinateDerivative_le _ i x).trans (hbound r x)).trans
      (mul_le_of_le_one_left hK hs)
  have hm (r : ℕ) : AEStronglyMeasurable (fun x => smoothCutoff n r x * f x *
      coordinateDerivative (smoothCutoff n r) i x) ν :=
    ((smoothCutoff_contDiff r).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable).mul
      (measurable_coordinateDerivative (smoothCutoff n r) i).aestronglyMeasurable
  have hdom (r : ℕ) (x : Space n) : ‖smoothCutoff n r x * f x *
      coordinateDerivative (smoothCutoff n r) i x‖ ≤ ‖f x‖ * K := by
    have hh := mul_le_mul (hχnorm r x) (hDnorm r x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    calc
      _ = ‖f x‖ * (‖smoothCutoff n r x‖ * ‖coordinateDerivative (smoothCutoff n r) i x‖) := by
        simp only [norm_mul]
        ring
      _ ≤ ‖f x‖ * K := mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hh) (norm_nonneg _)
  have hi (r : ℕ) : Integrable (fun x => smoothCutoff n r x * f x *
      coordinateDerivative (smoothCutoff n r) i x) ν :=
    (hf.norm.mul_const K).mono' (hm r) (Eventually.of_forall (hdom r))
  refine ⟨hi, ?_⟩
  have ht := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖ * K) hm
    (hf.norm.mul_const K) (fun r => Eventually.of_forall (hdom r))
    (Eventually.of_forall fun x => by
      simpa only [one_mul, mul_zero] using
        ((smoothCutoff_tendsto_one x).mul_const (f x)).mul
          (smoothCutoff_coordinateDerivative_tendsto_zero i x))
  simpa only [integral_zero] using ht

theorem integral_source_vector_boundary_terms_tendsto_zero (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i, MemLp (u i) 2 (potentialMeasure d.potential))
    (hDu : ∀ i j, MemLp (Du i j) 2 (potentialMeasure d.potential))
    (g : Space n → ℝ) (hg : MemLp g 2 (potentialMeasure d.potential)) :
    Tendsto (fun r => ∫ x, smoothCutoff n r x * g x *
      sourceVectorCutoffDot (smoothCutoff n r) u x ∂potentialMeasure d.potential) atTop (𝓝 0) ∧
      Tendsto (fun r => ∫ x, smoothCutoff n r x *
        sourceVectorCutoffCross (smoothCutoff n r) u Du x ∂potentialMeasure d.potential) atTop (𝓝 0) := by
  let ν := potentialMeasure d.potential
  have hfp (i : Fin n) : Integrable (fun x => g x * u i x) ν := hg.integrable_mul (hu i)
  have hcp (i j : Fin n) : Integrable (fun x => u i x * Du j i x) ν := (hu i).integrable_mul (hDu j i)
  have hforce (i : Fin n) := integral_cutoff_mul_derivative_tendsto_zero (hfp i) i
  have hcross (i j : Fin n) := integral_cutoff_mul_derivative_tendsto_zero (hcp i j) j
  have hflim := tendsto_finsetSum Finset.univ (fun i _ => (hforce i).2)
  have hclim := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ => (hcross i j).2))
  have hfeq (r : ℕ) : (∫ x, smoothCutoff n r x * g x * sourceVectorCutoffDot (smoothCutoff n r) u x ∂ν) =
      ∑ i : Fin n, ∫ x, smoothCutoff n r x * (g x * u i x) *
        coordinateDerivative (smoothCutoff n r) i x ∂ν := by
    calc
      _ = ∫ x, ∑ i : Fin n, smoothCutoff n r x * (g x * u i x) *
          coordinateDerivative (smoothCutoff n r) i x ∂ν := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          simp only [sourceVectorCutoffDot, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := integral_finsetSum Finset.univ (fun i _ => (hforce i).1 r)
  have hceq (r : ℕ) : (∫ x, smoothCutoff n r x * sourceVectorCutoffCross (smoothCutoff n r) u Du x ∂ν) =
      ∑ i : Fin n, ∑ j : Fin n, ∫ x, smoothCutoff n r x * (u i x * Du j i x) *
        coordinateDerivative (smoothCutoff n r) j x ∂ν := by
    calc
      _ = ∫ x, ∑ i : Fin n, ∑ j : Fin n, smoothCutoff n r x * (u i x * Du j i x) *
          coordinateDerivative (smoothCutoff n r) j x ∂ν := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          simp only [sourceVectorCutoffCross, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by
        rw [integral_finsetSum Finset.univ (fun i _ =>
          integrable_finsetSum Finset.univ (fun j _ => (hcross i j).1 r))]
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum Finset.univ (fun j _ => (hcross i j).1 r)
  constructor
  · simpa only [Finset.sum_const_zero] using hflim.congr (fun r => (hfeq r).symm)
  · simpa only [Finset.sum_const_zero] using hclim.congr (fun r => (hceq r).symm)

theorem integral_source_vector_global_gaffney (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i, MemLp (u i) 2 (potentialMeasure d.potential))
    (hDu : ∀ i j, MemLp (Du i j) 2 (potentialMeasure d.potential))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (u i) (Du i j) j)
    (g : Space n → ℝ) (hg : MemLp g 2 (potentialMeasure d.potential))
    (hadj : rawWeakSourceVectorAdjoint d.potential u Du =ᵐ[potentialMeasure d.potential] g) :
    (∫ x, sourceVectorMass d.potential u x + sourceVectorJacobianEnergy Du x
      ∂potentialMeasure d.potential) = ∫ x, g x ^ 2 ∂potentialMeasure d.potential := by
  let ν := potentialMeasure d.potential
  have hDloc (i j : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (Du i j) 2 (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure (hDu i j) d.source_C1.continuous hE
  have hM := source_vector_mass_integrable d u hu
  have hQ : Integrable (sourceVectorJacobianEnergy Du) ν :=
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => (hDu i j).integrable_mul (hDu j i)))
  have hE := hM.add hQ
  have hg2 : Integrable (fun x => g x ^ 2) ν := by
    have hm := hg.integrable_mul hg
    change Integrable (fun x => g x * g x) ν at hm
    simpa only [pow_two] using hm
  have hχm (r : ℕ) : AEStronglyMeasurable (fun x => smoothCutoff n r x ^ 2) ν :=
    ((smoothCutoff_contDiff r).continuous.pow 2).aestronglyMeasurable
  have hχnorm (r : ℕ) : ∀ᵐ x ∂ν, ‖smoothCutoff n r x ^ 2‖ ≤ 1 := Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    obtain ⟨hlo, hhi⟩ := faithfulCutoff_bounds r x
    nlinarith
  have hχlim : ∀ᵐ x ∂ν, Tendsto (fun r => smoothCutoff n r x ^ 2) atTop (𝓝 1) :=
    Eventually.of_forall fun x => by simpa only [one_pow] using (smoothCutoff_tendsto_one x).pow 2
  have hElim := (integral_mul_tendsto_of_ae_bounded_cutoffs hE hχm hχnorm hχlim).2
  have hglim := (integral_mul_tendsto_of_ae_bounded_cutoffs hg2 hχm hχnorm hχlim).2
  obtain ⟨hflim, hclim⟩ := integral_source_vector_boundary_terms_tendsto_zero d u Du hu hDu g hg
  have hr := (hglim.sub (hflim.const_mul 2)).sub (hclim.const_mul 2)
  have heq (r : ℕ) := integral_source_vector_localized_gaffney d u Du hu hDloc hw g hg hadj
    (smoothCutoff_contDiff r) (smoothCutoff_hasCompactSupport r)
  have hrlim : Tendsto (fun r => ∫ x, smoothCutoff n r x ^ 2 *
      (sourceVectorMass d.potential u x + sourceVectorJacobianEnergy Du x) ∂ν) atTop
      (𝓝 (∫ x, g x ^ 2 ∂ν)) := by
    simpa only [mul_zero, sub_zero] using hr.congr (fun r => (heq r).symm)
  exact tendsto_nhds_unique hElim hrlim

end KLSConstantImprovement.ActualSourceGaffneyBoundary405
#print axioms KLSConstantImprovement.ActualSourceGaffneyBoundary405.integral_cutoff_mul_derivative_tendsto_zero
#print axioms KLSConstantImprovement.ActualSourceGaffneyBoundary405.integral_source_vector_boundary_terms_tendsto_zero
#print axioms KLSConstantImprovement.ActualSourceGaffneyBoundary405.integral_source_vector_global_gaffney
