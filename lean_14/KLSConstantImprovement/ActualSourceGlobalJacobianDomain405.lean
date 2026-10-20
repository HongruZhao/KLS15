import KLSConstantImprovement.ActualSourceRegularizedJacobianCoercivity405
import KLSConstantImprovement.ActualUniformIntegralFatou405
import KLS.WeightedFaithfulCutoff

/-!
Fixed positive metric regularization has a genuine global source L2
Jacobian. Coercive cutoff absorption is followed by positive Fatou;
the global derivative norm is a conclusion rather than a premise of
the subsequent removal of boundary errors.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceGlobalJacobianDomain405
open KLS ActualBoundedCanonicalSource ActualSourceLocalizedGaffney405
open ActualSourceGaffneyAbsorption405 ActualUniformIntegralFatou405
open ActualSourceMetricRegularization405 ActualSourceRegularizedEnergyForm405
open ActualSourceRegularizedFluxH1405 ActualSourceRegularizedFluxCompatibility405
open ActualSourceRegularizedFluxDivergence405 ActualSourceRegularizedJacobianCoercivity405
open ActualCompactWeakSourceVectorSquare
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem source_vector_global_jacobian_domain_of_coercivity (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i, MemLp (u i) 2 (potentialMeasure d.potential))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (u i) (Du i j) j)
    (g : Space n → ℝ) (hg : MemLp g 2 (potentialMeasure d.potential))
    (hadj : rawWeakSourceVectorAdjoint d.potential u Du =ᵐ[potentialMeasure d.potential] g)
    {ell : ℝ} (hell : 0 < ell)
    (hcoercive : ∀ᵐ x ∂potentialMeasure d.potential,
      ell * sourceVectorJacobianSquare Du x ≤ sourceVectorJacobianEnergy Du x) :
    Integrable (sourceVectorJacobianSquare Du) (potentialMeasure d.potential) ∧
      ∀ i j, MemLp (Du i j) 2 (potentialMeasure d.potential) := by
  let ν := potentialMeasure d.potential
  have hac : ν ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  have hDmeas (i j : Fin n) : AEStronglyMeasurable (Du i j) ν :=
    (locallyIntegrable_of_memLp_two_on_compacts (hDu i j)).aestronglyMeasurable.mono_ac hac
  have hSmeas : AEStronglyMeasurable (sourceVectorJacobianSquare Du) ν := by
    unfold sourceVectorJacobianSquare
    apply Finset.aestronglyMeasurable_fun_sum
    intro i _
    apply Finset.aestronglyMeasurable_fun_sum
    intro j _
    exact (hDmeas i j).pow 2
  have hSn (x : Space n) : 0 ≤ sourceVectorJacobianSquare Du x :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (Du i j x)))
  obtain ⟨K, hK, hgrad⟩ := smoothCutoff_gradient_bound (n := n)
  have hcutgrad (r : ℕ) (x : Space n) :
      (∑ j : Fin n, coordinateDerivative (smoothCutoff n r) j x ^ 2) ≤ K ^ 2 := by
    have hs : cutoffScale r ≤ 1 := by
      unfold cutoffScale
      apply inv_le_one_of_one_le₀
      linarith [Nat.cast_nonneg (α := ℝ) r]
    have hb : ‖gradient (smoothCutoff n r) x‖ ≤ K :=
      (hgrad r x).trans (mul_le_of_le_one_left hK hs)
    have he : (∑ j : Fin n, coordinateDerivative (smoothCutoff n r) j x ^ 2) =
        ‖gradient (smoothCutoff n r) x‖ ^ 2 := by
      simp only [EuclideanSpace.real_norm_sq_eq, coordinateDerivative_eq_gradient]
    rw [he]
    nlinarith [norm_nonneg (gradient (smoothCutoff n r) x)]
  have hχsq (r : ℕ) (x : Space n) : smoothCutoff n r x ^ 2 ≤ 1 := by
    obtain ⟨hlo, hhi⟩ := faithfulCutoff_bounds r x
    nlinarith
  have hg2n : 0 ≤ ∫ x, g x ^ 2 ∂ν := integral_nonneg (fun x => sq_nonneg (g x))
  have hu2n : 0 ≤ ∫ x, sourceVectorValueSquare u x ∂ν :=
    integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg (u i x)))
  let C : ℝ := (2 * ell * (∫ x, g x ^ 2 ∂ν) +
    (ell + 2) * K ^ 2 * (∫ x, sourceVectorValueSquare u x ∂ν)) / (ell ^ 2 / 2)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hden : 0 < ell ^ 2 / 2 := by positivity
  have hcut (r : ℕ) : Integrable
      (fun x => smoothCutoff n r x ^ 2 * sourceVectorJacobianSquare Du x) ν :=
    source_vector_cutoff_jacobian_square_integrable d u Du hu hDu
      (smoothCutoff_contDiff r) (smoothCutoff_hasCompactSupport r)
  have hbound (r : ℕ) : (∫ x, ‖smoothCutoff n r x ^ 2 * sourceVectorJacobianSquare Du x‖ ∂ν) ≤ C := by
    have hh := integral_source_vector_cutoff_jacobian_bound d u Du hu hDu hw g hg hadj
      hell hcoercive (smoothCutoff_contDiff r) (smoothCutoff_hasCompactSupport r) (hχsq r) (hcutgrad r)
    have he : (∫ x, ‖smoothCutoff n r x ^ 2 * sourceVectorJacobianSquare Du x‖ ∂ν) =
        ∫ x, smoothCutoff n r x ^ 2 * sourceVectorJacobianSquare Du x ∂ν := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hSn x))
    rw [he]
    apply (le_div_iff₀ hden).mpr
    simpa only [mul_comm] using hh
  have hlim : ∀ᵐ x ∂ν, Tendsto
      (fun r => smoothCutoff n r x ^ 2 * sourceVectorJacobianSquare Du x) atTop
      (𝓝 (sourceVectorJacobianSquare Du x)) := Eventually.of_forall fun x => by
    have ht := (smoothCutoff_tendsto_one x).pow 2
    simpa only [one_pow, one_mul] using ht.mul_const (sourceVectorJacobianSquare Du x)
  obtain ⟨hSi, _⟩ := integrable_and_integral_norm_le_of_tendsto_uniform_bound hSmeas hcut hlim hC hbound
  refine ⟨hSi, ?_⟩
  intro i j
  apply (memLp_two_iff_integrable_sq (hDmeas i j)).mpr
  apply hSi.mono' ((hDmeas i j).pow 2)
  exact Eventually.of_forall fun x => by
    change ‖Du i j x ^ 2‖ ≤ sourceVectorJacobianSquare Du x
    rw [Real.norm_of_nonneg (sq_nonneg (Du i j x))]
    have hrow : Du i j x ^ 2 ≤ ∑ b : Fin n, Du i b x ^ 2 :=
      Finset.single_le_sum (fun b _ => sq_nonneg (Du i b x)) (Finset.mem_univ j)
    have hall : (∑ b : Fin n, Du i b x ^ 2) ≤ sourceVectorJacobianSquare Du x :=
      Finset.single_le_sum
        (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg (Du a b x))) (Finset.mem_univ i)
    exact hrow.trans hall

/-- The regularized inverse itself supplies every weak/coercive input
to the global Jacobian-domain theorem. -/
theorem exists_regularizedWeakFlux_global_jacobian (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0) :
    ∃ D : Fin n → Fin n → Space n → ℝ,
      (∀ i j, MemLp (regularizedFluxDerivative d hn k hε g D i j) 2 (potentialMeasure d.potential)) ∧
      (∀ i j, HasLocalWeakCoordinateDerivative (regularizedWeakFlux d hn k hε g i)
        (regularizedFluxDerivative d hn k hε g D i j) j) ∧
      (∀ᵐ x ∂(volume : Measure (Space n)),
        (regularizedMetricHessian d k ε x * regularizedFluxJacobian d hn k hε g D x).IsSymm) ∧
      rawWeakSourceVectorAdjoint d.potential (regularizedWeakFlux d hn k hε g)
        (regularizedFluxDerivative d hn k hε g D) =ᵐ[potentialMeasure d.potential] (g : Space n → ℝ) := by
  obtain ⟨D, hD, hw, hs, hDu, hDuw⟩ := exists_regularizedWeakFlux_rawH1 d hn k hε g hg
  have hc := regularizedFluxJacobian_compatible_ae d hn k hε g D hs
  have ha := regularizedWeakFlux_adjoint_eq_forcing_ae d hn k hε g hg D hD hw
  have hell : 0 < ε / (4 / d.targetConvexityConstant + ε) := by
    have hκ := d.target_convexity_pos
    positivity
  have hglobal := source_vector_global_jacobian_domain_of_coercivity d
    (regularizedWeakFlux d hn k hε g) (regularizedFluxDerivative d hn k hε g D)
    (regularizedWeakFlux_memLp d hn k hε g) hDu hDuw g (Lp.memLp _) ha hell
    (regularizedFluxJacobian_coercive_ae d hn k hε g D hc)
  exact ⟨D, hglobal.2, hDuw, hc, ha⟩

end KLSConstantImprovement.ActualSourceGlobalJacobianDomain405
#print axioms KLSConstantImprovement.ActualSourceGlobalJacobianDomain405.source_vector_global_jacobian_domain_of_coercivity
#print axioms KLSConstantImprovement.ActualSourceGlobalJacobianDomain405.exists_regularizedWeakFlux_global_jacobian
