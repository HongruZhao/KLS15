import KLSConstantImprovement.ActualSourceInverseTensor405
import KLS.WeightedCompactL2Maps

/-!
The actual inverse-Hessian gradient of a compact smooth source scalar has
compact raw H1 coordinates. Its weak derivatives are the literal ordered
inverse-tensor product formula. Every local and weighted L2 domain is proved;
the source is only C1,1 and no derivative of a chosen Poisson optimizer is
assumed. This supplies the actual input for compact canonical Bochner.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Matrix InnerProductSpace
open EllipticPdes.Regularity
open scoped BigOperators ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceInverseGradientDomain405
open KLS ActualBoundedCanonicalSource ActualSourceInverseTensor405
variable {n : ℕ} {μ : Measure (Space n)}

private theorem compact_localL2_to_source (d : SourceData μ)
    {f : Space n → ℝ} (hc : HasCompactSupport f)
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E)) :
    MemLp f 2 (potentialMeasure d.potential) := by
  have hv := memLp_compact_of_localL2 hf hc
  obtain ⟨χ, hχ, hχ1, _⟩ := exists_isTestFn_one_nhdsSet_of_isCompact hc isOpen_univ
    (subset_univ (tsupport f))
  have hm := memLp_compact_mul_volume_to_weighted d.source_C1.continuous hχ.1.continuous hχ.2.1
    (hv.toLp f)
  have he : (fun x => χ x * (hv.toLp f) x) =ᵐ[potentialMeasure d.potential] f := by
    have hac : potentialMeasure d.potential ≪ volume := withDensity_absolutelyContinuous _ _
    filter_upwards [hac.ae_eq hv.coeFn_toLp] with x hx
    rw [hx]
    by_cases hxf : x ∈ tsupport f
    · rw [hχ1.self_of_nhdsSet x hxf, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hxf, mul_zero]
  exact (memLp_congr_ae he).mp hm

def actualInverseGradient (d : SourceData μ) (ψ : Space n → ℝ) (i : Fin n) (x : Space n) : ℝ :=
  ∑ a, (coordinateHessian d.potential x)⁻¹ i a * coordinateDerivative ψ a x

/-- Da i j is the genuine weak derivative ∂j of the i-th inverse gradient. -/
def actualInverseGradientDerivative (d : SourceData μ) (ψ : Space n → ℝ)
    (i j : Fin n) (x : Space n) : ℝ :=
  ∑ a, (-(actualInverseTensor d j x i a) * coordinateDerivative ψ a x +
    (coordinateHessian d.potential x)⁻¹ i a * coordinateHessian ψ x j a)

theorem inverseGradient_compact (d : SourceData μ) {ψ : Space n → ℝ}
    (hc : HasCompactSupport ψ) (i : Fin n) : HasCompactSupport (actualInverseGradient d ψ i) := by
  have hsum := (HasCompactSupport.finset_sum (s := Finset.univ)
    (fun a _ => (hasCompactSupport_coordinateDerivative hc a).mul_left) :
      HasCompactSupport (∑ a : Fin n, fun x =>
        (coordinateHessian d.potential x)⁻¹ i a * coordinateDerivative ψ a x))
  have he : (∑ a : Fin n, fun x =>
      (coordinateHessian d.potential x)⁻¹ i a * coordinateDerivative ψ a x) =
      actualInverseGradient d ψ i := by
    funext x
    simp only [Finset.sum_apply, actualInverseGradient]
  exact he ▸ hsum

theorem inverseGradientDerivative_compact (d : SourceData μ) {ψ : Space n → ℝ}
    (hc : HasCompactSupport ψ) (i j : Fin n) :
    HasCompactSupport (actualInverseGradientDerivative d ψ i j) := by
  have hsum := (HasCompactSupport.finset_sum (s := Finset.univ)
    (fun a _ => ((hasCompactSupport_coordinateDerivative hc a).mul_left).add
      (hasCompactSupport_coordinateHessian hc j a).mul_left) :
      HasCompactSupport (∑ a : Fin n, fun x =>
        -(actualInverseTensor d j x i a) * coordinateDerivative ψ a x +
          (coordinateHessian d.potential x)⁻¹ i a * coordinateHessian ψ x j a))
  have he : (∑ a : Fin n, fun x =>
      -(actualInverseTensor d j x i a) * coordinateDerivative ψ a x +
        (coordinateHessian d.potential x)⁻¹ i a * coordinateHessian ψ x j a) =
      actualInverseGradientDerivative d ψ i j := by
    funext x
    simp only [Finset.sum_apply, actualInverseGradientDerivative]
  exact he ▸ hsum

theorem inverseGradient_local_top (d : SourceData μ) {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (actualInverseGradient d ψ i) ∞ (volume.restrict E) := by
  obtain ⟨hJ, _, _⟩ := actual_mongeAmpere_inverse_hasLocalWeakDerivative d.source_C1
    (d.target_smooth.of_le (by simp)) d.gradient_lipschitz
    (d.hessian_ae.mono fun _ hx => hx.2.1) d.third_local_L2 d.third_weak_derivative
  unfold actualInverseGradient
  exact memLp_finsetSum Finset.univ fun a _ => (hJ i a E hE).mul
    (memLp_top_restrict_compact_of_continuous
      (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) a).continuous hE)

theorem inverseGradientDerivative_local_L2 (d : SourceData μ) {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (i j : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (actualInverseGradientDerivative d ψ i j) 2 (volume.restrict E) := by
  obtain ⟨hJ, _, _⟩ := actual_mongeAmpere_inverse_hasLocalWeakDerivative d.source_C1
    (d.target_smooth.of_le (by simp)) d.gradient_lipschitz
    (d.hessian_ae.mono fun _ hx => hx.2.1) d.third_local_L2 d.third_weak_derivative
  unfold actualInverseGradientDerivative
  apply memLp_finsetSum
  intro a _
  have hp := memLp_top_restrict_compact_of_continuous
    (contDiff_coordinateDerivative (hψ.of_le (by norm_num) : ContDiff ℝ 1 ψ)
      (m := 0) (by norm_num) a).continuous hE
  have hC := memLp_continuous_on_compact
    (contDiff_coordinateHessian hψ (m := 0) (by norm_num) j a).continuous hE
  have hfirst : MemLp (fun x => coordinateDerivative ψ a x * -(actualInverseTensor d j x i a))
      2 (volume.restrict E) := hp.mul (inverse_tensor_local_L2 d j i a E hE).neg
  have ha : MemLp (fun x => -(actualInverseTensor d j x i a) * coordinateDerivative ψ a x)
      2 (volume.restrict E) := by simpa only [mul_comm] using hfirst
  exact ha.add ((hJ i a E hE).mul hC)

theorem inverseGradient_hasLocalWeakDerivative (d : SourceData μ) {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (i j : Fin n) :
    HasLocalWeakCoordinateDerivative (actualInverseGradient d ψ i)
      (actualInverseGradientDerivative d ψ i j) j := by
  obtain ⟨hJ, hDJ, hJw⟩ := actual_mongeAmpere_inverse_hasLocalWeakDerivative d.source_C1
    (d.target_smooth.of_le (by simp)) d.gradient_lipschitz
    (d.hessian_ae.mono fun _ hx => hx.2.1) d.third_local_L2 d.third_weak_derivative
  let p (a : Fin n) := coordinateDerivative ψ a
  have hp (a : Fin n) : ContDiff ℝ 1 (p a) := contDiff_coordinateDerivative hψ (by norm_num) a
  have hpl (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (p a) 2 (volume.restrict E) := memLp_continuous_on_compact (hp a).continuous hE
  have hCl (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => coordinateHessian ψ x j a) 2 (volume.restrict E) :=
    memLp_continuous_on_compact
      (contDiff_coordinateHessian hψ (m := 0) (by norm_num) j a).continuous hE
  have hDJj (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => -(actualInverseTensor d j x i a)) 2 (volume.restrict E) := by
    have h := hDJ j i a E hE
    change MemLp (fun x => -(actualInverseTensor d j x i a)) 2 (volume.restrict E) at h
    exact h
  have hw (a : Fin n) : HasLocalWeakCoordinateDerivative
      (fun x => (coordinateHessian d.potential x)⁻¹ i a * p a x)
      (fun x => -(actualInverseTensor d j x i a) * p a x +
        (coordinateHessian d.potential x)⁻¹ i a * coordinateHessian ψ x j a) j := by
    have h := hJw j i a
    change HasLocalWeakCoordinateDerivative (fun x => (coordinateHessian d.potential x)⁻¹ i a)
      (fun x => -(actualInverseTensor d j x i a)) j at h
    exact h.mul (hasLocalWeakCoordinateDerivative_of_contDiff (hp a) j)
      (memLp_two_on_compacts_of_top (hJ i a)) (hpl a) (hDJj a) (hCl a)
  have hl (a : Fin n) : LocallyIntegrable (fun x =>
      (coordinateHessian d.potential x)⁻¹ i a * p a x) volume := by
    apply locallyIntegrable_of_memLp_two_on_compacts
    intro E hE
    exact (hJ i a E hE).mul (hpl a E hE)
  have hDl (a : Fin n) : LocallyIntegrable (fun x =>
      -(actualInverseTensor d j x i a) * p a x +
        (coordinateHessian d.potential x)⁻¹ i a * coordinateHessian ψ x j a) volume := by
    apply locallyIntegrable_of_memLp_two_on_compacts
    intro E hE
    have hpTop := memLp_top_restrict_compact_of_continuous (hp a).continuous hE
    have ha : MemLp (fun x => p a x * -(actualInverseTensor d j x i a))
        2 (volume.restrict E) := hpTop.mul (hDJj a E hE)
    have ha' : MemLp (fun x => -(actualInverseTensor d j x i a) * p a x)
        2 (volume.restrict E) := by simpa only [mul_comm] using ha
    exact ha'.add ((hJ i a E hE).mul (hCl a E hE))
  have hs := hasLocalWeakCoordinateDerivative_finset_sum Finset.univ
    (fun a _ => hw a) (fun a _ => hl a) (fun a _ => hDl a)
  change HasLocalWeakCoordinateDerivative (actualInverseGradient d ψ i)
    (actualInverseGradientDerivative d ψ i j) j at hs
  exact hs

/-- All actual raw H1 input domains of compact source vector Bochner,
including the exact ordered derivative, are now conclusions. -/
theorem inverseGradient_weighted_H1 (d : SourceData μ) {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    MemLp (actualInverseGradient d ψ i) 2 (potentialMeasure d.potential) ∧
      ∀ j : Fin n, MemLp (actualInverseGradientDerivative d ψ i j) 2 (potentialMeasure d.potential) ∧
        HasLocalWeakCoordinateDerivative (actualInverseGradient d ψ i)
          (actualInverseGradientDerivative d ψ i j) j := by
  refine ⟨compact_localL2_to_source d (inverseGradient_compact d hc i)
    (memLp_two_on_compacts_of_top (inverseGradient_local_top d (hψ.of_le (by norm_num)) i)), ?_⟩
  intro j
  exact ⟨compact_localL2_to_source d (inverseGradientDerivative_compact d hc i j)
    (inverseGradientDerivative_local_L2 d hψ i j), inverseGradient_hasLocalWeakDerivative d hψ i j⟩

end KLSConstantImprovement.ActualSourceInverseGradientDomain405

#print axioms KLSConstantImprovement.ActualSourceInverseGradientDomain405.inverseGradient_compact
#print axioms KLSConstantImprovement.ActualSourceInverseGradientDomain405.inverseGradientDerivative_compact
#print axioms KLSConstantImprovement.ActualSourceInverseGradientDomain405.inverseGradient_hasLocalWeakDerivative
#print axioms KLSConstantImprovement.ActualSourceInverseGradientDomain405.inverseGradient_weighted_H1
