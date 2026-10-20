import KLSConstantImprovement.ActualWeightedCompactSourceVectorBochner
import KLS.WeightedBochnerDomain

/-! Actual noncompact source vector Bochner by ordinary source cutoffs.
Only first-order L1 products (or L2 adjoints/components/Jacobians) and the
curvature product are required. No global derivative-N product, graph-core,
Poisson optimizer, source potential existence or numerical cap is inferred. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory KLS Filter
open scoped BigOperators ContDiff Topology
namespace KLSConstantImprovement.ActualSourceVectorBochnerFirstOrderDomain
open ActualCompactSourceVectorBochner ActualWeightedCompactSourceVectorBochner
variable {n : ℕ}

private lemma continuous_adjoint {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hf : ContDiff ℝ 1 f) (i : Fin n) :
    Continuous (coordinateSourceAdjoint φ f i) := by
  exact (((contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous).mul
    hf.continuous).sub
    (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous

private lemma contDiff_adjoint {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 2 f) (i : Fin n) :
    ContDiff ℝ 1 (coordinateSourceAdjoint φ f i) := by
  exact ((contDiff_coordinateDerivative hφ (by norm_num) i).mul
    (hf.of_le (by norm_num))).sub
    (contDiff_coordinateDerivative hf (by norm_num) i)

private lemma compact_adjoint {φ f : Space n → ℝ}
    (hc : HasCompactSupport f) (i : Fin n) :
    HasCompactSupport (coordinateSourceAdjoint φ f i) := by
  exact hc.mul_left.sub (hasCompactSupport_coordinateDerivative hc i)

private lemma integrable_curvature {φ a b : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hc : HasCompactSupport a) (i j : Fin n) :
    Integrable (fun x => coordinateHessian φ x i j*a x*b x) (potentialMeasure φ) := by
  have hh := (contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous
  exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
    ((hh.mul ha.continuous).mul hb.continuous) hc.mul_left.mul_right

private lemma integrable_derivative_product {φ a b : Space n → ℝ}
    (hφ : Continuous φ) (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hc : HasCompactSupport a) (i j : Fin n) :
    Integrable (fun x => coordinateDerivative a j x*coordinateDerivative b i x)
      (potentialMeasure φ) := by
  have hda := (contDiff_coordinateDerivative ha (m := 0) (by norm_num) j).continuous
  have hdb := (contDiff_coordinateDerivative hb (m := 0) (by norm_num) i).continuous
  exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ
    (hda.mul hdb) (hasCompactSupport_coordinateDerivative hc j).mul_right

theorem compact_left_source_adjoint_ibp {φ f g : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport f) (i : Fin n) :
    (∫ x, coordinateSourceAdjoint φ f i x*g x ∂potentialMeasure φ) =
      ∫ x, f x*coordinateDerivative g i x ∂potentialMeasure φ := by
  have hdφ := (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous
  have hdf := (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous
  have hdg := (contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous
  have hfg : Integrable (fun x => f x*g x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hf.continuous.mul hg.continuous) hc.mul_right
  have hdfg : Integrable (fun x => coordinateDerivative f i x*g x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hdf.mul hg.continuous) (hasCompactSupport_coordinateDerivative hc i).mul_right
  have hfdg : Integrable (fun x => f x*coordinateDerivative g i x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hf.continuous.mul hdg) hc.mul_right
  have hfgφ : Integrable (fun x => f x*g x*coordinateDerivative φ i x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hf.continuous.mul hg.continuous).mul hdφ) hc.mul_right.mul_right
  have hi := integral_mul_fderiv_potentialMeasure
    (hφ.differentiable (by norm_num)) (hf.differentiable (by norm_num))
    (hg.differentiable (by norm_num)) (EuclideanSpace.single i 1) hfg hdfg hfdg hfgφ
  change (∫ x, f x*coordinateDerivative g i x ∂potentialMeasure φ) =
    (∫ x, f x*g x*coordinateDerivative φ i x ∂potentialMeasure φ)-
      ∫ x, coordinateDerivative f i x*g x ∂potentialMeasure φ at hi
  have he : (fun x => coordinateSourceAdjoint φ f i x*g x) =
      (fun x => f x*g x*coordinateDerivative φ i x-coordinateDerivative f i x*g x) := by
    funext x
    dsimp [coordinateSourceAdjoint]
    ring
  rw [he, integral_sub hfgφ hdfg]
  exact hi.symm

theorem compact_left_source_vector_bochner_coordinate {φ a b : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : HasCompactSupport a) (i j : Fin n) :
    (∫ x, coordinateSourceAdjoint φ a i x*coordinateSourceAdjoint φ b j x
      ∂potentialMeasure φ) =
      (∫ x, coordinateHessian φ x i j*a x*b x ∂potentialMeasure φ)+
        ∫ x, coordinateDerivative a j x*coordinateDerivative b i x ∂potentialMeasure φ := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have hb1 : ContDiff ℝ 1 b := hb.of_le (by norm_num)
  have hbi : ContDiff ℝ 1 (coordinateDerivative b i) :=
    contDiff_coordinateDerivative hb (by norm_num) i
  have hfirst := compact_left_source_adjoint_ibp hφ1 ha1 (contDiff_adjoint hφ hb j) hca i
  have he : (fun x => a x*coordinateDerivative (coordinateSourceAdjoint φ b j) i x) =
      (fun x => coordinateHessian φ x i j*a x*b x+
        a x*coordinateSourceAdjoint φ (coordinateDerivative b i) j x) := by
    funext x
    rw [coordinate_source_adjoint_derivative hφ hb i j x]
    have hs := (coordinateHessian_symmetric hb x).apply i j
    dsimp [coordinateSourceAdjoint]
    change coordinateHessian b x j i = coordinateHessian b x i j at hs
    change _ = coordinateHessian φ x i j*a x*b x+
      a x*(coordinateDerivative φ j x*coordinateDerivative b i x-coordinateHessian b x j i)
    rw [hs]
    ring
  have hcurv := integrable_curvature hφ ha1 hb1 hca i j
  have hrem : Integrable (fun x => a x*coordinateSourceAdjoint φ
      (coordinateDerivative b i) j x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (ha.continuous.mul (continuous_adjoint hφ1 hbi j)) hca.mul_right
  rw [he, integral_add hcurv hrem] at hfirst
  have hsecond := compact_source_adjoint_ibp hφ1 hbi ha1 hca j
  have hr : (∫ x, a x*coordinateSourceAdjoint φ (coordinateDerivative b i) j x
      ∂potentialMeasure φ) =
      ∫ x, coordinateDerivative a j x*coordinateDerivative b i x ∂potentialMeasure φ := by
    calc
      _ = ∫ x, coordinateSourceAdjoint φ (coordinateDerivative b i) j x*a x
          ∂potentialMeasure φ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = ∫ x, coordinateDerivative b i x*coordinateDerivative a j x
          ∂potentialMeasure φ := hsecond
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
  rw [hr] at hfirst
  exact hfirst

private lemma cutoff_integrable_mul {μ : Measure (Space n)} {F : Space n → ℝ}
    (hF : Integrable F μ) (k : ℕ) :
    Integrable (fun x => smoothCutoff n k x*F x) μ := by
  apply hF.norm.mono'
    ((smoothCutoff_contDiff k).continuous.aestronglyMeasurable.mul hF.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖smoothCutoff n k x*F x‖ ≤ ‖F x‖
  rw [norm_mul, Real.norm_of_nonneg (faithfulCutoff_bounds k x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (faithfulCutoff_bounds k x).2

private lemma cutoff_integral_tendsto {μ : Measure (Space n)} {F : Space n → ℝ}
    (hF : Integrable F μ) :
    Tendsto (fun k => ∫ x, smoothCutoff n k x*F x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖F x‖)
    (fun k => (smoothCutoff_contDiff k).continuous.aestronglyMeasurable.mul hF.aestronglyMeasurable)
    hF.norm
  · intro k
    filter_upwards [] with x
    change ‖smoothCutoff n k x*F x‖ ≤ ‖F x‖
    rw [norm_mul, Real.norm_of_nonneg (faithfulCutoff_bounds k x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (faithfulCutoff_bounds k x).2
  · filter_upwards [] with x
    simpa using (smoothCutoff_tendsto_one x).mul_const (F x)

private lemma cutoff_derivative_bound (K : ℝ)
    (hK : ∀ k x, ‖gradient (smoothCutoff n k) x‖ ≤ cutoffScale k*K)
    (k : ℕ) (i : Fin n) (x : Space n) :
    |coordinateDerivative (smoothCutoff n k) i x| ≤ cutoffScale k*K := by
  rw [coordinateDerivative_eq_gradient]
  have he : |(gradient (smoothCutoff n k) x) i| ≤ ‖gradient (smoothCutoff n k) x‖ := by
    simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le (gradient (smoothCutoff n k) x) i)
  exact he.trans (hK k x)

private lemma cutoff_derivative_integrable {μ : Measure (Space n)} {F : Space n → ℝ}
    (hF : Integrable F μ) (K : ℝ)
    (hK : ∀ k x, ‖gradient (smoothCutoff n k) x‖ ≤ cutoffScale k*K)
    (k : ℕ) (i : Fin n) :
    Integrable (fun x => coordinateDerivative (smoothCutoff n k) i x*F x) μ := by
  apply (hF.norm.const_mul (cutoffScale k*K)).mono'
    ((contDiff_coordinateDerivative (smoothCutoff_contDiff k) (m := 0)
      (by norm_num) i).continuous.aestronglyMeasurable.mul hF.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖coordinateDerivative (smoothCutoff n k) i x*F x‖ ≤ cutoffScale k*K*‖F x‖
  simpa only [norm_mul, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right (cutoff_derivative_bound K hK k i x) (abs_nonneg (F x))

private lemma cutoff_derivative_integral_zero {μ : Measure (Space n)} {F : Space n → ℝ}
    (hF : Integrable F μ) (K : ℝ)
    (hK : ∀ k x, ‖gradient (smoothCutoff n k) x‖ ≤ cutoffScale k*K)
    (i : Fin n) :
    Tendsto (fun k => ∫ x, coordinateDerivative (smoothCutoff n k) i x*F x ∂μ)
      atTop (𝓝 0) := by
  apply tendsto_integral_zero_of_vanishing_bound hF.norm
    (by simpa using cutoffScale_tendsto_zero.mul_const K)
  intro k x
  simpa only [abs_mul, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right (cutoff_derivative_bound K hK k i x) (abs_nonneg (F x))

theorem source_vector_bochner_coordinate_of_first_order_products {φ a b : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (i j : Fin n)
    (hL : Integrable (fun x => coordinateSourceAdjoint φ a i x*
      coordinateSourceAdjoint φ b j x) (potentialMeasure φ))
    (hH : Integrable (fun x => coordinateHessian φ x i j*a x*b x) (potentialMeasure φ))
    (hD : Integrable (fun x => coordinateDerivative a j x*coordinateDerivative b i x)
      (potentialMeasure φ))
    (hE : Integrable (fun x => a x*coordinateSourceAdjoint φ b j x) (potentialMeasure φ))
    (hF : Integrable (fun x => a x*coordinateDerivative b i x) (potentialMeasure φ)) :
    (∫ x, coordinateSourceAdjoint φ a i x*coordinateSourceAdjoint φ b j x
      ∂potentialMeasure φ) =
      (∫ x, coordinateHessian φ x i j*a x*b x ∂potentialMeasure φ)+
        ∫ x, coordinateDerivative a j x*coordinateDerivative b i x ∂potentialMeasure φ := by
  obtain ⟨K, hK0, hK⟩ := smoothCutoff_gradient_bound (n := n)
  have hχ2 (k : ℕ) : ContDiff ℝ 2 (smoothCutoff n k) :=
    (unitCutoff n).contDiff.comp (contDiff_id.const_smul (cutoffScale k))
  have heq (k : ℕ) :
      (∫ x, smoothCutoff n k x*(coordinateSourceAdjoint φ a i x*
        coordinateSourceAdjoint φ b j x) ∂potentialMeasure φ)-
      (∫ x, coordinateDerivative (smoothCutoff n k) i x*
        (a x*coordinateSourceAdjoint φ b j x) ∂potentialMeasure φ) =
      (∫ x, smoothCutoff n k x*(coordinateHessian φ x i j*a x*b x)
        ∂potentialMeasure φ)+
      (∫ x, smoothCutoff n k x*(coordinateDerivative a j x*coordinateDerivative b i x)
        ∂potentialMeasure φ)+
      ∫ x, coordinateDerivative (smoothCutoff n k) j x*
        (a x*coordinateDerivative b i x) ∂potentialMeasure φ := by
    have hc := compact_left_source_vector_bochner_coordinate hφ ((hχ2 k).mul ha) hb
      (smoothCutoff_hasCompactSupport k).mul_right i j
    have hl : (fun x => coordinateSourceAdjoint φ (fun y => smoothCutoff n k y*a y) i x*
        coordinateSourceAdjoint φ b j x) =
        (fun x => smoothCutoff n k x*(coordinateSourceAdjoint φ a i x*
          coordinateSourceAdjoint φ b j x)-coordinateDerivative (smoothCutoff n k) i x*
          (a x*coordinateSourceAdjoint φ b j x)) := by
      funext x
      rw [source_adjoint_weighted_product φ (smoothCutoff_contDiff k)
        (ha.of_le (by norm_num)) i x]
      ring
    have hh : (fun x => coordinateHessian φ x i j*(smoothCutoff n k x*a x)*b x) =
        (fun x => smoothCutoff n k x*(coordinateHessian φ x i j*a x*b x)) := by
      funext x
      ring
    have hd : (fun x => coordinateDerivative (fun y => smoothCutoff n k y*a y) j x*
        coordinateDerivative b i x) =
        (fun x => smoothCutoff n k x*(coordinateDerivative a j x*coordinateDerivative b i x)+
          coordinateDerivative (smoothCutoff n k) j x*(a x*coordinateDerivative b i x)) := by
      funext x
      rw [coordinateDerivative_mul ((smoothCutoff_contDiff k).differentiable (by norm_num) x)
        (ha.differentiable (by norm_num) x) j]
      ring
    rw [hl, hh, hd, integral_sub (cutoff_integrable_mul hL k)
      (cutoff_derivative_integrable hE K hK k i), integral_add (cutoff_integrable_mul hD k)
      (cutoff_derivative_integrable hF K hK k j)] at hc
    linarith
  have htL := (cutoff_integral_tendsto hL).sub
    (cutoff_derivative_integral_zero hE K hK i)
  have htR := ((cutoff_integral_tendsto hH).add (cutoff_integral_tendsto hD)).add
    (cutoff_derivative_integral_zero hF K hK j)
  have hlim := tendsto_nhds_unique htL (htR.congr' (Eventually.of_forall fun k => (heq k).symm))
  simpa only [sub_zero, add_zero] using hlim

theorem source_vector_bochner_coordinate_of_L2_first_order {φ a b : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) (i j : Fin n)
    (ha2 : MemLp a 2 (potentialMeasure φ))
    (hδa : MemLp (coordinateSourceAdjoint φ a i) 2 (potentialMeasure φ))
    (hδb : MemLp (coordinateSourceAdjoint φ b j) 2 (potentialMeasure φ))
    (hDa : MemLp (coordinateDerivative a j) 2 (potentialMeasure φ))
    (hDb : MemLp (coordinateDerivative b i) 2 (potentialMeasure φ))
    (hH : Integrable (fun x => coordinateHessian φ x i j*a x*b x) (potentialMeasure φ)) :
    (∫ x, coordinateSourceAdjoint φ a i x*coordinateSourceAdjoint φ b j x
      ∂potentialMeasure φ) =
      (∫ x, coordinateHessian φ x i j*a x*b x ∂potentialMeasure φ)+
        ∫ x, coordinateDerivative a j x*coordinateDerivative b i x ∂potentialMeasure φ :=
  source_vector_bochner_coordinate_of_first_order_products hφ ha hb i j
    (hδa.integrable_mul hδb) hH (hDa.integrable_mul hDb)
    (ha2.integrable_mul hδb) (ha2.integrable_mul hDb)

end KLSConstantImprovement.ActualSourceVectorBochnerFirstOrderDomain
#print axioms KLSConstantImprovement.ActualSourceVectorBochnerFirstOrderDomain.compact_left_source_adjoint_ibp
#print axioms KLSConstantImprovement.ActualSourceVectorBochnerFirstOrderDomain.compact_left_source_vector_bochner_coordinate
#print axioms KLSConstantImprovement.ActualSourceVectorBochnerFirstOrderDomain.source_vector_bochner_coordinate_of_first_order_products
#print axioms KLSConstantImprovement.ActualSourceVectorBochnerFirstOrderDomain.source_vector_bochner_coordinate_of_L2_first_order
