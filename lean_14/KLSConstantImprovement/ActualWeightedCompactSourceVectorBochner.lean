import KLSConstantImprovement.ActualCompactSourceVectorBochner

/-! Actual weighted, polarized vector Bochner for compact source fields.
Both derivative-weight and divergence-datum extras are retained. All
compact IBP/product requirements are discharged under C2 regularity.
No noncompact endpoint limit, row/column ordering or numeric cap follows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory KLS
open scoped BigOperators ContDiff
namespace KLSConstantImprovement.ActualWeightedCompactSourceVectorBochner
open ActualCompactSourceVectorBochner
variable {n : ℕ}

theorem source_adjoint_weighted_product (φ : Space n → ℝ)
    {w a : Space n → ℝ} (hw : ContDiff ℝ 1 w) (ha : ContDiff ℝ 1 a)
    (i : Fin n) (x : Space n) :
    coordinateSourceAdjoint φ (fun y => w y*a y) i x =
      w x*coordinateSourceAdjoint φ a i x-coordinateDerivative w i x*a x := by
  unfold coordinateSourceAdjoint
  rw [coordinateDerivative_mul (hw.differentiable (by norm_num) x)
    (ha.differentiable (by norm_num) x) i]
  ring

private lemma adjoint_continuous {φ a : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (ha : ContDiff ℝ 1 a) (i : Fin n) :
    Continuous (coordinateSourceAdjoint φ a i) := by
  exact (((contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous).mul
    ha.continuous).sub
    (contDiff_coordinateDerivative ha (m := 0) (by norm_num) i).continuous

private lemma adjoint_compact {φ a : Space n → ℝ}
    (hc : HasCompactSupport a) (i : Fin n) :
    HasCompactSupport (coordinateSourceAdjoint φ a i) :=
  hc.mul_left.sub (hasCompactSupport_coordinateDerivative hc i)

private lemma weighted_terms_integrable {φ w a b : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hw : ContDiff ℝ 2 w)
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) (hc : HasCompactSupport a)
    (i j : Fin n) :
    Integrable (fun x => w x*coordinateSourceAdjoint φ a i x*
      coordinateSourceAdjoint φ b j x) (potentialMeasure φ) ∧
    Integrable (fun x => w x*coordinateHessian φ x i j*a x*b x)
      (potentialMeasure φ) ∧
    Integrable (fun x => w x*coordinateDerivative a j x*coordinateDerivative b i x)
      (potentialMeasure φ) ∧
    Integrable (fun x => coordinateDerivative w j x*a x*coordinateDerivative b i x)
      (potentialMeasure φ) ∧
    Integrable (fun x => coordinateDerivative w i x*a x*coordinateSourceAdjoint φ b j x)
      (potentialMeasure φ) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have hb1 : ContDiff ℝ 1 b := hb.of_le (by norm_num)
  have hdw (k : Fin n) : Continuous (coordinateDerivative w k) :=
    (contDiff_coordinateDerivative hw (m := 0) (by norm_num) k).continuous
  have hda : Continuous (coordinateDerivative a j) :=
    (contDiff_coordinateDerivative ha (m := 0) (by norm_num) j).continuous
  have hdb : Continuous (coordinateDerivative b i) :=
    (contDiff_coordinateDerivative hb (m := 0) (by norm_num) i).continuous
  have hH : Continuous (fun x => coordinateHessian φ x i j) :=
    (contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hw.continuous.mul (adjoint_continuous hφ1 ha1 i)).mul
        (adjoint_continuous hφ1 hb1 j)) (adjoint_compact hc i).mul_left.mul_right
  · exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (((hw.continuous.mul hH).mul ha.continuous).mul hb.continuous) hc.mul_left.mul_right
  · exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hw.continuous.mul hda).mul hdb)
      (hasCompactSupport_coordinateDerivative hc j).mul_left.mul_right
  · exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (((hdw j).mul ha.continuous).mul hdb) hc.mul_left.mul_right
  · exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (((hdw i).mul ha.continuous).mul (adjoint_continuous hφ1 hb1 j))
      hc.mul_left.mul_right

private lemma integrable_four_sum {f g h k : Space n → ℝ}
    {μ : Measure (Space n)} (hf : Integrable f μ) (hg : Integrable g μ)
    (hh : Integrable h μ) (hk : Integrable k μ) :
    Integrable (fun x => f x + g x + h x + k x) μ := by
  have hi := ((hf.add hg).add hh).add hk
  have he : ((f + g) + h) + k = (fun x => f x + g x + h x + k x) := by
    funext x
    rfl
  rw [he] at hi
  exact hi

private lemma integral_four_sum {f g h k : Space n → ℝ}
    {μ : Measure (Space n)} (hf : Integrable f μ) (hg : Integrable g μ)
    (hh : Integrable h μ) (hk : Integrable k μ) :
    (∫ x, f x + g x + h x + k x ∂μ) =
      (∫ x, f x ∂μ) + (∫ x, g x ∂μ) + (∫ x, h x ∂μ) + (∫ x, k x ∂μ) := by
  calc
    _ = ∫ x, (((f + g) + h) + k) x ∂μ := rfl
    _ = (∫ x, ((f + g) + h) x ∂μ) + (∫ x, k x ∂μ) :=
      integral_add ((hf.add hg).add hh) hk
    _ = _ := by
      have he3 : (∫ x, ((f + g) + h) x ∂μ) =
          (∫ x, (f + g) x ∂μ) + (∫ x, h x ∂μ) :=
        integral_add (hf.add hg) hh
      have he2 : (∫ x, (f + g) x ∂μ) =
          (∫ x, f x ∂μ) + (∫ x, g x ∂μ) := integral_add hf hg
      rw [he3, he2]

theorem compact_weighted_vector_bochner_coordinate {φ w a b : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hw : ContDiff ℝ 2 w)
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b) (i j : Fin n) :
    (∫ x, w x*coordinateSourceAdjoint φ a i x*coordinateSourceAdjoint φ b j x
      ∂potentialMeasure φ) =
      ∫ x, w x*coordinateHessian φ x i j*a x*b x+
        w x*coordinateDerivative a j x*coordinateDerivative b i x+
        coordinateDerivative w j x*a x*coordinateDerivative b i x+
        coordinateDerivative w i x*a x*coordinateSourceAdjoint φ b j x
        ∂potentialMeasure φ := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have h := compact_source_vector_bochner_coordinate hφ (hw.mul ha) hb
    hca.mul_left hcb i j
  have he1 : (fun x => coordinateSourceAdjoint φ (fun y => w y*a y) i x*
      coordinateSourceAdjoint φ b j x) =
      (fun x => w x*coordinateSourceAdjoint φ a i x*coordinateSourceAdjoint φ b j x-
        coordinateDerivative w i x*a x*coordinateSourceAdjoint φ b j x) := by
    funext x
    rw [source_adjoint_weighted_product φ hw1 ha1 i x]
    ring
  have he2 : (fun x => coordinateHessian φ x i j*(w x*a x)*b x) =
      (fun x => w x*coordinateHessian φ x i j*a x*b x) := by
    funext x
    ring
  have he3 : (fun x => coordinateDerivative (fun y => w y*a y) j x*
      coordinateDerivative b i x) =
      (fun x => w x*coordinateDerivative a j x*coordinateDerivative b i x+
        coordinateDerivative w j x*a x*coordinateDerivative b i x) := by
    funext x
    rw [coordinateDerivative_mul (hw.differentiable (by norm_num) x)
      (ha.differentiable (by norm_num) x) j]
    ring
  rcases weighted_terms_integrable hφ hw ha hb hca i j with
    ⟨hleft, hcurv, hjac, hextra, hdatum⟩
  rw [he1, he2, he3, integral_sub hleft hdatum, integral_add hjac hextra] at h
  rw [integral_four_sum hcurv hjac hextra hdatum]
  linarith

theorem integral_compact_weighted_vector_adjoint_product {φ w : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hw : ContDiff ℝ 2 w)
    (a b : Fin n → Space n → ℝ)
    (ha : ∀ i, ContDiff ℝ 2 (a i)) (hb : ∀ i, ContDiff ℝ 2 (b i))
    (hca : ∀ i, HasCompactSupport (a i)) (hcb : ∀ i, HasCompactSupport (b i)) :
    (∫ x, w x*sourceVectorAdjoint φ a x*sourceVectorAdjoint φ b x ∂potentialMeasure φ) =
      ∫ x, ∑ i : Fin n, ∑ j : Fin n,
        (w x*coordinateHessian φ x i j*a i x*b j x+
          w x*coordinateDerivative (a i) j x*coordinateDerivative (b j) i x+
          coordinateDerivative w j x*a i x*coordinateDerivative (b j) i x+
          coordinateDerivative w i x*a i x*coordinateSourceAdjoint φ (b j) j x)
        ∂potentialMeasure φ := by
  have hi (i j : Fin n) := weighted_terms_integrable hφ hw (ha i) (hb j) (hca i) i j
  have hleft (i j : Fin n) := (hi i j).1
  have hright (i j : Fin n) : Integrable (fun x =>
      w x*coordinateHessian φ x i j*a i x*b j x+
        w x*coordinateDerivative (a i) j x*coordinateDerivative (b j) i x+
        coordinateDerivative w j x*a i x*coordinateDerivative (b j) i x+
        coordinateDerivative w i x*a i x*coordinateSourceAdjoint φ (b j) j x)
      (potentialMeasure φ) := by
    exact integrable_four_sum (hi i j).2.1 (hi i j).2.2.1
      (hi i j).2.2.2.1 (hi i j).2.2.2.2
  calc
    _ = ∫ x, ∑ i : Fin n, ∑ j : Fin n,
        w x*coordinateSourceAdjoint φ (a i) i x*coordinateSourceAdjoint φ (b j) j x
        ∂potentialMeasure φ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change (w x*(∑ i, coordinateSourceAdjoint φ (a i) i x))*
          (∑ j, coordinateSourceAdjoint φ (b j) j x) = _
        have hwExpand : w x*(∑ i, coordinateSourceAdjoint φ (a i) i x) =
            ∑ i, w x*coordinateSourceAdjoint φ (a i) i x := by rw [Finset.mul_sum]
        rw [hwExpand, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ∫ x, w x*coordinateSourceAdjoint φ (a i) i x*coordinateSourceAdjoint φ (b j) j x
          ∂potentialMeasure φ := by
      rw [integral_finsetSum Finset.univ
        (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hleft i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hleft i j)]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ∫ x, w x*coordinateHessian φ x i j*a i x*b j x+
          w x*coordinateDerivative (a i) j x*coordinateDerivative (b j) i x+
          coordinateDerivative w j x*a i x*coordinateDerivative (b j) i x+
          coordinateDerivative w i x*a i x*coordinateSourceAdjoint φ (b j) j x
          ∂potentialMeasure φ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact compact_weighted_vector_bochner_coordinate hφ hw (ha i) (hb j)
        (hca i) (hcb j) i j
    _ = _ := by
      symm
      rw [integral_finsetSum Finset.univ
        (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hright i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hright i j)]

end KLSConstantImprovement.ActualWeightedCompactSourceVectorBochner
#print axioms KLSConstantImprovement.ActualWeightedCompactSourceVectorBochner.source_adjoint_weighted_product
#print axioms KLSConstantImprovement.ActualWeightedCompactSourceVectorBochner.compact_weighted_vector_bochner_coordinate
#print axioms KLSConstantImprovement.ActualWeightedCompactSourceVectorBochner.integral_compact_weighted_vector_adjoint_product
