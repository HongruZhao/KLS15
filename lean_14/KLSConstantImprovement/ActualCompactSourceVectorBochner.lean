import KLS.HessianMetricIntegration

/-! Actual weighted vector Bochner identity on compact source fields.
The potential is finite C2 and every vector coordinate is C2/compact.
Every boundary/product integrability requirement is discharged. The
Jacobian contribution is Tr(Da²), not an unsigned Euclidean HS norm.
No potential existence, noncompact graph limit or numerical cap is claimed. -/
noncomputable section
open MeasureTheory KLS
open scoped BigOperators ContDiff
namespace KLSConstantImprovement.ActualCompactSourceVectorBochner

variable {n : ℕ}

def coordinateSourceAdjoint (φ f : Space n → ℝ) (i : Fin n) (x : Space n) : ℝ :=
  coordinateDerivative φ i x * f x-coordinateDerivative f i x

def sourceVectorAdjoint (φ : Space n → ℝ)
    (a : Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i, coordinateSourceAdjoint φ (a i) i x

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

theorem compact_source_adjoint_ibp {φ f g : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (i : Fin n) :
    (∫ x, coordinateSourceAdjoint φ f i x * g x ∂potentialMeasure φ) =
      ∫ x, f x * coordinateDerivative g i x ∂potentialMeasure φ := by
  have h := integral_mul_coordinateDrift_of_hasCompactSupport_left hφ hg hf hc i
  have he : (fun x => coordinateSourceAdjoint φ f i x * g x) =
      (fun x => -(g x * (coordinateDerivative f i x-coordinateDerivative φ i x*f x))) := by
    funext x
    dsimp [coordinateSourceAdjoint]
    ring
  rw [he, integral_neg, h, neg_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

theorem coordinate_source_adjoint_derivative {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 2 f) (i j : Fin n) (x : Space n) :
    coordinateDerivative (coordinateSourceAdjoint φ f j) i x =
      coordinateHessian φ x i j*f x+
        coordinateDerivative φ j x*coordinateDerivative f i x-coordinateHessian f x i j := by
  have hs : ContDiff ℝ 1 (coordinateDerivative φ j) :=
    contDiff_coordinateDerivative hφ (by norm_num) j
  have hd : ContDiff ℝ 1 (coordinateDerivative f j) :=
    contDiff_coordinateDerivative hf (by norm_num) j
  unfold coordinateSourceAdjoint
  rw [coordinateDerivative_sub ((hs.mul (hf.of_le (by norm_num))).differentiable
      (by norm_num) x) (hd.differentiable (by norm_num) x) i,
    coordinateDerivative_mul (hs.differentiable (by norm_num) x)
      (hf.differentiable (by norm_num) x) i]
  rfl

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

theorem compact_source_vector_bochner_coordinate {φ a b : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b) (i j : Fin n) :
    (∫ x, coordinateSourceAdjoint φ a i x*coordinateSourceAdjoint φ b j x
      ∂potentialMeasure φ) =
      (∫ x, coordinateHessian φ x i j*a x*b x ∂potentialMeasure φ)+
        ∫ x, coordinateDerivative a j x*coordinateDerivative b i x ∂potentialMeasure φ := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have hb1 : ContDiff ℝ 1 b := hb.of_le (by norm_num)
  have hbi : ContDiff ℝ 1 (coordinateDerivative b i) :=
    contDiff_coordinateDerivative hb (by norm_num) i
  have hfirst := compact_source_adjoint_ibp hφ1 ha1 (contDiff_adjoint hφ hb j)
    (compact_adjoint hcb j) i
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

theorem integral_compact_source_vector_adjoint_square {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (a : Fin n → Space n → ℝ)
    (ha : ∀ i, ContDiff ℝ 2 (a i)) (hc : ∀ i, HasCompactSupport (a i)) :
    (∫ x, (sourceVectorAdjoint φ a x)^2 ∂potentialMeasure φ) =
      ∫ x, ∑ i : Fin n, ∑ j : Fin n,
        (coordinateHessian φ x i j*a i x*a j x+
          coordinateDerivative (a i) j x*coordinateDerivative (a j) i x)
        ∂potentialMeasure φ := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have ha1 (i : Fin n) : ContDiff ℝ 1 (a i) := (ha i).of_le (by norm_num)
  have hi (i j : Fin n) : Integrable (fun x =>
      coordinateSourceAdjoint φ (a i) i x*coordinateSourceAdjoint φ (a j) j x)
      (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((contDiff_adjoint hφ (ha i) i).continuous.mul (contDiff_adjoint hφ (ha j) j).continuous)
      (compact_adjoint (hc i) i).mul_right
  have hj (i j : Fin n) : Integrable (fun x =>
      coordinateHessian φ x i j*a i x*a j x+
        coordinateDerivative (a i) j x*coordinateDerivative (a j) i x)
      (potentialMeasure φ) :=
    (integrable_curvature hφ (ha1 i) (ha1 j) (hc i) i j).add
      (integrable_derivative_product hφ.continuous (ha1 i) (ha1 j) (hc i) i j)
  calc
    _ = ∫ x, ∑ i : Fin n, ∑ j : Fin n,
        coordinateSourceAdjoint φ (a i) i x*coordinateSourceAdjoint φ (a j) j x
        ∂potentialMeasure φ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [sourceVectorAdjoint, pow_two, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ∫ x, coordinateSourceAdjoint φ (a i) i x*coordinateSourceAdjoint φ (a j) j x
          ∂potentialMeasure φ := by
      rw [integral_finsetSum Finset.univ
        (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ∫ x, coordinateHessian φ x i j*a i x*a j x+
          coordinateDerivative (a i) j x*coordinateDerivative (a j) i x
          ∂potentialMeasure φ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [compact_source_vector_bochner_coordinate hφ (ha i) (ha j) (hc i) (hc j) i j,
        integral_add (integrable_curvature hφ (ha1 i) (ha1 j) (hc i) i j)
          (integrable_derivative_product hφ.continuous (ha1 i) (ha1 j) (hc i) i j)]
    _ = _ := by
      symm
      rw [integral_finsetSum Finset.univ
        (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hj i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hj i j)]

end KLSConstantImprovement.ActualCompactSourceVectorBochner
#print axioms KLSConstantImprovement.ActualCompactSourceVectorBochner.compact_source_adjoint_ibp
#print axioms KLSConstantImprovement.ActualCompactSourceVectorBochner.coordinate_source_adjoint_derivative
#print axioms KLSConstantImprovement.ActualCompactSourceVectorBochner.compact_source_vector_bochner_coordinate
#print axioms KLSConstantImprovement.ActualCompactSourceVectorBochner.integral_compact_source_vector_adjoint_square
