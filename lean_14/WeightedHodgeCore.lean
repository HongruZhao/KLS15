import KLS.WeightedEnergyGraph

/-! The weighted Hodge identity on actual compact C² vector fields.
All operators are concrete coordinate derivatives and all integrals use
the actual density exp(-φ). This is a core identity; no closed-domain
Hodge decomposition or universal numerical spectral bound is assumed. -/

open MeasureTheory Set Filter Matrix
open scoped BigOperators ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ}

def weightedVectorDivergence (φ : Space n → ℝ)
    (F : Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i, weightedDerivativeTest φ (F i) i x

def vectorCurl (F : Fin n → Space n → ℝ) (i j : Fin n) (x : Space n) : ℝ :=
  coordinateDerivative (F j) i x - coordinateDerivative (F i) j x

def vectorGradientSquare (F : Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, (coordinateDerivative (F j) i x) ^ 2

/-- The factor one half counts each antisymmetric coordinate pair once. -/
def vectorCurlSquare (F : Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, (vectorCurl F i j x) ^ 2

def vectorCurvatureForm (φ : Space n → ℝ)
    (F : Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, coordinateHessian φ x i j * F i x * F j x

lemma contDiff_weightedDerivativeTest {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 2 f) (j : Fin n) :
    ContDiff ℝ 1 (weightedDerivativeTest φ f j) :=
  (contDiff_coordinateDerivative hf (by norm_num) j).sub
    ((hf.of_le (by norm_num)).mul (contDiff_coordinateDerivative hφ (by norm_num) j))

lemma coordinateDerivative_weightedDerivativeTest {φ g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 2 g) (i j : Fin n) (x : Space n) :
    coordinateDerivative (weightedDerivativeTest φ g j) i x =
      weightedDerivativeTest φ (coordinateDerivative g i) j x -
        g x * coordinateHessian φ x i j := by
  have hdg := (contDiff_coordinateDerivative hg (m := 1) (by norm_num) j).differentiable
    (by norm_num) x
  have hdφ := (contDiff_coordinateDerivative hφ (m := 1) (by norm_num) j).differentiable
    (by norm_num) x
  have hgx := hg.differentiable (by norm_num) x
  have hs := (coordinateHessian_symmetric hg x).apply i j
  have he := congrArg (fun L : Space n →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
    (hdg.hasFDerivAt.sub (hgx.hasFDerivAt.mul hdφ.hasFDerivAt)).fderiv
  change coordinateDerivative (weightedDerivativeTest φ g j) i x =
    coordinateHessian g x i j -
      (g x * coordinateHessian φ x i j +
        coordinateDerivative φ j x * coordinateDerivative g i x) at he
  rw [he]
  change coordinateHessian g x i j -
    (g x * coordinateHessian φ x i j +
      coordinateDerivative φ j x * coordinateDerivative g i x) =
    coordinateHessian g x j i - coordinateDerivative g i x * coordinateDerivative φ j x -
      g x * coordinateHessian φ x i j
  rw [hs]
  ring

/-- The exact two-coordinate weighted commutator, proved by two actual
compact integration-by-parts identities. -/
theorem integral_weightedDerivativeTest_mul {φ f g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (i j : Fin n) :
    (∫ x, weightedDerivativeTest φ f i x * weightedDerivativeTest φ g j x
      ∂potentialMeasure φ) =
      (∫ x, coordinateDerivative f j x * coordinateDerivative g i x ∂potentialMeasure φ) +
        ∫ x, coordinateHessian φ x i j * f x * g x ∂potentialMeasure φ := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hgi : ContDiff ℝ 1 (coordinateDerivative g i) :=
    contDiff_coordinateDerivative hg (by norm_num) i
  have hdg := contDiff_weightedDerivativeTest hφ hg j
  have h1 := integral_coordinateDerivative_mul_compact_test hφ1 hdg hf1 hfc i
  have h2 := integral_coordinateDerivative_mul_compact_test hφ1 hf1 hgi
    (hasCompactSupport_coordinateDerivative hgc i) j
  have hA : Integrable (fun x => f x *
      weightedDerivativeTest φ (coordinateDerivative g i) j x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hf.continuous.mul (weightedDerivativeTest_continuous hφ1 hgi j)) hfc.mul_right
  have hB : Integrable (fun x => coordinateHessian φ x i j * f x * g x)
      (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (((contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous.mul
        hf.continuous).mul hg.continuous) hfc.mul_left.mul_right
  have he : (∫ x, coordinateDerivative (weightedDerivativeTest φ g j) i x * f x
      ∂potentialMeasure φ) =
      (∫ x, f x * weightedDerivativeTest φ (coordinateDerivative g i) j x
        ∂potentialMeasure φ) -
        ∫ x, coordinateHessian φ x i j * f x * g x ∂potentialMeasure φ := by
    rw [← integral_sub hA hB]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [coordinateDerivative_weightedDerivativeTest hφ hg]
      ring
  have hc : (∫ x, weightedDerivativeTest φ g j x * weightedDerivativeTest φ f i x
      ∂potentialMeasure φ) =
      ∫ x, weightedDerivativeTest φ f i x * weightedDerivativeTest φ g j x
        ∂potentialMeasure φ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => mul_comm _ _
  rw [he, hc] at h1
  linarith

/-- The divergence energy is the mixed derivative energy plus the actual
curvature form. No convexity or probability normalization is required. -/
theorem integral_weightedVectorDivergence_sq {φ : Space n → ℝ}
    {F : Fin n → Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (hc : ∀ i, HasCompactSupport (F i)) :
    (∫ x, (weightedVectorDivergence φ F x) ^ 2 ∂potentialMeasure φ) =
      (∑ i, ∑ j, ∫ x, coordinateDerivative (F i) j x *
        coordinateDerivative (F j) i x ∂potentialMeasure φ) +
      ∑ i, ∑ j, ∫ x, coordinateHessian φ x i j * F i x * F j x
        ∂potentialMeasure φ := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hI (i j : Fin n) : Integrable (fun x =>
      weightedDerivativeTest φ (F i) i x * weightedDerivativeTest φ (F j) j x)
      (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((weightedDerivativeTest_continuous hφ1 ((hF i).of_le (by norm_num)) i).mul
        (weightedDerivativeTest_continuous hφ1 ((hF j).of_le (by norm_num)) j))
      (weightedDerivativeTest_hasCompactSupport (hc i) i).mul_right
  calc
    _ = ∑ i, ∑ j, ∫ x, weightedDerivativeTest φ (F i) i x *
        weightedDerivativeTest φ (F j) j x ∂potentialMeasure φ := by
      simp only [weightedVectorDivergence, pow_two]
      simp_rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [integral_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun j _ => hI i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hI i j)]
    _ = _ := by
      simp_rw [integral_weightedDerivativeTest_mul hφ (hF _) (hF _) (hc _) (hc _)]
      simp only [Finset.sum_add_distrib]

private theorem sum_integral_vectorCurl_sq {φ : Space n → ℝ}
    {F : Fin n → Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (hc : ∀ i, HasCompactSupport (F i)) :
    (1 / 2 : ℝ) * (∑ i, ∑ j, ∫ x, (vectorCurl F i j x) ^ 2 ∂potentialMeasure φ) =
      (∑ i, ∑ j, ∫ x, (coordinateDerivative (F j) i x) ^ 2 ∂potentialMeasure φ) -
      ∑ i, ∑ j, ∫ x, coordinateDerivative (F i) j x *
        coordinateDerivative (F j) i x ∂potentialMeasure φ := by
  have hd (i j : Fin n) : Continuous (coordinateDerivative (F j) i) :=
    (contDiff_coordinateDerivative (hF j) (m := 0) (by norm_num) i).continuous
  have hA (i j : Fin n) : Integrable (fun x => (coordinateDerivative (F j) i x) ^ 2)
      (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hd i j).pow 2) (by
        simpa only [pow_two, Pi.mul_def] using
          (hasCompactSupport_coordinateDerivative (hc j) i).mul_right
            (f' := coordinateDerivative (F j) i))
  have hM (i j : Fin n) : Integrable (fun x => coordinateDerivative (F i) j x *
      coordinateDerivative (F j) i x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hd j i).mul (hd i j)) (hasCompactSupport_coordinateDerivative (hc i) j).mul_right
  have he (i j : Fin n) : (∫ x, (vectorCurl F i j x) ^ 2 ∂potentialMeasure φ) =
      (∫ x, (coordinateDerivative (F j) i x) ^ 2 ∂potentialMeasure φ) +
      (∫ x, (coordinateDerivative (F i) j x) ^ 2 ∂potentialMeasure φ) -
      2 * ∫ x, coordinateDerivative (F i) j x * coordinateDerivative (F j) i x
        ∂potentialMeasure φ := by
    calc
      _ = ∫ x, (coordinateDerivative (F j) i x) ^ 2 +
          (coordinateDerivative (F i) j x) ^ 2 -
          2 * (coordinateDerivative (F i) j x * coordinateDerivative (F j) i x)
            ∂potentialMeasure φ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp [vectorCurl]; ring
      _ = _ := by
        have hs := integral_sub ((hA i j).add (hA j i)) ((hM i j).const_mul 2)
        simp only [Pi.add_apply] at hs
        rw [hs, integral_add (hA i j) (hA j i), integral_const_mul]
  simp_rw [he]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hswap : (∑ i, ∑ j, ∫ x, (coordinateDerivative (F i) j x) ^ 2 ∂potentialMeasure φ) =
      ∑ i, ∑ j, ∫ x, (coordinateDerivative (F j) i x) ^ 2 ∂potentialMeasure φ :=
    Finset.sum_comm
  rw [hswap]
  ring

/-- The weighted Hodge identity with the exact antisymmetric factor one half,
on genuine compact C² vector fields and a C² finite potential. -/
theorem integral_weightedHodge_core {φ : Space n → ℝ}
    {F : Fin n → Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (hc : ∀ i, HasCompactSupport (F i)) :
    (∫ x, (weightedVectorDivergence φ F x) ^ 2 ∂potentialMeasure φ) +
      (1 / 2 : ℝ) * (∑ i, ∑ j, ∫ x, (vectorCurl F i j x) ^ 2 ∂potentialMeasure φ) =
      (∑ i, ∑ j, ∫ x, (coordinateDerivative (F j) i x) ^ 2 ∂potentialMeasure φ) +
      ∑ i, ∑ j, ∫ x, coordinateHessian φ x i j * F i x * F j x
        ∂potentialMeasure φ := by
  rw [integral_weightedVectorDivergence_sq hφ hF hc,
    sum_integral_vectorCurl_sq hφ hF hc]
  ring

lemma vectorCurvatureForm_lower_bound {φ : Space n → ℝ} {κ : ℝ}
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (F : Fin n → Space n → ℝ) (x : Space n) :
    κ * (∑ i, (F i x) ^ 2) ≤ vectorCurvatureForm φ F x := by
  have h := hlower x (fun i => F i x)
  have he : (fun i => F i x) ⬝ᵥ (coordinateHessian φ x *ᵥ (fun i => F i x)) =
      vectorCurvatureForm φ F x := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, vectorCurvatureForm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at h
  simpa only [dotProduct, ← pow_two] using h

/-- The sharp lower-curvature Hodge estimate on the compact vector core.
The coefficient of gradient energy is one, and the curl energy has weight
one half. The conclusion holds for any real lower Hessian constant. -/
theorem integral_weightedHodge_core_coercive {φ : Space n → ℝ}
    {F : Fin n → Space n → ℝ} {κ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (hc : ∀ i, HasCompactSupport (F i))
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    (∑ i, ∑ j, ∫ x, (coordinateDerivative (F j) i x) ^ 2 ∂potentialMeasure φ) +
      κ * (∑ i, ∫ x, (F i x) ^ 2 ∂potentialMeasure φ) ≤
      (∫ x, (weightedVectorDivergence φ F x) ^ 2 ∂potentialMeasure φ) +
      (1 / 2 : ℝ) * (∑ i, ∑ j, ∫ x, (vectorCurl F i j x) ^ 2 ∂potentialMeasure φ) := by
  have hI (i : Fin n) : Integrable (fun x => (F i x) ^ 2) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hF i).continuous.pow 2) (by
        simpa only [pow_two, Pi.mul_def] using (hc i).mul_right (f' := F i))
  have hC (i j : Fin n) : Integrable (fun x => coordinateHessian φ x i j * F i x * F j x)
      (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (((contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous.mul
        (hF i).continuous).mul (hF j).continuous) (hc i).mul_left.mul_right
  have hCi : Integrable (vectorCurvatureForm φ F) (potentialMeasure φ) :=
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hC i j))
  have hl := integral_mono
    ((integrable_finsetSum Finset.univ (fun i _ => hI i)).const_mul κ) hCi
    (vectorCurvatureForm_lower_bound hlower F)
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hI i)] at hl
  have he : (∫ x, vectorCurvatureForm φ F x ∂potentialMeasure φ) =
      ∑ i, ∑ j, ∫ x, coordinateHessian φ x i j * F i x * F j x
        ∂potentialMeasure φ := by
    unfold vectorCurvatureForm
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hC i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun j _ => hC i j)]
  rw [he] at hl
  rw [integral_weightedHodge_core hφ hF hc]
  exact add_le_add (le_refl _) hl

/-- Positive curvature controls the actual vector L² norm by its actual
weighted divergence and curl, on the compact C² core. -/
theorem integral_weightedHodge_core_L2_bound {φ : Space n → ℝ}
    {F : Fin n → Space n → ℝ} {κ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (hc : ∀ i, HasCompactSupport (F i))
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    κ * (∑ i, ∫ x, (F i x) ^ 2 ∂potentialMeasure φ) ≤
      (∫ x, (weightedVectorDivergence φ F x) ^ 2 ∂potentialMeasure φ) +
      (1 / 2 : ℝ) * (∑ i, ∑ j, ∫ x, (vectorCurl F i j x) ^ 2 ∂potentialMeasure φ) := by
  have he := integral_weightedHodge_core_coercive hφ hF hc hlower
  have hnonneg : 0 ≤ ∑ i, ∑ j,
      ∫ x, (coordinateDerivative (F j) i x) ^ 2 ∂potentialMeasure φ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      integral_nonneg fun _ => sq_nonneg _
  linarith

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.integral_weightedDerivativeTest_mul
#print axioms KLS.DeterministicBridgeIntegration.integral_weightedVectorDivergence_sq
#print axioms KLS.DeterministicBridgeIntegration.integral_weightedHodge_core
#print axioms KLS.DeterministicBridgeIntegration.integral_weightedHodge_core_coercive
#print axioms KLS.DeterministicBridgeIntegration.integral_weightedHodge_core_L2_bound
