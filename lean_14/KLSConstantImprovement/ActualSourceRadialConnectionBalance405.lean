import KLSConstantImprovement.ActualSourceRadialConnectionDomains405

/-! Literal compact radial H-evolution balance for the actual natural flux.
Every signed term has an actual L1 domain and no mass bound is assumed.
Uniform local coercivity is a subsequent step. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualSourceRadialConnectionBalance405
open KLS ActualBoundedCanonicalSource ActualBoundedRawMetricDomain
open ActualSourceHessianEvolution405 ActualSourceConnectionFields405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualSourceRadialConnectionTest405 ActualSourceRadialConnectionBoundary405
open ActualSourceRadialConnectionDomains405 ActualRadialWeakMatrixTests405 ActualRadialMatrixCalculus405
open ActualSourceCompactConnectionDomains405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_compact_radial_connection_balance (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {δ : ℝ} (hδ : 0 < δ)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (hb : ∀ x, ‖χ x‖ ≤ 1) :
    (∫ x, χ x ^ 2 * (sourceConnectionTarget d (naturalCanonicalFlux d g) x +
        sourceConnectionGamma d (naturalCanonicalFlux d g) x) /
        radialDenom δ (fun a => naturalCanonicalFlux d g a x) ∂potentialMeasure d.potential) =
      (∫ x, χ x ^ 2 * sourceVectorMass d.potential (naturalCanonicalFlux d g) x /
        radialDenom δ (fun a => naturalCanonicalFlux d g a x) ∂potentialMeasure d.potential) -
      (∫ x, χ x ^ 2 * sourceConnectionCross d (naturalCanonicalFlux d g) Du x /
        radialDenom δ (fun a => naturalCanonicalFlux d g a x) ∂potentialMeasure d.potential) +
      2 * δ * (∫ x, χ x ^ 2 * sourceRadialExtra d (naturalCanonicalFlux d g) Du x /
        radialDenom δ (fun a => naturalCanonicalFlux d g a x) ^ 2 ∂potentialMeasure d.potential) -
      2 * (∫ x, χ x * sourceConnectionBoundary d χ (naturalCanonicalFlux d g) x /
        radialDenom δ (fun a => naturalCanonicalFlux d g a x) ∂potentialMeasure d.potential) := by
  let u := naturalCanonicalFlux d g
  let f (x : Space n) := radialDenom δ (fun a => u a x)
  let ν := potentialMeasure d.potential
  let T (i j a : Fin n) (x : Space n) : ℝ :=
    ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
      compactRadialMatrixDerivative χ δ u Du i j a x
  let R (i j : Fin n) (x : Space n) : ℝ :=
    (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) *
      compactRadialMatrixTest χ δ u i j x
  have ht (i j : Fin n) := actual_compact_radial_hessian_evolution d hδ hχ hc hb
    (naturalCanonicalFlux_local_L2 d g) hDu hw i j
  have hT (i j a : Fin n) : Integrable (T i j a) ν := (ht i j).1 a
  have hR (i j : Fin n) : Integrable (R i j) ν := (ht i j).2.1
  obtain ⟨hX, hE, hB, hH, hP, hG⟩ :=
    actual_compact_radial_connection_fields_integrable d g hδ Du hDu hχ hc
  change Integrable (fun x => χ x ^ 2 * sourceConnectionCross d u Du x / f x) ν at hX
  change Integrable (fun x => χ x ^ 2 * sourceRadialExtra d u Du x / f x ^ 2) ν at hE
  change Integrable (fun x => χ x * sourceConnectionBoundary d χ u x / f x) ν at hB
  change Integrable (fun x => χ x ^ 2 * sourceVectorMass d.potential u x / f x) ν at hH
  change Integrable (fun x => χ x ^ 2 * sourceConnectionTarget d u x / f x) ν at hP
  change Integrable (fun x => χ x ^ 2 * sourceConnectionGamma d u x / f x) ν at hG
  have hLT : (∫ x, ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, T i j a x ∂ν) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∫ x, T i j a x ∂ν := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun a _ => hT i j a)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum Finset.univ (fun a _ => hT i j a))]
    exact Finset.sum_congr rfl fun j _ => integral_finsetSum _ (fun a _ => hT i j a)
  have hRT : (∫ x, ∑ i : Fin n, ∑ j : Fin n, R i j x ∂ν) =
      ∑ i : Fin n, ∑ j : Fin n, ∫ x, R i j x ∂ν := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hR i j))]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ (fun j _ => hR i j)
  have hsum : -(∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∫ x, T i j a x ∂ν) =
      ∑ i : Fin n, ∑ j : Fin n, ∫ x, R i j x ∂ν := by
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n, -(∑ a : Fin n, ∫ x, T i j a x ∂ν) := by
        simp only [Finset.sum_neg_distrib]
      _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (ht i j).2.2
  have hTx (x : Space n) : (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, T i j a x) =
      χ x ^ 2 * sourceConnectionCross d u Du x / f x -
        (2 * δ) * (χ x ^ 2 * sourceRadialExtra d u Du x / f x ^ 2) +
        2 * (χ x * sourceConnectionBoundary d χ u x / f x) := by
    have hpoint (i j a : Fin n) : T i j a x =
        χ x ^ 2 * (((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
          (Du i a x * u j x + u i x * Du j a x)) / f x -
        (2 * δ) * (χ x ^ 2 * (((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
          (u i x * u j x) * (∑ k : Fin n, u k x * Du k a x)) / f x ^ 2) +
        2 * (χ x * (((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
          (u i x * u j x) * coordinateDerivative χ a x) / f x) := by
      dsimp only [T, compactRadialMatrixDerivative, rawCutoffDerivative, radialRawDerivative,
        radialMatrixEntry, f]
      rw [coordinateDerivative_square hχ]
      ring
    simp_rw [hpoint]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div,
      sourceConnectionCross, sourceRadialExtra, sourceConnectionBoundary]
  have hRx (x : Space n) : (∑ i : Fin n, ∑ j : Fin n, R i j x) =
      (-χ x ^ 2 * sourceVectorMass d.potential u x / f x +
        χ x ^ 2 * sourceConnectionTarget d u x / f x) +
        χ x ^ 2 * sourceConnectionGamma d u x / f x := by
    calc
      _ = -χ x ^ 2 * sourceVectorMass d.potential u x / f x +
          χ x ^ 2 * (∑ i : Fin n, ∑ j : Fin n,
            sourceConnectionCurvature d x i j * u i x * u j x) / f x := by
        simp only [sourceVectorMass, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [R, compactRadialMatrixTest, radialMatrixEntry]
        ring
      _ = _ := by rw [sourceConnectionCurvature_contraction]; ring
  have hLI : (∫ x, ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, T i j a x ∂ν) =
      (∫ x, χ x ^ 2 * sourceConnectionCross d u Du x / f x ∂ν) -
        (2 * δ) * (∫ x, χ x ^ 2 * sourceRadialExtra d u Du x / f x ^ 2 ∂ν) +
        2 * (∫ x, χ x * sourceConnectionBoundary d χ u x / f x ∂ν) := by
    calc
      _ = ∫ x, (χ x ^ 2 * sourceConnectionCross d u Du x / f x -
          (2 * δ) * (χ x ^ 2 * sourceRadialExtra d u Du x / f x ^ 2)) +
          2 * (χ x * sourceConnectionBoundary d χ u x / f x) ∂ν :=
        integral_congr_ae (Eventually.of_forall hTx)
      _ = _ := by
        have hmid : Integrable (fun x => χ x ^ 2 * sourceConnectionCross d u Du x / f x -
            (2 * δ) * (χ x ^ 2 * sourceRadialExtra d u Du x / f x ^ 2)) ν :=
          hX.sub (hE.const_mul (2 * δ))
        rw [integral_add hmid (hB.const_mul 2), integral_sub hX (hE.const_mul (2 * δ)),
          integral_const_mul, integral_const_mul]
  have hRI : (∫ x, ∑ i : Fin n, ∑ j : Fin n, R i j x ∂ν) =
      (-(∫ x, χ x ^ 2 * sourceVectorMass d.potential u x / f x ∂ν) +
        (∫ x, χ x ^ 2 * sourceConnectionTarget d u x / f x ∂ν)) +
        ∫ x, χ x ^ 2 * sourceConnectionGamma d u x / f x ∂ν := by
    calc
      _ = ∫ x, (-χ x ^ 2 * sourceVectorMass d.potential u x / f x +
          χ x ^ 2 * sourceConnectionTarget d u x / f x) +
          χ x ^ 2 * sourceConnectionGamma d u x / f x ∂ν :=
        integral_congr_ae (Eventually.of_forall hRx)
      _ = _ := by
        have hn : Integrable (fun x => -χ x ^ 2 * sourceVectorMass d.potential u x / f x) ν := by
          apply hH.neg.congr
          exact Eventually.of_forall fun x => by
            change -(χ x ^ 2 * sourceVectorMass d.potential u x / f x) =
              -χ x ^ 2 * sourceVectorMass d.potential u x / f x
            ring
        have hnp : Integrable (fun x => -χ x ^ 2 * sourceVectorMass d.potential u x / f x +
            χ x ^ 2 * sourceConnectionTarget d u x / f x) ν := hn.add hP
        rw [integral_add hnp hG, integral_add hn hP]
        have hni : (∫ x, -χ x ^ 2 * sourceVectorMass d.potential u x / f x ∂ν) =
            -(∫ x, χ x ^ 2 * sourceVectorMass d.potential u x / f x ∂ν) := by
          simpa only [Pi.neg_apply, neg_mul, neg_div] using
            integral_neg (fun x => χ x ^ 2 * sourceVectorMass d.potential u x / f x)
        rw [hni]
  have hPG : (∫ x, χ x ^ 2 * (sourceConnectionTarget d u x + sourceConnectionGamma d u x) /
      f x ∂ν) = (∫ x, χ x ^ 2 * sourceConnectionTarget d u x / f x ∂ν) +
        ∫ x, χ x ^ 2 * sourceConnectionGamma d u x / f x ∂ν := by
    simp only [mul_add, add_div]
    exact integral_add hP hG
  rw [← hLT, ← hRT, hLI, hRI] at hsum
  rw [hPG]
  linarith

end KLSConstantImprovement.ActualSourceRadialConnectionBalance405
#print axioms KLSConstantImprovement.ActualSourceRadialConnectionBalance405.actual_compact_radial_connection_balance
