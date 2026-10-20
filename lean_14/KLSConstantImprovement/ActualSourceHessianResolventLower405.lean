import KLSConstantImprovement.ActualSourceL1ResolventLower405
import KLSConstantImprovement.ActualSourceHessianFormEquation405
import KLSConstantImprovement.ActualSourceMatrixResolvent405
import KLSConstantImprovement.ActualSourceCurvatureMean405

/-!
Actual K=R1 H satisfies 2K-H >= 0. All scalar form representatives,
compact evolution identities, L1 forcing, forcing positivity and matrix
means are supplied by the constructed canonical source. The final AE
matrix assertion uses only a countable rational intersection followed by
continuity. No order certificate, L2 curvature or generator domain is an
input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators ContDiff Topology RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceHessianResolventLower405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualSourceHessianEvolution405 ActualSourceCurvatureDomains405 ActualSourceCurvatureMean405
open ActualSourceConservativeResolvent405 ActualSourceMatrixResolvent405
open ActualSourceHessianFormEquation405 ActualSourceL1ResolventLower405
variable {n : ℕ} {μ : Measure (Space n)}

def constantMatrixContraction (v : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (v i * v j) * A i j

theorem constantMatrixContraction_eq_dot (v : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    constantMatrixContraction v A = v ⬝ᵥ (A *ᵥ v) := by
  simp only [constantMatrixContraction, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integral_constantMatrixContraction {ρ : Measure (Space n)}
    (A : Space n → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, Integrable (fun x => A x i j) ρ) (v : Fin n → ℝ) :
    (∫ x, constantMatrixContraction v (A x) ∂ρ) =
      ∑ i, ∑ j, (v i * v j) * ∫ x, A x i j ∂ρ := by
  unfold constantMatrixContraction
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hA i j).const_mul (v i * v j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => (hA i j).const_mul (v i * v j))]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

def actualHessianQuadraticForm (d : SourceData μ) (v : Fin n → ℝ) :
    CanonicalMetricH1 d.potential := ∑ i, ∑ j, (v i * v j) • actualHessianForm d i j

def actualCurvatureQuadratic (d : SourceData μ) (v : Fin n → ℝ) (x : Space n) : ℝ :=
  constantMatrixContraction v (sourceConnectionCurvature d x)

theorem actualHessianQuadraticLp_ae (d : SourceData μ) (v : Fin n → ℝ) :
    (matrixQuadraticLp d (sourceHessianLp d) v : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => constantMatrixContraction v (coordinateHessian d.potential x) := by
  filter_upwards [matrixQuadraticLp_ae d (sourceHessianLp d) v, sourceHessianLp_ae d]
    with x hx hy
  rw [hx, hy, constantMatrixContraction_eq_dot]

theorem actualHessianQuadraticForm_value (d : SourceData μ) (v : Fin n → ℝ) :
    letI := d.source_probability
    canonicalMetricValue d.potential (actualHessianQuadraticForm d v) =
      CenteredL2.center (potentialMeasure d.potential) (matrixQuadraticLp d (sourceHessianLp d) v) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hentry (i j : Fin n) : canonicalMetricValue d.potential (actualHessianForm d i j) =
      CenteredL2.center (potentialMeasure d.potential) (sourceHessianLp d i j) :=
    actualHessianForm_value d i j
  calc
    _ = ∑ i, ∑ j, (v i * v j) • canonicalMetricValue d.potential (actualHessianForm d i j) := by
      simp only [actualHessianQuadraticForm, map_sum, map_smul]
    _ = ∑ i, ∑ j, (v i * v j) • CenteredL2.center (potentialMeasure d.potential)
        (sourceHessianLp d i j) := by simp_rw [hentry]
    _ = _ := by
      conv_rhs => rw [← CenteredL2.centerCLM_apply]
      simp only [matrixQuadraticLp, map_sum, map_smul, CenteredL2.centerCLM_apply]

theorem actualCurvatureQuadratic_integrable (d : SourceData μ) (v : Fin n → ℝ) :
    Integrable (actualCurvatureQuadratic d v) (potentialMeasure d.potential) :=
  integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
    (fun j _ => (actual_connection_curvature_entry_integrable d i j).const_mul (v i * v j)))

theorem actualCurvatureQuadratic_nonneg (d : SourceData μ) (v : Fin n → ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ actualCurvatureQuadratic d v x := by
  filter_upwards [actual_source_connection_curvature_positive d] with x hx
  rw [actualCurvatureQuadratic, constantMatrixContraction_eq_dot]
  simpa only [star_trivial] using hx.dotProduct_mulVec_nonneg v

theorem actualCurvatureQuadratic_mean (d : SourceData μ) (v : Fin n → ℝ) :
    (∫ x, actualCurvatureQuadratic d v x ∂potentialMeasure d.potential) =
      ∫ x, matrixQuadraticLp d (sourceHessianLp d) v x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  calc
    _ = ∑ i, ∑ j, (v i * v j) * ∫ x, sourceConnectionCurvature d x i j
        ∂potentialMeasure d.potential :=
      integral_constantMatrixContraction _ (actual_connection_curvature_entry_integrable d) v
    _ = ∑ i, ∑ j, (v i * v j) * ∫ x, coordinateHessian d.potential x i j
        ∂potentialMeasure d.potential := by
      simp_rw [(actual_connection_curvature_entry_mean d _ _).2]
    _ = ∫ x, constantMatrixContraction v (coordinateHessian d.potential x)
        ∂potentialMeasure d.potential :=
      (integral_constantMatrixContraction _
        (fun i j => (d.hessian_entry_memLp i j 1).integrable le_rfl) v).symm
    _ = _ := integral_congr_ae (actualHessianQuadraticLp_ae d v).symm

theorem actualHessianQuadraticForm_compact_evolution (d : SourceData μ) (v : Fin n → ℝ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ)
    (V : CanonicalMetricH1 d.potential)
    (hVd : ∀ i : Fin n, (canonicalMetricGradient d.potential i V : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] canonicalMetricDerivative d.potential ψ i) :
    canonicalMetricEnergy d.potential (actualHessianQuadraticForm d v) V =
      ∫ x, (matrixQuadraticLp d (sourceHessianLp d) v x - actualCurvatureQuadratic d v x) *
        ψ x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hψ2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hψ.continuous hc
  obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hc
  let A : Space n → Matrix (Fin n) (Fin n) ℝ := fun x => Matrix.of fun i j =>
    (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) * ψ x
  have hA (i j : Fin n) : Integrable (fun x => A x i j) (potentialMeasure d.potential) := by
    have hHψ : Integrable (fun x => coordinateHessian d.potential x i j * ψ x)
        (potentialMeasure d.potential) := (d.hessian_entry_memLp i j 2).integrable_mul hψ2
    have hSψ : Integrable (fun x => sourceConnectionCurvature d x i j * ψ x)
        (potentialMeasure d.potential) := (actual_connection_curvature_entry_integrable d i j).mul_bdd
      hψ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
    exact (hHψ.sub hSψ).congr (Eventually.of_forall fun x => by
      change coordinateHessian d.potential x i j * ψ x - sourceConnectionCurvature d x i j * ψ x =
        (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) * ψ x
      ring)
  have hlinear : canonicalMetricEnergy d.potential (actualHessianQuadraticForm d v) V =
      ∑ i, ∑ j, (v i * v j) * canonicalMetricEnergy d.potential (actualHessianForm d i j) V := by
    let E : CanonicalMetricH1 d.potential →L[ℝ] ℝ := (canonicalMetricEnergy d.potential).flip V
    change E (∑ i, ∑ j, (v i * v j) • actualHessianForm d i j) =
      ∑ i, ∑ j, (v i * v j) * E (actualHessianForm d i j)
    calc
      _ = ∑ i, E (∑ j, (v i * v j) • actualHessianForm d i j) :=
        map_sum E.toLinearMap _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          _ = ∑ j, E ((v i * v j) • actualHessianForm d i j) := map_sum E.toLinearMap _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro j _
            exact E.map_smul (v i * v j) (actualHessianForm d i j)
  calc
    _ = ∑ i, ∑ j, (v i * v j) * ∫ x, A x i j ∂potentialMeasure d.potential := by
      rw [hlinear]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [actual_hessian_form_compact_evolution d i j (hψ.of_le (by norm_num)) hc V hVd]
      rfl
    _ = ∫ x, constantMatrixContraction v (A x) ∂potentialMeasure d.potential :=
      (integral_constantMatrixContraction A hA v).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [actualHessianQuadraticLp_ae d v] with x hx
      rw [hx]
      simp only [A, actualCurvatureQuadratic, constantMatrixContraction, Matrix.of_apply,
        mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]

/-- This is the actual source-Hessian comparison, with every L1/form
evolution premise instantiated from SourceData. -/
theorem actualHessianResolvent_quadratic_lower (d : SourceData μ) (v : Fin n → ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      v ⬝ᵥ (coordinateHessian d.potential x *ᵥ v) ≤
        2 * (v ⬝ᵥ (matrixFieldValue d (sourceMatrixResolvent d (sourceHessianLp d)) x *ᵥ v)) := by
  have hl := fullR1_twice_ge_of_actual_L1_form_evolution d
    (matrixQuadraticLp d (sourceHessianLp d) v) (actualHessianQuadraticForm d v)
    (actualCurvatureQuadratic d v) (actualCurvatureQuadratic_integrable d v)
    (actualCurvatureQuadratic_nonneg d v) (actualCurvatureQuadratic_mean d v)
    (actualHessianQuadraticForm_value d v)
    (fun ψ hψ hc V _ hd => actualHessianQuadraticForm_compact_evolution d v hψ hc V hd)
  rw [← sourceMatrixResolvent_quadratic d (sourceHessianLp d) v] at hl
  filter_upwards [hl, actualHessianQuadraticLp_ae d v,
    matrixQuadraticLp_ae d (sourceMatrixResolvent d (sourceHessianLp d)) v] with x hx hh hk
  rw [hh, constantMatrixContraction_eq_dot, hk] at hx
  exact hx

/-- The natural boundary-domain Loewner bound for the actual matrix
resolvent, obtained by L1 variational comparison. -/
theorem actualHessianResolvent_twice_sub_H_posSemidef (d : SourceData μ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      ((2 : ℝ) • matrixFieldValue d (sourceMatrixResolvent d (sourceHessianLp d)) x -
        coordinateHessian d.potential x).PosSemidef := by
  have hrat : ∀ᵐ x ∂potentialMeasure d.potential, ∀ q : Fin n → ℚ,
      (fun i => (q i : ℝ)) ⬝ᵥ (coordinateHessian d.potential x *ᵥ fun i => (q i : ℝ)) ≤
        2 * ((fun i => (q i : ℝ)) ⬝ᵥ
          (matrixFieldValue d (sourceMatrixResolvent d (sourceHessianLp d)) x *ᵥ fun i => (q i : ℝ))) :=
    ae_all_iff.mpr fun q => actualHessianResolvent_quadratic_lower d (fun i => (q i : ℝ))
  have hdense : DenseRange (fun q : Fin n → ℚ => fun i => (q i : ℝ)) := by
    have hd : DenseRange (Pi.map (fun _ : Fin n => fun q : ℚ => (q : ℝ))) :=
      DenseRange.piMap (fun _ : Fin n =>
        (Rat.denseRange_cast : DenseRange (fun q : ℚ => (q : ℝ))))
    have he : Pi.map (fun _ : Fin n => fun q : ℚ => (q : ℝ)) =
        (fun q : Fin n → ℚ => fun i => (q i : ℝ)) := by funext q i; rfl
    rw [he] at hd
    exact hd
  filter_upwards [hrat, actualHessianResolvent_posSemidef d, d.hessian_ae_source] with x hq hK hH
  let A := (2 : ℝ) • matrixFieldValue d (sourceMatrixResolvent d (sourceHessianLp d)) x -
    coordinateHessian d.potential x
  have hsym : A.IsSymm := by
    change A.transpose = A
    dsimp only [A]
    rw [Matrix.transpose_sub, Matrix.transpose_smul, hK.isHermitian.isSymm.eq, hH.1.isHermitian.isSymm.eq]
  have hquad (v : Fin n → ℝ) : v ⬝ᵥ (A *ᵥ v) =
      2 * (v ⬝ᵥ (matrixFieldValue d (sourceMatrixResolvent d (sourceHessianLp d)) x *ᵥ v)) -
        v ⬝ᵥ (coordinateHessian d.potential x *ᵥ v) := by
    simp only [A, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_iff_isSymm.mpr hsym)
  intro v
  simp only [star_trivial]
  exact hdense.induction_on (p := fun w : Fin n → ℝ => 0 ≤ w ⬝ᵥ (A *ᵥ w)) v
    (isClosed_le continuous_const (by fun_prop))
    (fun q => by rw [hquad]; exact sub_nonneg.mpr (hq q))

end KLSConstantImprovement.ActualSourceHessianResolventLower405

#print axioms KLSConstantImprovement.ActualSourceHessianResolventLower405.actualHessianQuadraticForm_value
#print axioms KLSConstantImprovement.ActualSourceHessianResolventLower405.actualHessianQuadraticForm_compact_evolution
#print axioms KLSConstantImprovement.ActualSourceHessianResolventLower405.actualHessianResolvent_quadratic_lower
#print axioms KLSConstantImprovement.ActualSourceHessianResolventLower405.actualHessianResolvent_twice_sub_H_posSemidef
