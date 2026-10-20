import KLSConstantImprovement.ActualSourceBoundedMassBochner405
import KLS.MatrixEntryLpProducts

/-! Actual global L2 coordinates of the natural canonical Hessian and
its whitened form. The ordinary Hessian is reconstructed with globally
bounded positive roots, paying the domains needed for global source
Stein tests. Bounded mass remains explicit only in the final constructor. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualSourceNaturalWhitenedHessian405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalHessian405 ActualSourceBoundedMassBochner405
open ActualSourceNaturalGaffney405 ActualSourceLimitFluxDomains405 ActualSourceNaturalTargetCurvatureDomain405
open ActualSourceConnectionPointwise405 ActualSourceConnectionFields405 ActualSourceLocalizedGaffney405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricOrdinaryGraph ActualSourceMetricFaithfulness405
open ActualCompatibleConnectionYoung405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def naturalWhitenedHessian (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  canonicalMetricRoot d.potential x * naturalCanonicalHessian d g Du x * canonicalMetricRoot d.potential x

theorem naturalWhitenedHessian_local_L2 (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (Du : Fin n → Fin n → Space n → ℝ)
    (hC : ∀ i j E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i j) 2 (volume.restrict E))
    (i j : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (fun x => naturalWhitenedHessian d g Du x i j) 2 (volume.restrict E) := by
  have hR (a b : Fin n) : MemLp (fun x => canonicalMetricRoot d.potential x a b) ∞ (volume.restrict E) :=
    actualRoot_entry_top_on_compact d hE a b
  have hRC (a b : Fin n) : MemLp (fun x =>
      (canonicalMetricRoot d.potential x * naturalCanonicalHessian d g Du x) a b) 2 (volume.restrict E) :=
    memLp_matrix_mul_entries (p := ∞) (q := 2) (r := 2) hR (fun a b => hC a b E hE) a b
  exact memLp_matrix_mul_entries (p := 2) (q := ∞) (r := 2) hRC hR i j

theorem naturalWhitenedHessian_square_eq_energy_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (Du : Fin n → Fin n → Space n → ℝ)
    (hC : ∀ᵐ x ∂potentialMeasure d.potential, (naturalCanonicalHessian d g Du x).IsSymm) :
    (fun x => matrixFrobeniusSq (naturalWhitenedHessian d g Du x)) =ᵐ[potentialMeasure d.potential]
      naturalCanonicalHessianEnergy d g Du := by
  filter_upwards [d.hessian_ae_source, hC] with x hp hc
  exact whitened_connection_square (coordinateHessian d.potential x) (naturalCanonicalHessian d g Du x) hp.1 hc

theorem naturalWhitenedHessian_entry_memLp (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (Du : Fin n → Fin n → Space n → ℝ)
    (hCloc : ∀ i j E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i j) 2 (volume.restrict E))
    (hCsym : ∀ᵐ x ∂potentialMeasure d.potential, (naturalCanonicalHessian d g Du x).IsSymm)
    (hE : Integrable (naturalCanonicalHessianEnergy d g Du) (potentialMeasure d.potential)) (i j : Fin n) :
    MemLp (fun x => naturalWhitenedHessian d g Du x i j) 2 (potentialMeasure d.potential) := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  have hm : AEStronglyMeasurable (fun x => naturalWhitenedHessian d g Du x i j) (potentialMeasure d.potential) :=
    (locallyIntegrable_of_memLp_two_on_compacts (naturalWhitenedHessian_local_L2 d g Du hCloc i j)).aestronglyMeasurable.mono_ac hac
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply hE.mono' (hm.pow 2)
  filter_upwards [naturalWhitenedHessian_square_eq_energy_ae d g Du hCsym] with x hx
  change ‖naturalWhitenedHessian d g Du x i j ^ 2‖ ≤ naturalCanonicalHessianEnergy d g Du x
  rw [Real.norm_of_nonneg (sq_nonneg _), ← hx]
  have hrow : naturalWhitenedHessian d g Du x i j ^ 2 ≤
      ∑ b : Fin n, naturalWhitenedHessian d g Du x i b ^ 2 :=
    Finset.single_le_sum (fun b _ => sq_nonneg (naturalWhitenedHessian d g Du x i b)) (Finset.mem_univ j)
  have hall : (∑ b : Fin n, naturalWhitenedHessian d g Du x i b ^ 2) ≤
      matrixFrobeniusSq (naturalWhitenedHessian d g Du x) :=
    Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg (naturalWhitenedHessian d g Du x a b))
      (Finset.mem_univ i)
  exact hrow.trans hall

theorem naturalCanonicalHessian_reconstruct_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (Du : Fin n → Fin n → Space n → ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential, naturalCanonicalHessian d g Du x =
      canonicalMetricUnroot d.potential x * naturalWhitenedHessian d g Du x * canonicalMetricUnroot d.potential x := by
  filter_upwards [d.hessian_ae_source] with x hp
  let R := canonicalMetricRoot d.potential x
  let S := canonicalMetricUnroot d.potential x
  let C := naturalCanonicalHessian d g Du x
  change C = S * (R * C * R) * S
  have hSR : S * R = 1 := canonicalMetricUnroot_mul_root_at hp.1
  have hRS : R * S = 1 := canonicalMetricRoot_mul_unroot_at hp.1
  calc
    _ = (S * R) * C * (R * S) := by rw [hSR, hRS, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem naturalCanonicalHessian_entry_memLp (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (Du : Fin n → Fin n → Space n → ℝ)
    (hCloc : ∀ i j E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i j) 2 (volume.restrict E))
    (hCsym : ∀ᵐ x ∂potentialMeasure d.potential, (naturalCanonicalHessian d g Du x).IsSymm)
    (hE : Integrable (naturalCanonicalHessianEnergy d g Du) (potentialMeasure d.potential)) (i j : Fin n) :
    MemLp (fun x => naturalCanonicalHessian d g Du x i j) 2 (potentialMeasure d.potential) := by
  have hW (a b : Fin n) : MemLp (fun x => naturalWhitenedHessian d g Du x a b) 2
      (potentialMeasure d.potential) := naturalWhitenedHessian_entry_memLp d g Du hCloc hCsym hE a b
  have hS (a b : Fin n) : MemLp (fun x => canonicalMetricUnroot d.potential x a b) ∞
      (potentialMeasure d.potential) := actualUnroot_entry_memLp_top d a b
  have hSW (a b : Fin n) : MemLp (fun x =>
      (canonicalMetricUnroot d.potential x * naturalWhitenedHessian d g Du x) a b) 2
      (potentialMeasure d.potential) :=
    memLp_matrix_mul_entries (p := ∞) (q := 2) (r := 2) hS hW a b
  have hm : MemLp (fun x => (canonicalMetricUnroot d.potential x * naturalWhitenedHessian d g Du x *
      canonicalMetricUnroot d.potential x) i j) 2 (potentialMeasure d.potential) :=
    memLp_matrix_mul_entries (p := 2) (q := ∞) (r := 2) hSW hS i j
  apply (memLp_congr_ae ?_).mp hm
  filter_upwards [naturalCanonicalHessian_reconstruct_ae d g Du] with x hx
  exact (congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hx).symm

/-- The ordinary Hessian and whitened response are constructed from the
same actual inverse; their weak derivative and global L2 domains are paid.
The bounded mass hypothesis must still be proved for each polynomial data. -/
theorem exists_naturalHessian_global_L2_of_mass_bound (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C) :
    ∃ Du : Fin n → Fin n → Space n → ℝ,
      (∀ i j, MemLp (fun x => naturalWhitenedHessian d g Du x i j) 2 (potentialMeasure d.potential)) ∧
      (∀ i j, MemLp (fun x => naturalCanonicalHessian d g Du x i j) 2 (potentialMeasure d.potential)) ∧
      (∀ i j, HasLocalWeakCoordinateDerivative (naturalCanonicalRawGradient d g i)
        (fun x => naturalCanonicalHessian d g Du x i j) j) ∧
      (∫ x, matrixFrobeniusSq (naturalWhitenedHessian d g Du x) ∂potentialMeasure d.potential) ≤ ‖g‖ ^ 2 := by
  obtain ⟨Du, _, _, _, hCloc, hw, hCsym, hEi, _, hPi, hbound⟩ :=
    exists_naturalCanonicalHessian_bochner_of_mass_bound d hn g hg hC hM
  refine ⟨Du, naturalWhitenedHessian_entry_memLp d g Du hCloc hCsym hEi,
    naturalCanonicalHessian_entry_memLp d g Du hCloc hCsym hEi, hw, ?_⟩
  have hPnonneg : 0 ≤ ∫ x, sourceConnectionTarget d (naturalCanonicalFlux d g) x ∂potentialMeasure d.potential :=
    integral_nonneg_of_ae (sourceConnectionTarget_nonnegative_ae d (naturalCanonicalFlux d g))
  have he : (∫ x, matrixFrobeniusSq (naturalWhitenedHessian d g Du x) ∂potentialMeasure d.potential) =
      ∫ x, naturalCanonicalHessianEnergy d g Du x ∂potentialMeasure d.potential :=
    integral_congr_ae (naturalWhitenedHessian_square_eq_energy_ae d g Du hCsym)
  rw [integral_add hEi hPi] at hbound
  rw [he]
  linarith

end KLSConstantImprovement.ActualSourceNaturalWhitenedHessian405
#print axioms KLSConstantImprovement.ActualSourceNaturalWhitenedHessian405.naturalWhitenedHessian_local_L2
#print axioms KLSConstantImprovement.ActualSourceNaturalWhitenedHessian405.naturalWhitenedHessian_square_eq_energy_ae
#print axioms KLSConstantImprovement.ActualSourceNaturalWhitenedHessian405.naturalWhitenedHessian_entry_memLp
#print axioms KLSConstantImprovement.ActualSourceNaturalWhitenedHessian405.naturalCanonicalHessian_reconstruct_ae
#print axioms KLSConstantImprovement.ActualSourceNaturalWhitenedHessian405.naturalCanonicalHessian_entry_memLp
#print axioms KLSConstantImprovement.ActualSourceNaturalWhitenedHessian405.exists_naturalHessian_global_L2_of_mass_bound
