import Mathlib

/-! A genuine two-factor Efron--Stein inequality for bounded measurable
functions on arbitrary probability-product measures. No variance inequality is
assumed. The integrability hypotheses are derived from the displayed bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.Tensorization
set_option maxHeartbeats 2000000

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem product_variance_efron_stein_two (f : α × β → ℝ)
    (hf : StronglyMeasurable f) {C : ℝ} (hbound : ∀ p, ‖f p‖ ≤ C) :
    variance f (μ.prod ν) ≤
      (∫ x, variance (fun y => f (x,y)) ν ∂μ)+
      (∫ y, variance (fun x => f (x,y)) μ ∂ν) := by
  let G : α → ℝ := fun x => ∫ y, f (x,y) ∂ν
  let H : β → ℝ := fun y => ∫ x, f (x,y) ∂μ
  let GP : α × β → ℝ := fun p => G p.1
  let HP : α × β → ℝ := fun p => H p.2
  have hGsm : StronglyMeasurable G := hf.integral_prod_right'
  have hHsm : StronglyMeasurable H := hf.integral_prod_left'
  have hGb (x : α) : ‖G x‖ ≤ C := by
    simpa [G] using (norm_integral_le_of_norm_le_const
      (μ := ν) (f := fun y => f (x,y)) (.of_forall fun y => hbound (x,y)))
  have hHb (y : β) : ‖H y‖ ≤ C := by
    simpa [H] using (norm_integral_le_of_norm_le_const
      (μ := μ) (f := fun x => f (x,y)) (.of_forall fun x => hbound (x,y)))
  have hF : MemLp f 2 (μ.prod ν) :=
    MemLp.of_bound hf.aestronglyMeasurable C (.of_forall hbound)
  have hG : MemLp G 2 μ := MemLp.of_bound hGsm.aestronglyMeasurable C (.of_forall hGb)
  have hH : MemLp H 2 ν := MemLp.of_bound hHsm.aestronglyMeasurable C (.of_forall hHb)
  have hGP : MemLp GP 2 (μ.prod ν) := hG.comp_fst ν
  have hHP : MemLp HP 2 (μ.prod ν) := hH.comp_snd μ
  have hFy (x : α) : MemLp (fun y => f (x,y)) 2 ν :=
    MemLp.of_bound (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable C
      (.of_forall fun y => hbound (x,y))
  have hFx (y : β) : MemLp (fun x => f (x,y)) 2 μ :=
    MemLp.of_bound (hf.comp_measurable measurable_prodMk_right).aestronglyMeasurable C
      (.of_forall fun x => hbound (x,y))
  have hmeanG : (∫ p, f p ∂μ.prod ν) = ∫ x, G x ∂μ :=
    integral_prod f (hF.integrable (by norm_num))
  have hmeanH : (∫ p, f p ∂μ.prod ν) = ∫ y, H y ∂ν :=
    integral_prod_symm f (hF.integrable (by norm_num))
  have hmeanGP : (∫ p, GP p ∂μ.prod ν) = ∫ x, G x ∂μ := by
    rw [integral_prod GP (hGP.integrable (by norm_num))]
    simp [GP]
  have hmeanHP : (∫ p, HP p ∂μ.prod ν) = ∫ y, H y ∂ν := by
    rw [integral_prod_symm HP (hHP.integrable (by norm_num))]
    simp [HP]
  have hsquareGP : (∫ p, (GP p)^2 ∂μ.prod ν) = ∫ x, (G x)^2 ∂μ := by
    rw [integral_prod (fun p => (GP p)^2) hGP.integrable_sq]
    simp [GP]
  have hsquareHP : (∫ p, (HP p)^2 ∂μ.prod ν) = ∫ y, (H y)^2 ∂ν := by
    rw [integral_prod_symm (fun p => (HP p)^2) hHP.integrable_sq]
    simp [HP]
  have hmulG : (∫ p, f p*GP p ∂μ.prod ν) = ∫ x, (G x)^2 ∂μ := by
    rw [integral_prod (fun p => f p*GP p) (hF.integrable_mul hGP)]
    simp only [GP, integral_mul_const]
    congr 1
    funext x
    change (∫ y, f (x,y) ∂ν)*(∫ y, f (x,y) ∂ν) = _
    simp only [G, pow_two]
  have hmulH : (∫ p, f p*HP p ∂μ.prod ν) = ∫ y, (H y)^2 ∂ν := by
    rw [integral_prod_symm (fun p => f p*HP p) (hF.integrable_mul hHP)]
    simp only [HP, integral_mul_const]
    congr 1
    funext y
    change (∫ x, f (x,y) ∂μ)*(∫ x, f (x,y) ∂μ) = _
    simp only [H, pow_two]
  have hcovG : covariance f GP (μ.prod ν) = variance GP (μ.prod ν) := by
    rw [covariance_eq_sub hF hGP, variance_eq_sub hGP]
    change (∫ p, f p*GP p ∂μ.prod ν)-
      (∫ p, f p ∂μ.prod ν)*(∫ p, GP p ∂μ.prod ν) =
      (∫ p, (GP p)^2 ∂μ.prod ν)-(∫ p, GP p ∂μ.prod ν)^2
    rw [hmulG, hsquareGP, hmeanG, hmeanGP]
    ring
  have hcovH : covariance f HP (μ.prod ν) = variance HP (μ.prod ν) := by
    rw [covariance_eq_sub hF hHP, variance_eq_sub hHP]
    change (∫ p, f p*HP p ∂μ.prod ν)-
      (∫ p, f p ∂μ.prod ν)*(∫ p, HP p ∂μ.prod ν) =
      (∫ p, (HP p)^2 ∂μ.prod ν)-(∫ p, HP p ∂μ.prod ν)^2
    rw [hmulH, hsquareHP, hmeanH, hmeanHP]
    ring
  have hcovGH : covariance GP HP (μ.prod ν) = 0 := covariance_fst_snd_prod hG hH
  have hres := variance_nonneg (f-GP-HP) (μ.prod ν)
  rw [variance_sub (hF.sub hGP) hHP, variance_sub hF hGP,
    covariance_sub_left hF hGP hHP, hcovG, hcovH, hcovGH] at hres
  have hcondG : (∫ x, variance (fun y => f (x,y)) ν ∂μ) =
      variance f (μ.prod ν)-variance GP (μ.prod ν) := by
    have hv (x : α) : variance (fun y => f (x,y)) ν =
        (∫ y, (f (x,y))^2 ∂ν)-(G x)^2 := variance_eq_sub (hFy x)
    simp_rw [hv]
    rw [integral_sub hF.integrable_sq.integral_prod_left hG.integrable_sq,
      ← integral_prod (fun p => (f p)^2) hF.integrable_sq,
      variance_eq_sub hF, variance_eq_sub hGP]
    change _ = ((∫ p, (f p)^2 ∂μ.prod ν)-(∫ p, f p ∂μ.prod ν)^2)-
      ((∫ p, (GP p)^2 ∂μ.prod ν)-(∫ p, GP p ∂μ.prod ν)^2)
    rw [hsquareGP, hmeanG, hmeanGP]
    ring
  have hcondH : (∫ y, variance (fun x => f (x,y)) μ ∂ν) =
      variance f (μ.prod ν)-variance HP (μ.prod ν) := by
    have hv (y : β) : variance (fun x => f (x,y)) μ =
        (∫ x, (f (x,y))^2 ∂μ)-(H y)^2 := variance_eq_sub (hFx y)
    simp_rw [hv]
    rw [integral_sub hF.integrable_sq.integral_prod_right hH.integrable_sq,
      ← integral_prod_symm (fun p => (f p)^2) hF.integrable_sq,
      variance_eq_sub hF, variance_eq_sub hHP]
    change _ = ((∫ p, (f p)^2 ∂μ.prod ν)-(∫ p, f p ∂μ.prod ν)^2)-
      ((∫ p, (HP p)^2 ∂μ.prod ν)-(∫ p, HP p ∂μ.prod ν)^2)
    rw [hsquareHP, hmeanH, hmeanHP]
    ring
  rw [hcondG, hcondH]
  linarith

end KLSImprovement.Tensorization

#print axioms KLSImprovement.Tensorization.product_variance_efron_stein_two
