import ProductExponentialPoincare

/-! Finite-dimensional tensorization with explicitly measurable bounded energies.
The auxiliary theorem accepts coordinate slice estimates; the exponential
specialization discharges these with the proved actual scalar compact core. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.Tensorization
open KLSImprovement.Exponential
set_option maxHeartbeats 4000000
local instance : IsProbabilityMeasure law := isProbabilityMeasure_expMeasure (by norm_num)
abbrev productLaw (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi (fun _ => law)

lemma cons_measurable {n : ℕ} : Measurable (fun p : ℝ × (Fin n → ℝ) => Fin.cons (α := fun _ : Fin (n+1) => ℝ) p.1 p.2) := by
  have he := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm.measurable
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk,
    Fin.insertNth_zero'] using he

lemma cons_measurePreserving (n : ℕ) :
    MeasurePreserving (fun p : ℝ × (Fin n → ℝ) => Fin.cons p.1 p.2)
      (law.prod (productLaw n)) (productLaw (n+1)) := by
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => law) 0).symm
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk,
    Fin.insertNth_zero', Fin.zero_succAbove] using he

/-- Bounded coordinate energies tensorize on the actual finite product. -/
theorem finite_product_energy_bound (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : StronglyMeasurable f) {C D : ℝ} (hb : ∀ x, ‖f x‖ ≤ C)
    (q : Fin n → (Fin n → ℝ) → ℝ)
    (hq : ∀ i, StronglyMeasurable (q i)) (hqb : ∀ i x, ‖q i x‖ ≤ D)
    (hslice : ∀ i x, variance (fun t => f (Function.update x i t)) law ≤
      ∫ t, q i (Function.update x i t) ∂law) :
    variance f (productLaw n) ≤ ∫ x, ∑ i, q i x ∂productLaw n := by
  induction n with
  | zero =>
    have he : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext x
      congr 1
      funext i
      exact Fin.elim0 i
    rw [he]
    simp [variance, evariance]
  | succ n ih =>
    let F : ℝ × (Fin n → ℝ) → ℝ := fun p => f (Fin.cons p.1 p.2)
    have hF : StronglyMeasurable F := hf.comp_measurable cons_measurable
    have hFb (p) : ‖F p‖ ≤ C := hb _
    have hqint (i) : Integrable (q i) (productLaw (n+1)) :=
      (MemLp.of_bound (hq i).aestronglyMeasurable D (.of_forall (hqb i))
        : MemLp (q i) 2 (productLaw (n+1))).integrable (by norm_num)
    have hqF (i) : Integrable (fun p : ℝ × (Fin n → ℝ) => q i (Fin.cons p.1 p.2))
        (law.prod (productLaw n)) :=
      ((cons_measurePreserving n).integrable_comp (hq i).aestronglyMeasurable).mpr (hqint i)
    have ht (t : ℝ) : variance (fun x => F (t,x)) (productLaw n) ≤
        ∫ x, ∑ i : Fin n, q i.succ (Fin.cons t x) ∂productLaw n := by
      apply ih (fun x => F (t,x))
        (hF.comp_measurable measurable_prodMk_left) (fun x => hFb (t,x))
        (fun i x => q i.succ (Fin.cons t x))
        (fun i => (hq i.succ).comp_measurable
          (cons_measurable.comp measurable_prodMk_left))
        (fun i x => hqb i.succ _)
      intro i x
      have he := hslice i.succ (Fin.cons t x)
      simpa only [F, ← Fin.cons_update] using he
    have hs (x : Fin n → ℝ) : variance (fun t => F (t,x)) law ≤
        ∫ t, q 0 (Fin.cons t x) ∂law := by
      have he := hslice 0 (Fin.cons 0 x)
      simpa only [F, Fin.update_cons_zero] using he
    have hvt : Integrable (fun t => variance (fun x => F (t,x)) (productLaw n)) law :=
      bounded_slice_variance_integrable F hF hFb
    have hvs : Integrable (fun x => variance (fun t => F (t,x)) law) (productLaw n) :=
      bounded_slice_variance_integrable (fun p : (Fin n → ℝ) × ℝ => F (p.2,p.1))
        (hF.comp_measurable measurable_swap) (fun p => hFb (p.2,p.1))
    have htail : Integrable (fun p : ℝ × (Fin n → ℝ) =>
        ∑ i : Fin n, q i.succ (Fin.cons p.1 p.2)) (law.prod (productLaw n)) :=
      integrable_finsetSum _ (fun i _ => hqF i.succ)
    have het := integral_mono hvt htail.integral_prod_left ht
    have hes := integral_mono hvs (hqF 0).integral_prod_right hs
    have hvar := product_variance_efron_stein_two (μ := law) (ν := productLaw n) F hF hFb
    rw [(cons_measurePreserving n).variance_fun_comp hf.measurable.aemeasurable] at hvar
    have hsum : (∫ x, ∑ i, q i x ∂productLaw (n+1)) =
        (∫ t, ∫ x, ∑ i : Fin n, q i.succ (Fin.cons t x) ∂productLaw n ∂law) +
        (∫ x, ∫ t, q 0 (Fin.cons t x) ∂law ∂productLaw n) := by
      have he := (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n+1) => law) 0).symm.integral_comp' (fun x => ∑ i, q i x)
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk,
        Fin.insertNth_zero', Fin.zero_succAbove] at he
      rw [← he]
      simp_rw [Fin.sum_univ_succ]
      rw [integral_add (hqF 0) htail, integral_prod _ htail,
        integral_prod_symm _ (hqF 0)]
      ring
    rw [hsum]
    linarith

end KLSImprovement.Tensorization
#print axioms KLSImprovement.Tensorization.finite_product_energy_bound

namespace KLSImprovement.Tensorization
open KLSImprovement.Exponential
local instance : IsProbabilityMeasure law := isProbabilityMeasure_expMeasure (by norm_num)

/-- The ordinary partial derivative, in the original coordinate units. -/
def coordinateDeriv {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n)
    (x : Fin n → ℝ) : ℝ := deriv (fun t => f (Function.update x i t)) (x i)

lemma coordinateDeriv_update {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n)
    (x : Fin n → ℝ) (t : ℝ) :
    coordinateDeriv f i (Function.update x i t) =
      deriv (fun s => f (Function.update x i s)) t := by
  simp [coordinateDeriv, Function.update_idem]

/-- Constant four for the actual d-dimensional product of Exp(1) laws.
Every coordinate slice is C¹ with compact support. Boundedness and measurability
of the ordinary partial derivatives are stated explicitly to make Fubini
integrability transparent; no inequality about the law is assumed. -/
theorem exponential_finite_product_poincare (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : StronglyMeasurable f) {C D : ℝ} (hb : ∀ x, ‖f x‖ ≤ C)
    (hreg : ∀ i x, ContDiff ℝ 1 (fun t => f (Function.update x i t)))
    (hc : ∀ i x, HasCompactSupport (fun t => f (Function.update x i t)))
    (hd : ∀ i, StronglyMeasurable (coordinateDeriv f i))
    (hdb : ∀ i x, ‖coordinateDeriv f i x‖ ≤ D) :
    variance f (productLaw n) ≤
      4 * (∫ x, ∑ i, (coordinateDeriv f i x)^2 ∂productLaw n) := by
  have he := finite_product_energy_bound n f hf hb
    (fun i x => 4 * (coordinateDeriv f i x)^2)
    (fun i => (hd i).pow 2 |>.const_mul 4)
    (D := 4 * D^2)
    (fun i x => by
      rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 4),
        Real.norm_of_nonneg (sq_nonneg _)]
      have hD : 0 ≤ D := (norm_nonneg _).trans (hdb i x)
      have he := (sq_le_sq₀ (norm_nonneg (coordinateDeriv f i x)) hD).mpr (hdb i x)
      simp only [Real.norm_eq_abs, sq_abs] at he
      nlinarith)
    (fun i x => by
      simpa only [coordinateDeriv_update, integral_const_mul] using
        poincare_core (fun t => f (Function.update x i t)) (hreg i x) (hc i x))
  simpa only [← Finset.mul_sum, integral_const_mul] using he

end KLSImprovement.Tensorization
#print axioms KLSImprovement.Tensorization.exponential_finite_product_poincare
