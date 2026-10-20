import ActualNormalizedDampingJets
import Mathlib

/-! Genuine normalized all-order directional damping/tilt commutation.
This identifies the right derivatives proved by the finite recurrence
with the directional jets of the actual covariance response. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3

 theorem LocalNormExponentialDomain.mul_quadratic_rate
    {μ : Measure (Space n)} {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r) :
    LocalNormExponentialDomain μ (fun x => f x*(‖x‖^2/2)) r := by
  refine ⟨hf.1.mul (by fun_prop),fun m => ?_⟩
  apply (hf.2 (m+2)).mono' (by exact (((hf.1.mul (by fun_prop)).norm).mul (by fun_prop)).mul (by fun_prop))
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),norm_mul]
    have hx : ‖(‖x‖^2/2 : ℝ)‖ = ‖x‖^2/2 := by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    rw [hx,pow_add]
    nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (f x)) (pow_nonneg (norm_nonneg x) m))
      (mul_nonneg (sq_nonneg ‖x‖) (Real.exp_pos (r*‖x‖)).le)]

 def actualDampingResponse (μ : Measure (Space n)) (f : Space n → ℝ)
    (z : Space n) : ℝ :=
  -actualDampedAverage μ (fun x => f x*(‖x‖^2/2)) 0 z +
    actualDampedAverage μ f 0 z*actualDampedAverage μ (fun x => ‖x‖^2/2) 0 z

 def actualDirectionalDampingResponseJet (μ : Measure (Space n))
    (f : Space n → ℝ) (d : ℕ) (v : Space n) : ℝ :=
  iteratedDeriv d (fun t : ℝ => actualDampingResponse μ f (t • v)) 0

 theorem contDiffAt_actualDampingResponse_zero
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r)
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r) (hr : 0 < r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (actualDampingResponse μ f) 0 := by
  have hrD : LocalNormExponentialDomain μ (fun x : Space n => ‖x‖^2/2) r := by
    simpa only [one_mul] using LocalNormExponentialDomain.mul_quadratic_rate h1
  exact (contDiffAt_actualDampedAverage_zero
    (LocalNormExponentialDomain.mul_quadratic_rate hf) h1 hr (by simp)).neg.add
      ((contDiffAt_actualDampedAverage_zero hf h1 hr (by simp)).mul
        (contDiffAt_actualDampedAverage_zero hrD h1 hr (by simp)))

 theorem actualDampingResponse_jet_convolution
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r)
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r) (hr : 0 < r)
    (d : ℕ) (v : Space n) :
    (∑ i ∈ Finset.range (d+1), (d.choose i : ℝ)*
      actualDirectionalDampingResponseJet μ f i v*
      actualDampedDirectionalRawJet μ (fun _ => 1) (d-i) v 0) =
      -∫ x, (f x*(inner ℝ x v)^d)*(‖x‖^2/2) ∂μ +
      ∑ i ∈ Finset.range (d+1), (d.choose i : ℝ)*
        actualDampedDirectionalJet μ f i v 0*
        ∫ x, (inner ℝ x v)^(d-i)*(‖x‖^2/2) ∂μ := by
  let Z : ℝ → ℝ := fun t => actualDampedNumerator μ (fun _ => 1) 0 (t • v)
  let A : ℝ → ℝ := fun t => actualDampedAverage μ f 0 (t • v)
  let R : ℝ → ℝ := fun t => actualDampingResponse μ f (t • v)
  let Nr : ℝ → ℝ := fun t => actualDampedNumerator μ (fun x => ‖x‖^2/2) 0 (t • v)
  let Nfr : ℝ → ℝ := fun t => actualDampedNumerator μ (fun x => f x*(‖x‖^2/2)) 0 (t • v)
  have hrD : LocalNormExponentialDomain μ (fun x : Space n => ‖x‖^2/2) r := by
    simpa only [one_mul] using LocalNormExponentialDomain.mul_quadratic_rate h1
  have hp : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => t • v) 0 := by fun_prop
  have hsN (g : Space n → ℝ) (hg : LocalNormExponentialDomain μ g r) :
      ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => actualDampedNumerator μ g 0 (t • v)) 0 := by
    change ContDiffAt ℝ (⊤ : ℕ∞)
      ((actualDampedNumerator μ g 0) ∘ (fun t : ℝ => t • v)) 0
    apply ContDiffAt.comp (f := fun t : ℝ => t • v) 0 _ hp
    simpa only [zero_smul] using contDiffAt_actualDampedNumerator_zero hg hr (show (0 : ℝ) ≤ 0 from le_rfl)
  have hsA : ContDiffAt ℝ (⊤ : ℕ∞) A 0 := by
    change ContDiffAt ℝ (⊤ : ℕ∞)
      ((actualDampedAverage μ f 0) ∘ (fun t : ℝ => t • v)) 0
    apply ContDiffAt.comp (f := fun t : ℝ => t • v) 0 _ hp
    simpa only [zero_smul] using contDiffAt_actualDampedAverage_zero hf h1 hr (show (0 : ℝ) ≤ 0 from le_rfl)
  have hsR : ContDiffAt ℝ (⊤ : ℕ∞) R 0 := by
    change ContDiffAt ℝ (⊤ : ℕ∞)
      ((actualDampingResponse μ f) ∘ (fun t : ℝ => t • v)) 0
    apply ContDiffAt.comp (f := fun t : ℝ => t • v) 0 _ hp
    simpa only [zero_smul] using contDiffAt_actualDampingResponse_zero hf h1 hr
  have hsZ : ContDiffAt ℝ (⊤ : ℕ∞) Z 0 := hsN _ h1
  have hsr : ContDiffAt ℝ (⊤ : ℕ∞) Nr 0 := hsN _ hrD
  have hsfr : ContDiffAt ℝ (⊤ : ℕ∞) Nfr 0 :=
    hsN _ (LocalNormExponentialDomain.mul_quadratic_rate hf)
  have hz0 : Z 0 ≠ 0 := by simp [Z,actualDampedNumerator]
  have he : R*Z =ᶠ[𝓝 0] -Nfr+A*Nr := by
    filter_upwards [hsZ.continuousAt.eventually_ne hz0] with t ht
    change actualDampedNumerator μ (fun _ => 1) 0 (t • v) ≠ 0 at ht
    dsimp [R,Z,A,Nfr,Nr,actualDampingResponse,actualDampedAverage]
    field_simp [ht]
  have hd := he.iteratedDeriv_eq d
  rw [iteratedDeriv_mul (hsR.of_le (by simp)) (hsZ.of_le (by simp))] at hd
  change _ = iteratedDeriv d (fun t => -Nfr t+A t*Nr t) 0 at hd
  rw [iteratedDeriv_fun_add (hsfr.neg.of_le (by simp)) ((hsA.mul hsr).of_le (by simp)),
    iteratedDeriv_fun_neg,
    iteratedDeriv_fun_mul (hsA.of_le (by simp)) (hsr.of_le (by simp))] at hd
  change (∑ i ∈ Finset.range (d+1), (d.choose i : ℝ)*
      actualDirectionalDampingResponseJet μ f i v*
      actualDampedDirectionalRawJet μ (fun _ => 1) (d-i) v 0) =
      -actualDampedDirectionalRawJet μ (fun x => f x*(‖x‖^2/2)) d v 0 +
      ∑ i ∈ Finset.range (d+1), (d.choose i : ℝ)*
        actualDampedDirectionalJet μ f i v 0*
        actualDampedDirectionalRawJet μ (fun x => ‖x‖^2/2) (d-i) v 0 at hd
  rw [actualDampedDirectionalRawJet_eq_moment
    (LocalNormExponentialDomain.mul_quadratic_rate hf) hr (show (0 : ℝ) ≤ 0 from le_rfl)] at hd
  simp only [neg_zero,zero_mul,Real.exp_zero,mul_one] at hd
  simp_rw [actualDampedDirectionalRawJet_eq_moment hrD hr (show (0 : ℝ) ≤ 0 from le_rfl)] at hd
  simp only [neg_zero,zero_mul,Real.exp_zero,mul_one] at hd
  convert hd using 1
  congr 1
  · congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  · apply Finset.sum_congr rfl
    intro i hi
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring

/-- Actual one-sided damping differentiation commutes with every
directional theta jet of the normalized expectation.  The response is
the negative covariance with |X|²/2 under the actual tilted law. -/
 theorem derivWithin_actualDampedDirectionalJet_eq_response
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (v : Space n) :
    derivWithin (fun s : ℝ => actualDampedDirectionalJet μ f d v s) (Ici 0) 0 =
      actualDirectionalDampingResponseJet μ f d v := by
  obtain ⟨r,hr,hD,h1D⟩ := exists_common_local_exponential_domains hLC hf
  have hz0 : actualDampedDirectionalRawJet μ (fun _ => 1) 0 v 0 = 1 := by
    simp [actualDampedDirectionalRawJet,actualDampedNumerator]
  induction d using Nat.strong_induction_on with
  | h d ih =>
    have hd := actualDampedDirectionalJet_damping_convolution hLC hf d v
    have hrsp := actualDampingResponse_jet_convolution hD h1D hr d v
    have hexp :
        (∑ i ∈ Finset.range (d+1), (d.choose i : ℝ)*
          (derivWithin (fun s : ℝ => actualDampedDirectionalJet μ f i v s) (Ici 0) 0*
              actualDampedDirectionalRawJet μ (fun _ => 1) (d-i) v 0 -
            actualDampedDirectionalJet μ f i v 0*
              ∫ x, (inner ℝ x v)^(d-i)*(‖x‖^2/2) ∂μ)) =
        (∑ i ∈ Finset.range (d+1), (d.choose i : ℝ)*
          derivWithin (fun s : ℝ => actualDampedDirectionalJet μ f i v s) (Ici 0) 0*
            actualDampedDirectionalRawJet μ (fun _ => 1) (d-i) v 0) -
        ∑ i ∈ Finset.range (d+1), (d.choose i : ℝ)*
          actualDampedDirectionalJet μ f i v 0*
            ∫ x, (inner ℝ x v)^(d-i)*(‖x‖^2/2) ∂μ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hexp] at hd
    have heq :
        (∑ i ∈ Finset.range (d+1), (d.choose i : ℝ)*
          derivWithin (fun s : ℝ => actualDampedDirectionalJet μ f i v s) (Ici 0) 0*
            actualDampedDirectionalRawJet μ (fun _ => 1) (d-i) v 0) =
        ∑ i ∈ Finset.range (d+1), (d.choose i : ℝ)*
          actualDirectionalDampingResponseJet μ f i v*
            actualDampedDirectionalRawJet μ (fun _ => 1) (d-i) v 0 := by linarith
    rw [Finset.sum_range_succ,Finset.sum_range_succ] at heq
    have hpref :
        (∑ i ∈ Finset.range d, (d.choose i : ℝ)*
          derivWithin (fun s : ℝ => actualDampedDirectionalJet μ f i v s) (Ici 0) 0*
            actualDampedDirectionalRawJet μ (fun _ => 1) (d-i) v 0) =
        ∑ i ∈ Finset.range d, (d.choose i : ℝ)*
          actualDirectionalDampingResponseJet μ f i v*
            actualDampedDirectionalRawJet μ (fun _ => 1) (d-i) v 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih i (Finset.mem_range.mp hi)]
    rw [hpref] at heq
    simp only [Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,hz0,mul_one] at heq
    linarith

 theorem hasDerivWithinAt_actualDampedDirectionalJet_response
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (v : Space n) :
    HasDerivWithinAt (fun s : ℝ => actualDampedDirectionalJet μ f d v s)
      (actualDirectionalDampingResponseJet μ f d v) (Ici 0) 0 := by
  rw [← derivWithin_actualDampedDirectionalJet_eq_response hLC hf d v]
  exact (differentiableWithinAt_actualDampedDirectionalJet hLC hf d v).hasDerivWithinAt

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualDampingResponse_jet_convolution
#print axioms KLS.DeterministicBridgeIntegration.hasDerivWithinAt_actualDampedDirectionalJet_response
