import ActualDampedLaplaceJets
import Mathlib

/-! Actual normalized directional jets and genuine right damping derivatives.
The finite Leibniz recurrence is derived from the actual quotient.  It is
then used to prove differentiability at every order; no coefficient
evolution assumption is introduced. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 3

 theorem contDiffAt_actualDampedNumerator_zero
    {μ : Measure (Space n)} {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r) (hr : 0 < r)
    {s : ℝ} (hs : 0 ≤ s) :
    ContDiffAt ℝ (⊤ : ℕ∞) (actualDampedNumerator μ f s) 0 := by
  have he : actualDampedNumerator μ f s =
      tiltNumerator μ (fun _ => 0) (fun x => f x*Real.exp (-s*(‖x‖^2/2))) := by
    funext z
    simp only [actualDampedNumerator,tiltNumerator,zero_add]
  rw [he]
  exact (contDiffOn_tiltNumerator_of_localNormExponentialDomain
    (LocalNormExponentialDomain.mul_nonneg_damping hf hs)).contDiffAt
      (isOpen_ball.mem_nhds (by simpa using hr : (0 : Space n) ∈ ball 0 r))

 theorem actualDampedNumerator_one_zero_pos
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] {r : ℝ}
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r) (hr : 0 < r)
    {s : ℝ} (hs : 0 ≤ s) :
    0 < actualDampedNumerator μ (fun _ => 1) s 0 := by
  have hi : Integrable (fun x : Space n => Real.exp (-s*(‖x‖^2/2))) μ := by
    simpa only [inner_zero_left,Real.exp_zero,mul_one,one_mul] using
      (LocalNormExponentialDomain.mul_nonneg_damping h1 hs).integrable_tilt
        (show ‖(0 : Space n)‖ ≤ r by simpa using hr.le)
  simpa only [actualDampedNumerator,one_mul,inner_zero_left,Real.exp_zero,mul_one] using
    integral_exp_pos hi

 theorem contDiffAt_actualDampedAverage_zero
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r)
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r) (hr : 0 < r)
    {s : ℝ} (hs : 0 ≤ s) :
    ContDiffAt ℝ (⊤ : ℕ∞) (actualDampedAverage μ f s) 0 := by
  exact (contDiffAt_actualDampedNumerator_zero hf hr hs).div
    (contDiffAt_actualDampedNumerator_zero h1 hr hs)
    (actualDampedNumerator_one_zero_pos h1 hr hs).ne'

/-- The exact finite convolution for actual normalized directional jets. -/
 theorem actualDampedDirectionalJet_convolution
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r)
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r) (hr : 0 < r)
    {s : ℝ} (hs : 0 ≤ s) (d : ℕ) (v : Space n) :
    actualDampedDirectionalRawJet μ f d v s =
      ∑ i ∈ Finset.range (d+1), (d.choose i : ℝ)*
        actualDampedDirectionalJet μ f i v s*
        actualDampedDirectionalRawJet μ (fun _ => 1) (d-i) v s := by
  let N : ℝ → ℝ := fun t => actualDampedNumerator μ f s (t • v)
  let Z : ℝ → ℝ := fun t => actualDampedNumerator μ (fun _ => 1) s (t • v)
  let A : ℝ → ℝ := fun t => actualDampedAverage μ f s (t • v)
  have hp : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => t • v) 0 := by fun_prop
  have hZ : ContDiffAt ℝ (⊤ : ℕ∞) Z 0 := by
    change ContDiffAt ℝ (⊤ : ℕ∞)
      ((actualDampedNumerator μ (fun _ => 1) s) ∘ (fun t : ℝ => t • v)) 0
    apply ContDiffAt.comp (f := fun t : ℝ => t • v) 0 _ hp
    simpa only [zero_smul] using contDiffAt_actualDampedNumerator_zero h1 hr hs
  have hA : ContDiffAt ℝ (⊤ : ℕ∞) A 0 := by
    change ContDiffAt ℝ (⊤ : ℕ∞)
      ((actualDampedAverage μ f s) ∘ (fun t : ℝ => t • v)) 0
    apply ContDiffAt.comp (f := fun t : ℝ => t • v) 0 _ hp
    simpa only [zero_smul] using contDiffAt_actualDampedAverage_zero hf h1 hr hs
  have hz0 : Z 0 ≠ 0 := by
    simpa only [Z,zero_smul] using (actualDampedNumerator_one_zero_pos h1 hr hs).ne'
  have hNZ : N =ᶠ[𝓝 0] A*Z := by
    filter_upwards [hZ.continuousAt.eventually_ne hz0] with t ht
    simp only [N,A,Z,Pi.mul_apply,actualDampedAverage]
    exact (div_mul_cancel₀ _ ht).symm
  change iteratedDeriv d N 0 = _
  rw [hNZ.iteratedDeriv_eq d,iteratedDeriv_mul (hA.of_le (by simp)) (hZ.of_le (by simp))]
  rfl

 theorem actualDampedDirectionalJet_recurrence
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r)
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r) (hr : 0 < r)
    {s : ℝ} (hs : 0 ≤ s) (d : ℕ) (v : Space n) :
    actualDampedDirectionalJet μ f d v s =
      (actualDampedDirectionalRawJet μ f d v s -
        ∑ i ∈ Finset.range d, (d.choose i : ℝ)*
          actualDampedDirectionalJet μ f i v s*
          actualDampedDirectionalRawJet μ (fun _ => 1) (d-i) v s) /
      actualDampedDirectionalRawJet μ (fun _ => 1) 0 v s := by
  have he := actualDampedDirectionalJet_convolution hf h1 hr hs d v
  rw [Finset.sum_range_succ] at he
  simp only [Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self] at he
  have hz : actualDampedDirectionalRawJet μ (fun _ => 1) 0 v s ≠ 0 := by
    simpa only [actualDampedDirectionalRawJet,iteratedDeriv_zero,zero_smul] using
      (actualDampedNumerator_one_zero_pos h1 hr hs).ne'
  apply (eq_div_iff hz).mpr
  linarith

 theorem differentiableWithinAt_actualDampedDirectionalJet
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (v : Space n) :
    DifferentiableWithinAt ℝ (fun s : ℝ => actualDampedDirectionalJet μ f d v s)
      (Ici 0) 0 := by
  obtain ⟨r,hr,hD,h1D⟩ := exists_common_local_exponential_domains hLC hf
  have h1L : MemLp (fun _ : Space n => (1 : ℝ)) 2 μ := memLp_const 1
  have hraw (k : ℕ) :=
    (hasDerivWithinAt_damped_directional_raw_jet hLC hf k v).differentiableWithinAt
  have hzraw (k : ℕ) :=
    (hasDerivWithinAt_damped_directional_raw_jet hLC h1L k v).differentiableWithinAt
  have hz : actualDampedDirectionalRawJet μ (fun _ => 1) 0 v 0 ≠ 0 := by
    simp [actualDampedDirectionalRawJet,actualDampedNumerator]
  induction d using Nat.strong_induction_on with
  | h d ih =>
    have hsum : DifferentiableWithinAt ℝ
        (fun s : ℝ => ∑ i ∈ Finset.range d, (d.choose i : ℝ)*
          actualDampedDirectionalJet μ f i v s*
          actualDampedDirectionalRawJet μ (fun _ => 1) (d-i) v s) (Ici 0) 0 := by
      apply DifferentiableWithinAt.fun_sum
      intro i hi
      exact ((ih i (Finset.mem_range.mp hi)).const_mul _).mul (hzraw (d-i))
    have hd := ((hraw d).sub hsum).div (hzraw 0) hz
    apply hd.congr
    · intro s hs
      exact actualDampedDirectionalJet_recurrence hD h1D hr hs d v
    · exact actualDampedDirectionalJet_recurrence hD h1D hr (show (0 : ℝ) ≤ 0 from le_rfl) d v

/-- Differentiate the exact convolution.  Together with its nonzero
zeroth partition entry, this uniquely determines every normalized
damping derivative from actual polynomial moments. -/
 theorem actualDampedDirectionalJet_damping_convolution
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (v : Space n) :
    (∑ i ∈ Finset.range (d+1), (d.choose i : ℝ)*
      (derivWithin (fun s : ℝ => actualDampedDirectionalJet μ f i v s) (Ici 0) 0*
          actualDampedDirectionalRawJet μ (fun _ => 1) (d-i) v 0 -
        actualDampedDirectionalJet μ f i v 0*
          ∫ x, (inner ℝ x v)^(d-i)*(‖x‖^2/2) ∂μ)) =
      -∫ x, (f x*(inner ℝ x v)^d)*(‖x‖^2/2) ∂μ := by
  obtain ⟨r,hr,hD,h1D⟩ := exists_common_local_exponential_domains hLC hf
  have h1L : MemLp (fun _ : Space n => (1 : ℝ)) 2 μ := memLp_const 1
  have hb (i : ℕ) :=
    (differentiableWithinAt_actualDampedDirectionalJet hLC hf i v).hasDerivWithinAt
  have hz (i : ℕ) : HasDerivWithinAt
      (fun s : ℝ => actualDampedDirectionalRawJet μ (fun _ => 1) i v s)
      (-∫ x, (inner ℝ x v)^i*(‖x‖^2/2) ∂μ) (Ici 0) 0 := by
    simpa only [one_mul] using hasDerivWithinAt_damped_directional_raw_jet hLC h1L i v
  have hsum := HasDerivWithinAt.fun_sum (u := Finset.range (d+1))
    (fun i _ => ((hb i).mul (hz (d-i))).const_mul (d.choose i : ℝ))
  have hsum' : HasDerivWithinAt
      (fun s : ℝ => actualDampedDirectionalRawJet μ f d v s)
      (∑ i ∈ Finset.range (d+1), (d.choose i : ℝ)*
        (derivWithin (fun s : ℝ => actualDampedDirectionalJet μ f i v s) (Ici 0) 0*
            actualDampedDirectionalRawJet μ (fun _ => 1) (d-i) v 0 -
          actualDampedDirectionalJet μ f i v 0*
            ∫ x, (inner ℝ x v)^(d-i)*(‖x‖^2/2) ∂μ)) (Ici 0) 0 := by
    convert hsum.congr_of_mem (f₁ := fun s => actualDampedDirectionalRawJet μ f d v s)
      (fun s hs => by simpa only [Pi.mul_apply,mul_assoc] using
        actualDampedDirectionalJet_convolution hD h1D hr hs d v) (by simp) using 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [← hsum'.derivWithin (uniqueDiffWithinAt_Ici 0)]
  exact (hasDerivWithinAt_damped_directional_raw_jet hLC hf d v).derivWithin
    (uniqueDiffWithinAt_Ici 0)

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualDampedDirectionalJet_recurrence
#print axioms KLS.DeterministicBridgeIntegration.differentiableWithinAt_actualDampedDirectionalJet
#print axioms KLS.DeterministicBridgeIntegration.actualDampedDirectionalJet_damping_convolution
