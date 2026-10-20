import ActualWeightedAppellEnergy
import ActualJointCumulantContraction
import CoupledDriftCauchy
import GenericFactorialConvolution

/-! The literal weighted Appell remainder, controlled by the previous
finite joint bound. All cumulant contractions and factorials are actual;
the triangular Cauchy step retains a joint Bessel inequality. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped ContDiff BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def coupledAppellScale (K : ℝ) (d : ℕ) : ℝ := (d.factorial : ℝ)*(Real.sqrt K)^d
def coupledAppellP (μ : Measure (Space n)) (f : Space n → ℝ) (K : ℝ) (d : ℕ) : ℝ :=
  (d : ℝ)*Real.sqrt (actualAppellEnergy μ f d)/coupledAppellScale K d
def coupledAppellQ (μ : Measure (Space n)) (f : Space n → ℝ) (K : ℝ) (a b : ℕ) : ℝ :=
  (b : ℝ)*Real.sqrt (actualCanonicalContractionSquare μ f a (b-1))/
    (coupledAppellScale K a*coupledAppellScale K b)

theorem coupledAppellScale_positive {K : ℝ} (hK : 0 < K) (d : ℕ) :
    0 < coupledAppellScale K d := by
  unfold coupledAppellScale
  positivity

theorem coupledAppellScale_sq {K : ℝ} (hK : 0 < K) (d : ℕ) :
    (coupledAppellScale K d)^2=K^d*(d.factorial : ℝ)^2 := by
  unfold coupledAppellScale
  rw [mul_pow, ← pow_mul, Nat.mul_comm d 2, pow_mul, Real.sq_sqrt hK.le]
  ring

theorem coupledAppellWeight_scale {K : ℝ} (hK : 0 < K) (d : ℕ) :
    (K^d*(d.factorial : ℝ)^2)⁻¹ = 1/(coupledAppellScale K d)^2 := by
  rw [coupledAppellScale_sq hK]
  simp

theorem coupledAppellP_sq {μ : Measure (Space n)} (f : Space n → ℝ)
    {K : ℝ} (hK : 0 < K) (d : ℕ) :
    (coupledAppellP μ f K d)^2=
      (d : ℝ)^2*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
  unfold coupledAppellP
  rw [div_pow,mul_pow,Real.sq_sqrt (actualAppellEnergy_nonneg _ _ _),coupledAppellScale_sq hK]
  ring

theorem coupledAppellQ_sq {μ : Measure (Space n)} (f : Space n → ℝ)
    {K : ℝ} (hK : 0 < K) (a b : ℕ) :
    (coupledAppellQ μ f K a b)^2=
      ((b : ℝ)^2/(coupledAppellScale K b)^2)*
        ((K^a*(a.factorial : ℝ)^2)⁻¹*actualCanonicalContractionSquare μ f a (b-1)) := by
  unfold coupledAppellQ
  rw [div_pow,mul_pow,Real.sq_sqrt (actualCanonicalContractionSquare_nonneg _ _ _ _),mul_pow]
  rw [coupledAppellScale_sq hK a]
  ring

theorem coupledAppellQ_joint_square_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (f : Space n → ℝ)
    {K C : ℝ} (hK : 0 < K) (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ))
    {b : ℕ} (hb : b ∈ Finset.Icc 2 N) :
    (∑ a ∈ Finset.Icc 2 (N-1), (coupledAppellQ μ f K a b)^2) ≤
      C*(coupledAppellP μ f K b)^2 := by
  have hbc : b-1+1=b := by have := (Finset.mem_Icc.mp hb).1; omega
  have hj := actual_joint_canonical_contraction_square_le hμ f (Finset.Icc 2 (N-1))
    (fun a => (K^a*(a.factorial : ℝ)^2)⁻¹) hprevious (b-1)
  rw [hbc] at hj
  simp_rw [coupledAppellQ_sq f hK]
  rw [← Finset.mul_sum]
  calc
    _ ≤ ((b : ℝ)^2/(coupledAppellScale K b)^2)*(C*actualAppellEnergy μ f b) :=
      mul_le_mul_of_nonneg_left hj (by positivity)
    _ = _ := by rw [coupledAppellP_sq f hK, coupledAppellScale_sq hK]; ring

theorem coupledAppellScale_choose {K : ℝ} (hK : 0 < K) {d a : ℕ}
    (hd : 3 ≤ d) (ha : a ∈ Finset.Icc 2 (d-1)) :
    (d.choose a : ℝ)*coupledAppellScale K a*coupledAppellScale K (d-a+1)=
      ((d-a+1 : ℕ) : ℝ)*Real.sqrt K*coupledAppellScale K d := by
  have hale : a ≤ d := by have := (Finset.mem_Icc.mp ha).2; omega
  have hf := FactorialScheme.choose_factorial_shift hale
  have hp : (Real.sqrt K)^a*(Real.sqrt K)^(d-a+1)=(Real.sqrt K)^(d+1) := by
    rw [← pow_add]
    congr 1
    omega
  unfold coupledAppellScale
  calc
    _ = ((d.choose a : ℝ)*(a.factorial : ℝ)*((d-a+1).factorial : ℝ))*
        ((Real.sqrt K)^a*(Real.sqrt K)^(d-a+1)) := by ring
    _ = (d.factorial : ℝ)*((d-a+1 : ℕ) : ℝ)*(Real.sqrt K)^(d+1) := by rw [hf,hp]
    _ = _ := by rw [pow_succ]; ring

theorem coupledAppell_normalized_term
    {μ : Measure (Space n)} (f : Space n → ℝ) {K : ℝ} (hK : 0 < K)
    {d a : ℕ} (hd : 3 ≤ d) (ha : a ∈ Finset.Icc 2 (d-1)) :
    (K^d*(d.factorial : ℝ)^2)⁻¹*Real.sqrt (actualAppellEnergy μ f d)*
        ((d.choose a : ℝ)*Real.sqrt (actualCanonicalContractionSquare μ f a (d-a))) =
      Real.sqrt K*(coupledAppellP μ f K d/(d : ℝ))*
        coupledAppellQ μ f K a (d-a+1) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hbc : d-a+1-1=d-a := by omega
  have hs0 (i : ℕ) : coupledAppellScale K i ≠ 0 := ne_of_gt (coupledAppellScale_positive hK i)
  have hf := coupledAppellScale_choose hK hd ha
  have hc : (K^d*(d.factorial : ℝ)^2)⁻¹*(d.choose a : ℝ) =
      Real.sqrt K*((d-a+1 : ℕ) : ℝ)/
        (coupledAppellScale K d*coupledAppellScale K a*coupledAppellScale K (d-a+1)) := by
    rw [coupledAppellWeight_scale hK]
    field_simp [hs0 d,hs0 a,hs0 (d-a+1)]
    nlinarith [hf]
  have hp : coupledAppellP μ f K d/(d : ℝ)=
      Real.sqrt (actualAppellEnergy μ f d)/coupledAppellScale K d := by
    unfold coupledAppellP
    field_simp
  rw [hp]
  unfold coupledAppellQ
  rw [hbc]
  calc
    _ = ((K^d*(d.factorial : ℝ)^2)⁻¹*(d.choose a : ℝ))*
        (Real.sqrt (actualAppellEnergy μ f d)*Real.sqrt (actualCanonicalContractionSquare μ f a (d-a))) := by ring
    _ = _ := by rw [hc]; ring

/-- Genuine proper cumulant drift from the preceding coupled bound.
No individual cumulant estimate or next-rank coefficient bound is used. -/
theorem actual_weighted_proper_drift_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K C : ℝ} (hK : 0 < K) (hC : 0 ≤ C)
    (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ)) :
    2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) ≤
      Real.sqrt (K*C/2)*(∑ d ∈ Finset.Icc 2 N,
        (d : ℝ)^2*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hper (d : ℕ) (hd : d ∈ Finset.Icc 3 N) :
      (K^d*(d.factorial : ℝ)^2)⁻¹*
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d) ≤
      Real.sqrt K*(∑ a ∈ Finset.Icc 2 (d-1),
        (coupledAppellP μ f K d/(d : ℝ))*coupledAppellQ μ f K a (d-a+1)) := by
    have hh := mul_le_mul_of_nonneg_left (actual_proper_pairing_le_canonical_sum hμ.logConcave hf d)
      (show 0 ≤ (K^d*(d.factorial : ℝ)^2)⁻¹ by positivity)
    calc
      _ ≤ _ := hh
      _ = _ := by
        rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        simpa only [mul_assoc] using coupledAppell_normalized_term (μ := μ) f hK
          (Finset.mem_Icc.mp hd).1 ha
  have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by norm_num : (0 : ℝ) ≤ 2)
  rw [← Finset.mul_sum] at hsum
  have hcs := coupled_triangle_cauchy N (coupledAppellP μ f K) (coupledAppellQ μ f K) hC hK.le
    (fun b hb => coupledAppellQ_joint_square_le hμ f hK N hprevious hb)
  simp_rw [coupledAppellP_sq f hK] at hcs
  exact hsum.trans (by convert hcs using 1 <;> ring)

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_weighted_proper_drift_le
