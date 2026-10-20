import ActualCoupledAppellTerminal
import DegreeYoungDrift
import ActualCenteredAppellTerminal

/-! Genuine proper Appell drift with its exact triangular degree weight.
This strengthens the1/8 bound without changing any actual-law input. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem degreeYoung_coupledAppellP_div_sq {μ : Measure (Space n)} (f : Space n → ℝ)
    {K : ℝ} (hK : 0<K) {d : ℕ} (hd : 0<d) :
    (coupledAppellP μ f K d/(d : ℝ))^2=
      (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
  have hd0 : (d : ℝ)≠0 := by exact_mod_cast (ne_of_gt hd)
  rw [div_pow,coupledAppellP_sq f hK]
  field_simp

theorem actual_weighted_proper_drift_degree_young_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K C : ℝ}
    (hK : 0<K) (_hC : 0≤C) (s : ℕ→ℝ) (hs : ∀ b,2≤b→0<s b) (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x,(g x)^2 ∂μ)) :
    2*(∑ d∈Finset.Icc 3 N,(K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) ≤
      (∑ d∈Finset.Icc 3 N,properYoungPrefix s d*(K^d*(d.factorial : ℝ)^2)⁻¹*
        actualAppellEnergy μ f d)+
      (∑ d∈Finset.Icc 2 N,(K*C/s d)*
        (d : ℝ)^2*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hper (d : ℕ) (hd : d∈Finset.Icc 3 N) :
      (K^d*(d.factorial : ℝ)^2)⁻¹*
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d) ≤
      Real.sqrt K*(∑ a∈Finset.Icc 2 (d-1),
        (coupledAppellP μ f K d/(d : ℝ))*coupledAppellQ μ f K a (d-a+1)) := by
    have hh := mul_le_mul_of_nonneg_left
      (actual_proper_pairing_le_canonical_sum hμ.logConcave hf d)
      (show 0≤(K^d*(d.factorial : ℝ)^2)⁻¹ by positivity)
    calc
      _ ≤ _ := hh
      _ = _ := by
        rw [←mul_assoc,Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        simpa only [mul_assoc] using coupledAppell_normalized_term (μ:=μ) f hK
          (Finset.mem_Icc.mp hd).1 ha
  have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper)
    (by norm_num : (0 : ℝ)≤2)
  rw [←Finset.mul_sum] at hsum
  have hcs := coupled_triangle_degree_young N (coupledAppellP μ f K) (coupledAppellQ μ f K) s
    hK.le hs (fun b hb => coupledAppellQ_joint_square_le hμ f hK N hprevious hb)
  have hfirst : (∑ d∈Finset.Icc 3 N,properYoungPrefix s d*
      (coupledAppellP μ f K d/(d : ℝ))^2) =
      ∑ d∈Finset.Icc 3 N,properYoungPrefix s d*(K^d*(d.factorial : ℝ)^2)⁻¹*
        actualAppellEnergy μ f d := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [degreeYoung_coupledAppellP_div_sq f hK (by have := (Finset.mem_Icc.mp hd).1; omega)]
    ring
  rw [hfirst] at hcs
  have hsecond : (∑ d∈Finset.Icc 2 N,(K*C/s d)*(coupledAppellP μ f K d)^2)=
      ∑ d∈Finset.Icc 2 N,(K*C/s d)*(d : ℝ)^2*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [coupledAppellP_sq f hK]
    ring
  rw [hsecond] at hcs
  exact hsum.trans (by convert hcs using 1; ring)

theorem actual_weighted_centered_full_drift_degree_young_le
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {K C : ℝ}
    (hK : 0<K) (hC : 0≤C) (s : ℕ→ℝ) (hs : ∀ b,2≤b→0<s b) (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x,(g x)^2 ∂μ))
    (hstat : ∀ ell : Lp ℝ 2 μ,actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell) :
    2*(∑ d∈Finset.Icc 2 N,(K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d))-
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤
      actualWeightedAppellEnergy μ f K N+
      (∑ d∈Finset.Icc 3 N,properYoungPrefix s d*(K^d*(d.factorial : ℝ)^2)⁻¹*
        actualAppellEnergy μ f d)+
      (∑ d∈Finset.Icc 2 N,(K*C/s d)*
        (d : ℝ)^2*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) := by
  have ht := actual_weighted_terminal_eq hμ f K N hstat
  have hb : actualAppellEnergy μ f 1≤1 := by
    rw [actualAppellEnergy_eq_norm_sq]
    simpa only [hunit,one_pow] using fullClassAppellTensor_one_norm_sq_le hμ.logConcave hμ.isotropic f
  have hM := actualWeightedAppellEnergy_nonneg μ f hK N
  have hMb := mul_le_of_le_one_right hM hb
  have hp := actual_weighted_proper_drift_degree_young_le hμ (Lp.memLp f) hK hC s hs N hprevious
  rw [actual_weighted_proper_drift_sum_eq f K N] at hp
  have he : (∑ d∈Finset.Icc 2 N,(K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)) =
      (∑ d∈Finset.Icc 2 N,(K^d*(d.factorial : ℝ)^2)⁻¹*
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellCoefficient μ
          (fun x => inner ℝ x (affineProjectionVector hμ.isotropic f)) d))+
      (∑ d∈Finset.Icc 2 N,(K^d*(d.factorial : ℝ)^2)⁻¹*
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [actualAppellLowerDriftTensor_terminal_split hμ.logConcave hμ.isotropic f
      (Finset.mem_Icc.mp hd).1,dotProduct_add]
    ring
  rw [he]
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_weighted_proper_drift_degree_young_le
#print axioms KLS.DeterministicBridgeNext.actual_weighted_centered_full_drift_degree_young_le
