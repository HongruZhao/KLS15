import KLSConstantImprovement.ReservedQTriangleBudget
import ActualSelectedRowsBoundaryAppellDrift
import ActualSelectiveBudgetAppellDrift

/-! Literal all-law canonical size-two refunds, including the unused
last column cell of the previous joint budget. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLSConstantImprovement.SignedReservedCanonicalDrift
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.ReservedQTriangleBudget
variable {n : ℕ}
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

theorem actual_selected_remainder_with_last_refund_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K C : ℝ} (s : ℕ → ℝ) (rho lambda : ℕ → ℕ → ℝ)
    (hK : 0 < K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (hrho : ∀ d a, 3 ≤ d → 0 ≤ rho d a)
    (hlambda : ∀ a b, 2 ≤ a → 2 ≤ b → lambda a b ≤ 1)
    (hboundary : ∀ d a, 3 ≤ d → a ∈ Finset.Icc 2 (d-1) →
      lambda a (d-a+1) = 1 → rho d a = 0) (N : ℕ) (hN : 3 ≤ N)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ)) :
    2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualProfileProperRemainder μ f rho d)) +
      (∑ p ∈ coupledDriftPairs N, (lambda p.2 (p.1-p.2+1)*K/s (p.1-p.2+1)) *
        (coupledAppellQ μ f K p.2 (p.1-p.2+1))^2) +
      (lambda 2 N*K/s N)*(coupledAppellQ μ f K 2 N)^2 ≤
      (∑ d ∈ Finset.Icc 3 N, selectedRowsPrefix s rho lambda d *
        (K^d*(d.factorial : ℝ)^2)⁻¹ * actualAppellEnergy μ f d) +
      ∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(b : ℝ)^2 *
        (K^b*(b.factorial : ℝ)^2)⁻¹ * actualAppellEnergy μ f b := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hper (d : ℕ) (hd : d ∈ Finset.Icc 3 N) :
      (K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ actualProfileProperRemainder μ f rho d) ≤
      Real.sqrt K*(∑ a ∈ Finset.Icc 2 (d-1), rho d a *
        (coupledAppellP μ f K d/(d : ℝ))*coupledAppellQ μ f K a (d-a+1)) := by
    have hh := mul_le_mul_of_nonneg_left
      (actual_profile_pairing_le_canonical_sum hμ.logConcave hf rho d
        (fun a => hrho d a (Finset.mem_Icc.mp hd).1))
      (show 0 ≤ (K^d*(d.factorial : ℝ)^2)⁻¹ by positivity)
    calc
      _ ≤ _ := hh
      _ = _ := by
        rw [←mul_assoc,Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        have he := coupledAppell_normalized_term (μ := μ) f hK
          (Finset.mem_Icc.mp hd).1 ha
        calc
          _ = rho d a *
              ((K^d*(d.factorial : ℝ)^2)⁻¹ * Real.sqrt (actualAppellEnergy μ f d) *
                ((d.choose a : ℝ)*Real.sqrt (actualCanonicalContractionSquare μ f a (d-a)))) := by ring
          _ = _ := by rw [he]; ring
  have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper)
    (by norm_num : (0 : ℝ) ≤ 2)
  rw [←Finset.mul_sum] at hsum
  have hy := coupled_triangle_selected_rows_young_with_last_refund N hN (coupledAppellP μ f K)
    (coupledAppellQ μ f K) s rho lambda hK.le hs hlambda hboundary
    (fun b hb => coupledAppellQ_joint_square_le hμ f hK N hprevious hb)
  have hfirst : (∑ d ∈ Finset.Icc 3 N, selectedRowsPrefix s rho lambda d *
      (coupledAppellP μ f K d/(d : ℝ))^2) =
      ∑ d ∈ Finset.Icc 3 N, selectedRowsPrefix s rho lambda d *
        (K^d*(d.factorial : ℝ)^2)⁻¹ * actualAppellEnergy μ f d := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [coupledAppellP_div_sq f hK (by have := (Finset.mem_Icc.mp hd).1; omega)]
    ring
  rw [hfirst] at hy
  simp_rw [coupledAppellP_sq f hK] at hy
  have hr : (∑ b ∈ Finset.Icc 2 N, (K*C/s b) *
      ((b : ℝ)^2*(K^b*(b.factorial : ℝ)^2)⁻¹ * actualAppellEnergy μ f b)) =
      ∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(b : ℝ)^2 *
        (K^b*(b.factorial : ℝ)^2)⁻¹ * actualAppellEnergy μ f b := by
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [hr] at hy
  change _ + (∑ p ∈ coupledDriftPairs N, (lambda p.2 (p.1-p.2+1)*K/s (p.1-p.2+1)) *
        (coupledAppellQ μ f K p.2 (p.1-p.2+1))^2) +
      (lambda 2 N*K/s N)*(coupledAppellQ μ f K 2 N)^2 ≤ _ at hy
  have hsum' : 2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualProfileProperRemainder μ f rho d)) ≤
      2*Real.sqrt K * (∑ d ∈ Finset.Icc 3 N,
        ∑ a ∈ Finset.Icc 2 (d-1), rho d a *
          (coupledAppellP μ f K d/(d : ℝ))*coupledAppellQ μ f K a (d-a+1)) := by
    convert hsum using 1; ring
  linarith


def kappa (K : ℝ) (young lambda : ℕ→ℝ) (b : ℕ) : ℝ :=
  lambda b*(b : ℝ)^2/(4*K*young b)

theorem selective_prefix_eq (young theta lambda : ℕ→ℝ) (d : ℕ) (hd : 3 ≤ d) :
    selectedRowsPrefix young (thetaTriangleCoefficient theta)
      (fun a b=>if a=2 then lambda b else 0) d=selectiveDegreePrefix young theta lambda d := by
  unfold selectedRowsPrefix selectiveDegreePrefix
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h2:a=2
  · subst a
    have hs:d-2+1=d-1:=by omega
    simp [selectiveTriangleFraction,hs]
  · simp [selectiveTriangleFraction,h2]

theorem canonical_charge_sum_reindex (K : ℝ) (young lambda : ℕ→ℝ)
    (Q : ℕ→ℕ→ℝ) (N : ℕ) (hN : 3 ≤ N) :
    (∑ p ∈ coupledDriftPairs N,
      ((if p.2=2 then lambda (p.1-p.2+1) else 0)*K/young (p.1-p.2+1))*(Q p.2 (p.1-p.2+1))^2)+
      (lambda N*K/young N)*(Q 2 N)^2=
      ∑ b ∈ Finset.Icc 2 N,(lambda b*K/young b)*(Q 2 b)^2 := by
  classical
  have hrows:(∑ p ∈ coupledDriftPairs N,
      ((if p.2=2 then lambda (p.1-p.2+1) else 0)*K/young (p.1-p.2+1))*(Q p.2 (p.1-p.2+1))^2)=
      ∑ d ∈ Finset.Icc 3 N,(lambda (d-1)*K/young (d-1))*(Q 2 (d-1))^2 := by
    rw [coupledDriftPairs,Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro d hd
    have ht:(∑ a ∈ Finset.Icc 2 (d-1),
        ((if a=2 then lambda (d-a+1) else 0)*K/young (d-a+1))*(Q a (d-a+1))^2)=
        ∑ a ∈ Finset.Icc 2 (d-1),if a=2 then
          (lambda (d-1)*K/young (d-1))*(Q 2 (d-1))^2 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h2:a=2
      · subst a
        have hs:d-2+1=d-1:=by have:=(Finset.mem_Icc.mp hd).1;omega
        simp [hs]
      · simp [h2]
    rw [ht]
    have hm:2∈Finset.Icc 2 (d-1):=by simp only [Finset.mem_Icc] at hd ⊢;omega
    simp [hm]
  rw [hrows]
  have hshift:(∑ d ∈ Finset.Icc 3 N,(lambda (d-1)*K/young (d-1))*(Q 2 (d-1))^2)=
      ∑ b ∈ Finset.Icc 2 (N-1),(lambda b*K/young b)*(Q 2 b)^2 := by
    apply Finset.sum_bij (fun d _=>d-1)
    · intro d hd
      simp only [Finset.mem_Icc] at hd ⊢
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_Icc] at ha hb
      omega
    · intro b hb
      refine ⟨b+1,?_,by omega⟩
      simp only [Finset.mem_Icc] at hb ⊢
      omega
    · intro d hd
      rfl
  rw [hshift]
  have hs:Finset.Icc 2 N=insert N (Finset.Icc 2 (N-1)):=by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hn:N∉Finset.Icc 2 (N-1):=by simp only [Finset.mem_Icc];omega
  rw [hs,Finset.sum_insert hn]
  ring

theorem actual_full_reserved_proper_drift_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n→ℝ} (hf : MemLp f 2 μ) {K C : ℝ} (young theta lambda : ℕ→ℝ)
    (hK : 0<K) (hy : ∀ b,2 ≤ b→0<young b)
    (ht : ∀ d,3 ≤ d→theta d ≤ 1) (hl : ∀ b,2 ≤ b→lambda b ≤ 1)
    (hb : ∀ b,2 ≤ b→lambda b=1→theta (b+1)=1) (N : ℕ) (hN : 3 ≤ N)
    (hprevious : ∀ g : Space n→ℝ,MemLp g 2 μ→
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x,(g x)^2 ∂μ)) :
    2*(∑ d ∈ Finset.Icc 3 N,(K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d))+
      (∑ b ∈ Finset.Icc 2 N,kappa K young lambda b*(K^b*(b.factorial : ℝ)^2)⁻¹*
        actualCanonicalContractionSquare μ f 2 (b-1))  ≤ 
      (∑ d ∈ Finset.Icc 3 N,selectiveDegreePrefix young theta lambda d*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)+
      (∑ b ∈ Finset.Icc 2 N,(K*C/young b)*(b : ℝ)^2*
        (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b)+
      2*(∑ d ∈ Finset.Icc 3 N,theta d*(K^d*(d.factorial : ℝ)^2)⁻¹*
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d)) := by
  have hnonneg:∀ d a,3 ≤ d→0 ≤ thetaTriangleCoefficient theta d a := by
    intro d a hd
    unfold thetaTriangleCoefficient
    split_ifs
    · linarith [ht d hd]
    · norm_num
  have hcap:∀ a b,2 ≤ a→2 ≤ b→(if a=2 then lambda b else 0) ≤ 1 := by
    intro a b ha hb'
    split_ifs
    · exact hl b hb'
    · norm_num
  have hboundary:∀ d a,3 ≤ d→a∈Finset.Icc 2 (d-1)→
      (if a=2 then lambda (d-a+1) else 0)=1→thetaTriangleCoefficient theta d a=0 := by
    intro d a hd ha he
    by_cases h2:a=2
    · subst a
      have hs:d-2+1=d-1:=by omega
      have hd1:d-1+1=d:=by omega
      simp only [ite_true,hs] at he
      have hh:=hb (d-1) (by omega) he
      rw [hd1] at hh
      simp [thetaTriangleCoefficient,hh]
    · simp [h2] at he
  have hh:=actual_selected_remainder_with_last_refund_le hμ hf young
    (thetaTriangleCoefficient theta) (fun a b=>if a=2 then lambda b else 0)
    hK hy hnonneg hcap hboundary N hN hprevious
  change 2*(∑ d ∈ Finset.Icc 3 N,(K^d*(d.factorial : ℝ)^2)⁻¹*
    (actualAppellCoefficient μ f d ⬝ᵥ actualThetaProperRemainder μ f theta d)) +
    (∑ p ∈ coupledDriftPairs N,((if p.2=2 then lambda (p.1-p.2+1) else 0)*K/young (p.1-p.2+1))*
      (coupledAppellQ μ f K p.2 (p.1-p.2+1))^2)+
    (lambda N*K/young N)*(coupledAppellQ μ f K 2 N)^2  ≤  _ at hh
  rw [add_assoc,canonical_charge_sum_reindex K young lambda (coupledAppellQ μ f K) N hN] at hh
  have hcharge:(∑ b ∈ Finset.Icc 2 N,(lambda b*K/young b)*(coupledAppellQ μ f K 2 b)^2)=
      ∑ b ∈ Finset.Icc 2 N,kappa K young lambda b*(K^b*(b.factorial : ℝ)^2)⁻¹*
        actualCanonicalContractionSquare μ f 2 (b-1) := by
    apply Finset.sum_congr rfl
    intro b hb'
    exact actual_size_two_budget_charge f hK young lambda b
  rw [hcharge] at hh
  have hp:(∑ d ∈ Finset.Icc 3 N,selectedRowsPrefix young (thetaTriangleCoefficient theta)
      (fun a b=>if a=2 then lambda b else 0) d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)=
      ∑ d ∈ Finset.Icc 3 N,selectiveDegreePrefix young theta lambda d*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [selective_prefix_eq young theta lambda d (Finset.mem_Icc.mp hd).1]
  rw [hp] at hh
  have he:(∑ d ∈ Finset.Icc 3 N,(K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d))=
      (∑ d ∈ Finset.Icc 3 N,(K^d*(d.factorial : ℝ)^2)⁻¹*
        (actualAppellCoefficient μ f d ⬝ᵥ actualThetaProperRemainder μ f theta d))+
      ∑ d ∈ Finset.Icc 3 N,theta d*(K^d*(d.factorial : ℝ)^2)⁻¹*
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [actualThetaProperRemainder_pairing_split μ f theta d (Finset.mem_Icc.mp hd).1]
    ring
  rw [he]
  linarith

end KLSConstantImprovement.SignedReservedCanonicalDrift
#print axioms KLSConstantImprovement.SignedReservedCanonicalDrift.actual_selected_remainder_with_last_refund_le

#print axioms KLSConstantImprovement.SignedReservedCanonicalDrift.actual_full_reserved_proper_drift_le
