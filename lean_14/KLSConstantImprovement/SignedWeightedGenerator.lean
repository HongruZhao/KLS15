import KLSConstantImprovement.SignedRowNoiseHigh
import ActualThetaWeightedAppellDrift
import ActualCubicJointGenerator
import ActualCenteredAppellTerminal
import CoupledVariableEnergyShift

/-! Exact signed completion of every retained proper size-two row.
The finite last cell uses gamma=1 and is dominated by the profile loss;
there is no assumption about an unobserved row beyond the degree cutoff. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLSConstantImprovement.SignedWeightedGenerator
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSBelow25.PairTensor KLSBelow25.PairProjection
open KLSConstantImprovement.SignedRowNoiseHigh
variable {n : ℕ}
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

def gamma (K : ℝ) (theta : ℕ → ℝ) (d : ℕ) : ℝ :=
  1+theta (d+1)/(2*K*((d : ℝ)+1))

def generatorLoss (K : ℝ) (alpha theta : ℕ → ℝ) (d : ℕ) : ℝ :=
  if d=2 then 64*(gamma K theta 2)^2/(3*(1-alpha 2))-18
  else signedNoiseLoss (d : ℝ) (alpha d) (gamma K theta d)+(d : ℝ)

def cost (K C : ℝ) (young theta : ℕ → ℝ) (d : ℕ) : ℝ :=
  (K*C/young d)*(d : ℝ)^2+if 3 ≤ d then thetaDegreePrefix young theta d else 0

def coefficient (K C : ℝ) (young alpha theta : ℕ → ℝ) (d : ℕ) : ℝ :=
  K*alpha (d-1)*(d : ℝ)^2-generatorLoss K alpha theta d-1-cost K C young theta d

def head (K C : ℝ) (young alpha theta : ℕ → ℝ) : ℝ :=
  generatorLoss K alpha theta 2+1+cost K C young theta 2

theorem gamma_ge_one {K : ℝ} (hK : 0<K) (theta : ℕ → ℝ)
    (d : ℕ) (ht : 0 ≤ theta (d+1)) : 1 ≤ gamma K theta d := by
  unfold gamma
  exact le_add_of_nonneg_right (div_nonneg ht (by positivity))

theorem signedNoiseLoss_one_le {d beta g : ℝ}
    (hd : 3 ≤ d) (hb : beta<1) (hg : 1 ≤ g) :
    signedNoiseLoss d beta 1 ≤ signedNoiseLoss d beta g := by
  have hdm : 0<d-1 := by linarith
  have hd0 : 0 ≤ d := by linarith
  have hd2 : 0 ≤ d-2 := by linarith
  have hl : 0 ≤ leadingNoiseCoefficient d := by unfold leadingNoiseCoefficient; positivity
  have hh : 0 ≤ highLeading d := by unfold highLeading; positivity
  have hgs : (1 : ℝ) ≤ g^2 := by nlinarith
  unfold signedNoiseLoss
  apply max_le_max
  · apply sub_le_sub_right
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by simpa using hgs) hl)
      (by linarith : 0 ≤ 1-beta)
  · apply sub_le_sub_right
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by simpa using hgs) hh)
      (by linarith : 0 ≤ 1-beta)

theorem actual_proper_three_eq_pair (mu : Measure (Space n)) (f : Space n→ℝ) :
    actualAppellProperRemainder mu f 3=actualAppellPairContractionSum mu f 3 := by
  rw [actualAppellProperRemainder_eq_pair_add_higher mu f 3 (by omega)]
  have hh : actualAppellHigherContractionSum mu f 3=0 := by
    unfold actualAppellHigherContractionSum
    apply Finset.sum_eq_zero
    intro S hS
    have hn : ¬(3 ≤ S.card ∧ S.card ≤ 3-1) := by omega
    simp [hn]
  rw [hh,add_zero]

theorem actual_signed_degree_generator_lower
    {mu : Measure (Space n)} (hmu : admissibleMeasure mu)
    {f : Space n→ℝ} (hf : MemLp f 2 mu) (d : ℕ) (hd : 3 ≤ d)
    {beta g : ℝ} (hb0 : 0 ≤ beta) (hb1 : beta<1) (hg : 1 ≤ g) :
    beta*actualAppellEnergy mu f (d+1)-
      (signedNoiseLoss (d : ℝ) beta g+(d : ℝ))*actualAppellEnergy mu f d-
      2*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellLowerDriftTensor mu f d)+
      (4*(g-1)/((d : ℝ)+1))*(actualAppellCoefficient mu f (d+1) ⬝ᵥ
        actualAppellPairContractionSum mu f (d+1))  ≤ 
    actualAppellEnergyHeatGenerator mu f d := by
  let : IsProbabilityMeasure mu := hmu.isProb
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hd
  have hdr : d=r+3 := by omega
  rw [hdr]
  have hT := actualAppellCoefficient_pair_symmetric (d:=r+3) hmu.logConcave hf
  have hW := actualAppellCoefficient_pair_symmetric (d:=r+4) hmu.logConcave hf
  have hp : actualAppellPairContractionSum mu f (r+3+1)=
      creation (actualThirdCubicArray mu) (actualAppellCoefficient mu f (r+3)) := by
    simpa only [Nat.add_assoc,Nat.reduceAdd] using
      actualAppellPairContractionSum_eq_creation (r:=r+2) hmu hf
  rw [hp]
  have hh := actual_all_rank_signed_pair_noise_unrestricted hmu
    (actualAppellCoefficient mu f (r+3)) hT (actualAppellCoefficient mu f (r+4)) hW hb0 hb1 hg
  unfold actualAppellEnergyHeatGenerator
  rw [actualCovarianceAppellEnergy_generator_exact hmu hf (r+3)]
  simp only [Nat.add_assoc,Nat.reduceAdd,square,actualAppellEnergy,pairing,dotProduct,Nat.cast_add,Nat.cast_ofNat] at hh ⊢
  ring_nf at hh ⊢
  linarith

theorem gamma_weight_identity {K : ℝ} (hK : 0<K)
    (theta : ℕ→ℝ) (d : ℕ) :
    (4*(gamma K theta d-1)/((d : ℝ)+1))*CoupledEnergy.factorialWeight K d=
      2*theta (d+1)*CoupledEnergy.factorialWeight K (d+1) := by
  have hd : (d : ℝ)+1≠0 := by positivity
  rw [CoupledEnergy.factorialWeight_step hK d]
  unfold gamma
  push_cast
  field_simp [ne_of_gt hK,hd]
  ring

theorem actual_signed_weighted_degree_lower
    {mu : Measure (Space n)} (hmu : admissibleMeasure mu)
    {f : Space n→ℝ} (hf : MemLp f 2 mu) {K : ℝ} (hK : 0<K)
    (alpha theta : ℕ→ℝ) (d : ℕ) (hd : 2 ≤ d)
    (hb0 : 0 ≤ alpha d) (hb1 : alpha d<1) (ht : 0 ≤ theta (d+1))
    (hQ : 2-4*(gamma K theta 2)^2/(3*(1-alpha 2)) ≤ 0)
    (hR : 1-8*(gamma K theta 2)^2/(3*(1-alpha 2)) ≤ 0) :
    CoupledEnergy.factorialWeight K d*(alpha d*actualAppellEnergy mu f (d+1)-
      generatorLoss K alpha theta d*actualAppellEnergy mu f d-
      2*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellLowerDriftTensor mu f d))+
      2*theta (d+1)*CoupledEnergy.factorialWeight K (d+1)*
        (actualAppellCoefficient mu f (d+1) ⬝ᵥ actualAppellPairContractionSum mu f (d+1))  ≤ 
    CoupledEnergy.factorialWeight K d*actualAppellEnergyHeatGenerator mu f d := by
  by_cases h2 : d=2
  · subst d
    have hg : gamma K theta 2=1+theta 3/(6*K) := by norm_num [gamma]; ring
    have hh := actual_weighted_generator_two_joint_proper_three_lower
      (θ:=theta 3) (s:=(1:ℝ)) (lmb:=0) hmu hf hK hb1
      (by simpa [hg] using hQ) (by simpa [hg] using hR)
    rw [actual_proper_three_eq_pair] at hh
    simp only [zero_div,zero_mul,mul_zero,sub_zero,add_zero] at hh
    unfold generatorLoss
    simp only [ite_true,Nat.reduceAdd]
    rw [hg]
    linarith
  · have hd3 : 3 ≤ d := by omega
    have hh := mul_le_mul_of_nonneg_left
      (actual_signed_degree_generator_lower hmu hf d hd3 hb0 hb1 (gamma_ge_one hK theta d ht))
      (CoupledEnergy.factorialWeight_nonneg hK d)
    rw [mul_add,←mul_assoc,mul_comm (CoupledEnergy.factorialWeight K d)
      (4*(gamma K theta d-1)/((d : ℝ)+1)),gamma_weight_identity hK theta d] at hh
    simpa only [generatorLoss,h2,ite_false] using hh

theorem actual_signed_last_degree_lower
    {mu : Measure (Space n)} (hmu : admissibleMeasure mu)
    {f : Space n→ℝ} (hf : MemLp f 2 mu) {K : ℝ} (hK : 0<K)
    (alpha theta : ℕ→ℝ) (d : ℕ) (hd : 3 ≤ d)
    (hb0 : 0 ≤ alpha d) (hb1 : alpha d<1) (ht : 0 ≤ theta (d+1)) :
    alpha d*actualAppellEnergy mu f (d+1)-generatorLoss K alpha theta d*actualAppellEnergy mu f d-
      2*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellLowerDriftTensor mu f d)  ≤ 
    actualAppellEnergyHeatGenerator mu f d := by
  have hh := actual_signed_degree_generator_lower hmu hf d hd hb0 hb1 (le_refl (1:ℝ))
  simp only [sub_self,mul_zero,zero_div,zero_mul,add_zero] at hh
  have hdr : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hl := signedNoiseLoss_one_le hdr hb1 (gamma_ge_one hK theta d ht)
  have hm := mul_le_mul_of_nonneg_right hl (actualAppellEnergy_nonneg mu f d)
  have h2 : d≠2 := by omega
  simp only [generatorLoss,h2,ite_false]
  linarith

theorem retained_row_shift (K : ℝ) (theta row : ℕ→ℝ) (N : ℕ) (hN : 3 ≤ N) :
    (∑ d ∈ Finset.Icc 2 N, if d<N then
      2*theta (d+1)*CoupledEnergy.factorialWeight K (d+1)*row (d+1) else 0)=
      2*(∑ d ∈ Finset.Icc 3 N, theta d*CoupledEnergy.factorialWeight K d*row d) := by
  classical
  have hs : (Finset.Icc 2 N).filter (fun d=>d<N)=Finset.Icc 2 (N-1) := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc]
    omega
  rw [←Finset.sum_filter,hs,Finset.mul_sum]
  apply Finset.sum_bij (fun d _=>d+1)
  · intro d hd
    simp only [Finset.mem_Icc] at hd ⊢
    omega
  · intro a ha b hb hab
    omega
  · intro d hd
    simp only [Finset.mem_Icc] at hd
    refine ⟨d-1,?_,by omega⟩
    simp only [Finset.mem_Icc]
    omega
  · intro d hd
    ring

theorem actual_signed_centered_generator_sum_lower
    {mu : Measure (Space n)} [IsProbabilityMeasure mu] (hmu : admissibleMeasure mu)
    (f : Lp ℝ 2 mu) (hunit : ‖f‖=1) {K C : ℝ} (hK : 0<K)
    (young alpha theta : ℕ→ℝ)
    (hy : ∀ b,2 ≤ b→0<young b)
    (ha0 : ∀ d,2 ≤ d→0 ≤ alpha d) (ha1 : ∀ d,2 ≤ d→alpha d<1)
    (ht0 : ∀ d,3 ≤ d→0 ≤ theta d) (ht1 : ∀ d,3 ≤ d→theta d ≤ 1)
    (hQ : 2-4*(gamma K theta 2)^2/(3*(1-alpha 2)) ≤ 0)
    (hR : 1-8*(gamma K theta 2)^2/(3*(1-alpha 2)) ≤ 0)
    (N : ℕ) (hN : 3 ≤ N)
    (hprevious : ∀ g : Space n→ℝ,MemLp g 2 mu→
      actualWeightedAppellEnergy mu g K (N-1) ≤ C*(∫ x,(g x)^2 ∂mu))
    (hstat : ∀ ell : Lp ℝ 2 mu,actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy mu f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator mu f K N+
      actualWeightedAppellEnergy mu f K N*actualAppellEnergy mu f 1 ≤ 0) :
    (∑ d ∈ Finset.Icc 2 N,alpha d*CoupledEnergy.factorialWeight K d*actualAppellEnergy mu f (d+1)) ≤ 
      ∑ d ∈ Finset.Icc 2 N,(generatorLoss K alpha theta d+1+cost K C young theta d)*
        CoupledEnergy.factorialWeight K d*actualAppellEnergy mu f d := by
  classical
  let w:=CoupledEnergy.factorialWeight K
  let R:=∑ d ∈ Finset.Icc 2 N,w d*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellLowerDriftTensor mu f d)
  let D:=∑ d ∈ Finset.Icc 2 N,cost K C young theta d*w d*actualAppellEnergy mu f d
  let S:=∑ d ∈ Finset.Icc 2 N,alpha d*w d*actualAppellEnergy mu f (d+1)
  let L:=∑ d ∈ Finset.Icc 2 N,generatorLoss K alpha theta d*w d*actualAppellEnergy mu f d
  let P:=∑ d ∈ Finset.Icc 3 N,theta d*w d*
    (actualAppellCoefficient mu f d ⬝ᵥ actualAppellPairContractionSum mu f d)
  have hcell (d : ℕ) (hd : d ∈ Finset.Icc 2 N) :
      w d*(alpha d*actualAppellEnergy mu f (d+1)-generatorLoss K alpha theta d*actualAppellEnergy mu f d-
        2*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellLowerDriftTensor mu f d))+
        (if d<N then 2*theta (d+1)*w (d+1)*
          (actualAppellCoefficient mu f (d+1) ⬝ᵥ actualAppellPairContractionSum mu f (d+1)) else 0) ≤ 
      w d*actualAppellEnergyHeatGenerator mu f d := by
    have hd2:2 ≤ d:=(Finset.mem_Icc.mp hd).1
    by_cases hi:d<N
    · rw [ite_eq_left hi]
      exact actual_signed_weighted_degree_lower hmu (Lp.memLp f) hK alpha theta d hd2
        (ha0 d hd2) (ha1 d hd2) (ht0 (d+1) (by omega)) hQ hR
    · have hd3:3 ≤ d:=by have := (Finset.mem_Icc.mp hd).2;omega
      rw [ite_eq_right hi,add_zero]
      exact mul_le_mul_of_nonneg_left
        (actual_signed_last_degree_lower hmu (Lp.memLp f) hK alpha theta d hd3
          (ha0 d hd2) (ha1 d hd2) (ht0 (d+1) (by omega))) (CoupledEnergy.factorialWeight_nonneg hK d)
  have hlower:=Finset.sum_le_sum hcell
  have he:S-L-2*R+2*P=∑ d ∈ Finset.Icc 2 N,
      (w d*(alpha d*actualAppellEnergy mu f (d+1)-generatorLoss K alpha theta d*actualAppellEnergy mu f d-
        2*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellLowerDriftTensor mu f d))+
        (if d<N then 2*theta (d+1)*w (d+1)*
          (actualAppellCoefficient mu f (d+1) ⬝ᵥ actualAppellPairContractionSum mu f (d+1)) else 0)) := by
    rw [Finset.sum_add_distrib,retained_row_shift K theta
      (fun d=>actualAppellCoefficient mu f d ⬝ᵥ actualAppellPairContractionSum mu f d) N hN]
    dsimp only [S,L,R,P,w]
    rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hlower':S-L-2*R+2*P ≤ actualWeightedAppellHeatGenerator mu f K N := by
    rw [he]
    exact hlower
  have hproper:=actual_weighted_proper_drift_retained_pair_le hmu (Lp.memLp f)
    young theta hK hy ht1 N hprevious
  have hcost:(∑ d ∈ Finset.Icc 3 N,thetaDegreePrefix young theta d*w d*actualAppellEnergy mu f d)+
      (∑ d ∈ Finset.Icc 2 N,(K*C/young d)*(d : ℝ)^2*w d*actualAppellEnergy mu f d)=D := by
    dsimp only [D,cost]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    have hs:(Finset.Icc 2 N).filter (fun d=>3 ≤ d)=Finset.Icc 3 N := by
      ext d
      simp only [Finset.mem_filter,Finset.mem_Icc]
      omega
    simp_rw [ite_mul,zero_mul]
    rw [←Finset.sum_filter,hs]
    ring
  change _ ≤ (∑ d ∈ Finset.Icc 3 N,thetaDegreePrefix young theta d*w d*actualAppellEnergy mu f d)+
    (∑ d ∈ Finset.Icc 2 N,(K*C/young d)*(d : ℝ)^2*w d*actualAppellEnergy mu f d)+2*P at hproper
  rw [hcost,actual_weighted_proper_drift_sum_eq f K N] at hproper
  have ht:=actual_weighted_terminal_eq hmu f K N hstat
  have hb:actualAppellEnergy mu f 1 ≤ 1 := by
    rw [actualAppellEnergy_eq_norm_sq]
    simpa only [hunit,one_pow] using fullClassAppellTensor_one_norm_sq_le hmu.logConcave hmu.isotropic f
  have hM:=actualWeightedAppellEnergy_nonneg mu f hK N
  have hMb:=mul_le_of_le_one_right hM hb
  have hdrift:R=(∑ d ∈ Finset.Icc 2 N,w d*(actualAppellCoefficient mu f d ⬝ᵥ
      actualAppellCoefficient mu (fun x=>inner ℝ x (affineProjectionVector hmu.isotropic f)) d))+
      ∑ d ∈ Finset.Icc 2 N,w d*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellProperRemainder mu f d) := by
    dsimp only [R]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [actualAppellLowerDriftTensor_terminal_split hmu.logConcave hmu.isotropic f
      (Finset.mem_Icc.mp hd).1,dotProduct_add]
    ring
  have hdrift':2*R-2*P-actualWeightedAppellEnergy mu f K N*actualAppellEnergy mu f 1 ≤ 
      actualWeightedAppellEnergy mu f K N+D := by
    rw [hdrift]
    dsimp only [w,CoupledEnergy.factorialWeight] at *
    linarith
  have hr:(∑ d ∈ Finset.Icc 2 N,(generatorLoss K alpha theta d+1+cost K C young theta d)*
      w d*actualAppellEnergy mu f d)=L+actualWeightedAppellEnergy mu f K N+D := by
    dsimp only [L,D,w,CoupledEnergy.factorialWeight]
    unfold actualWeightedAppellEnergy
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  change S ≤ _
  rw [hr]
  linarith

theorem actual_signed_generator_coefficients_nonpos
    {mu : Measure (Space n)} [IsProbabilityMeasure mu] (hmu : admissibleMeasure mu)
    (f : Lp ℝ 2 mu) (hunit : ‖f‖=1) {K C : ℝ} (hK : 0<K)
    (young alpha theta : ℕ→ℝ)
    (hy : ∀ b,2 ≤ b→0<young b)
    (ha0 : ∀ d,2 ≤ d→0 ≤ alpha d) (ha1 : ∀ d,2 ≤ d→alpha d<1)
    (ht0 : ∀ d,3 ≤ d→0 ≤ theta d) (ht1 : ∀ d,3 ≤ d→theta d ≤ 1)
    (hQ : 2-4*(gamma K theta 2)^2/(3*(1-alpha 2)) ≤ 0)
    (hR : 1-8*(gamma K theta 2)^2/(3*(1-alpha 2)) ≤ 0)
    (N : ℕ) (hN : 3 ≤ N)
    (hprevious : ∀ g : Space n→ℝ,MemLp g 2 mu→
      actualWeightedAppellEnergy mu g K (N-1) ≤ C*(∫ x,(g x)^2 ∂mu))
    (hstat : ∀ ell : Lp ℝ 2 mu,actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy mu f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator mu f K N+
      actualWeightedAppellEnergy mu f K N*actualAppellEnergy mu f 1 ≤ 0) :
    (∑ d ∈ Finset.Icc 3 N,coefficient K C young alpha theta d*
      (CoupledEnergy.factorialWeight K d*actualAppellEnergy mu f d))-
      head K C young alpha theta*(CoupledEnergy.factorialWeight K 2*actualAppellEnergy mu f 2) ≤ 0 := by
  classical
  have hlower:=actual_signed_centered_generator_sum_lower hmu f hunit hK young alpha theta
    hy ha0 ha1 ht0 ht1 hQ hR N hN hprevious hstat hheat
  have hshift:=CoupledEnergy.variable_factorial_weight_energy_shift
    (fun d=>actualAppellEnergy mu f d) alpha hK ha0 (fun d=>actualAppellEnergy_nonneg _ _ _) N (by omega)
  have hsum:=hshift.trans hlower
  have hs:Finset.Icc 2 N=insert 2 (Finset.Icc 3 N) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hn:2∉Finset.Icc 3 N := by simp
  have he:(∑ d ∈ Finset.Icc 3 N,coefficient K C young alpha theta d*
      (CoupledEnergy.factorialWeight K d*actualAppellEnergy mu f d))-
      head K C young alpha theta*(CoupledEnergy.factorialWeight K 2*actualAppellEnergy mu f 2)=
      (∑ d ∈ Finset.Icc 3 N,K*alpha (d-1)*(d : ℝ)^2*
        CoupledEnergy.factorialWeight K d*actualAppellEnergy mu f d)-
      ∑ d ∈ Finset.Icc 2 N,(generatorLoss K alpha theta d+1+cost K C young theta d)*
        CoupledEnergy.factorialWeight K d*actualAppellEnergy mu f d := by
    rw [hs,Finset.sum_insert hn]
    have ht:(∑ d ∈ Finset.Icc 3 N,coefficient K C young alpha theta d*
        (CoupledEnergy.factorialWeight K d*actualAppellEnergy mu f d))=
        (∑ d ∈ Finset.Icc 3 N,K*alpha (d-1)*(d : ℝ)^2*
          CoupledEnergy.factorialWeight K d*actualAppellEnergy mu f d)-
        ∑ d ∈ Finset.Icc 3 N,(generatorLoss K alpha theta d+1+cost K C young theta d)*
          CoupledEnergy.factorialWeight K d*actualAppellEnergy mu f d := by
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      unfold coefficient
      ring
    rw [ht]
    unfold head
    ring
  rw [he]
  exact sub_nonpos.mpr hsum

end KLSConstantImprovement.SignedWeightedGenerator
#print axioms KLSConstantImprovement.SignedWeightedGenerator.actual_signed_degree_generator_lower
#print axioms KLSConstantImprovement.SignedWeightedGenerator.actual_signed_last_degree_lower
#print axioms KLSConstantImprovement.SignedWeightedGenerator.actual_signed_generator_coefficients_nonpos
