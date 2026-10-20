import KLSConstantImprovement.PositiveEnergyWeightedDrift
import KLSConstantImprovement.SignedWeightedGenerator
import KLSConstantImprovement.SignedRowReservedNoise
import KLSConstantImprovement.SignedQuadraticReservedNoise
import KLSConstantImprovement.GeneralWeightedCenteredHeat

/-! Signed generator assembly for arbitrary positive degree energy weights.
Every retained pair row and canonical square is paid by the actual full
previous weighted budget, including the finite last column. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLSConstantImprovement.PositiveEnergyWeightedGenerator
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSBelow25.PairTensor KLSBelow25.PairProjection
open KLSConstantImprovement.PositiveEnergyWeightedDrift
open KLSConstantImprovement.SignedRowReservedNoise
open KLSConstantImprovement.SignedRowNoiseHigh
open KLSConstantImprovement.SignedQuadraticReservedNoise
variable {n : ℕ}
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

def gamma (K : ℝ) (t theta : ℕ → ℝ) (d : ℕ) : ℝ :=
  1+theta (d+1)*t (d+1)/(t d*2*K*((d : ℝ)+1))
def degreeLoss (d : ℕ) (alpha g kap : ℝ) : ℝ :=
  (if d=2 then quadraticNoiseLoss alpha g kap else reservedNoiseLoss (d : ℝ) alpha g kap)+(d : ℝ)
def generatorLoss (K : ℝ) (young t alpha theta lambda : ℕ → ℝ) (d : ℕ) : ℝ :=
  degreeLoss d (alpha d) (gamma K t theta d) (kappa K young t lambda d)
def cost (K C : ℝ) (young t theta lambda : ℕ → ℝ) (d : ℕ) : ℝ :=
  (K*C/young d)*(d : ℝ)^2+if 3 ≤ d then firstCost young t theta lambda d else 0
def incoming (K : ℝ) (t alpha : ℕ → ℝ) (d : ℕ) : ℝ :=
  K*(t (d-1)/t d)*alpha (d-1)*(d : ℝ)^2
def coefficient (K C : ℝ) (young t alpha theta lambda : ℕ → ℝ) (d : ℕ) : ℝ :=
  incoming K t alpha d-generatorLoss K young t alpha theta lambda d-1-cost K C young t theta lambda d
def head (K C : ℝ) (young t alpha theta lambda : ℕ → ℝ) : ℝ :=
  generatorLoss K young t alpha theta lambda 2+1+cost K C young t theta lambda 2

theorem gamma_ge_one {K : ℝ} (hK : 0<K) (t theta : ℕ → ℝ) (d : ℕ)
    (ht : 0<t d) (htn : 0<t (d+1)) (hth : 0 ≤ theta (d+1)) : 1 ≤ gamma K t theta d := by
  unfold gamma
  exact le_add_of_nonneg_right (div_nonneg (mul_nonneg hth htn.le) (by positivity))

theorem reservedNoiseLoss_one_le {d alpha g kap : ℝ}
    (hd : 3 ≤ d) (ha : alpha<1) (hg : 1 ≤ g) :
    reservedNoiseLoss d alpha 1 kap ≤ reservedNoiseLoss d alpha g kap := by
  have hdm:0<d-1:=by linarith
  have hd0:0 ≤ d:=by linarith
  have hd2:0 ≤ d-2:=by linarith
  have hl:0 ≤ leadingNoiseCoefficient d:=by unfold leadingNoiseCoefficient;positivity
  have hh:0 ≤ highLeading d:=by unfold highLeading;positivity
  have hgs:(1:ℝ) ≤ g^2:=by nlinarith
  unfold reservedNoiseLoss
  apply max_le_max
  · apply sub_le_sub_right
    apply sub_le_sub_right
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by simpa using hgs) hl)
      (by linarith : 0 ≤ 1-alpha)
  · apply sub_le_sub_right
    apply sub_le_sub_right
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by simpa using hgs) hh)
      (by linarith : 0 ≤ 1-alpha)

theorem actual_reserved_degree_generator_lower
    {mu : Measure (Space n)} (hmu : admissibleMeasure mu) {f : Space n → ℝ} (hf : MemLp f 2 mu)
    (d : ℕ) (hd : 2 ≤ d) {alpha g kap : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha<1) (hg : 1 ≤ g) (hk : 0 ≤ kap)
    (hquad : d=2 → 3+kap ≤ 4*g^2/(1-alpha))
    (hpay : 3 ≤ d → ((d : ℝ)+kap)*(1-alpha) ≤ (d : ℝ)*g^2) :
    alpha*actualAppellEnergy mu f (d+1)-degreeLoss d alpha g kap*actualAppellEnergy mu f d-
      2*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellLowerDriftTensor mu f d)-
      kap*actualCanonicalContractionSquare mu f 2 (d-1)+
      (4*(g-1)/((d : ℝ)+1))*(actualAppellCoefficient mu f (d+1) ⬝ᵥ
        actualAppellPairContractionSum mu f (d+1)) ≤ actualAppellEnergyHeatGenerator mu f d := by
  let : IsProbabilityMeasure mu:=hmu.isProb
  by_cases h2:d=2
  · subst d
    have hh:=actual_noise_two_signed_reserved_lower hmu hf ha1 hk (hquad rfl)
    rw [SignedWeightedGenerator.actual_proper_three_eq_pair] at hh
    unfold actualAppellEnergyHeatGenerator
    rw [actualCovarianceAppellEnergy_generator_exact hmu hf 2]
    simp only [degreeLoss,ite_true,Nat.reduceSub,Nat.reduceAdd,Nat.cast_ofNat]
    linarith
  · have hd3:3 ≤ d:=by omega
    obtain ⟨r,hr⟩:=Nat.exists_eq_add_of_le hd3
    have hdr:d=r+3:=by omega
    rw [hdr]
    have hT:=actualAppellCoefficient_pair_symmetric (d:=r+3) hmu.logConcave hf
    have hW:=actualAppellCoefficient_pair_symmetric (d:=r+4) hmu.logConcave hf
    have hp:actualAppellPairContractionSum mu f (r+3+1)=
        creation (actualThirdCubicArray mu) (actualAppellCoefficient mu f (r+3)) := by
      simpa only [Nat.add_assoc,Nat.reduceAdd] using
        actualAppellPairContractionSum_eq_creation (r:=r+2) hmu hf
    have hqc:square (kernel (actualThirdCubicArray mu) (actualAppellCoefficient mu f (r+3))
        (incidentPair (0 : Fin (r+3))))=actualCanonicalContractionSquare mu f 2 (r+2) := by
      simpa only [Nat.add_assoc,Nat.reduceAdd] using
        actual_pair_kernel_square_eq_canonical (r:=r+1) hmu hf (incidentPair (0 : Fin (r+3)))
    have hpay':((r : ℝ)+3+kap)*(1-alpha) ≤ ((r : ℝ)+3)*g^2 := by
      simpa only [hdr,Nat.cast_add,Nat.cast_ofNat] using hpay hd3
    have hh:=actual_all_rank_signed_reserved_pair_noise hmu
      (actualAppellCoefficient mu f (r+3)) hT (actualAppellCoefficient mu f (r+4)) hW ha0 ha1 hg hk hpay'
    rw [hqc] at hh
    have hn:r+3≠2:=by omega
    have hs:r+3-1=r+2:=by omega
    rw [hp,hs]
    unfold actualAppellEnergyHeatGenerator
    rw [actualCovarianceAppellEnergy_generator_exact hmu hf (r+3)]
    simp only [degreeLoss,hn,ite_false,Nat.add_assoc,Nat.reduceAdd,square,actualAppellEnergy,
      PairTensor.pairing,dotProduct,Nat.cast_add,Nat.cast_ofNat] at hh ⊢
    ring_nf at hh ⊢
    linarith

theorem gamma_weight_identity {K : ℝ} (hK : 0<K) (t theta : ℕ → ℝ) (d : ℕ) (ht : 0<t d) :
    (4*(gamma K t theta d-1)/((d : ℝ)+1))*weight K t d=2*theta (d+1)*weight K t (d+1) := by
  have hd:(d : ℝ)+1≠0:=by positivity
  unfold weight gamma
  rw [CoupledEnergy.factorialWeight_step hK d]
  push_cast
  field_simp [ne_of_gt hK,ne_of_gt ht,hd]
  ring

theorem actual_terminal_eq
    {mu : Measure (Space n)} [IsProbabilityMeasure mu] (hmu : admissibleMeasure mu)
    (f : Lp ℝ 2 mu) (w : ℕ → ℝ) (N : ℕ)
    (hstat : ∀ ell : Lp ℝ 2 mu,GeneralWeighted.pairing f ell w N=
      GeneralWeighted.energy mu f w N*inner ℝ f ell) :
    (∑ d ∈ Finset.Icc 2 N,w d*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellCoefficient mu
      (fun x=>inner ℝ x (affineProjectionVector hmu.isotropic f)) d))=
      GeneralWeighted.energy mu f w N*actualAppellEnergy mu f 1 := by
  have hs:=hstat (isotropicLinearObservable hmu.isotropic (affineProjectionVector hmu.isotropic f))
  unfold GeneralWeighted.pairing at hs
  simp_rw [fullClassAppellTensor_linear_observable,actualAppell_tensor_inner_array] at hs
  rw [inner_isotropicLinearObservable_projection] at hs
  rw [hs,actualAppellEnergy_eq_norm_sq,fullClassAppellTensor_one_norm_sq hmu.logConcave hmu.isotropic]

theorem proper_sum_eq (mu : Measure (Space n)) (f : Space n → ℝ) (w : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 3 N,w d*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellProperRemainder mu f d))=
      ∑ d ∈ Finset.Icc 2 N,w d*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellProperRemainder mu f d) := by
  classical
  apply Finset.sum_subset (by intro d hd;simp only [Finset.mem_Icc] at hd ⊢;omega)
  intro d hd hn
  have hd2:d=2:=by simp only [Finset.mem_Icc] at hd hn;omega
  subst d
  rw [actualAppellProperRemainder_two_zero]
  simp

theorem retained_row_shift (w theta row : ℕ → ℝ) (N : ℕ) (hN : 3 ≤ N) :
    (∑ d ∈ Finset.Icc 2 N,if d<N then 2*theta (d+1)*w (d+1)*row (d+1) else 0)=
      2*(∑ d ∈ Finset.Icc 3 N,theta d*w d*row d) := by
  classical
  have hs:(Finset.Icc 2 N).filter (fun d=>d<N)=Finset.Icc 2 (N-1):=by
    ext d;simp only [Finset.mem_filter,Finset.mem_Icc];omega
  rw [←Finset.sum_filter,hs,Finset.mul_sum]
  apply Finset.sum_bij (fun d _=>d+1)
  · intro d hd;simp only [Finset.mem_Icc] at hd ⊢;omega
  · intro a ha b hb hab;omega
  · intro d hd
    simp only [Finset.mem_Icc] at hd
    refine ⟨d-1,?_,by omega⟩
    simp only [Finset.mem_Icc];omega
  · intro d hd;ring

theorem incoming_shift {K : ℝ} (hK : 0<K) (t alpha E : ℕ → ℝ)
    (ht : ∀ d,2 ≤ d → 0<t d) (ha : ∀ d,2 ≤ d → 0 ≤ alpha d) (hE : ∀ d,0 ≤ E d)
    (N : ℕ) (hN : 2 ≤ N) :
    (∑ d ∈ Finset.Icc 3 N,incoming K t alpha d*weight K t d*E d) ≤ 
      ∑ d ∈ Finset.Icc 2 N,alpha d*weight K t d*E (d+1) := by
  have hs:=CoupledEnergy.variable_factorial_weight_energy_shift E (fun d=>alpha d*t d) hK
    (fun d hd=>mul_nonneg (ha d hd) (ht d hd).le) hE N hN
  calc
    _=∑ d ∈ Finset.Icc 3 N,K*(alpha (d-1)*t (d-1))*(d : ℝ)^2*
        CoupledEnergy.factorialWeight K d*E d := by
      apply Finset.sum_congr rfl
      intro d hd
      have htd:t d≠0:=ne_of_gt (ht d (by have:=(Finset.mem_Icc.mp hd).1;omega))
      unfold incoming weight
      field_simp
    _ ≤ _:=hs
    _=_:=by apply Finset.sum_congr rfl;intro d hd;unfold weight;ring


theorem actual_centered_generator_sum_lower
    {mu : Measure (Space n)} [IsProbabilityMeasure mu] (hmu : admissibleMeasure mu)
    (f : Lp ℝ 2 mu) (hunit : ‖f‖=1) {K C : ℝ} (hK : 0<K)
    (young t alpha theta lambda : ℕ → ℝ)
    (hy : ∀ d,2 ≤ d → 0<young d) (ht : ∀ d,2 ≤ d → 0<t d)
    (ha0 : ∀ d,2 ≤ d → 0 ≤ alpha d) (ha1 : ∀ d,2 ≤ d → alpha d<1)
    (hth0 : ∀ d,3 ≤ d → 0 ≤ theta d) (hth1 : ∀ d,3 ≤ d → theta d ≤ 1)
    (hl0 : ∀ d,2 ≤ d → 0 ≤ lambda d) (hl1 : ∀ d,2 ≤ d → lambda d ≤ 1)
    (hboundary : ∀ d,2 ≤ d → lambda d=1 → theta (d+1)=1)
    (hquad : 3+kappa K young t lambda 2 ≤ 4*(gamma K t theta 2)^2/(1-alpha 2))
    (hpay : ∀ (d : ℕ),3 ≤ d → ((d : ℝ)+kappa K young t lambda d)*(1-alpha d) ≤ (d : ℝ))
    (N : ℕ) (hN : 3 ≤ N)
    (hprevious : ∀ g : Space n → ℝ,MemLp g 2 mu → 
      GeneralWeighted.energy mu g (weight K t) (N-1) ≤ C*(∫ x,(g x)^2 ∂mu))
    (hstat : ∀ ell : Lp ℝ 2 mu,GeneralWeighted.pairing f ell (weight K t) N=
      GeneralWeighted.energy mu f (weight K t) N*inner ℝ f ell)
    (hheat : GeneralWeighted.heatGenerator mu f (weight K t) N+
      GeneralWeighted.energy mu f (weight K t) N*actualAppellEnergy mu f 1 ≤ 0) :
    (∑ d ∈ Finset.Icc 2 N,alpha d*weight K t d*actualAppellEnergy mu f (d+1)) ≤ 
      ∑ d ∈ Finset.Icc 2 N,(generatorLoss K young t alpha theta lambda d+1+cost K C young t theta lambda d)*
        weight K t d*actualAppellEnergy mu f d := by
  classical
  let w:=weight K t
  let R:=∑ d ∈ Finset.Icc 2 N,w d*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellLowerDriftTensor mu f d)
  let D:=∑ d ∈ Finset.Icc 2 N,cost K C young t theta lambda d*w d*actualAppellEnergy mu f d
  let S:=∑ d ∈ Finset.Icc 2 N,alpha d*w d*actualAppellEnergy mu f (d+1)
  let L:=∑ d ∈ Finset.Icc 2 N,generatorLoss K young t alpha theta lambda d*w d*actualAppellEnergy mu f d
  let H:=∑ d ∈ Finset.Icc 2 N,kappa K young t lambda d*w d*actualCanonicalContractionSquare mu f 2 (d-1)
  let P:=∑ d ∈ Finset.Icc 3 N,theta d*w d*
    (actualAppellCoefficient mu f d ⬝ᵥ actualAppellPairContractionSum mu f d)
  have hg:∀ d,2 ≤ d → 1 ≤ gamma K t theta d := by
    intro d hd
    exact gamma_ge_one hK t theta d (ht d hd) (ht (d+1) (by omega)) (hth0 (d+1) (by omega))
  have hk:∀ d,2 ≤ d → 0 ≤ kappa K young t lambda d := by
    intro d hd
    unfold kappa
    exact div_nonneg (mul_nonneg (mul_nonneg (hl0 d hd) (ht 2 (by omega)).le) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) hK.le) (hy d hd).le)
  have hcell (d : ℕ) (hd:d∈Finset.Icc 2 N) :
      w d*(alpha d*actualAppellEnergy mu f (d+1)-generatorLoss K young t alpha theta lambda d*actualAppellEnergy mu f d-
        2*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellLowerDriftTensor mu f d)-
        kappa K young t lambda d*actualCanonicalContractionSquare mu f 2 (d-1))+
        (if d<N then 2*theta (d+1)*w (d+1)*
          (actualAppellCoefficient mu f (d+1) ⬝ᵥ actualAppellPairContractionSum mu f (d+1)) else 0)  ≤ 
      w d*actualAppellEnergyHeatGenerator mu f d := by
    have hd2:2 ≤ d:=(Finset.mem_Icc.mp hd).1
    by_cases hi:d<N
    · rw [ite_eq_left hi]
      have hp:3 ≤ d → ((d : ℝ)+kappa K young t lambda d)*(1-alpha d) ≤ (d : ℝ)*(gamma K t theta d)^2 := by
        intro hd3
        have hgs:(1:ℝ) ≤ (gamma K t theta d)^2:=by nlinarith [hg d hd2]
        exact (hpay d hd3).trans (le_mul_of_one_le_right (Nat.cast_nonneg _) hgs)
      have hq:d=2 → 3+kappa K young t lambda d ≤ 4*(gamma K t theta d)^2/(1-alpha d) := by
        intro hd'
        subst d
        exact hquad
      have hh:=mul_le_mul_of_nonneg_left
        (actual_reserved_degree_generator_lower hmu (Lp.memLp f) d hd2 (ha0 d hd2) (ha1 d hd2)
          (hg d hd2) (hk d hd2) hq hp) (weight_positive hK t d (ht d hd2)).le
      rw [mul_add,←mul_assoc,mul_comm (weight K t d)
        (4*(gamma K t theta d-1)/((d : ℝ)+1)),gamma_weight_identity hK t theta d (ht d hd2)] at hh
      exact hh
    · have hd3:3 ≤ d:=by have:=(Finset.mem_Icc.mp hd).2;omega
      rw [ite_eq_right hi,add_zero]
      have hq:d=2 → 3+kappa K young t lambda d ≤ 4*(1:ℝ)^2/(1-alpha d):=by intro hh;omega
      have hh:=actual_reserved_degree_generator_lower hmu (Lp.memLp f) d hd2 (ha0 d hd2) (ha1 d hd2)
        (le_refl (1:ℝ)) (hk d hd2) hq (by intro _;simpa using hpay d hd3)
      simp only [sub_self,mul_zero,zero_div,zero_mul,add_zero] at hh
      have hm:=reservedNoiseLoss_one_le (d:=(d : ℝ)) (kap:=kappa K young t lambda d)
        (by exact_mod_cast hd3) (ha1 d hd2) (hg d hd2)
      have hm':degreeLoss d (alpha d) 1 (kappa K young t lambda d) ≤ generatorLoss K young t alpha theta lambda d := by
        have hn:d≠2:=by omega
        simpa only [generatorLoss,degreeLoss,hn,ite_false,add_comm] using add_le_add_right hm (d : ℝ)
      have hp:=mul_le_mul_of_nonneg_right hm' (actualAppellEnergy_nonneg mu f d)
      have hh':alpha d*actualAppellEnergy mu f (d+1)-generatorLoss K young t alpha theta lambda d*actualAppellEnergy mu f d-
          2*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellLowerDriftTensor mu f d)-
          kappa K young t lambda d*actualCanonicalContractionSquare mu f 2 (d-1) ≤ actualAppellEnergyHeatGenerator mu f d := by
        linarith
      exact mul_le_mul_of_nonneg_left hh' (weight_positive hK t d (ht d hd2)).le
  have hlower:=Finset.sum_le_sum hcell
  have he:S-L-2*R-H+2*P=∑ d ∈ Finset.Icc 2 N,
      (w d*(alpha d*actualAppellEnergy mu f (d+1)-generatorLoss K young t alpha theta lambda d*actualAppellEnergy mu f d-
        2*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellLowerDriftTensor mu f d)-
        kappa K young t lambda d*actualCanonicalContractionSquare mu f 2 (d-1))+
        (if d<N then 2*theta (d+1)*w (d+1)*
          (actualAppellCoefficient mu f (d+1) ⬝ᵥ actualAppellPairContractionSum mu f (d+1)) else 0)) := by
    rw [Finset.sum_add_distrib,retained_row_shift w theta
      (fun d=>actualAppellCoefficient mu f d ⬝ᵥ actualAppellPairContractionSum mu f d) N hN]
    dsimp only [S,L,R,H,P]
    rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hlower':S-L-2*R-H+2*P ≤ GeneralWeighted.heatGenerator mu f w N := by
    rw [he]
    exact hlower
  have hproper:=PositiveEnergyWeightedDrift.actual_full_reserved_proper_drift_le hmu (Lp.memLp f) hK
    young t theta lambda hy ht hth1 hl1 hboundary N hN hprevious
  have hcost:(∑ d ∈ Finset.Icc 3 N,firstCost young t theta lambda d*w d*actualAppellEnergy mu f d)+
      (∑ d ∈ Finset.Icc 2 N,(K*C/young d)*(d : ℝ)^2*w d*actualAppellEnergy mu f d)=D := by
    dsimp only [D,cost]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    have hs:(Finset.Icc 2 N).filter (fun d=>3 ≤ d)=Finset.Icc 3 N := by
      ext d;simp only [Finset.mem_filter,Finset.mem_Icc];omega
    simp_rw [ite_mul,zero_mul]
    rw [←Finset.sum_filter,hs]
    ring
  change 2*(∑ d ∈ Finset.Icc 3 N,w d*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellProperRemainder mu f d))+H  ≤ 
    (∑ d ∈ Finset.Icc 3 N,firstCost young t theta lambda d*w d*actualAppellEnergy mu f d)+
    (∑ d ∈ Finset.Icc 2 N,(K*C/young d)*(d : ℝ)^2*w d*actualAppellEnergy mu f d)+2*P at hproper
  rw [hcost,proper_sum_eq mu f w N] at hproper
  have hterm:=actual_terminal_eq hmu f w N hstat
  have hb:actualAppellEnergy mu f 1 ≤ 1 := by
    rw [actualAppellEnergy_eq_norm_sq]
    simpa only [hunit,one_pow] using fullClassAppellTensor_one_norm_sq_le hmu.logConcave hmu.isotropic f
  have hM:=GeneralWeighted.energy_nonneg mu f w (fun d hd=>(weight_positive hK t d (ht d hd)).le) N
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
  have hdrift':2*R-2*P+H-GeneralWeighted.energy mu f w N*actualAppellEnergy mu f 1 ≤ 
      GeneralWeighted.energy mu f w N+D := by
    rw [hdrift]
    linarith
  have hr:(∑ d ∈ Finset.Icc 2 N,(generatorLoss K young t alpha theta lambda d+1+cost K C young t theta lambda d)*
      w d*actualAppellEnergy mu f d)=L+GeneralWeighted.energy mu f w N+D := by
    dsimp only [L,D]
    unfold GeneralWeighted.energy
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  change S ≤ _
  rw [hr]
  linarith

theorem actual_generator_coefficients_nonpos
    {mu : Measure (Space n)} [IsProbabilityMeasure mu] (hmu : admissibleMeasure mu)
    (f : Lp ℝ 2 mu) (hunit : ‖f‖=1) {K C : ℝ} (hK : 0<K)
    (young t alpha theta lambda : ℕ → ℝ)
    (hy : ∀ d,2 ≤ d → 0<young d) (ht : ∀ d,2 ≤ d → 0<t d)
    (ha0 : ∀ d,2 ≤ d → 0 ≤ alpha d) (ha1 : ∀ d,2 ≤ d → alpha d<1)
    (hth0 : ∀ d,3 ≤ d → 0 ≤ theta d) (hth1 : ∀ d,3 ≤ d → theta d ≤ 1)
    (hl0 : ∀ d,2 ≤ d → 0 ≤ lambda d) (hl1 : ∀ d,2 ≤ d → lambda d ≤ 1)
    (hboundary : ∀ d,2 ≤ d → lambda d=1 → theta (d+1)=1)
    (hquad : 3+kappa K young t lambda 2 ≤ 4*(gamma K t theta 2)^2/(1-alpha 2))
    (hpay : ∀ (d : ℕ),3 ≤ d → ((d : ℝ)+kappa K young t lambda d)*(1-alpha d) ≤ (d : ℝ))
    (N : ℕ) (hN : 3 ≤ N)
    (hprevious : ∀ g : Space n → ℝ,MemLp g 2 mu → 
      GeneralWeighted.energy mu g (weight K t) (N-1) ≤ C*(∫ x,(g x)^2 ∂mu))
    (hstat : ∀ ell : Lp ℝ 2 mu,GeneralWeighted.pairing f ell (weight K t) N=
      GeneralWeighted.energy mu f (weight K t) N*inner ℝ f ell)
    (hheat : GeneralWeighted.heatGenerator mu f (weight K t) N+
      GeneralWeighted.energy mu f (weight K t) N*actualAppellEnergy mu f 1 ≤ 0) :
    (∑ d ∈ Finset.Icc 3 N,coefficient K C young t alpha theta lambda d*
      (weight K t d*actualAppellEnergy mu f d))-
      head K C young t alpha theta lambda*(weight K t 2*actualAppellEnergy mu f 2) ≤ 0 := by
  classical
  have hlower:=actual_centered_generator_sum_lower hmu f hunit hK young t alpha theta lambda
    hy ht ha0 ha1 hth0 hth1 hl0 hl1 hboundary hquad hpay N hN hprevious hstat hheat
  have hshift:=incoming_shift hK t alpha (fun d=>actualAppellEnergy mu f d) ht ha0
    (fun d=>actualAppellEnergy_nonneg _ _ _) N (by omega)
  have hsum:=hshift.trans hlower
  have hs:Finset.Icc 2 N=insert 2 (Finset.Icc 3 N) := by
    ext d;simp only [Finset.mem_Icc,Finset.mem_insert];omega
  have hn:2∉Finset.Icc 3 N:=by simp
  have he:(∑ d ∈ Finset.Icc 3 N,coefficient K C young t alpha theta lambda d*
      (weight K t d*actualAppellEnergy mu f d))-
      head K C young t alpha theta lambda*(weight K t 2*actualAppellEnergy mu f 2)=
      (∑ d ∈ Finset.Icc 3 N,incoming K t alpha d*weight K t d*actualAppellEnergy mu f d)-
      ∑ d ∈ Finset.Icc 2 N,(generatorLoss K young t alpha theta lambda d+1+cost K C young t theta lambda d)*
        weight K t d*actualAppellEnergy mu f d := by
    rw [hs,Finset.sum_insert hn]
    have htail:(∑ d ∈ Finset.Icc 3 N,coefficient K C young t alpha theta lambda d*
        (weight K t d*actualAppellEnergy mu f d))=
        (∑ d ∈ Finset.Icc 3 N,incoming K t alpha d*weight K t d*actualAppellEnergy mu f d)-
        ∑ d ∈ Finset.Icc 3 N,(generatorLoss K young t alpha theta lambda d+1+cost K C young t theta lambda d)*
          weight K t d*actualAppellEnergy mu f d := by
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      unfold coefficient
      ring
    rw [htail]
    unfold head
    ring
  rw [he]
  exact sub_nonpos.mpr hsum

end KLSConstantImprovement.PositiveEnergyWeightedGenerator
#print axioms KLSConstantImprovement.PositiveEnergyWeightedGenerator.actual_reserved_degree_generator_lower
#print axioms KLSConstantImprovement.PositiveEnergyWeightedGenerator.incoming_shift

#print axioms KLSConstantImprovement.PositiveEnergyWeightedGenerator.actual_generator_coefficients_nonpos
