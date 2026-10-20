import KLSConstantImprovement.PositiveEnergyWeightedGenerator
import KLSConstantImprovement.TriplePositiveEnergyWeightedBudgetDrift

/-! Actual signed generator with reserved canonical pair squares and weighted
harmonic triple rows, including the finite last column. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLSConstantImprovement.TriplePositiveEnergyWeightedGenerator
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSBelow25.PairTensor KLSBelow25.PairProjection
open KLSConstantImprovement.PositiveEnergyWeightedDrift
open KLSConstantImprovement.PositiveEnergyWeightedGenerator
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudgetDrift (rawFirstCost)
open KLSConstantImprovement.SignedRowReservedNoise
open KLSConstantImprovement.SignedRowNoiseHigh
open KLSConstantImprovement.SignedQuadraticReservedNoise
variable {n : ℕ}
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

def cost (K C : ℝ) (young t theta lambda zeta : ℕ → ℝ) (d : ℕ) : ℝ :=
  (K*C/young d)*(d : ℝ)^2+(if 3 ≤ d then rawFirstCost young t theta lambda zeta d else 0)+
    t 3*tripleHarmonicNeighborCharge K young zeta d

def coefficient (K C : ℝ) (young t alpha theta lambda zeta : ℕ → ℝ) (d : ℕ) : ℝ :=
  incoming K t alpha d-generatorLoss K young t alpha theta lambda d-1-cost K C young t theta lambda zeta d

def head (K C : ℝ) (young t alpha theta lambda zeta : ℕ → ℝ) : ℝ :=
  generatorLoss K young t alpha theta lambda 2+1+cost K C young t theta lambda zeta 2

theorem actual_centered_generator_sum_lower
    {mu : Measure (Space n)} [IsProbabilityMeasure mu] (hmu : admissibleMeasure mu)
    (f : Lp ℝ 2 mu) (hunit : ‖f‖=1) {K C : ℝ} (hK : 0<K)
    (young t alpha theta lambda zeta : ℕ → ℝ)
    (hy : ∀ d,2 ≤ d → 0<young d) (ht : ∀ d,2 ≤ d → 0<t d)
    (ha0 : ∀ d,2 ≤ d → 0 ≤ alpha d) (ha1 : ∀ d,2 ≤ d → alpha d<1)
    (hth0 : ∀ d,3 ≤ d → 0 ≤ theta d) (hth1 : ∀ d,3 ≤ d → theta d ≤ 1)
    (hl0 : ∀ d,2 ≤ d → 0 ≤ lambda d) (hl1 : ∀ d,2 ≤ d → lambda d ≤ 1)
    (hboundary : ∀ d,2 ≤ d → lambda d=1 → theta (d+1)=1)
    (hz : ∀ b,2 ≤ b → 0 ≤ zeta b)
    (hcap : ∀ (b : ℕ),2 ≤ b → tripleHarmonicRatio (b : ℝ)*zeta b<1)
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
      ∑ d ∈ Finset.Icc 2 N,(generatorLoss K young t alpha theta lambda d+1+cost K C young t theta lambda zeta d)*
        weight K t d*actualAppellEnergy mu f d := by
  classical
  let w:=weight K t
  let R:=∑ d ∈ Finset.Icc 2 N,w d*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellLowerDriftTensor mu f d)
  let D:=∑ d ∈ Finset.Icc 2 N,cost K C young t theta lambda zeta d*w d*actualAppellEnergy mu f d
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
  have hproper:=TriplePositiveEnergyWeightedBudgetDrift.actual_full_reserved_proper_drift_le hmu (Lp.memLp f) hK
    young t theta lambda zeta hy ht hth1 hl1 hboundary hz hcap N hN hprevious
  have hcost:(∑ d ∈ Finset.Icc 3 N,rawFirstCost young t theta lambda zeta d*w d*actualAppellEnergy mu f d)+
      (∑ d ∈ Finset.Icc 2 N,(K*C/young d)*(d : ℝ)^2*w d*actualAppellEnergy mu f d)+
      (∑ d ∈ Finset.Icc 2 N,t 3*tripleHarmonicNeighborCharge K young zeta d*w d*actualAppellEnergy mu f d)=D := by
    dsimp only [D,cost]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
    have hs:(Finset.Icc 2 N).filter (fun d=>3 ≤ d)=Finset.Icc 3 N := by
      ext d;simp only [Finset.mem_filter,Finset.mem_Icc];omega
    simp_rw [ite_mul,zero_mul]
    rw [←Finset.sum_filter,hs]
    ring
  change 2*(∑ d ∈ Finset.Icc 3 N,w d*(actualAppellCoefficient mu f d ⬝ᵥ actualAppellProperRemainder mu f d))+H ≤
    (∑ d ∈ Finset.Icc 3 N,rawFirstCost young t theta lambda zeta d*w d*actualAppellEnergy mu f d)+
    (∑ d ∈ Finset.Icc 2 N,(K*C/young d)*(d : ℝ)^2*w d*actualAppellEnergy mu f d)+
    (∑ d ∈ Finset.Icc 2 N,t 3*tripleHarmonicNeighborCharge K young zeta d*w d*actualAppellEnergy mu f d)+2*P at hproper
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
  have hr:(∑ d ∈ Finset.Icc 2 N,(generatorLoss K young t alpha theta lambda d+1+cost K C young t theta lambda zeta d)*
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
    (young t alpha theta lambda zeta : ℕ → ℝ)
    (hy : ∀ d,2 ≤ d → 0<young d) (ht : ∀ d,2 ≤ d → 0<t d)
    (ha0 : ∀ d,2 ≤ d → 0 ≤ alpha d) (ha1 : ∀ d,2 ≤ d → alpha d<1)
    (hth0 : ∀ d,3 ≤ d → 0 ≤ theta d) (hth1 : ∀ d,3 ≤ d → theta d ≤ 1)
    (hl0 : ∀ d,2 ≤ d → 0 ≤ lambda d) (hl1 : ∀ d,2 ≤ d → lambda d ≤ 1)
    (hboundary : ∀ d,2 ≤ d → lambda d=1 → theta (d+1)=1)
    (hz : ∀ b,2 ≤ b → 0 ≤ zeta b)
    (hcap : ∀ (b : ℕ),2 ≤ b → tripleHarmonicRatio (b : ℝ)*zeta b<1)
    (hquad : 3+kappa K young t lambda 2 ≤ 4*(gamma K t theta 2)^2/(1-alpha 2))
    (hpay : ∀ (d : ℕ),3 ≤ d → ((d : ℝ)+kappa K young t lambda d)*(1-alpha d) ≤ (d : ℝ))
    (N : ℕ) (hN : 3 ≤ N)
    (hprevious : ∀ g : Space n → ℝ,MemLp g 2 mu → 
      GeneralWeighted.energy mu g (weight K t) (N-1) ≤ C*(∫ x,(g x)^2 ∂mu))
    (hstat : ∀ ell : Lp ℝ 2 mu,GeneralWeighted.pairing f ell (weight K t) N=
      GeneralWeighted.energy mu f (weight K t) N*inner ℝ f ell)
    (hheat : GeneralWeighted.heatGenerator mu f (weight K t) N+
      GeneralWeighted.energy mu f (weight K t) N*actualAppellEnergy mu f 1 ≤ 0) :
    (∑ d ∈ Finset.Icc 3 N,coefficient K C young t alpha theta lambda zeta d*
      (weight K t d*actualAppellEnergy mu f d))-
      head K C young t alpha theta lambda zeta*(weight K t 2*actualAppellEnergy mu f 2) ≤ 0 := by
  classical
  have hlower:=actual_centered_generator_sum_lower hmu f hunit hK young t alpha theta lambda zeta
    hy ht ha0 ha1 hth0 hth1 hl0 hl1 hboundary hz hcap hquad hpay N hN hprevious hstat hheat
  have hshift:=incoming_shift hK t alpha (fun d=>actualAppellEnergy mu f d) ht ha0
    (fun d=>actualAppellEnergy_nonneg _ _ _) N (by omega)
  have hsum:=hshift.trans hlower
  have hs:Finset.Icc 2 N=insert 2 (Finset.Icc 3 N) := by
    ext d;simp only [Finset.mem_Icc,Finset.mem_insert];omega
  have hn:2∉Finset.Icc 3 N:=by simp
  have he:(∑ d ∈ Finset.Icc 3 N,coefficient K C young t alpha theta lambda zeta d*
      (weight K t d*actualAppellEnergy mu f d))-
      head K C young t alpha theta lambda zeta*(weight K t 2*actualAppellEnergy mu f 2)=
      (∑ d ∈ Finset.Icc 3 N,incoming K t alpha d*weight K t d*actualAppellEnergy mu f d)-
      ∑ d ∈ Finset.Icc 2 N,(generatorLoss K young t alpha theta lambda d+1+cost K C young t theta lambda zeta d)*
        weight K t d*actualAppellEnergy mu f d := by
    rw [hs,Finset.sum_insert hn]
    have htail:(∑ d ∈ Finset.Icc 3 N,coefficient K C young t alpha theta lambda zeta d*
        (weight K t d*actualAppellEnergy mu f d))=
        (∑ d ∈ Finset.Icc 3 N,incoming K t alpha d*weight K t d*actualAppellEnergy mu f d)-
        ∑ d ∈ Finset.Icc 3 N,(generatorLoss K young t alpha theta lambda d+1+cost K C young t theta lambda zeta d)*
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

end KLSConstantImprovement.TriplePositiveEnergyWeightedGenerator
#print axioms KLSConstantImprovement.TriplePositiveEnergyWeightedGenerator.actual_centered_generator_sum_lower
#print axioms KLSConstantImprovement.TriplePositiveEnergyWeightedGenerator.actual_generator_coefficients_nonpos
