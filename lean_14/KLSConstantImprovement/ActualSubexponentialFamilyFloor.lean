import KLSConstantImprovement.ActualSubexponentialTailDegree
import KLSConstantImprovement.SubexponentialContractionObstruction
import KLSConstantImprovement.GeneralSubexponentialWeightedObservation

/-! A method-family obstruction that includes nonconstant polynomial
weight tails.  It requires no eventual constancy of alpha, Young, or t.
This is NOT a lower bound for the optimal universal KLS constant. -/
noncomputable section
namespace KLSConstantImprovement.ActualSubexponentialFamilyFloor
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
open KLSConstantImprovement.ActualSubexponentialTailDegree
open KLSConstantImprovement.GeneralSubexponentialWeightedObservation

theorem K_lower_of_actual_subexponential_profile (P : Parameters)
    (hK : 0 < P.K) (hC : 0 ≤ P.C) (hc : 0 ≤ P.c)
    (hy : ∀ d,2 ≤ d → 0 < P.young d)
    (ht : ∀ d,2 ≤ d → 0 < P.t d)
    (ha0 : ∀ d,2 ≤ d → 0 ≤ P.alpha d)
    (ha1 : ∀ d,2 ≤ d → P.alpha d < 1)
    (hsub : SubexponentialLowerWeight P.t)
    (N : ℕ)
    (hth : ∀ d,N ≤ d → P.theta d=0)
    (hl : ∀ d,N ≤ d → P.lambda d=0)
    (hzeta : ∀ d,N ≤ d → P.zeta d=0)
    (hcoef : ∀ d,5 ≤ d → P.c ≤ coefficient P d) :
    6+4*Real.sqrt 2 ≤ P.K := by
  have hcritical : 0 < critical := by unfold critical; positivity
  have hstep (d : ℕ) (hd : N+5 ≤ d) :
      critical*(1-1/(d : ℝ))*(P.t d*P.alpha d) ≤
        P.K*(P.t (d-1)*P.alpha (d-1)) ∧
      2*(1-1/(d : ℝ))*P.t d ≤ P.K*(P.t (d-1)*P.alpha (d-1)) := by
    exact degree_contractions P hK hC hy ht d (by omega)
      (ha0 d (by omega)) (ha1 d (by omega))
      (hth d (by omega)) (hth (d+1) (by omega))
      (hl d (by omega)) (hl (d-1) (by omega))
      (hzeta d (by omega)) (hzeta (d-2) (by omega))
      (hc.trans (hcoef d (by omega)))
  exact SubexponentialContractionObstruction.le_of_degree_contractions
    P.K critical hK hcritical (fun d=>P.t d*P.alpha d) P.t (N+5) (by omega)
    hsub (fun d hd=>(hstep d hd).1) (fun d hd=>(hstep d hd).2)

theorem endpoint_lower_of_actual_subexponential_profile (P : Parameters)
    (p : ℝ) (hp : 1 ≤ p)
    (hK : 0 < P.K) (hC : 0 ≤ P.C) (hc : 0 ≤ P.c)
    (hy : ∀ d,2 ≤ d → 0 < P.young d)
    (ht : ∀ d,2 ≤ d → 0 < P.t d)
    (ha0 : ∀ d,2 ≤ d → 0 ≤ P.alpha d)
    (ha1 : ∀ d,2 ≤ d → P.alpha d < 1)
    (hsub : SubexponentialLowerWeight P.t)
    (N : ℕ)
    (hth : ∀ d,N ≤ d → P.theta d=0)
    (hl : ∀ d,N ≤ d → P.lambda d=0)
    (hzeta : ∀ d,N ≤ d → P.zeta d=0)
    (hcoef : ∀ d,5 ≤ d → P.c ≤ coefficient P d) :
    7+4*Real.sqrt 2 ≤ 1+P.K*p := by
  have hk := K_lower_of_actual_subexponential_profile P hK hC hc hy ht
    ha0 ha1 hsub N hth hl hzeta hcoef
  have hm := mul_le_mul_of_nonneg_left hp hK.le
  nlinarith

end KLSConstantImprovement.ActualSubexponentialFamilyFloor
#print axioms KLSConstantImprovement.ActualSubexponentialFamilyFloor.K_lower_of_actual_subexponential_profile
#print axioms KLSConstantImprovement.ActualSubexponentialFamilyFloor.endpoint_lower_of_actual_subexponential_profile
