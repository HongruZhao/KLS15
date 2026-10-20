import KLSConstantImprovement.ReservedQTriangleBudget
import KLSConstantImprovement.SignedReservedCanonicalDrift

/-! Actual proper drift with arbitrary positive degree energy multipliers.
The normalized shared canonical budget and its last-cell refund are literal;
the first cost contains the exact rational energy-weight ratios. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLSConstantImprovement.PositiveEnergyWeightedDrift
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.ReservedQTriangleBudget
open KLSConstantImprovement.SignedReservedCanonicalDrift
variable {n : ℕ}
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def weight (K : ℝ) (t : ℕ → ℝ) (d : ℕ) : ℝ := t d*CoupledEnergy.factorialWeight K d
def normalizedP (mu : Measure (Space n)) (f : Space n → ℝ) (K : ℝ) (t : ℕ → ℝ) (d : ℕ) : ℝ :=
  Real.sqrt (t d)*coupledAppellP mu f K d
def normalizedQ (mu : Measure (Space n)) (f : Space n → ℝ) (K : ℝ) (t : ℕ → ℝ) (a b : ℕ) : ℝ :=
  Real.sqrt (t a)*Real.sqrt (t b)*coupledAppellQ mu f K a b
def rowFactor (t : ℕ → ℝ) (d a : ℕ) : ℝ :=
  Real.sqrt (t d)/(Real.sqrt (t a)*Real.sqrt (t (d-a+1)))
def firstCost (young t theta lambda : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 2 (d-1),young (d-a+1)*(t d/(t a*t (d-a+1)))*
    (thetaTriangleCoefficient theta d a)^2/selectiveTriangleFraction lambda d a
def kappa (K : ℝ) (young t lambda : ℕ → ℝ) (d : ℕ) : ℝ :=
  lambda d*t 2*(d : ℝ)^2/(4*K*young d)

theorem weight_positive {K : ℝ} (hK : 0<K) (t : ℕ → ℝ) (d : ℕ) (ht : 0<t d) :
    0<weight K t d := by unfold weight CoupledEnergy.factorialWeight;positivity

theorem normalizedP_sq (mu : Measure (Space n)) (f : Space n → ℝ)
    {K : ℝ} (hK : 0<K) (t : ℕ → ℝ) (d : ℕ) (ht : 0 ≤ t d) :
    (normalizedP mu f K t d)^2=(d : ℝ)^2*weight K t d*actualAppellEnergy mu f d := by
  unfold normalizedP weight CoupledEnergy.factorialWeight
  rw [mul_pow,Real.sq_sqrt ht,coupledAppellP_sq f hK]
  ring

theorem normalizedQ_sq (mu : Measure (Space n)) (f : Space n → ℝ)
    {K : ℝ} (hK : 0<K) (t : ℕ → ℝ) (a b : ℕ) (ha : 0 ≤ t a) (hb : 0 ≤ t b) :
    (normalizedQ mu f K t a b)^2=
      (t b*(b : ℝ)^2/(coupledAppellScale K b)^2)*
        (weight K t a*actualCanonicalContractionSquare mu f a (b-1)) := by
  unfold normalizedQ weight CoupledEnergy.factorialWeight
  rw [mul_pow,mul_pow,Real.sq_sqrt ha,Real.sq_sqrt hb,coupledAppellQ_sq f hK]
  ring

theorem normalizedQ_joint_square_le
    {mu : Measure (Space n)} (hmu : admissibleMeasure mu) (f : Space n → ℝ)
    {K C : ℝ} (hK : 0<K) (t : ℕ → ℝ) (ht : ∀ d,2 ≤ d → 0<t d) (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ,MemLp g 2 mu → 
      (∑ d ∈ Finset.Icc 2 (N-1),weight K t d*actualAppellEnergy mu g d) ≤ C*(∫ x,(g x)^2 ∂mu))
    {b : ℕ} (hb : b∈Finset.Icc 2 N) :
    (∑ a ∈ Finset.Icc 2 (N-1),(normalizedQ mu f K t a b)^2) ≤ C*(normalizedP mu f K t b)^2 := by
  have hb2:2 ≤ b:=(Finset.mem_Icc.mp hb).1
  have htb : 0<t b := ht b hb2
  have hbc:b-1+1=b:=by omega
  have hj:=actual_joint_canonical_contraction_square_le hmu f (Finset.Icc 2 (N-1))
    (weight K t) hprevious (b-1)
  rw [hbc] at hj
  have he:(∑ a ∈ Finset.Icc 2 (N-1),(normalizedQ mu f K t a b)^2)=
      (t b*(b : ℝ)^2/(coupledAppellScale K b)^2)*
        ∑ a ∈ Finset.Icc 2 (N-1),weight K t a*actualCanonicalContractionSquare mu f a (b-1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact normalizedQ_sq mu f hK t a b (ht a (Finset.mem_Icc.mp ha).1).le (ht b hb2).le
  rw [he]
  calc
    _ ≤ (t b*(b : ℝ)^2/(coupledAppellScale K b)^2)*(C*actualAppellEnergy mu f b) :=
      mul_le_mul_of_nonneg_left hj (by positivity)
    _=_:=by rw [normalizedP_sq mu f hK t b (ht b hb2).le];
            unfold weight CoupledEnergy.factorialWeight;rw [coupledAppellScale_sq hK];ring

theorem rowFactor_square (t : ℕ → ℝ) (d a : ℕ)
    (hd : 0 ≤ t d) (ha : 0 ≤ t a) (hb : 0 ≤ t (d-a+1)) :
    (rowFactor t d a)^2=t d/(t a*t (d-a+1)) := by
  unfold rowFactor
  rw [div_pow,mul_pow,Real.sq_sqrt hd,Real.sq_sqrt ha,Real.sq_sqrt hb]

theorem normalized_term (mu : Measure (Space n)) (f : Space n → ℝ)
    {K : ℝ} (hK : 0<K) (t : ℕ → ℝ) (ht : ∀ d,2 ≤ d → 0<t d)
    (d a : ℕ) (hd : 3 ≤ d) (ha : a∈Finset.Icc 2 (d-1)) :
    weight K t d*Real.sqrt (actualAppellEnergy mu f d)*
      ((d.choose a : ℝ)*Real.sqrt (actualCanonicalContractionSquare mu f a (d-a)))=
      Real.sqrt K*rowFactor t d a*(normalizedP mu f K t d/(d : ℝ))*
        normalizedQ mu f K t a (d-a+1) := by
  have ha2:2 ≤ a:=(Finset.mem_Icc.mp ha).1
  have hb2:2 ≤ d-a+1:=by have:=(Finset.mem_Icc.mp ha).2;omega
  have hsa:Real.sqrt (t a)≠0:=ne_of_gt (Real.sqrt_pos.2 (ht a ha2))
  have hsb:Real.sqrt (t (d-a+1))≠0:=ne_of_gt (Real.sqrt_pos.2 (ht _ hb2))
  have hfactor:rowFactor t d a*Real.sqrt (t d)*Real.sqrt (t a)*Real.sqrt (t (d-a+1))=t d := by
    calc
      _=(Real.sqrt (t d))^2:=by unfold rowFactor;field_simp [hsa,hsb]
      _=t d:=Real.sq_sqrt (ht d (by omega)).le
  calc
    _=t d*((K^d*(d.factorial : ℝ)^2)⁻¹*Real.sqrt (actualAppellEnergy mu f d)*
        ((d.choose a : ℝ)*Real.sqrt (actualCanonicalContractionSquare mu f a (d-a)))) := by
      unfold weight CoupledEnergy.factorialWeight;ring
    _=t d*(Real.sqrt K*(coupledAppellP mu f K d/(d : ℝ))*coupledAppellQ mu f K a (d-a+1)) := by
      rw [coupledAppell_normalized_term f hK hd ha]
    _=_:=by unfold normalizedP normalizedQ;nth_rw 1 [←hfactor];ring

theorem actual_full_reserved_proper_drift_le
    {mu : Measure (Space n)} (hmu : admissibleMeasure mu) {f : Space n → ℝ} (hf : MemLp f 2 mu)
    {K C : ℝ} (hK : 0<K) (young t theta lambda : ℕ → ℝ)
    (hy : ∀ b,2 ≤ b → 0<young b) (ht : ∀ d,2 ≤ d → 0<t d)
    (hth : ∀ d,3 ≤ d → theta d ≤ 1) (hl : ∀ b,2 ≤ b → lambda b ≤ 1)
    (hboundary : ∀ b,2 ≤ b → lambda b=1 → theta (b+1)=1) (N : ℕ) (hN : 3 ≤ N)
    (hprevious : ∀ g : Space n → ℝ,MemLp g 2 mu → 
      (∑ d ∈ Finset.Icc 2 (N-1),weight K t d*actualAppellEnergy mu g d) ≤ C*(∫ x,(g x)^2 ∂mu)) :
    2*(∑ d ∈ Finset.Icc 3 N,weight K t d*
      (actualAppellCoefficient mu f d ⬝ᵥ actualAppellProperRemainder mu f d))+
      (∑ b ∈ Finset.Icc 2 N,kappa K young t lambda b*weight K t b*
        actualCanonicalContractionSquare mu f 2 (b-1))  ≤ 
      (∑ d ∈ Finset.Icc 3 N,firstCost young t theta lambda d*weight K t d*actualAppellEnergy mu f d)+
      (∑ b ∈ Finset.Icc 2 N,(K*C/young b)*(b : ℝ)^2*weight K t b*actualAppellEnergy mu f b)+
      2*(∑ d ∈ Finset.Icc 3 N,theta d*weight K t d*
        (actualAppellCoefficient mu f d ⬝ᵥ actualAppellPairContractionSum mu f d)) := by
  let : IsProbabilityMeasure mu:=hmu.isProb
  let rho:=fun d a=>thetaTriangleCoefficient theta d a*rowFactor t d a
  let lmb:=fun a b=>if a=2 then lambda b else 0
  have hrho:∀ d a,3 ≤ d → a∈Finset.Icc 2 (d-1) → 0 ≤ rho d a := by
    intro d a hd ha
    have hc:0 ≤ thetaTriangleCoefficient theta d a:=by
      unfold thetaTriangleCoefficient;split_ifs;linarith [hth d hd];norm_num
    exact mul_nonneg hc (div_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  have hlmb:∀ a b,2 ≤ a → 2 ≤ b → lmb a b ≤ 1 := by
    intro a b ha hb
    dsimp only [lmb]
    split_ifs
    · exact hl b hb
    · norm_num
  have hbd:∀ d a,3 ≤ d → a∈Finset.Icc 2 (d-1) → lmb a (d-a+1)=1 → rho d a=0 := by
    intro d a hd ha he
    by_cases h2:a=2
    · subst a
      have hs:d-2+1=d-1:=by omega
      have hsp:d-1+1=d:=by omega
      dsimp only [lmb] at he
      simp only [ite_true,hs] at he
      have hh:=hboundary (d-1) (by omega) he
      rw [hsp] at hh
      simp [rho,thetaTriangleCoefficient,hh]
    · simp [lmb,h2] at he
  have hper (d : ℕ) (hd:d∈Finset.Icc 3 N) :
      weight K t d*(actualAppellCoefficient mu f d ⬝ᵥ actualThetaProperRemainder mu f theta d)  ≤ 
      Real.sqrt K*(∑ a ∈ Finset.Icc 2 (d-1),rho d a*
        (normalizedP mu f K t d/(d : ℝ))*normalizedQ mu f K t a (d-a+1)) := by
    have hh:=mul_le_mul_of_nonneg_left
      (actual_theta_pairing_le_canonical_sum hmu.logConcave hf theta d (hth d (Finset.mem_Icc.mp hd).1))
      (weight_positive hK t d (ht d (by have:=(Finset.mem_Icc.mp hd).1;omega))).le
    calc
      _ ≤ _:=hh
      _=_:=by
        rw [←mul_assoc,Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        have he:=normalized_term mu f hK t ht d a (Finset.mem_Icc.mp hd).1 ha
        dsimp only [rho]
        calc
          _=thetaTriangleCoefficient theta d a*(weight K t d*Real.sqrt (actualAppellEnergy mu f d)*
            ((d.choose a : ℝ)*Real.sqrt (actualCanonicalContractionSquare mu f a (d-a)))):=by ring
          _=_:=by rw [he];ring
  have hsum:=mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by norm_num : (0:ℝ) ≤ 2)
  rw [←Finset.mul_sum] at hsum
  have hyoung:=coupled_triangle_selected_rows_young_with_last_refund N hN
    (normalizedP mu f K t) (normalizedQ mu f K t) young rho lmb hK.le hy hlmb hbd
    (fun b hb=>normalizedQ_joint_square_le hmu f hK t ht N hprevious hb)
  have hfirst:(∑ d ∈ Finset.Icc 3 N,selectedRowsPrefix young rho lmb d*
      (normalizedP mu f K t d/(d : ℝ))^2)=
      ∑ d ∈ Finset.Icc 3 N,firstCost young t theta lambda d*weight K t d*actualAppellEnergy mu f d := by
    apply Finset.sum_congr rfl
    intro d hd
    have hd3:3 ≤ d:=(Finset.mem_Icc.mp hd).1
    have hd0:(d : ℝ)≠0:=by exact_mod_cast (by omega : d≠0)
    have hps:(normalizedP mu f K t d/(d : ℝ))^2=weight K t d*actualAppellEnergy mu f d := by
      rw [div_pow,normalizedP_sq mu f hK t d (ht d (by omega)).le]
      field_simp
    have hprefix:selectedRowsPrefix young rho lmb d=firstCost young t theta lambda d := by
      unfold selectedRowsPrefix firstCost
      apply Finset.sum_congr rfl
      intro a ha
      have ha2:2 ≤ a:=(Finset.mem_Icc.mp ha).1
      have hb2:2 ≤ d-a+1:=by have:=(Finset.mem_Icc.mp ha).2;omega
      dsimp only [rho,lmb]
      rw [mul_pow,rowFactor_square t d a (ht d (by omega)).le (ht a ha2).le (ht _ hb2).le]
      by_cases h2:a=2
      · subst a
        have hs:d-2+1=d-1:=by omega
        simp only [ite_true,selectiveTriangleFraction,hs]
        ring
      · simp [h2,selectiveTriangleFraction]
        ring
    rw [hps,hprefix]
    ring
  have hsecond:(∑ b ∈ Finset.Icc 2 N,(K*C/young b)*(normalizedP mu f K t b)^2)=
      ∑ b ∈ Finset.Icc 2 N,(K*C/young b)*(b : ℝ)^2*weight K t b*actualAppellEnergy mu f b := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [normalizedP_sq mu f hK t b (ht b (Finset.mem_Icc.mp hb).1).le]
    ring
  rw [hfirst,hsecond] at hyoung
  have hcharge:(∑ p ∈ coupledDriftPairs N,(lmb p.2 (p.1-p.2+1)*K/young (p.1-p.2+1))*
      (normalizedQ mu f K t p.2 (p.1-p.2+1))^2)+
      (lmb 2 N*K/young N)*(normalizedQ mu f K t 2 N)^2=
      ∑ b ∈ Finset.Icc 2 N,kappa K young t lambda b*weight K t b*
        actualCanonicalContractionSquare mu f 2 (b-1) := by
    dsimp only [lmb]
    simp only [ite_true]
    rw [canonical_charge_sum_reindex K young lambda (normalizedQ mu f K t) N hN]
    apply Finset.sum_congr rfl
    intro b hb
    rw [normalizedQ_sq mu f hK t 2 b (ht 2 (by omega)).le (ht b (Finset.mem_Icc.mp hb).1).le,
      coupledAppellScale_sq hK]
    unfold kappa weight CoupledEnergy.factorialWeight
    norm_num only [Nat.factorial,Nat.cast_ofNat]
    field_simp
  have hyoung':2*Real.sqrt K*(∑ d ∈ Finset.Icc 3 N,∑ a ∈ Finset.Icc 2 (d-1),rho d a*
      (normalizedP mu f K t d/(d : ℝ))*normalizedQ mu f K t a (d-a+1))+
      (∑ b ∈ Finset.Icc 2 N,kappa K young t lambda b*weight K t b*
        actualCanonicalContractionSquare mu f 2 (b-1))  ≤ 
      (∑ d ∈ Finset.Icc 3 N,firstCost young t theta lambda d*weight K t d*actualAppellEnergy mu f d)+
      ∑ b ∈ Finset.Icc 2 N,(K*C/young b)*(b : ℝ)^2*weight K t b*actualAppellEnergy mu f b := by
    rw [add_assoc,hcharge] at hyoung
    exact hyoung
  have he:(∑ d ∈ Finset.Icc 3 N,weight K t d*
      (actualAppellCoefficient mu f d ⬝ᵥ actualAppellProperRemainder mu f d))=
      (∑ d ∈ Finset.Icc 3 N,weight K t d*
        (actualAppellCoefficient mu f d ⬝ᵥ actualThetaProperRemainder mu f theta d))+
      ∑ d ∈ Finset.Icc 3 N,theta d*weight K t d*
        (actualAppellCoefficient mu f d ⬝ᵥ actualAppellPairContractionSum mu f d) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [actualThetaProperRemainder_pairing_split mu f theta d (Finset.mem_Icc.mp hd).1]
    ring
  rw [he]
  linarith

end KLSConstantImprovement.PositiveEnergyWeightedDrift
#print axioms KLSConstantImprovement.PositiveEnergyWeightedDrift.normalizedQ_joint_square_le
#print axioms KLSConstantImprovement.PositiveEnergyWeightedDrift.actual_full_reserved_proper_drift_le
