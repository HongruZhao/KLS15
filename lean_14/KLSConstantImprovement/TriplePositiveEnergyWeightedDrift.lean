import KLSConstantImprovement.PositiveEnergyWeightedDrift
import ActualHarmonicTripleAppellDrift

/-! Selected positive-weight proper rows and harmonic triple payment.
The full previous canonical budget retains its unused last pair cell. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLSConstantImprovement.TriplePositiveEnergyWeightedDrift
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.PositiveEnergyWeightedDrift
open KLSConstantImprovement.ReservedQTriangleBudget
variable {n : ℕ}
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

def selectedFirstCost (young t : ℕ → ℝ) (rprofile lambda : ℕ → ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 2 (d-1),young (d-a+1)*(t d/(t a*t (d-a+1)))*
    (rprofile d a)^2/(1-lambda a (d-a+1))

theorem selected_prefix_eq (young t : ℕ → ℝ) (ht : ∀ d,2 ≤ d → 0<t d)
    (rprofile lambda : ℕ → ℕ → ℝ) (d : ℕ) (hd : 3 ≤ d) :
    selectedRowsPrefix young (fun d a=>rprofile d a*rowFactor t d a) lambda d=
      selectedFirstCost young t rprofile lambda d := by
  unfold selectedRowsPrefix selectedFirstCost
  apply Finset.sum_congr rfl
  intro a ha
  have ha2:2 ≤ a:=(Finset.mem_Icc.mp ha).1
  have hb2:2 ≤ d-a+1:=by have:=(Finset.mem_Icc.mp ha).2;omega
  rw [mul_pow,rowFactor_square t d a (ht d (by omega)).le (ht a ha2).le (ht _ hb2).le]
  ring

theorem actual_selected_remainder_with_last_refund_le
    {mu : Measure (Space n)} (hmu : admissibleMeasure mu) {f : Space n → ℝ} (hf : MemLp f 2 mu)
    {K C : ℝ} (hK : 0<K) (young t : ℕ → ℝ) (rprofile lambda : ℕ → ℕ → ℝ)
    (hy : ∀ d,2 ≤ d → 0<young d) (ht : ∀ d,2 ≤ d → 0<t d)
    (hr : ∀ d a,3 ≤ d → 0 ≤ rprofile d a)
    (hl : ∀ a b,2 ≤ a → 2 ≤ b → lambda a b ≤ 1)
    (hboundary : ∀ d a,3 ≤ d → a∈Finset.Icc 2 (d-1) → lambda a (d-a+1)=1 → rprofile d a=0)
    (N : ℕ) (hN : 3 ≤ N)
    (hprevious : ∀ g : Space n → ℝ,MemLp g 2 mu → 
      (∑ d ∈ Finset.Icc 2 (N-1),weight K t d*actualAppellEnergy mu g d) ≤ C*(∫ x,(g x)^2 ∂mu)) :
    2*(∑ d ∈ Finset.Icc 3 N,weight K t d*
      (actualAppellCoefficient mu f d ⬝ᵥ actualProfileProperRemainder mu f rprofile d))+
      (∑ p ∈ coupledDriftPairs N,(lambda p.2 (p.1-p.2+1)*K/young (p.1-p.2+1))*
        (normalizedQ mu f K t p.2 (p.1-p.2+1))^2)+
      (lambda 2 N*K/young N)*(normalizedQ mu f K t 2 N)^2  ≤ 
      (∑ d ∈ Finset.Icc 3 N,selectedFirstCost young t rprofile lambda d*weight K t d*actualAppellEnergy mu f d)+
      ∑ b ∈ Finset.Icc 2 N,(K*C/young b)*(b : ℝ)^2*weight K t b*actualAppellEnergy mu f b := by
  let : IsProbabilityMeasure mu:=hmu.isProb
  let rho:=fun d a=>rprofile d a*rowFactor t d a
  have hb:∀ d a,3 ≤ d → a∈Finset.Icc 2 (d-1) → lambda a (d-a+1)=1 → rho d a=0 := by
    intro d a hd ha he
    simp only [rho,hboundary d a hd ha he,zero_mul]
  have hper (d : ℕ) (hd:d∈Finset.Icc 3 N) :
      weight K t d*(actualAppellCoefficient mu f d ⬝ᵥ actualProfileProperRemainder mu f rprofile d)  ≤ 
      Real.sqrt K*(∑ a ∈ Finset.Icc 2 (d-1),rho d a*(normalizedP mu f K t d/(d : ℝ))*
        normalizedQ mu f K t a (d-a+1)) := by
    have hh:=mul_le_mul_of_nonneg_left
      (actual_profile_pairing_le_canonical_sum hmu.logConcave hf rprofile d
        (fun a=>hr d a (Finset.mem_Icc.mp hd).1))
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
          _=rprofile d a*(weight K t d*Real.sqrt (actualAppellEnergy mu f d)*
            ((d.choose a : ℝ)*Real.sqrt (actualCanonicalContractionSquare mu f a (d-a)))):=by ring
          _=_:=by rw [he];ring
  have hsum:=mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by norm_num : (0:ℝ) ≤ 2)
  rw [←Finset.mul_sum] at hsum
  have hyoung:=coupled_triangle_selected_rows_young_with_last_refund N hN
    (normalizedP mu f K t) (normalizedQ mu f K t) young rho lambda hK.le hy hl hb
    (fun b hb'=>normalizedQ_joint_square_le hmu f hK t ht N hprevious hb')
  have hfirst:(∑ d ∈ Finset.Icc 3 N,selectedRowsPrefix young rho lambda d*
      (normalizedP mu f K t d/(d : ℝ))^2)=
      ∑ d ∈ Finset.Icc 3 N,selectedFirstCost young t rprofile lambda d*weight K t d*actualAppellEnergy mu f d := by
    apply Finset.sum_congr rfl
    intro d hd
    have hd3:3 ≤ d:=(Finset.mem_Icc.mp hd).1
    have hd0:(d : ℝ)≠0:=by exact_mod_cast (by omega : d≠0)
    have hps:(normalizedP mu f K t d/(d : ℝ))^2=weight K t d*actualAppellEnergy mu f d := by
      rw [div_pow,normalizedP_sq mu f hK t d (ht d (by omega)).le]
      field_simp
    rw [hps,selected_prefix_eq young t ht rprofile lambda d hd3]
    ring
  have hsecond:(∑ b ∈ Finset.Icc 2 N,(K*C/young b)*(normalizedP mu f K t b)^2)=
      ∑ b ∈ Finset.Icc 2 N,(K*C/young b)*(b : ℝ)^2*weight K t b*actualAppellEnergy mu f b := by
    apply Finset.sum_congr rfl
    intro b hb'
    rw [normalizedP_sq mu f hK t b (ht b (Finset.mem_Icc.mp hb').1).le]
    ring
  rw [hfirst,hsecond] at hyoung
  linarith

end KLSConstantImprovement.TriplePositiveEnergyWeightedDrift
#print axioms KLSConstantImprovement.TriplePositiveEnergyWeightedDrift.actual_selected_remainder_with_last_refund_le
