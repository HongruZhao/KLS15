import TwoRowsHarmonicBudgetPrefix
import ActualTwoRowsAppellCharges
import ActualTripleAppellAffineQ

/-! Genuine size-three affine-Q Young bound matched to its own retained
canonical square. The square and all fourth-cumulant geometry are actual;
the original full joint budget is not reduced. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
open KLSBelow25.TripleCreation
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def tripleHarmonicNeighborCharge (K : ℝ) (s zeta : ℕ → ℝ) (b : ℕ) : ℝ :=
  zeta b*affineRest (exactCap b) ((b : ℝ)+2)/
    (K^2*((b : ℝ)+2)^2*((b : ℝ)+1)^2*s b)

theorem actual_triple_weighted_young_affineQ_degree
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K v : ℝ} (hK : 0 < K) (hv : 0 < v)
    (d : ℕ) (hd : 4 ≤ d) :
    2*(K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellTripleContractionSum μ f d) ≤
      v*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d+
      (affineQ (d : ℝ)/(K^2*(d : ℝ)^2*((d : ℝ)-1)^2*v))*
        (K^(d-2)*((d-2).factorial : ℝ)^2)⁻¹*actualCanonicalContractionSquare μ f 3 (d-3)+
      (affineRest (exactCap (d-2)) (d : ℝ)/(K^2*(d : ℝ)^2*((d : ℝ)-1)^2*v))*
        (K^(d-2)*((d-2).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-2) := by
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hd
  have hdr : d=r+4 := by omega
  have hdr2 : d-2=r+2 := by omega
  have hdr3 : d-3=r+1 := by omega
  rw [hdr3,hdr2,hdr]
  have h := actualAppellTripleContractionSum_weighted_young_affineQ (r := r) hμ hf hK hv
  simp only [CoupledEnergy.factorialWeight] at h
  dsimp only [PairTensor.pairing,dotProduct] at h ⊢
  push_cast
  convert h using 1
  ring

theorem actual_harmonic_triple_young_matching_charge
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K : ℝ} (hK : 0 < K)
    (s zeta : ℕ → ℝ) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (hzeta : ∀ b, 2 ≤ b → 0 ≤ zeta b) (d : ℕ) (hd : 4 ≤ d) :
    2*tripleHarmonicThetaProfile zeta d*(K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellTripleContractionSum μ f d) ≤
      tripleHarmonicThetaProfile zeta d*tripleHarmonicEtaProfile zeta d*s (d-2)*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d+
      actualTwoRowsTripleCharge μ f K s (tripleHarmonicLambdaProfile zeta) d+
      tripleHarmonicNeighborCharge K s zeta (d-2)*
        (K^(d-2)*((d-2).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-2) := by
  have hb : 2 ≤ d-2 := by omega
  have hbc : (2 : ℝ) ≤ ((d-2 : ℕ) : ℝ) := by exact_mod_cast hb
  have hz := hzeta (d-2) hb
  have hs' := hs (d-2) hb
  have hη : 0 < tripleHarmonicEtaProfile zeta d := tripleHarmonicEtaProfile_pos zeta hzeta d
  have hθ : 0 ≤ tripleHarmonicThetaProfile zeta d := tripleHarmonicThetaProfile_nonneg zeta hzeta d
  have h := mul_le_mul_of_nonneg_left
    (actual_triple_weighted_young_affineQ_degree hμ hf hK (mul_pos hη hs') d hd) hθ
  have hc : ((d-2 : ℕ) : ℝ) = (d : ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ d)]
    norm_num
  have hcharge : actualTwoRowsTripleCharge μ f K s (tripleHarmonicLambdaProfile zeta) d =
      tripleHarmonicThetaProfile zeta d*
        (affineQ (d : ℝ)/(K^2*(d : ℝ)^2*((d : ℝ)-1)^2*(tripleHarmonicEtaProfile zeta d*s (d-2))))*
        (K^(d-2)*((d-2).factorial : ℝ)^2)⁻¹*actualCanonicalContractionSquare μ f 3 (d-3) := by
    unfold actualTwoRowsTripleCharge
    rw [ite_eq_left hd]
    rw [actual_size_three_budget_charge f hK s (fun _ b => tripleHarmonicLambdaProfile zeta b) (d-2)]
    have he := tripleHarmonic_charge_identity hbc hz hK hs'
    have hsub : d-2-1=d-3 := by omega
    rw [hsub]
    dsimp only [tripleHarmonicLambdaProfile]
    rw [he]
    simp only [tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,ite_eq_left hd]
    unfold tripleCreationQCoefficient
    rw [hc]
    have he1 : (d : ℝ)-2+2=(d : ℝ) := by ring
    have he2 : (d : ℝ)-2+1=(d : ℝ)-1 := by ring
    rw [he1,he2]
    ring
  have hrest : tripleHarmonicNeighborCharge K s zeta (d-2) =
      tripleHarmonicThetaProfile zeta d*
        (affineRest (exactCap (d-2)) (d : ℝ)/
          (K^2*(d : ℝ)^2*((d : ℝ)-1)^2*(tripleHarmonicEtaProfile zeta d*s (d-2)))) := by
    have he := tripleHarmonic_rest_identity (R := affineRest (exactCap (d-2)) (((d-2 : ℕ) : ℝ)+2)) hbc hz hK hs'
    unfold tripleHarmonicNeighborCharge
    simp only [tripleHarmonicThetaProfile,tripleHarmonicEtaProfile,ite_eq_left hd]
    rw [←he,hc]
    have he1 : (d : ℝ)-2+2=(d : ℝ) := by ring
    have he2 : (d : ℝ)-2+1=(d : ℝ)-1 := by ring
    rw [he1,he2]
    ring
  rw [hcharge,hrest]
  nlinarith [h]

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_triple_weighted_young_affineQ_degree
#print axioms KLS.DeterministicBridgeNext.actual_harmonic_triple_young_matching_charge
