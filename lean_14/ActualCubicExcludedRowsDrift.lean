import CubicExcludedRowsProfiles

/-! The actual selected proper drift in degrees at least four retains the
whole canonical (2,2) normalized square. The previous all-test joint C
budget remains unchanged; no charge for a higher cumulant row is removed. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

 theorem actual_weighted_selected_rows_excluding_cubic_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K C : ℝ}
    (s : ℕ → ℝ) (rho lambda : ℕ → ℕ → ℝ) (hK : 0 < K)
    (hs : ∀ b, 2 ≤ b → 0 < s b)
    (hrho : ∀ d a, 3 ≤ d → 0 ≤ rho d a)
    (hlambda : ∀ a b, 2 ≤ a → 2 ≤ b → lambda a b < 1)
    (N : ℕ) (hN : 3 ≤ N)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ)) :
    2*(∑ d ∈ Finset.Icc 4 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualProfileProperRemainder μ f rho d))+
      (K/s 2)*(coupledAppellQ μ f K 2 2)^2+
      (∑ d ∈ Finset.Icc 4 N, ∑ a ∈ Finset.Icc 2 (d-1),
        (lambda a (d-a+1)*K/s (d-a+1))*(coupledAppellQ μ f K a (d-a+1))^2) ≤
    (∑ d ∈ Finset.Icc 4 N, selectedRowsPrefix s rho lambda d*
      (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)+
      ∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(b : ℝ)^2*
        (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b := by
  classical
  have hh := actual_weighted_selected_rows_remainder_boundary_le hμ hf s
    (cubicExcludedProfile rho) (cubicRetainedLambda lambda) hK hs
    (cubicExcludedProfile_nonneg rho hrho) (cubicRetainedLambda_le_one lambda hlambda)
    (cubicExcludedProfile_boundary rho lambda hlambda) N hprevious
  have hi : Finset.Icc 3 N=insert 3 (Finset.Icc 4 N) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hn : 3 ∉ Finset.Icc 4 N := by simp
  have hp0 : actualProfileProperRemainder μ f (cubicExcludedProfile rho) 3=0 := by
    ext a
    simp [actualProfileProperRemainder,cubicExcludedProfile]
  have hp (d : ℕ) (hd : d ∈ Finset.Icc 4 N) :
      actualProfileProperRemainder μ f (cubicExcludedProfile rho) d=
      actualProfileProperRemainder μ f rho d := by
    have hd3 : d ≠ 3 := by have := (Finset.mem_Icc.mp hd).1; omega
    unfold actualProfileProperRemainder
    congr 1
    funext S
    simp only [cubicExcludedProfile,hd3,ite_false]
  have he1 : (∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualProfileProperRemainder μ f (cubicExcludedProfile rho) d))=
      ∑ d ∈ Finset.Icc 4 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
        (actualAppellCoefficient μ f d ⬝ᵥ actualProfileProperRemainder μ f rho d) := by
    rw [hi,Finset.sum_insert hn,hp0,dotProduct_zero,mul_zero,zero_add]
    exact Finset.sum_congr rfl fun d hd => by rw [hp d hd]
  have he2 : (∑ d ∈ Finset.Icc 3 N,
      selectedRowsPrefix s (cubicExcludedProfile rho) (cubicRetainedLambda lambda) d*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)=
      ∑ d ∈ Finset.Icc 4 N, selectedRowsPrefix s rho lambda d*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
    rw [hi,Finset.sum_insert hn,cubicExcludedRowsPrefix s rho lambda 3 (by omega)]
    simp only [ite_true,zero_mul,zero_add]
    apply Finset.sum_congr rfl
    intro d hd
    have hd3 : d ≠ 3 := by have := (Finset.mem_Icc.mp hd).1; omega
    rw [cubicExcludedRowsPrefix s rho lambda d (by have := (Finset.mem_Icc.mp hd).1; omega)]
    simp only [hd3,ite_false]
  rw [he1,he2,cubicExcludedRowsCharge (coupledAppellQ μ f K) s lambda K N hN] at hh
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_weighted_selected_rows_excluding_cubic_le
