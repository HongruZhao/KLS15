import ActualSelectedRowsBoundaryAppellDrift

/-! Exact profiles that remove only the cubic proper remainder and retain
its whole canonical second-factor square. Higher rows keep their original
coefficients and the full shared column budget. -/
noncomputable section
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1500000

def cubicExcludedProfile (rho : ℕ → ℕ → ℝ) (d a : ℕ) : ℝ :=
  if d=3 then 0 else rho d a

def cubicRetainedLambda (lambda : ℕ → ℕ → ℝ) (a b : ℕ) : ℝ :=
  if a=2 ∧ b=2 then 1 else lambda a b

 theorem cubicExcludedProfile_nonneg (rho : ℕ → ℕ → ℝ)
    (hrho : ∀ d a, 3 ≤ d → 0 ≤ rho d a) :
    ∀ d a, 3 ≤ d → 0 ≤ cubicExcludedProfile rho d a := by
  intro d a hd
  by_cases h : d=3 <;> simp [cubicExcludedProfile,h,hrho d a hd]

 theorem cubicRetainedLambda_le_one (lambda : ℕ → ℕ → ℝ)
    (hlambda : ∀ a b, 2 ≤ a → 2 ≤ b → lambda a b < 1) :
    ∀ a b, 2 ≤ a → 2 ≤ b → cubicRetainedLambda lambda a b ≤ 1 := by
  intro a b ha hb
  by_cases h : a=2 ∧ b=2
  · simp [cubicRetainedLambda,h]
  · simp only [cubicRetainedLambda,h,ite_false]
    exact (hlambda a b ha hb).le

 theorem cubicExcludedProfile_boundary (rho lambda : ℕ → ℕ → ℝ)
    (hlambda : ∀ a b, 2 ≤ a → 2 ≤ b → lambda a b < 1) :
    ∀ d a, 3 ≤ d → a ∈ Finset.Icc 2 (d-1) →
      cubicRetainedLambda lambda a (d-a+1)=1 → cubicExcludedProfile rho d a=0 := by
  intro d a hd ha heq
  have ha' := Finset.mem_Icc.mp ha
  have hb : 2 ≤ d-a+1 := by omega
  by_cases h : a=2 ∧ d-a+1=2
  · have hd3 : d=3 := by omega
    simp [cubicExcludedProfile,hd3]
  · simp only [cubicRetainedLambda,h,ite_false] at heq
    exact False.elim ((ne_of_lt (hlambda a (d-a+1) ha'.1 hb)) heq)

 theorem cubicExcludedRowsPrefix (s : ℕ → ℝ) (rho lambda : ℕ → ℕ → ℝ)
    (d : ℕ) (hd : 3 ≤ d) :
    selectedRowsPrefix s (cubicExcludedProfile rho) (cubicRetainedLambda lambda) d =
      if d=3 then 0 else selectedRowsPrefix s rho lambda d := by
  by_cases h3 : d=3
  · subst d
    simp [selectedRowsPrefix,cubicExcludedProfile]
  · simp only [h3,ite_false,selectedRowsPrefix]
    apply Finset.sum_congr rfl
    intro a ha
    have hn : ¬ (a=2 ∧ d-a+1=2) := by omega
    simp only [cubicExcludedProfile,h3,ite_false,cubicRetainedLambda,hn]

 theorem cubicExcludedRowsCharge (Q : ℕ → ℕ → ℝ) (s : ℕ → ℝ)
    (lambda : ℕ → ℕ → ℝ) (K : ℝ) (N : ℕ) (hN : 3 ≤ N) :
    (∑ p ∈ coupledDriftPairs N,
      (cubicRetainedLambda lambda p.2 (p.1-p.2+1)*K/s (p.1-p.2+1))*
        (Q p.2 (p.1-p.2+1))^2) =
    (K/s 2)*(Q 2 2)^2+
      ∑ d ∈ Finset.Icc 4 N, ∑ a ∈ Finset.Icc 2 (d-1),
        (lambda a (d-a+1)*K/s (d-a+1))*(Q a (d-a+1))^2 := by
  classical
  have hi : Finset.Icc 3 N=insert 3 (Finset.Icc 4 N) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hn : 3 ∉ Finset.Icc 4 N := by simp
  rw [coupledDriftPairs,Finset.sum_sigma,hi,Finset.sum_insert hn]
  congr 1
  · norm_num [cubicRetainedLambda]
  · apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro a ha
    have hh : ¬ (a=2 ∧ d-a+1=2) := by
      have := (Finset.mem_Icc.mp hd).1
      omega
    simp only [cubicRetainedLambda,hh,ite_false]

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.cubicExcludedProfile_boundary
#print axioms KLS.DeterministicBridgeNext.cubicExcludedRowsPrefix
#print axioms KLS.DeterministicBridgeNext.cubicExcludedRowsCharge
