import CoupledJointNoiseSeed239Numerics

/-! Exact range check for the proposed finite-grade projection improvement.
This adds no actual-law or universal endpoint assumption. -/
noncomputable section
namespace KLSBelow25.CoupledEnergy.NumericsJointNoiseSeed239

theorem alpha_le_low_threshold (d : ℕ) (hd4 : 4 ≤ d) (hd24 : d ≤ 24) :
    alpha d ≤ ((d : ℝ)-1)/((d : ℝ)+1) := by
  interval_cases d <;> norm_num [alpha]

end KLSBelow25.CoupledEnergy.NumericsJointNoiseSeed239
#print axioms KLSBelow25.CoupledEnergy.NumericsJointNoiseSeed239.alpha_le_low_threshold
