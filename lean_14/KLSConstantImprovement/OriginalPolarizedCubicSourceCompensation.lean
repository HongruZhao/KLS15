import Mathlib

/-! Positive finite spectral remainder and exact scalar bookkeeping for
a polarized original moment-map cubic trace calculation. The source PDE,
entrywise Brascamp-Lieb domains and same-source tensor contractions remain
analytic inputs. The weighted quadratic BL deficit is not paid uniformly;
no all-law combined-energy or Poincare improvement is asserted. -/
noncomputable section
namespace KLSConstantImprovement.OriginalPolarizedCubicSourceCompensation

theorem symmetric_cubic_spectral_remainder {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a^3+b^3+c^3)/3 ≥
      (a^2*b+a*b^2+a^2*c+a*c^2+b^2*c+b*c^2)/6 := by
  have hab := mul_nonneg (sq_nonneg (a-b)) (add_nonneg ha hb)
  have hac := mul_nonneg (sq_nonneg (a-c)) (add_nonneg ha hc)
  have hbc := mul_nonneg (sq_nonneg (b-c)) (add_nonneg hb hc)
  nlinarith

theorem integrated_signed_compensation {m p remainder cross mean energy : ℝ}
    (hpde : m = p + remainder + (3/2 : ℝ)*energy)
    (hcross : cross = energy-m+mean) :
    m+2*p+2*remainder+3*cross = 3*mean := by linarith

theorem paid_remainders_retained {m p remainder cross mean : ℝ}
    (hidentity : m+2*p+2*remainder+3*cross = 3*mean)
    (hp : 0 ≤ p) (hr : 0 ≤ remainder) :
    m ≤ 3*mean-3*cross := by linarith

end KLSConstantImprovement.OriginalPolarizedCubicSourceCompensation
#print axioms KLSConstantImprovement.OriginalPolarizedCubicSourceCompensation.symmetric_cubic_spectral_remainder
#print axioms KLSConstantImprovement.OriginalPolarizedCubicSourceCompensation.integrated_signed_compensation
#print axioms KLSConstantImprovement.OriginalPolarizedCubicSourceCompensation.paid_remainders_retained
