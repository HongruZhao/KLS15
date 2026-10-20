import ActualCorrelatedQuarticTangentCaps200000

/-! Two genuine concave tangents give an exact supporting plane for the
three-energy feasible region.  The two tangent points need not coincide
under either inverse parameterization. -/
noncomputable section
open Set
namespace KLSBelow25.QuarticObservationSupport
open KLS.DeterministicBridgeNext
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def effective (b c v₀ : ℝ) : ℝ :=
  b*CreationSeed239.B+c*QuarticCreation200000.observationScale*
    deriv QuarticCreation200000.seedPhi v₀

def height (a b c u₀ v₀ : ℝ) : ℝ :=
  c*QuarticCreation200000.observationScale*
    (QuarticCreation200000.seedPhi v₀-v₀*deriv QuarticCreation200000.seedPhi v₀)+
  effective b c v₀*(CreationSeed239.seedPhi u₀-u₀*deriv CreationSeed239.seedPhi u₀)+
  max (2*a+effective b c v₀*deriv CreationSeed239.seedPhi u₀) 0

theorem supporting_shape {a b c u₀ v₀ : ℝ} (hc : 0 ≤ c)
    (hu₀ : u₀ ∈ Icc (0 : ℝ) 1) (hv₀ : v₀ ∈ Icc (0 : ℝ) 1)
    (heff : 0 ≤ effective b c v₀)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
    (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1)
    (hcurve : v ≤ CreationSeed239.seedPhi u) :
    2*a*u+b*CreationSeed239.B*v+(c/576)*200000*
      QuarticCreation200000.seedPhi v ≤ height a b c u₀ v₀ := by
  have h4 := concave_barrier_tangent QuarticCreation200000.seedInverseBarrier.concaveOn_phi
    hv₀ hv ((QuarticCreation200000.hasDerivAt_seedPhi hv₀).differentiableAt.hasDerivAt)
  change QuarticCreation200000.seedPhi v ≤ QuarticCreation200000.seedPhi v₀+
    deriv QuarticCreation200000.seedPhi v₀*(v-v₀) at h4
  have hm4 := mul_le_mul_of_nonneg_left h4
    (mul_nonneg hc (by norm_num [QuarticCreation200000.observationScale] :
      0 ≤ QuarticCreation200000.observationScale))
  have hc3 := mul_le_mul_of_nonneg_left hcurve heff
  have h3 := concave_barrier_tangent CreationSeed239.seedInverseBarrier.concaveOn_phi
    hu₀ hu ((CreationSeed239.hasDerivAt_seedPhi hu₀).differentiableAt.hasDerivAt)
  change CreationSeed239.seedPhi u ≤ CreationSeed239.seedPhi u₀+
    deriv CreationSeed239.seedPhi u₀*(u-u₀) at h3
  have hm3 := mul_le_mul_of_nonneg_left h3 heff
  have hlinear : (2*a+effective b c v₀*deriv CreationSeed239.seedPhi u₀)*u ≤
      max (2*a+effective b c v₀*deriv CreationSeed239.seedPhi u₀) 0 := by
    by_cases hpos : 0 ≤ 2*a+effective b c v₀*deriv CreationSeed239.seedPhi u₀
    · rw [max_eq_left hpos]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hu.2 hpos
    · rw [max_eq_right (le_of_not_ge hpos)]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hpos) hu.1
  dsimp only [height, effective] at *
  norm_num only [QuarticCreation200000.observationScale] at *
  nlinarith only [hm4, hc3, hm3, hlinear]

end KLSBelow25.QuarticObservationSupport
#print axioms KLSBelow25.QuarticObservationSupport.supporting_shape
