import VariableAlpha24BernsteinData
import VariableAlpha24PolynomialJets
import RadicalInverseBarrier

/-! The two actual C1 inverse branches, with all polynomial and endpoint
inputs discharged by exact scalar certificates. -/
noncomputable section
open Set
namespace VariableAlpha24
open KLSBelow25
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def seedInverseBarrier : DescendingC1Barrier :=
  RadicalBarrier.toDescendingC1Barrier seedT_range.1 seedT_range.2
    continuous_seedV continuous_seedVFirst hasDerivAt_seedV hasDerivAt_seedVFirst
    (fun t ht => seedV_positive ht)
    (fun t ht => by simpa only [RadicalBarrier.slope,seedSlope,seedVp,seedVFirst] using seedSlope_positive ht)
    (fun t ht => by simpa only [RadicalBarrier.concavity,seedConcavity,seedVp,seedVpp,
      seedVFirst,seedVSecond] using seedConcavity_positive ht)
    seed_endpoint_above_one

def commonInverseBarrier : DescendingC1Barrier :=
  RadicalBarrier.toDescendingC1Barrier commonT_range.1 commonT_range.2
    continuous_commonV continuous_commonVFirst hasDerivAt_commonV hasDerivAt_commonVFirst
    (fun t ht => commonV_positive ht)
    (fun t ht => by simpa only [RadicalBarrier.slope,commonSlope,commonVp,commonVFirst] using commonSlope_positive ht)
    (fun t ht => by simpa only [RadicalBarrier.concavity,commonConcavity,commonVp,commonVpp,
      commonVFirst,commonVSecond] using commonConcavity_positive ht)
    common_endpoint_above_one

def seedPhi : ℝ → ℝ := seedInverseBarrier.phi
def commonPhi : ℝ → ℝ := commonInverseBarrier.phi
def seedParameter (u : ℝ) : ℝ := RadicalBarrier.parameter (seedPhi u)
def commonParameter (u : ℝ) : ℝ := RadicalBarrier.parameter (commonPhi u)

theorem seedPhi_zero : seedPhi 0=1 := seedInverseBarrier.phi_zero
theorem commonPhi_zero : commonPhi 0=1 := commonInverseBarrier.phi_zero

theorem seedPhi_range {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    seedPhi u ∈ Ioc (1-seedT^2) 1 := (seedInverseBarrier.phi_branch_of_unit hu).1
theorem commonPhi_range {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    commonPhi u ∈ Ioc (1-commonT^2) 1 := (commonInverseBarrier.phi_branch_of_unit hu).1

theorem seedParameter_range {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    seedParameter u ∈ Icc (0 : ℝ) seedT :=
  RadicalBarrier.parameter_mem_interval seedT_range.1 (seedPhi_range hu).1.le
theorem commonParameter_range {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    commonParameter u ∈ Icc (0 : ℝ) commonT :=
  RadicalBarrier.parameter_mem_interval commonT_range.1 (commonPhi_range hu).1.le

theorem seedPhi_inverse {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    RadicalBarrier.value seedV (seedPhi u)=u := (seedInverseBarrier.phi_branch_of_unit hu).2
theorem commonPhi_inverse {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    RadicalBarrier.value commonV (commonPhi u)=u := (commonInverseBarrier.phi_branch_of_unit hu).2

theorem seedPhi_z_identity {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    seedPhi u=1-(seedParameter u)^2 := by
  have hs : (seedParameter u)^2=1-seedPhi u :=
    Real.sq_sqrt (sub_nonneg.mpr (seedPhi_range hu).2)
  linarith
theorem commonPhi_z_identity {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    commonPhi u=1-(commonParameter u)^2 := by
  have hs : (commonParameter u)^2=1-commonPhi u :=
    Real.sq_sqrt (sub_nonneg.mpr (commonPhi_range hu).2)
  linarith

theorem seedPhi_u_identity {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    u=(seedParameter u)^2*(seedV (seedParameter u))^2 := by
  have hi := seedPhi_inverse hu
  change (1-seedPhi u)*(seedV (seedParameter u))^2=u at hi
  rw [seedPhi_z_identity hu] at hi
  simpa only [sub_sub_cancel] using hi.symm
theorem commonPhi_u_identity {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    u=(commonParameter u)^2*(commonV (commonParameter u))^2 := by
  have hi := commonPhi_inverse hu
  change (1-commonPhi u)*(commonV (commonParameter u))^2=u at hi
  rw [commonPhi_z_identity hu] at hi
  simpa only [sub_sub_cancel] using hi.symm

theorem seedParameter_positive {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hu0 : 0 < u) :
    0 < seedParameter u := by
  have hnonneg := (seedParameter_range hu).1
  have hid := seedPhi_u_identity hu
  by_contra hn
  have he : seedParameter u=0 := le_antisymm (not_lt.mp hn) hnonneg
  rw [he] at hid
  norm_num at hid
  linarith
theorem commonParameter_positive {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hu0 : 0 < u) :
    0 < commonParameter u := by
  have hnonneg := (commonParameter_range hu).1
  have hid := commonPhi_u_identity hu
  by_contra hn
  have he : commonParameter u=0 := le_antisymm (not_lt.mp hn) hnonneg
  rw [he] at hid
  norm_num at hid
  linarith

theorem hasDerivAt_seedPhi {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    HasDerivAt seedPhi
      (-(seedV (seedParameter u)*seedSlope (seedParameter u)))⁻¹ u := by
  simpa only [seedInverseBarrier,RadicalBarrier.toDescendingC1Barrier,RadicalBarrier.derivative,
    seedPhi,seedParameter,seedSlope,seedVp,seedVFirst,neg_mul] using seedInverseBarrier.hasDerivAt_phi hu
theorem hasDerivAt_commonPhi {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    HasDerivAt commonPhi
      (-(commonV (commonParameter u)*commonSlope (commonParameter u)))⁻¹ u := by
  simpa only [commonInverseBarrier,RadicalBarrier.toDescendingC1Barrier,RadicalBarrier.derivative,
    commonPhi,commonParameter,commonSlope,commonVp,commonVFirst,neg_mul] using commonInverseBarrier.hasDerivAt_phi hu

end VariableAlpha24
#print axioms VariableAlpha24.hasDerivAt_seedPhi
#print axioms VariableAlpha24.hasDerivAt_commonPhi
