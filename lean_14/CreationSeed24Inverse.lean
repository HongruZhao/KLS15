import CreationSeed24Jets
import RadicalInverseBarrier
noncomputable section
open Set
namespace KLSBelow25.CreationSeed24
open KLSBelow25
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
def seedInverseBarrier : DescendingC1Barrier :=
  RadicalBarrier.toDescendingC1Barrier seedT_range.1 seedT_range.2
    continuous_seedV continuous_seedVp hasDerivAt_seedV hasDerivAt_seedVp
    (fun t ht => seedV_positive ht)
    (fun t ht => by simpa only [RadicalBarrier.slope,seedSlope,seedVp,seedVp] using seedSlope_positive ht)
    (fun t ht => by simpa only [RadicalBarrier.concavity,seedConcavity,seedVp,seedVpp,
      seedVp,seedVpp] using seedConcavity_positive ht)
    seed_endpoint_above_one

def seedPhi : ℝ → ℝ := seedInverseBarrier.phi
def seedParameter (u : ℝ) : ℝ := RadicalBarrier.parameter (seedPhi u)
theorem seedPhi_zero : seedPhi 0=1 := seedInverseBarrier.phi_zero
theorem seedPhi_range {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    seedPhi u ∈ Ioc (1-seedT^2) 1 := (seedInverseBarrier.phi_branch_of_unit hu).1
theorem seedParameter_range {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    seedParameter u ∈ Icc (0 : ℝ) seedT :=
  RadicalBarrier.parameter_mem_interval seedT_range.1 (seedPhi_range hu).1.le
theorem seedPhi_inverse {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    RadicalBarrier.value seedV (seedPhi u)=u := (seedInverseBarrier.phi_branch_of_unit hu).2
theorem seedPhi_z_identity {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    seedPhi u=1-(seedParameter u)^2 := by
  have hs : (seedParameter u)^2=1-seedPhi u :=
    Real.sq_sqrt (sub_nonneg.mpr (seedPhi_range hu).2)
  linarith
theorem seedPhi_u_identity {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    u=(seedParameter u)^2*(seedV (seedParameter u))^2 := by
  have hi := seedPhi_inverse hu
  change (1-seedPhi u)*(seedV (seedParameter u))^2=u at hi
  rw [seedPhi_z_identity hu] at hi
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
theorem hasDerivAt_seedPhi {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    HasDerivAt seedPhi
      (-(seedV (seedParameter u)*seedSlope (seedParameter u)))⁻¹ u := by
  simpa only [seedInverseBarrier,RadicalBarrier.toDescendingC1Barrier,RadicalBarrier.derivative,
    seedPhi,seedParameter,seedSlope,seedVp,seedVp,neg_mul] using seedInverseBarrier.hasDerivAt_phi hu

end KLSBelow25.CreationSeed24
#print axioms KLSBelow25.CreationSeed24.hasDerivAt_seedPhi
