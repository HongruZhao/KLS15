import KLSConstantImprovement.RawCubicQuarticAffineFamily
import KLSConstantImprovement.RawCubicQuarticWeightedBudget

/-! The universal affine cubic/quartic support is discharged from a prior
universal cubic theorem, through the actual same-test maximizer transfer.
No law-specific quartic premise is introduced. -/
noncomputable section
open MeasureTheory Set
namespace KLSConstantImprovement.RawCubicQuarticAffineSupport
open KLS KLS.DeterministicBridgeNext
open RawCubicQuarticAffineFamily RawCubicQuarticTransfer
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def slope (s : ℝ) : ℝ := 9/2+(22/3)*s/(1-s)
def height (H s : ℝ) : ℝ := (H/216)*(44/(1-s)+27/s)

theorem normalized_support {H s : ℝ} (hH : 216 ≤ H)
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound H)
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    RawCubicQuarticWeightedBudget.UniversalCubicQuarticUnitSupport
      (slope s) (height H s) := by
  intro n μ hμ f hf
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hHp : 0 < H := by linarith
  have hb := actual_raw_cubic_quartic_joint_unit_bound hHp hraw
    (J_positive hHp hs) (barrier hH hs) hμ f hf
  change actualAppellEnergy μ f 4 ≤ J H s *
    (1-s*(actualAppellEnergy μ f 3/H)) at hb
  have hsp : 0 < 1-s := sub_pos.mpr hs.2
  have he : actualAppellEnergy μ f 4/576+
      slope s*(actualAppellEnergy μ f 3/36)-height H s =
        (actualAppellEnergy μ f 4-J H s*(1-s*(actualAppellEnergy μ f 3/H)))/576 := by
    unfold slope height J
    field_simp [hHp.ne',hs.1.ne',hsp.ne'] <;> ring
  apply sub_nonpos.mp
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb) (by norm_num)

end KLSConstantImprovement.RawCubicQuarticAffineSupport
#print axioms KLSConstantImprovement.RawCubicQuarticAffineSupport.normalized_support
