import KLSConstantImprovement.Raw401317Quartic13999Profile
import KLSConstantImprovement.RawCubicQuarticEndpointBarrier
import KLSConstantImprovement.OriginalCubic401317

/-! Exact endpoint scalar payment discharges the improved affine barrier
on the entire u,Z domain. The original-law raw401.317 theorem is the sole
analytic input; it is already proved without an additional mass premise. -/
noncomputable section
open MeasureTheory Set
namespace KLSConstantImprovement.OriginalQuartic13999Support
open KLS KLS.DeterministicBridgeNext
open Raw401317Quartic13999ProfileData Raw401317Quartic13999Profile
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def radA : ℝ := 1956373760591/1000000000000
def radB : ℝ := 462563801677/200000000000
def radC : ℝ := 723508104509/250000000000

theorem endpoint_certificate :
    RawCubicQuarticEndpointBarrier.EndpointCertificate H J contact radA radB radC := by
  constructor <;> norm_num [H,J,contact,radA,radB,radC]

theorem original_raw : RawCubicWeightedBudget.UniversalRawCubicBound H :=
  OriginalCubic401317.original_observation_raw401317

theorem quartic_support :
    RawCubicQuarticWeightedBudget.UniversalCubicQuarticUnitSupport A B :=
  @RawCubicQuarticEndpointBarrier.normalized_support H J contact radA radB radC endpoint_certificate (@original_raw)

end KLSConstantImprovement.OriginalQuartic13999Support
#print axioms KLSConstantImprovement.OriginalQuartic13999Support.endpoint_certificate
#print axioms KLSConstantImprovement.OriginalQuartic13999Support.original_raw
#print axioms KLSConstantImprovement.OriginalQuartic13999Support.quartic_support
