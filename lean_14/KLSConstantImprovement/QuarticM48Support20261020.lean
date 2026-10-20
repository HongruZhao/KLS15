import KLSConstantImprovement.QuarticM48Profile20261020
import KLSConstantImprovement.RawCubicQuarticEndpointBarrier
import KLSConstantImprovement.OriginalCubic4013023465

/-! Exact endpoint scalar payment discharges the improved affine barrier
on the entire u,Z domain. The original-law raw401.3023465 theorem is the sole
analytic input; it is already proved without an additional mass premise. -/
noncomputable section
open MeasureTheory Set
namespace KLSConstantImprovement.QuarticM48Support20261020
open KLS KLS.DeterministicBridgeNext
open QuarticM48Profile20261020Data QuarticM48Profile20261020
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def radA : ℝ := 61137796207/31250000000
def radB : ℝ := 1144808687127/500000000000
def radC : ℝ := 2865052500323/1000000000000

theorem endpoint_certificate :
    RawCubicQuarticEndpointBarrier.EndpointCertificate H J contact radA radB radC := by
  constructor <;> norm_num [H,J,contact,radA,radB,radC]

theorem original_raw : RawCubicWeightedBudget.UniversalRawCubicBound H :=
  OriginalCubic4013023465.original_observation_raw4013023465

theorem quartic_support :
    RawCubicQuarticWeightedBudget.UniversalCubicQuarticUnitSupport A B :=
  @RawCubicQuarticEndpointBarrier.normalized_support H J contact radA radB radC endpoint_certificate (@original_raw)

end KLSConstantImprovement.QuarticM48Support20261020
#print axioms KLSConstantImprovement.QuarticM48Support20261020.endpoint_certificate
#print axioms KLSConstantImprovement.QuarticM48Support20261020.original_raw
#print axioms KLSConstantImprovement.QuarticM48Support20261020.quartic_support
