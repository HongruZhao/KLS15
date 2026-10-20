import KLSConstantImprovement.M12OptimizedProfile
import KLSConstantImprovement.RawCubicQuarticEndpointBarrier
import KLSConstantImprovement.OriginalCubic401317

/-! Exact endpoint scalar payment discharges the improved affine barrier
on the entire u,Z domain. The original-law raw401.317 theorem is the sole
analytic input; it is already proved without an additional mass premise. -/
noncomputable section
open MeasureTheory Set
namespace KLSConstantImprovement.M12OptimizedSupport
open KLS KLS.DeterministicBridgeNext
open M12OptimizedProfileData M12OptimizedProfile
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def radA : ℝ := 1956373760591/1000000000000
def radB : ℝ := 461306781823/200000000000
def radC : ℝ := 5637046617/1953125000

theorem endpoint_certificate :
    RawCubicQuarticEndpointBarrier.EndpointCertificate H J contact radA radB radC := by
  constructor <;> norm_num [H,J,contact,radA,radB,radC]

theorem original_raw : RawCubicWeightedBudget.UniversalRawCubicBound H :=
  OriginalCubic401317.original_observation_raw401317

theorem quartic_support :
    RawCubicQuarticWeightedBudget.UniversalCubicQuarticUnitSupport A B :=
  @RawCubicQuarticEndpointBarrier.normalized_support H J contact radA radB radC endpoint_certificate (@original_raw)

end KLSConstantImprovement.M12OptimizedSupport
#print axioms KLSConstantImprovement.M12OptimizedSupport.endpoint_certificate
#print axioms KLSConstantImprovement.M12OptimizedSupport.original_raw
#print axioms KLSConstantImprovement.M12OptimizedSupport.quartic_support
