import KLSConstantImprovement.SourceProductionJointRaw405Payoff

/-! A tighter support certificate for the two already proved production branches.
No analytic hypotheses are changed. All losses are retained at their new
mixing weights; the affine q coefficient cancels exactly at 8/33. -/
noncomputable section
namespace KLSConstantImprovement.ProductionMix404894545
open SourceMatchedMeanResponseConditionalPayoff

theorem raw404894545_disk_certificate :
    0 ≤ (404894545/1000000:ℝ)-(1220/7:ℝ) ∧
    (1220/7:ℝ)^2+(11628/77:ℝ)^2 ≤
      ((404894545/1000000:ℝ)-(1220/7:ℝ))^2 := by
  norm_num

theorem retained_joint_raw404894545
    {V N g r t q rowLoss newLoss : ℝ}
    (hg : 0 ≤ g) (hneff : 0 ≤ N-g/2)
    (hdisk : (r-(N-g/2))^2+t^2 ≤ (N-g/2)^2)
    (hq : 0 ≤ q) (hrowLoss : 0 ≤ rowLoss) (hnewLoss : 0 ≤ newLoss)
    (hrow : V ≤ 168*r+147*t+(63/2:ℝ)*q-rowLoss)
    (hnew : V ≤ (30852/175:ℝ)*r+(26652/175:ℝ)*t-
      (252/25:ℝ)*q-newLoss) :
    V ≤ (404894545/1000000:ℝ)*N-(404894545/2000000:ℝ)*g-
      (8/33:ℝ)*rowLoss-(25/33:ℝ)*newLoss ∧
      V ≤ (404894545/1000000:ℝ)*N := by
  have hc := raw404894545_disk_certificate
  have hsupport := disk_linear_support hneff hc.1 hc.2 hdisk
  have haverage : V ≤ (1220/7:ℝ)*r+(11628/77:ℝ)*t-
      (8/33:ℝ)*rowLoss-(25/33:ℝ)*newLoss := by
    linarith only [hrow,hnew]
  have hfirst : V ≤ (404894545/1000000:ℝ)*N-(404894545/2000000:ℝ)*g-
      (8/33:ℝ)*rowLoss-(25/33:ℝ)*newLoss := by
    nlinarith only [hsupport,haverage]
  exact ⟨hfirst, by linarith only [hfirst,hg,hrowLoss,hnewLoss]⟩

end KLSConstantImprovement.ProductionMix404894545
#print axioms KLSConstantImprovement.ProductionMix404894545.raw404894545_disk_certificate
#print axioms KLSConstantImprovement.ProductionMix404894545.retained_joint_raw404894545
