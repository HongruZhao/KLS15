import KLSConstantImprovement.TrueCapTwoStageOrbitObstruction
import KLSConstantImprovement.ConstantTailFamilyLowerBound
import KLSConstantImprovement.QuadraticCapBellmanCertificates

/-! Correct orbit-normalized method obstruction for accepted chord-based
StageCertificates. The original C<p*(line0).positive(p) comparison is used
without strengthening. These are scalar certificate-family lower bounds. -/
noncomputable section
namespace KLSConstantImprovement.TwoStageOrbitObstruction
open PositiveFiniteHeadBellman QuadraticCapBellmanCertificates
set_option maxHeartbeats 3000000

theorem stage_positive_truecap
    {A R w : ℝ} {current next : Affine}
    (h : StageCertificate w R (capChord A R) current next)
    (hA : 0 ≤ A) (hR : 0 < R)
    {r s : ℝ} (hr : 1 ≤ r) (hrR : r ≤ R)
    (hs : 1 ≤ s) (hcap : r-A/r ≤ s) (hsr : s ≤ r) :
    current.positive r ≤ w*(r-s)+s*next.positive s := by
  have hlower := (capChord_le_quadratic_transition hA hR hr hrR).trans hcap
  have he := h.stage r hr hrR s hs hlower hsr
  have hn : 0 ≤ w*(r-s)+s*next.positive s :=
    add_nonneg (mul_nonneg h.weight_nonneg (by linarith))
      (mul_nonneg (by linarith) (next.positive_nonneg s))
  exact max_le hn he

theorem chord_family_endpoint_gt_129
    (K C R w p : ℝ) (L0 L1 L2 : Affine)
    (hKfloor : 6+4*Real.sqrt 2 ≤ K) (hR : 0 < R)
    (hp : 1 ≤ p) (hpR : p ≤ R)
    (h0 : StageCertificate 1 R (capChord (2/K^2) R) L0 L1)
    (h1 : StageCertificate w R (capChord (2/K^2) R) L1 L2)
    (hbase : 2/K^2+w*((802604693/2000000 : ℝ)/(36*K^3)) ≤ C)
    (hbudget : C < p*L0.positive p) :
    (129/10 : ℝ) < 1+K*p := by
  have hA : 0 ≤ (2 : ℝ)/K^2 := by positivity
  apply TrueCapTwoStageOrbitObstruction.true_cap_family_endpoint_gt_129 K C w p
    L0.positive L1.positive L2.positive hKfloor h1.weight_nonneg hp
    ?_ ?_ ?_ hbase hbudget
  · intro s hs hcap hsp
    simpa only [one_mul] using stage_positive_truecap h0 hA hR hp hpR hs hcap hsp
  · intro r hr hrp s hs hcap hsr
    exact stage_positive_truecap h1 hA hR hr (hrp.trans hpR) hs hcap hsr
  · exact L2.positive_zero h1.next_slope_nonneg h1.next_at_one (le_refl _)

theorem current_constant_tail_family_endpoint_gt_129
    (K C y alpha R w p : ℝ) (L0 L1 L2 : Affine)
    (hK : 0 < K) (hC : 0 < C) (hy : 0 < y)
    (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (hq : 0 ≤ K*alpha-4/(1-alpha)+2-K*C/y)
    (hR : 0 < R) (hp : 1 ≤ p) (hpR : p ≤ R)
    (h0 : StageCertificate 1 R (capChord (2/K^2) R) L0 L1)
    (h1 : StageCertificate w R (capChord (2/K^2) R) L1 L2)
    (hbase : 2/K^2+w*((802604693/2000000 : ℝ)/(36*K^3)) ≤ C)
    (hbudget : C < p*L0.positive p) :
    (129/10 : ℝ) < 1+K*p := by
  have hfloor := ConstantTailFamilyLowerBound.K_lower_of_tail_coefficient K C y alpha hK hC hy ha ha1 hq
  exact chord_family_endpoint_gt_129 K C R w p L0 L1 L2 hfloor.le hR hp hpR h0 h1 hbase hbudget

end KLSConstantImprovement.TwoStageOrbitObstruction
#print axioms KLSConstantImprovement.TwoStageOrbitObstruction.stage_positive_truecap
#print axioms KLSConstantImprovement.TwoStageOrbitObstruction.chord_family_endpoint_gt_129
#print axioms KLSConstantImprovement.TwoStageOrbitObstruction.current_constant_tail_family_endpoint_gt_129
