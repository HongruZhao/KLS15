import KLS.WeightedCompactSmoothing
import KLS.CompactRawWeakDerivative

/-!
Actual compact mollifiers approximate raw H1 functions and their supplied
genuine weak derivatives in the continuous-potential weighted L2 norm.
No local Lipschitz condition is imposed on the function. Compact support of
the displayed derivatives is retained explicitly, as holds for compact
inverse-Hessian target-gradient coordinates and their literal product rule.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualCompactWeakH1Smoothing
open KLS
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem compact_rawWeak_weighted_smoothing
    {φ f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport f)
    (hfμ : MemLp f 2 (potentialMeasure φ))
    (hFμ : ∀ i, MemLp (F i) 2 (potentialMeasure φ))
    (hFc : ∀ i, HasCompactSupport (F i))
    (hFw : ∀ i, HasLocalWeakCoordinateDerivative f (F i) i) :
    (∀ k, ContDiff ℝ 3 (mollify k f) ∧ HasCompactSupport (mollify k f) ∧
      MemLp (mollify k f) 2 (potentialMeasure φ) ∧
      ∀ i, MemLp (coordinateDerivative (mollify k f) i) 2 (potentialMeasure φ)) ∧
    Tendsto (fun k => eLpNorm (mollify k f - f) 2 (potentialMeasure φ)) atTop (𝓝 0) ∧
    ∀ i, Tendsto (fun k => eLpNorm
      (coordinateDerivative (mollify k f) i - F i) 2 (potentialMeasure φ)) atTop (𝓝 0) := by
  have hfV := memLp_volume_of_potentialMeasure_hasCompactSupport hfμ hφ hc
  have hFV (i : Fin n) := memLp_volume_of_potentialMeasure_hasCompactSupport (hFμ i) hφ (hFc i)
  let G (i : Fin n) : Lp ℝ 2 (volume : Measure (Space n)) := (hFV i).toLp (F i)
  have hGe (i : Fin n) : (G i : Space n → ℝ) =ᵐ[volume] F i := (hFV i).coeFn_toLp
  have hG (i : Fin n) : HasWeakCoordinateDerivative f i (G i) := by
    change HasLocalWeakCoordinateDerivative f (fun x => G i x) i
    exact (hFw i).congr_ae Filter.EventuallyEq.rfl (hGe i).symm
  have hmk (k : ℕ) : ContDiff ℝ 3 (mollify k f) :=
    (mollify_contDiff (hfV.locallyIntegrable (by norm_num)) k).of_le (by simp)
  have hmc (k : ℕ) := hasCompactSupport_mollify hc k
  have hmμ (k : ℕ) := memLp_of_continuous_hasCompactSupport hφ (hmk k).continuous (hmc k)
  have hmdμ (k : ℕ) (i : Fin n) := memLp_of_continuous_hasCompactSupport hφ
    (contDiff_coordinateDerivative (hmk k) (m := 0) (by norm_num) i).continuous
    (hasCompactSupport_coordinateDerivative (hmc k) i)
  refine ⟨fun k => ⟨hmk k, hmc k, hmμ k, hmdμ k⟩, ?_, ?_⟩
  · exact eLpNorm_potentialMeasure_sub_tendsto_zero_of_compact_support hφ
      (isCompact_mollifierEnlargement hc) (tsupport_mollify_subset hc)
      (subset_mollifierEnlargement _) (fun k => memLp_mollify hfV k) hfV hmμ hfμ
      (eLpNorm_mollify_sub_tendsto_zero hfV)
  · intro i
    let S : Set (Space n) := mollifierEnlargement (tsupport f) ∪ tsupport (F i)
    have hS : IsCompact S := (isCompact_mollifierEnlargement hc).union (hFc i)
    have hDS (k : ℕ) : tsupport (coordinateDerivative (mollify k f) i) ⊆ S :=
      (tsupport_coordinateDerivative_subset _ i).trans
        ((tsupport_mollify_subset hc k).trans subset_union_left)
    have hlim : Tendsto (fun k => eLpNorm
        (coordinateDerivative (mollify k f) i - F i) 2 volume) atTop (𝓝 0) := by
      have ht := (hG i).eLpNorm_mollify_derivative_sub_tendsto_zero hfV
      have he (k : ℕ) : eLpNorm
          (coordinateDerivative (mollify k f) i - (G i : Space n → ℝ)) 2 volume =
          eLpNorm (coordinateDerivative (mollify k f) i - F i) 2 volume :=
        eLpNorm_congr_ae (EventuallyEq.rfl.sub (hGe i))
      simpa only [he] using ht
    exact eLpNorm_potentialMeasure_sub_tendsto_zero_of_compact_support hφ hS hDS
      subset_union_right
      (fun k => (contDiff_coordinateDerivative (hmk k) (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_coordinateDerivative (hmc k) i))
      (hFV i) (fun k => hmdμ k i) (hFμ i) hlim

end KLSConstantImprovement.ActualCompactWeakH1Smoothing
#print axioms KLSConstantImprovement.ActualCompactWeakH1Smoothing.compact_rawWeak_weighted_smoothing
