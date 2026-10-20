import KLSConstantImprovement.ActualCompactRawSubsolutionTests405
import KLS.LocalWeakAlgebra

/-! A bounded compact raw cutoff squared times an unbounded raw-H1
function is a genuine compact raw-H1 test, with its full literal product
derivative. No truncation of the positive-part tail is used. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff
namespace KLSConstantImprovement.ActualCompactRawExcessTest405
open KLS
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ}

def rawExcessTest (χ e : Space n → ℝ) : Space n → ℝ := fun x => χ x^2*e x

def rawExcessTestDerivative (χ e : Space n → ℝ)
    (Dχ De : Fin n → Space n → ℝ) (i : Fin n) : Space n → ℝ :=
  fun x => 2*χ x*Dχ i x*e x + χ x^2*De i x

theorem rawExcessTest_domains
    {χ e : Space n → ℝ} {Dχ De : Fin n → Space n → ℝ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hDχ : ∀ i E, IsCompact E → MemLp (Dχ i) ∞ (volume.restrict E))
    (hwχ : ∀ i, HasLocalWeakCoordinateDerivative χ (Dχ i) i)
    (he : ∀ E, IsCompact E → MemLp e 2 (volume.restrict E))
    (hDe : ∀ i E, IsCompact E → MemLp (De i) 2 (volume.restrict E))
    (hwe : ∀ i, HasLocalWeakCoordinateDerivative e (De i) i) :
    HasCompactSupport (rawExcessTest χ e) ∧
      (∀ E, IsCompact E → MemLp (rawExcessTest χ e) 2 (volume.restrict E)) ∧
      (∀ i E, IsCompact E → MemLp (rawExcessTestDerivative χ e Dχ De i) 2 (volume.restrict E)) ∧
      ∀ i, HasLocalWeakCoordinateDerivative (rawExcessTest χ e)
        (rawExcessTestDerivative χ e Dχ De i) i := by
  have hχtop : MemLp χ ∞ (volume : Measure (Space n)) :=
    hχ.memLp_of_hasCompactSupport hc
  have hχ2 : MemLp χ 2 (volume : Measure (Space n)) := hχ.memLp_of_hasCompactSupport hc
  have hχsq2 : MemLp (fun x => χ x^2) 2 (volume : Measure (Space n)) :=
    (hχ.pow 2).memLp_of_hasCompactSupport (by simpa only [pow_two, Pi.mul_def] using hc.mul_right (f' := χ))
  have hχsqtop : MemLp (fun x => χ x^2) ∞ (volume : Measure (Space n)) := by
    have hh : MemLp (χ * χ) ∞ (volume : Measure (Space n)) := hχtop.mul hχtop
    change MemLp (fun x => χ x*χ x) ∞ (volume : Measure (Space n)) at hh
    simpa only [pow_two] using hh
  have hDχ2 (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (Dχ i) 2 (volume.restrict E) := by
    letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
    exact (hDχ i E hE).mono_exponent (by norm_num)
  have hDsq2 (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => 2*χ x*Dχ i x) 2 (volume.restrict E) := by
    simpa only [mul_assoc, Pi.mul_apply] using ((hχtop.restrict E).mul (hDχ2 i E hE)).const_mul 2
  have hwsq (i : Fin n) : HasLocalWeakCoordinateDerivative (fun x => χ x^2)
      (fun x => 2*χ x*Dχ i x) i := by
    have hh := (hwχ i).mul (hwχ i) (fun E _ => hχ2.restrict E)
      (fun E _ => hχ2.restrict E) (hDχ2 i) (hDχ2 i)
    refine hh.congr_ae (Eventually.of_forall fun x => by ring)
      (Eventually.of_forall fun x => by ring)
  have htest (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (rawExcessTest χ e) 2 (volume.restrict E) :=
    (hχsqtop.restrict E).mul (he E hE)
  have htestD (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (rawExcessTestDerivative χ e Dχ De i) 2 (volume.restrict E) := by
    have ha : MemLp (fun x => 2*χ x*Dχ i x*e x) 2 (volume.restrict E) := by
      have htop : MemLp (fun x => 2*χ x*Dχ i x) ∞ (volume.restrict E) :=
        by simpa only [mul_assoc, Pi.mul_apply] using ((hχtop.restrict E).mul (hDχ i E hE)).const_mul 2
      exact htop.mul (he E hE)
    exact ha.add ((hχsqtop.restrict E).mul (hDe i E hE))
  refine ⟨?_, htest, htestD, fun i => ?_⟩
  · change HasCompactSupport (fun x => χ x^2*e x)
    simpa only [pow_two, Pi.mul_def] using (hc.mul_right (f' := χ)).mul_right (f' := e)
  · have hh := (hwsq i).mul (hwe i) (fun E _ => hχsq2.restrict E) he (hDsq2 i) (hDe i)
    change HasLocalWeakCoordinateDerivative (fun x => χ x^2*e x)
      (fun x => 2*χ x*Dχ i x*e x + χ x^2*De i x) i
    exact hh

end KLSConstantImprovement.ActualCompactRawExcessTest405
#print axioms KLSConstantImprovement.ActualCompactRawExcessTest405.rawExcessTest_domains
