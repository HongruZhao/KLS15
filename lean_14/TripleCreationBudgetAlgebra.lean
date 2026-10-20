import TripleCreationRecurrenceAlgebra
import SelectedRowsHarmonicParameters

/-! Exact coefficient matching for a selected proper a=3 insertion row.
Actual tensor bounds must supply the affine square estimate separately. -/
noncomputable section
namespace KLSBelow25.TripleCreation
set_option maxHeartbeats 1200000

def affineQ (n : ℝ) : ℝ := chooseThree n*(3*n-8)

def affineRest (B n : ℝ) : ℝ :=
  9*n*(n-1)*(n-2)*(n-3)*(n-4)+recurrenceMultiplier n*B

def canonicalCharge (K b : ℝ) : ℝ := b^2/(36*K^2)

def chargeRatio (b : ℝ) : ℝ := 6*(3*b-2)/(b*(b+1)*(b+2))

def effectiveNeighbor (B K b : ℝ) : ℝ :=
  affineRest B (b+2)/(K^2*(b+2)^2*(b+1)^2*(1-chargeRatio b))

theorem chargeRatio_two : chargeRatio 2=1 := by norm_num [chargeRatio]

theorem chargeRatio_identity (b : ℝ) (hb : 2 ≤ b) :
    1-chargeRatio b=(b-2)*(b-1)*(b+6)/(b*(b+1)*(b+2)) := by
  have h0 : b ≠ 0 := by linarith
  have h1 : b+1 ≠ 0 := by linarith
  have h2 : b+2 ≠ 0 := by linarith
  unfold chargeRatio
  field_simp
  ring

theorem chargeRatio_nonneg (b : ℝ) (hb : 2 ≤ b) : 0 ≤ chargeRatio b := by
  unfold chargeRatio
  have h0 : 0 ≤ b := by linarith
  have h1 : 0 ≤ b+1 := by linarith
  have h2 : 0 ≤ b+2 := by linarith
  have h3 : 0 ≤ 3*b-2 := by linarith
  positivity

theorem chargeRatio_lt_one (b : ℝ) (hb : 2 < b) : chargeRatio b<1 := by
  have he := chargeRatio_identity b hb.le
  have h0 : 0 < b := by linarith
  have h1 : 0 < b+1 := by linarith
  have h2 : 0 < b+2 := by linarith
  have h3 : 0 < b-2 := by linarith
  have h4 : 0 < b-1 := by linarith
  have h5 : 0 < b+6 := by linarith
  have hp : 0 < (b-2)*(b-1)*(b+6)/(b*(b+1)*(b+2)) := by positivity
  linarith

theorem affineQ_normalization (K b : ℝ) (hK : K ≠ 0) (hb : 2 ≤ b) :
    affineQ (b+2)/(K^2*(b+2)^2*(b+1)^2) =
      chargeRatio b*canonicalCharge K b := by
  have h0 : b ≠ 0 := by linarith
  have h1 : b+1 ≠ 0 := by linarith
  have h2 : b+2 ≠ 0 := by linarith
  unfold affineQ chooseThree chargeRatio canonicalCharge
  field_simp
  ring

theorem affine_recurrence_split (L B n : ℝ) :
    forcing L n+recurrenceMultiplier n*B=affineQ n*L+affineRest B n := by
  unfold forcing affineQ affineRest chooseThree
  ring

theorem effectiveNeighbor_three (B K : ℝ) (hK : K ≠ 0) :
    effectiveNeighbor B K 3=9/K^2 := by
  norm_num [effectiveNeighbor,affineRest,recurrenceMultiplier,chargeRatio]
  field_simp
  ring

theorem effectiveNeighbor_four (K : ℝ) (hK : K ≠ 0) :
    effectiveNeighbor 13824 K 4=(264/5)/K^2 := by
  norm_num [effectiveNeighbor,affineRest,recurrenceMultiplier,chargeRatio]
  field_simp
  ring

theorem effectiveNeighbor_nonneg {B K b : ℝ} (hB : 0 ≤ B) (hK : 0 < K)
    (hb : 3 ≤ b) : 0 ≤ effectiveNeighbor B K b := by
  have hr := chargeRatio_lt_one b (by linarith)
  have hn : 5 ≤ b+2 := by linarith
  have hm := recurrenceMultiplier_nonneg (b+2) hn
  have h0 : 0 ≤ b+2 := by linarith
  have h1 : 0 ≤ b+2-1 := by linarith
  have h2 : 0 ≤ b+2-2 := by linarith
  have h3 : 0 ≤ b+2-3 := by linarith
  have h4 : 0 ≤ b+2-4 := by linarith
  have hrest : 0 ≤ affineRest B (b+2) := by unfold affineRest; positivity
  unfold effectiveNeighbor
  exact div_nonneg hrest (by positivity)

end KLSBelow25.TripleCreation
#print axioms KLSBelow25.TripleCreation.affineQ_normalization
#print axioms KLSBelow25.TripleCreation.chargeRatio_lt_one
#print axioms KLSBelow25.TripleCreation.effectiveNeighbor_three
#print axioms KLSBelow25.TripleCreation.effectiveNeighbor_four
