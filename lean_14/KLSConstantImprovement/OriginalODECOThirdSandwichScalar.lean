import Mathlib

/- Finite ODECO lift and scalar consequences. Matrix positivity, original
same-joint-H cube upper and directional response are explicit premises.
No all-tensor diagonalization or original-law Lean bridge is asserted. -/

namespace KLSConstantImprovement.OriginalODECOThirdSandwichScalar

theorem absolute_off_cube_from_pinching
    (offAbs weightedOff cube diagonalCube : ℝ)
    (hentry : offAbs ≤ weightedOff)
    (hpinching : 2 * weightedOff ≤ cube - diagonalCube) :
    2 * offAbs ≤ cube - diagonalCube := by
  linarith

theorem odeco_half_cube_lift
    (w diagonalCube offAbs cube : ℝ)
    (htriangle : w ≤ diagonalCube + offAbs)
    (hoff : 2 * offAbs ≤ cube - diagonalCube) :
    2 * w ≤ cube + diagonalCube := by
  linarith

theorem original_odeco_third_upper
    (w cube diagonalCube N d q : ℝ)
    (hlift : 2 * w ≤ cube + diagonalCube)
    (hcube : cube ≤ 8 * Real.sqrt 2 * N)
    (hdiagonal : diagonalCube ≤ 6 * N + 3 * q + (3 / 4 : ℝ) * d) :
    w ≤ (3 + 4 * Real.sqrt 2) * N + (3 / 2 : ℝ) * q + (3 / 8 : ℝ) * d := by
  nlinarith

#print axioms KLSConstantImprovement.OriginalODECOThirdSandwichScalar.absolute_off_cube_from_pinching
#print axioms KLSConstantImprovement.OriginalODECOThirdSandwichScalar.odeco_half_cube_lift
#print axioms KLSConstantImprovement.OriginalODECOThirdSandwichScalar.original_odeco_third_upper

end KLSConstantImprovement.OriginalODECOThirdSandwichScalar
