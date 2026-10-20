import PairNoiseSquareCompletion
import PairProjectionHilbert

/-! Exact all-rank noise control for a literal unordered-pair Gram family.
The actual-law realization supplies the coordinate Gram and scalar
contraction bounds, rather than a desired generator inequality. -/
noncomputable section
open scoped RealInnerProductSpace
namespace KLSBelow25.PairProjection
variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem pair_projection_noise_low (U : Pair N→H) (W : H) (i : Fin N)
    {Q R S t β E : ℝ} (hN : 4≤N) (hGram : Gram U Q R S)
    (hConstant : ∀ e,inner ℝ W (U e)=t)
    (hβ0 : 0≤β) (hβhi : β≤((N : ℝ)-2)/(N : ℝ))
    (hR : R≤4*E) (hS : S≤(4+8/(3*((N : ℝ)-2)))*E) :
    β*‖W‖^2-(leadingNoiseCoefficient ((N : ℝ)-1)/(1-β)-
      positiveNoiseCoefficient ((N : ℝ)-1))*E≤
      covarianceNoiseForm W (star U i) ((N : ℝ)-1) Q := by
  have hNr : (4 : ℝ)≤N := by exact_mod_cast hN
  have hNp : 0<(N : ℝ) := by linarith
  have hd : 3≤(N : ℝ)-1 := by linarith
  have hβ1 : β<1 := hβhi.trans_lt ((div_lt_one hNp).mpr (by linarith))
  have hδ : 0<1-β := by linarith
  have hδ1 : 1-β≤1 := by linarith
  have hβmul := (le_div_iff₀ hNp).mp hβhi
  have hδlo : 2≤(((N : ℝ)-1)+1)*(1-β) := by nlinarith
  have hV : ‖star U i‖^2=((N : ℝ)-1)*Q+
      ((N : ℝ)-1)*(((N : ℝ)-1)-1)*R := by
    convert star_sq U hGram i using 1; ring
  have hP : ‖projection U‖^2=(2*((N : ℝ)-1)/(((N : ℝ)-1)+1))*
      (Q+2*(((N : ℝ)-1)-1)*R+
        ((((N : ℝ)-1)-1)*(((N : ℝ)-1)-2)/2)*S) := by
    convert projection_sq U hGram (by omega) using 1; unfold row; ring
  have hres : (((N : ℝ)-1)-2)*S≤Q+(((N : ℝ)-1)-3)*R := by
    convert residual_relation U hGram (by omega) using 1 <;> ring
  have hS' : S≤(4+8/(3*(((N : ℝ)-1)-1)))*E := by
    convert hS using 1; ring
  have hh := low_noise_bound_of_projection_data W (star U i) (projection U)
    hd hδ hδ1 hδlo (constant_pairing U W hConstant i) hV hP hres hR hS'
  convert hh using 1; ring

end KLSBelow25.PairProjection
#print axioms KLSBelow25.PairProjection.pair_projection_noise_low
