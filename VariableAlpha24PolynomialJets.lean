import VariableAlpha24Numerics
noncomputable section
namespace VariableAlpha24
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
def seedVFirst (t : ℝ) : ℝ := (-99963/50000)*t^0 + (91727/50000)*t^1 + (-135333/50000)*t^2 + (2793/2500)*t^3 + (2583/800)*t^4 + (-639747/50000)*t^5 + (336287/20000)*t^6 + (-116239/12500)*t^7
def seedVSecond (t : ℝ) : ℝ := (91727/50000)*t^0 + (-135333/25000)*t^1 + (8379/2500)*t^2 + (2583/200)*t^3 + (-639747/10000)*t^4 + (1008861/10000)*t^5 + (-813673/12500)*t^6
theorem hasDerivAt_seedV (t : ℝ) : HasDerivAt seedV (seedVFirst t) t := by
  have h := (((((((((hasDerivAt_const t ((8228/3125) : ℝ))).add (((hasDerivAt_id' t).pow 1).const_mul ((-99963/50000) : ℝ))).add (((hasDerivAt_id' t).pow 2).const_mul ((91727/100000) : ℝ))).add (((hasDerivAt_id' t).pow 3).const_mul ((-45111/50000) : ℝ))).add (((hasDerivAt_id' t).pow 4).const_mul ((2793/10000) : ℝ))).add (((hasDerivAt_id' t).pow 5).const_mul ((2583/4000) : ℝ))).add (((hasDerivAt_id' t).pow 6).const_mul ((-213249/100000) : ℝ))).add (((hasDerivAt_id' t).pow 7).const_mul ((48041/20000) : ℝ))).add (((hasDerivAt_id' t).pow 8).const_mul ((-116239/100000) : ℝ))
  convert h using 1
  · ext x; norm_num [seedV] <;> ring
  · norm_num [seedVFirst] <;> ring
theorem hasDerivAt_seedVFirst (t : ℝ) : HasDerivAt seedVFirst (seedVSecond t) t := by
  have h := ((((((((hasDerivAt_const t ((-99963/50000) : ℝ))).add (((hasDerivAt_id' t).pow 1).const_mul ((91727/50000) : ℝ))).add (((hasDerivAt_id' t).pow 2).const_mul ((-135333/50000) : ℝ))).add (((hasDerivAt_id' t).pow 3).const_mul ((2793/2500) : ℝ))).add (((hasDerivAt_id' t).pow 4).const_mul ((2583/800) : ℝ))).add (((hasDerivAt_id' t).pow 5).const_mul ((-639747/50000) : ℝ))).add (((hasDerivAt_id' t).pow 6).const_mul ((336287/20000) : ℝ))).add (((hasDerivAt_id' t).pow 7).const_mul ((-116239/12500) : ℝ))
  convert h using 1
  · ext x; norm_num [seedVFirst] <;> ring
  · norm_num [seedVSecond] <;> ring
theorem continuous_seedV : Continuous seedV :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_seedV t).continuousAt)
theorem continuous_seedVFirst : Continuous seedVFirst :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_seedVFirst t).continuousAt)
def commonVFirst (t : ℝ) : ℝ := (-8668/3125)*t^0 + (15879/6250)*t^1 + (-4971/1250)*t^2 + (2777/625)*t^3 + (-29807/4000)*t^4 + (16917/2000)*t^5 + (-566461/100000)*t^6
def commonVSecond (t : ℝ) : ℝ := (15879/6250)*t^0 + (-4971/625)*t^1 + (8331/625)*t^2 + (-29807/1000)*t^3 + (16917/400)*t^4 + (-1699383/50000)*t^5
theorem hasDerivAt_commonV (t : ℝ) : HasDerivAt commonV (commonVFirst t) t := by
  have h := ((((((((hasDerivAt_const t ((307869/100000) : ℝ))).add (((hasDerivAt_id' t).pow 1).const_mul ((-8668/3125) : ℝ))).add (((hasDerivAt_id' t).pow 2).const_mul ((15879/12500) : ℝ))).add (((hasDerivAt_id' t).pow 3).const_mul ((-1657/1250) : ℝ))).add (((hasDerivAt_id' t).pow 4).const_mul ((2777/2500) : ℝ))).add (((hasDerivAt_id' t).pow 5).const_mul ((-29807/20000) : ℝ))).add (((hasDerivAt_id' t).pow 6).const_mul ((5639/4000) : ℝ))).add (((hasDerivAt_id' t).pow 7).const_mul ((-80923/100000) : ℝ))
  convert h using 1
  · ext x; norm_num [commonV] <;> ring
  · norm_num [commonVFirst] <;> ring
theorem hasDerivAt_commonVFirst (t : ℝ) : HasDerivAt commonVFirst (commonVSecond t) t := by
  have h := (((((((hasDerivAt_const t ((-8668/3125) : ℝ))).add (((hasDerivAt_id' t).pow 1).const_mul ((15879/6250) : ℝ))).add (((hasDerivAt_id' t).pow 2).const_mul ((-4971/1250) : ℝ))).add (((hasDerivAt_id' t).pow 3).const_mul ((2777/625) : ℝ))).add (((hasDerivAt_id' t).pow 4).const_mul ((-29807/4000) : ℝ))).add (((hasDerivAt_id' t).pow 5).const_mul ((16917/2000) : ℝ))).add (((hasDerivAt_id' t).pow 6).const_mul ((-566461/100000) : ℝ))
  convert h using 1
  · ext x; norm_num [commonVFirst] <;> ring
  · norm_num [commonVSecond] <;> ring
theorem continuous_commonV : Continuous commonV :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_commonV t).continuousAt)
theorem continuous_commonVFirst : Continuous commonVFirst :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_commonVFirst t).continuousAt)
end VariableAlpha24
#print axioms VariableAlpha24.hasDerivAt_seedV
#print axioms VariableAlpha24.hasDerivAt_commonVFirst
