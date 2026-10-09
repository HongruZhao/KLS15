import SymmetricCenteredSeed245Data
noncomputable section
namespace KLSBelow25.SymmetricCenteredSeed245
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
theorem hasDerivAt_seedV (t:ℝ) : HasDerivAt seedV (seedVp t) t := by
  have h := ((((((((((hasDerivAt_const t ((25015851/10000000) : ℝ)).add (((hasDerivAt_id' t).pow 1).const_mul ((-18353223/10000000) : ℝ))).add (((hasDerivAt_id' t).pow 2).const_mul ((9111363/10000000) : ℝ))).add (((hasDerivAt_id' t).pow 3).const_mul ((-9350509/10000000) : ℝ))).add (((hasDerivAt_id' t).pow 4).const_mul ((3076451/5000000) : ℝ))).add (((hasDerivAt_id' t).pow 5).const_mul ((-3362359/10000000) : ℝ))).add (((hasDerivAt_id' t).pow 6).const_mul ((-7075723/10000000) : ℝ))).add (((hasDerivAt_id' t).pow 7).const_mul ((11621021/5000000) : ℝ))).add (((hasDerivAt_id' t).pow 8).const_mul ((-7243477/2000000) : ℝ))).add (((hasDerivAt_id' t).pow 9).const_mul ((3673631/1250000) : ℝ))).add (((hasDerivAt_id' t).pow 10).const_mul ((-10683347/10000000) : ℝ))
  convert h using 1
  · ext x; norm_num [seedV]
  · norm_num [seedVp]; ring
theorem hasDerivAt_seedVp (t:ℝ) : HasDerivAt seedVp (seedVpp t) t := by
  have h := (((((((((hasDerivAt_const t ((-18353223/10000000) : ℝ)).add (((hasDerivAt_id' t).pow 1).const_mul ((9111363/5000000) : ℝ))).add (((hasDerivAt_id' t).pow 2).const_mul ((-28051527/10000000) : ℝ))).add (((hasDerivAt_id' t).pow 3).const_mul ((3076451/1250000) : ℝ))).add (((hasDerivAt_id' t).pow 4).const_mul ((-3362359/2000000) : ℝ))).add (((hasDerivAt_id' t).pow 5).const_mul ((-21227169/5000000) : ℝ))).add (((hasDerivAt_id' t).pow 6).const_mul ((81347147/5000000) : ℝ))).add (((hasDerivAt_id' t).pow 7).const_mul ((-7243477/250000) : ℝ))).add (((hasDerivAt_id' t).pow 8).const_mul ((33062679/1250000) : ℝ))).add (((hasDerivAt_id' t).pow 9).const_mul ((-10683347/1000000) : ℝ))
  convert h using 1
  · ext x; norm_num [seedVp]
  · norm_num [seedVpp]; ring
theorem continuous_seedV : Continuous seedV := continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_seedV t).continuousAt)
theorem continuous_seedVp : Continuous seedVp := continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_seedVp t).continuousAt)
end KLSBelow25.SymmetricCenteredSeed245
#print axioms KLSBelow25.SymmetricCenteredSeed245.hasDerivAt_seedV
#print axioms KLSBelow25.SymmetricCenteredSeed245.hasDerivAt_seedVp
