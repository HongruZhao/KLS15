import CreationSeed24Data
noncomputable section
namespace KLSBelow25.CreationSeed24
set_option maxHeartbeats 2000000
theorem hasDerivAt_seedV (t:ℝ) : HasDerivAt seedV (seedVp t) t := by
  have h := (((((((((((hasDerivAt_const t ((2597264627/1000000000):ℝ)).add (((hasDerivAt_id' t).pow 1).const_mul ((-273250639/125000000):ℝ))).add (((hasDerivAt_id' t).pow 2).const_mul ((93973447/62500000):ℝ))).add (((hasDerivAt_id' t).pow 3).const_mul ((-172700393/100000000):ℝ))).add (((hasDerivAt_id' t).pow 4).const_mul ((32240537/20000000):ℝ))).add (((hasDerivAt_id' t).pow 5).const_mul ((-362803509/250000000):ℝ))).add (((hasDerivAt_id' t).pow 6).const_mul ((124066413/500000000):ℝ))).add (((hasDerivAt_id' t).pow 7).const_mul ((966615801/500000000):ℝ))).add (((hasDerivAt_id' t).pow 8).const_mul ((-1941981253/500000000):ℝ))).add (((hasDerivAt_id' t).pow 9).const_mul ((27041411/8000000):ℝ))).add (((hasDerivAt_id' t).pow 10).const_mul ((-312551231/250000000):ℝ)))
  convert h using 1
  · ext x; norm_num [seedV]
  · norm_num [seedVp]; ring
theorem hasDerivAt_seedVp (t:ℝ) : HasDerivAt seedVp (seedVpp t) t := by
  have h := ((((((((((hasDerivAt_const t ((-273250639/125000000):ℝ)).add (((hasDerivAt_id' t).pow 1).const_mul ((93973447/31250000):ℝ))).add (((hasDerivAt_id' t).pow 2).const_mul ((-518101179/100000000):ℝ))).add (((hasDerivAt_id' t).pow 3).const_mul ((32240537/5000000):ℝ))).add (((hasDerivAt_id' t).pow 4).const_mul ((-362803509/50000000):ℝ))).add (((hasDerivAt_id' t).pow 5).const_mul ((372199239/250000000):ℝ))).add (((hasDerivAt_id' t).pow 6).const_mul ((6766310607/500000000):ℝ))).add (((hasDerivAt_id' t).pow 7).const_mul ((-1941981253/62500000):ℝ))).add (((hasDerivAt_id' t).pow 8).const_mul ((243372699/8000000):ℝ))).add (((hasDerivAt_id' t).pow 9).const_mul ((-312551231/25000000):ℝ)))
  convert h using 1
  · ext x; norm_num [seedVp]
  · norm_num [seedVpp]; ring
theorem continuous_seedV : Continuous seedV := continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_seedV t).continuousAt)
theorem continuous_seedVp : Continuous seedVp := continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_seedVp t).continuousAt)
end KLSBelow25.CreationSeed24
