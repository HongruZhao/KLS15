import QuarticCreation200000Data
noncomputable section
namespace KLSBelow25.QuarticCreation200000
set_option maxHeartbeats 2000000
theorem hasDerivAt_seedV (t:ℝ) : HasDerivAt seedV (seedVp t) t := by
  have h := (((((((((((hasDerivAt_const t ((1367111307/500000000):ℝ)).add (((hasDerivAt_id' t).pow 1).const_mul ((-1170727613/500000000):ℝ))).add (((hasDerivAt_id' t).pow 2).const_mul ((198257713/100000000):ℝ))).add (((hasDerivAt_id' t).pow 3).const_mul ((-9568960343/1000000000):ℝ))).add (((hasDerivAt_id' t).pow 4).const_mul ((33804081167/500000000):ℝ))).add (((hasDerivAt_id' t).pow 5).const_mul ((-82925044299/250000000):ℝ))).add (((hasDerivAt_id' t).pow 6).const_mul ((32087759257/31250000):ℝ))).add (((hasDerivAt_id' t).pow 7).const_mul ((-7803149229/3906250):ℝ))).add (((hasDerivAt_id' t).pow 8).const_mul ((2369459715771/1000000000):ℝ))).add (((hasDerivAt_id' t).pow 9).const_mul ((-781907691767/500000000):ℝ))).add (((hasDerivAt_id' t).pow 10).const_mul ((1097068033/2500000):ℝ)))
  convert h using 1
  · ext x; norm_num [seedV]
  · norm_num [seedVp]; ring
theorem hasDerivAt_seedVp (t:ℝ) : HasDerivAt seedVp (seedVpp t) t := by
  have h := ((((((((((hasDerivAt_const t ((-1170727613/500000000):ℝ)).add (((hasDerivAt_id' t).pow 1).const_mul ((198257713/50000000):ℝ))).add (((hasDerivAt_id' t).pow 2).const_mul ((-28706881029/1000000000):ℝ))).add (((hasDerivAt_id' t).pow 3).const_mul ((33804081167/125000000):ℝ))).add (((hasDerivAt_id' t).pow 4).const_mul ((-82925044299/50000000):ℝ))).add (((hasDerivAt_id' t).pow 5).const_mul ((96263277771/15625000):ℝ))).add (((hasDerivAt_id' t).pow 6).const_mul ((-54622044603/3906250):ℝ))).add (((hasDerivAt_id' t).pow 7).const_mul ((2369459715771/125000000):ℝ))).add (((hasDerivAt_id' t).pow 8).const_mul ((-7037169225903/500000000):ℝ))).add (((hasDerivAt_id' t).pow 9).const_mul ((1097068033/250000):ℝ)))
  convert h using 1
  · ext x; norm_num [seedVp]
  · norm_num [seedVpp]; ring
theorem continuous_seedV : Continuous seedV := continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_seedV t).continuousAt)
theorem continuous_seedVp : Continuous seedVp := continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_seedVp t).continuousAt)
end KLSBelow25.QuarticCreation200000
