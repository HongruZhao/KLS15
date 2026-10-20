import CreationSeed239Data
noncomputable section
namespace KLSBelow25.CreationSeed239
set_option maxHeartbeats 2000000
theorem hasDerivAt_seedV (t:ℝ) : HasDerivAt seedV (seedVp t) t := by
  have h := (((((((((((hasDerivAt_const t ((647961997539/250000000000):ℝ)).add (((hasDerivAt_id' t).pow 1).const_mul ((-17451541841/8000000000):ℝ))).add (((hasDerivAt_id' t).pow 2).const_mul ((750151057993/500000000000):ℝ))).add (((hasDerivAt_id' t).pow 3).const_mul ((-1721077631831/1000000000000):ℝ))).add (((hasDerivAt_id' t).pow 4).const_mul ((793956760467/500000000000):ℝ))).add (((hasDerivAt_id' t).pow 5).const_mul ((-167474327593/125000000000):ℝ))).add (((hasDerivAt_id' t).pow 6).const_mul ((-20102629939/200000000000):ℝ))).add (((hasDerivAt_id' t).pow 7).const_mul ((1312514357219/500000000000):ℝ))).add (((hasDerivAt_id' t).pow 8).const_mul ((-294929171183/62500000000):ℝ))).add (((hasDerivAt_id' t).pow 9).const_mul ((3939423990321/1000000000000):ℝ))).add (((hasDerivAt_id' t).pow 10).const_mul ((-1409372403097/1000000000000):ℝ)))
  convert h using 1
  · ext x; norm_num [seedV]
  · norm_num [seedVp]; ring
theorem hasDerivAt_seedVp (t:ℝ) : HasDerivAt seedVp (seedVpp t) t := by
  have h := ((((((((((hasDerivAt_const t ((-17451541841/8000000000):ℝ)).add (((hasDerivAt_id' t).pow 1).const_mul ((750151057993/250000000000):ℝ))).add (((hasDerivAt_id' t).pow 2).const_mul ((-5163232895493/1000000000000):ℝ))).add (((hasDerivAt_id' t).pow 3).const_mul ((793956760467/125000000000):ℝ))).add (((hasDerivAt_id' t).pow 4).const_mul ((-167474327593/25000000000):ℝ))).add (((hasDerivAt_id' t).pow 5).const_mul ((-60307889817/100000000000):ℝ))).add (((hasDerivAt_id' t).pow 6).const_mul ((9187600500533/500000000000):ℝ))).add (((hasDerivAt_id' t).pow 7).const_mul ((-294929171183/7812500000):ℝ))).add (((hasDerivAt_id' t).pow 8).const_mul ((35454815912889/1000000000000):ℝ))).add (((hasDerivAt_id' t).pow 9).const_mul ((-1409372403097/100000000000):ℝ)))
  convert h using 1
  · ext x; norm_num [seedVp]
  · norm_num [seedVpp]; ring
theorem continuous_seedV : Continuous seedV := continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_seedV t).continuousAt)
theorem continuous_seedVp : Continuous seedVp := continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_seedVp t).continuousAt)
end KLSBelow25.CreationSeed239
