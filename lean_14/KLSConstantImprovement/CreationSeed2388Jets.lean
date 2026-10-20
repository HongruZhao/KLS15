import KLSConstantImprovement.CreationSeed2388Data
noncomputable section
namespace KLSBelow25.CreationSeed2388
set_option maxHeartbeats 2000000
theorem hasDerivAt_seedV (t:ℝ) : HasDerivAt seedV (seedVp t) t := by
  have h := ((((((((((hasDerivAt_const t ((64787814099/25000000000):ℝ)).add (((hasDerivAt_id' t).pow 1).const_mul ((-436401499041/200000000000):ℝ))).add (((hasDerivAt_id' t).pow 2).const_mul ((187693406769/125000000000):ℝ))).add (((hasDerivAt_id' t).pow 3).const_mul ((-431255989321/250000000000):ℝ))).add (((hasDerivAt_id' t).pow 4).const_mul ((321303086749/200000000000):ℝ))).add (((hasDerivAt_id' t).pow 5).const_mul ((-703274166553/500000000000):ℝ))).add (((hasDerivAt_id' t).pow 6).const_mul ((321584431/6250000000):ℝ))).add (((hasDerivAt_id' t).pow 7).const_mul ((30208897091/12500000000):ℝ))).add (((hasDerivAt_id' t).pow 8).const_mul ((-569950394813/125000000000):ℝ))).add (((hasDerivAt_id' t).pow 9).const_mul ((3883925636809/1000000000000):ℝ))).add (((hasDerivAt_id' t).pow 10).const_mul ((-1405770740843/1000000000000):ℝ))
  convert h using 1
  · ext x; norm_num [seedV]
  · norm_num [seedVp]; ring
theorem hasDerivAt_seedVp (t:ℝ) : HasDerivAt seedVp (seedVpp t) t := by
  have h := (((((((((hasDerivAt_const t ((-436401499041/200000000000):ℝ)).add (((hasDerivAt_id' t).pow 1).const_mul ((187693406769/62500000000):ℝ))).add (((hasDerivAt_id' t).pow 2).const_mul ((-1293767967963/250000000000):ℝ))).add (((hasDerivAt_id' t).pow 3).const_mul ((321303086749/50000000000):ℝ))).add (((hasDerivAt_id' t).pow 4).const_mul ((-703274166553/100000000000):ℝ))).add (((hasDerivAt_id' t).pow 5).const_mul ((964753293/3125000000):ℝ))).add (((hasDerivAt_id' t).pow 6).const_mul ((211462279637/12500000000):ℝ))).add (((hasDerivAt_id' t).pow 7).const_mul ((-569950394813/15625000000):ℝ))).add (((hasDerivAt_id' t).pow 8).const_mul ((34955330731281/1000000000000):ℝ))).add (((hasDerivAt_id' t).pow 9).const_mul ((-1405770740843/100000000000):ℝ))
  convert h using 1
  · ext x; norm_num [seedVp]
  · norm_num [seedVpp]; ring
theorem continuous_seedV : Continuous seedV := continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_seedV t).continuousAt)
theorem continuous_seedVp : Continuous seedVp := continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_seedVp t).continuousAt)
end KLSBelow25.CreationSeed2388
#print axioms KLSBelow25.CreationSeed2388.hasDerivAt_seedV
#print axioms KLSBelow25.CreationSeed2388.hasDerivAt_seedVp
