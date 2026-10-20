import KLSConstantImprovement.OptimizedJointCreationSeed23849Data
noncomputable section
namespace KLSBelow25.OptimizedJointCreationSeed23849
set_option maxHeartbeats 2000000
theorem hasDerivAt_seedV (t:ℝ) : HasDerivAt seedV (seedVp t) t := by
  have h := ((((((((((((((((hasDerivAt_const t ((2589809074537/1000000000000):ℝ)).add (((hasDerivAt_id' t).pow 1).const_mul ((-2158656989933/1000000000000):ℝ))).add (((hasDerivAt_id' t).pow 2).const_mul ((119426986437/100000000000):ℝ))).add (((hasDerivAt_id' t).pow 3).const_mul ((10767353721117/1000000000000):ℝ))).add (((hasDerivAt_id' t).pow 4).const_mul ((-157332941479279/500000000000):ℝ))).add (((hasDerivAt_id' t).pow 5).const_mul ((298543698452853/62500000000):ℝ))).add (((hasDerivAt_id' t).pow 6).const_mul ((-2926017527404081/62500000000):ℝ))).add (((hasDerivAt_id' t).pow 7).const_mul ((2449149823073599/7812500000):ℝ))).add (((hasDerivAt_id' t).pow 8).const_mul ((-5794413505331619/3906250000):ℝ))).add (((hasDerivAt_id' t).pow 9).const_mul ((494368948725881/97656250):ℝ))).add (((hasDerivAt_id' t).pow 10).const_mul ((-3072686119798052/244140625):ℝ))).add (((hasDerivAt_id' t).pow 11).const_mul ((1113146339590548/48828125):ℝ))).add (((hasDerivAt_id' t).pow 12).const_mul ((-7263727366386527/244140625):ℝ))).add (((hasDerivAt_id' t).pow 13).const_mul ((6650473415158707/244140625):ℝ))).add (((hasDerivAt_id' t).pow 14).const_mul ((-810553288481022/48828125):ℝ))).add (((hasDerivAt_id' t).pow 15).const_mul ((5904291238395287/976562500):ℝ))).add (((hasDerivAt_id' t).pow 16).const_mul ((-388938147088417/390625000):ℝ))
  convert h using 1
  · ext x; norm_num [seedV]
  · norm_num [seedVp]; ring
theorem hasDerivAt_seedVp (t:ℝ) : HasDerivAt seedVp (seedVpp t) t := by
  have h := (((((((((((((((hasDerivAt_const t ((-2158656989933/1000000000000):ℝ)).add (((hasDerivAt_id' t).pow 1).const_mul ((119426986437/50000000000):ℝ))).add (((hasDerivAt_id' t).pow 2).const_mul ((32302061163351/1000000000000):ℝ))).add (((hasDerivAt_id' t).pow 3).const_mul ((-157332941479279/125000000000):ℝ))).add (((hasDerivAt_id' t).pow 4).const_mul ((298543698452853/12500000000):ℝ))).add (((hasDerivAt_id' t).pow 5).const_mul ((-8778052582212243/31250000000):ℝ))).add (((hasDerivAt_id' t).pow 6).const_mul ((17144048761515193/7812500000):ℝ))).add (((hasDerivAt_id' t).pow 7).const_mul ((-5794413505331619/488281250):ℝ))).add (((hasDerivAt_id' t).pow 8).const_mul ((4449320538532929/97656250):ℝ))).add (((hasDerivAt_id' t).pow 9).const_mul ((-6145372239596104/48828125):ℝ))).add (((hasDerivAt_id' t).pow 10).const_mul ((12244609735496028/48828125):ℝ))).add (((hasDerivAt_id' t).pow 11).const_mul ((-87164728396638324/244140625):ℝ))).add (((hasDerivAt_id' t).pow 12).const_mul ((86456154397063191/244140625):ℝ))).add (((hasDerivAt_id' t).pow 13).const_mul ((-11347746038734308/48828125):ℝ))).add (((hasDerivAt_id' t).pow 14).const_mul ((17712873715185861/195312500):ℝ))).add (((hasDerivAt_id' t).pow 15).const_mul ((-777876294176834/48828125):ℝ))
  convert h using 1
  · ext x; norm_num [seedVp]
  · norm_num [seedVpp]; ring
theorem continuous_seedV : Continuous seedV := continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_seedV t).continuousAt)
theorem continuous_seedVp : Continuous seedVp := continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_seedVp t).continuousAt)
end KLSBelow25.OptimizedJointCreationSeed23849
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.hasDerivAt_seedV
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.hasDerivAt_seedVp
