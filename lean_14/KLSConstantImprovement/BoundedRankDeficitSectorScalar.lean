import KLSConstantImprovement.DeficitCurvatureScalar

/-! Rational transfer for the bounded-rank original-law stability sector.
The bounded-rank variance/signed-annihilation conclusion and the same-law
projection/perturbation estimates remain explicit inputs. No dimension-free
threshold, original-law compactness theorem, or new CP endpoint is asserted. -/
noncomputable section
namespace KLSConstantImprovement.BoundedRankDeficitSectorScalar

theorem deficit_transfer {N H dT dU eta : ℝ}
    (hdT : dT ≤ eta*N/8) (hH : H ≤ eta*N/64)
    (htransfer : dU ≤ 2*dT+16*H) :
    dU ≤ eta*N/2 := by
  nlinarith

theorem projected_norm_lower {N H U : ℝ}
    (hH : H ≤ N/1024) (hU : U = N-H) :
    (1023/1024:ℝ)*N ≤ U := by
  linarith

theorem projected_deficit_below_threshold {N H U dT dU eta : ℝ}
    (hN : 0 < N) (heta : 0 < eta)
    (hdT : dT ≤ eta*N/8) (hHeta : H ≤ eta*N/64)
    (hHN : H ≤ N/1024) (hU : U = N-H)
    (htransfer : dU ≤ 2*dT+16*H) :
    dU < eta*U := by
  have hd := deficit_transfer hdT hHeta htransfer
  have hnorm := projected_norm_lower hHN hU
  have hUhalf : N/2 < U := by linarith
  have hmul := mul_lt_mul_of_pos_left hUhalf heta
  nlinarith

theorem variance_transfer {N H U V VU : ℝ}
    (hH0 : 0 ≤ H) (hHN : H ≤ N/1024) (hU : U = N-H)
    (hVU : VU < 217*U)
    (hV : V ≤ (17/16:ℝ)*VU+17*900*H) :
    V < (62849/256:ℝ)*N := by
  have hVU' : VU < 217*N := by nlinarith
  nlinarith

theorem signed_annihilation_transfer {N H U S SU : ℝ}
    (hHN : H ≤ N/1024) (hU : U = N-H)
    (hSU : 3*U < SU) (hS : SU-S ≤ N/2) :
    (2557/1024:ℝ)*N < S := by
  have hnorm := projected_norm_lower hHN hU
  nlinarith

theorem additive_sector {N V S : ℝ}
    (hV : V < (62849/256:ℝ)*N)
    (hS : (2557/1024:ℝ)*N < S) :
    (31677/1024:ℝ)*N < 224*N+21*S-V := by
  linarith

theorem paid_projected_sector {N H U dT dU eta V VU S SU : ℝ}
    (hN : 0 < N) (heta : 0 < eta) (hH0 : 0 ≤ H)
    (hdT : dT ≤ eta*N/8) (hHeta : H ≤ eta*N/64)
    (hHN : H ≤ N/1024) (hU : U = N-H)
    (hdeficit : dU ≤ 2*dT+16*H)
    (hboundedRank : dU < eta*U → VU < 217*U ∧ 3*U < SU)
    (hvariance : V ≤ (17/16:ℝ)*VU+17*900*H)
    (hperturbation : SU-S ≤ N/2) :
    V < (62849/256:ℝ)*N ∧ (2557/1024:ℝ)*N < S ∧
      (31677/1024:ℝ)*N < 224*N+21*S-V ∧ V < 308*N := by
  have hd := projected_deficit_below_threshold hN heta hdT hHeta hHN hU hdeficit
  obtain ⟨hVU,hSU⟩ := hboundedRank hd
  have hV := variance_transfer hH0 hHN hU hVU hvariance
  have hS := signed_annihilation_transfer hHN hU hSU hperturbation
  refine ⟨hV,hS,additive_sector hV hS,?_⟩
  nlinarith

end KLSConstantImprovement.BoundedRankDeficitSectorScalar
#print axioms KLSConstantImprovement.BoundedRankDeficitSectorScalar.deficit_transfer
#print axioms KLSConstantImprovement.BoundedRankDeficitSectorScalar.projected_norm_lower
#print axioms KLSConstantImprovement.BoundedRankDeficitSectorScalar.projected_deficit_below_threshold
#print axioms KLSConstantImprovement.BoundedRankDeficitSectorScalar.variance_transfer
#print axioms KLSConstantImprovement.BoundedRankDeficitSectorScalar.signed_annihilation_transfer
#print axioms KLSConstantImprovement.BoundedRankDeficitSectorScalar.additive_sector
#print axioms KLSConstantImprovement.BoundedRankDeficitSectorScalar.paid_projected_sector
