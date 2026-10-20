import KLSConstantImprovement.OptimizedJointCreationSeed23849IntegerDetCapHorner

/-! The frozen Cap positivity theorem is supplied by the complete ordinary-kernel
Horner certificate.  The original direct-power fallback source and retirement
receipt are preserved separately. -/
noncomputable section
namespace KLSBelow25.OptimizedJointCreationSeed23849

theorem seedDetCap_positive {t : ℝ} (ht : t ∈ Set.Icc seedSwitch seedT) :
    0 < seedDetCap t := rootHornerCap_positive ht

end KLSBelow25.OptimizedJointCreationSeed23849
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seedDetCap_positive
