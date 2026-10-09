import VariableAlpha24Numerics
import VariableAlpha24IntegerCertificates

/-! Exact signs for the actual inverse-barrier polynomials, obtained from
denominator-cleared integer Bernstein identities checked by Lean. -/
noncomputable section
open Set
namespace VariableAlpha24
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def seedVp (t : ℝ) : ℝ := (-99963/50000)*t^0 + (91727/50000)*t^1 + (-135333/50000)*t^2 + (2793/2500)*t^3 + (2583/800)*t^4 + (-639747/50000)*t^5 + (336287/20000)*t^6 + (-116239/12500)*t^7

def seedVpp (t : ℝ) : ℝ := (91727/50000)*t^0 + (-135333/25000)*t^1 + (8379/2500)*t^2 + (2583/200)*t^3 + (-639747/10000)*t^4 + (1008861/10000)*t^5 + (-813673/12500)*t^6

def seedSlope (t : ℝ) : ℝ := seedV t+t*seedVp t

def seedConcavity (t : ℝ) : ℝ := -(3*seedV t*seedVp t+
  t*((seedVp t)^2+seedV t*seedVpp t))

def seedP (t : ℝ) : ℝ := -17*(1-t^2)*seedV t*seedSlope t+
  (9/2)*B*(1-t^2)+16*t^2*(seedV t)^2

def seedNegQ (t : ℝ) : ℝ := seedR*seedV t*seedSlope t+
  ((9/2)*B*seedC+24/seedC)*t*seedV t

def seedDet (t : ℝ) : ℝ := (seedP t)^2-(1-t^2)*(seedNegQ t)^2

def seedAlphaPoly (t : ℝ) : ℝ := 1-t^2-seedC^2*t^2*(seedV t)^2

theorem seedV_integer_certificate_eq (t : ℝ) :
    seedV t = IntegerBernsteinCertificates.seedV t := by
  norm_num [seedV, seedVp, seedVpp, seedSlope, seedConcavity, seedP, seedNegQ, seedDet, seedAlphaPoly, B, K, seedC, seedR, IntegerBernsteinCertificates.seedV]
  ring

theorem seedV_positive {t : ℝ} (ht : t ∈ Icc 0 seedT) :
    0 < seedV t := by
  rw [seedV_integer_certificate_eq]
  exact IntegerBernsteinCertificates.seedV_pos (by simpa [seedT] using ht)

theorem seedSlope_integer_certificate_eq (t : ℝ) :
    seedSlope t = IntegerBernsteinCertificates.seedSlope t := by
  norm_num [seedV, seedVp, seedVpp, seedSlope, seedConcavity, seedP, seedNegQ, seedDet, seedAlphaPoly, B, K, seedC, seedR, IntegerBernsteinCertificates.seedSlope]
  ring

theorem seedSlope_positive {t : ℝ} (ht : t ∈ Icc 0 seedT) :
    0 < seedSlope t := by
  rw [seedSlope_integer_certificate_eq]
  exact IntegerBernsteinCertificates.seedSlope_pos (by simpa [seedT] using ht)

theorem seedConcavity_integer_certificate_eq (t : ℝ) :
    seedConcavity t = IntegerBernsteinCertificates.seedConcavity t := by
  norm_num [seedV, seedVp, seedVpp, seedSlope, seedConcavity, seedP, seedNegQ, seedDet, seedAlphaPoly, B, K, seedC, seedR, IntegerBernsteinCertificates.seedConcavity]
  ring

theorem seedConcavity_positive {t : ℝ} (ht : t ∈ Icc 0 seedT) :
    0 < seedConcavity t := by
  rw [seedConcavity_integer_certificate_eq]
  exact IntegerBernsteinCertificates.seedConcavity_pos (by simpa [seedT] using ht)

theorem seedP_integer_certificate_eq (t : ℝ) :
    seedP t = IntegerBernsteinCertificates.seedP t := by
  norm_num [seedV, seedVp, seedVpp, seedSlope, seedConcavity, seedP, seedNegQ, seedDet, seedAlphaPoly, B, K, seedC, seedR, IntegerBernsteinCertificates.seedP]
  ring

theorem seedP_positive {t : ℝ} (ht : t ∈ Icc 0 seedT) :
    0 < seedP t := by
  rw [seedP_integer_certificate_eq]
  exact IntegerBernsteinCertificates.seedP_pos (by simpa [seedT] using ht)

theorem seedNegQ_integer_certificate_eq (t : ℝ) :
    seedNegQ t = IntegerBernsteinCertificates.seedNegQ t := by
  norm_num [seedV, seedVp, seedVpp, seedSlope, seedConcavity, seedP, seedNegQ, seedDet, seedAlphaPoly, B, K, seedC, seedR, IntegerBernsteinCertificates.seedNegQ]
  ring

theorem seedNegQ_positive {t : ℝ} (ht : t ∈ Icc 0 seedT) :
    0 < seedNegQ t := by
  rw [seedNegQ_integer_certificate_eq]
  exact IntegerBernsteinCertificates.seedNegQ_pos (by simpa [seedT] using ht)

theorem seedDet_integer_certificate_eq (t : ℝ) :
    seedDet t = IntegerBernsteinCertificates.seedDet t := by
  norm_num [seedV, seedVp, seedVpp, seedSlope, seedConcavity, seedP, seedNegQ, seedDet, seedAlphaPoly, B, K, seedC, seedR, IntegerBernsteinCertificates.seedDet]
  ring

theorem seedDet_positive {t : ℝ} (ht : t ∈ Icc 0 seedT) :
    0 < seedDet t := by
  rw [seedDet_integer_certificate_eq]
  exact IntegerBernsteinCertificates.seedDet_pos (by simpa [seedT] using ht)

theorem seedAlphaPoly_integer_certificate_eq (t : ℝ) :
    seedAlphaPoly t = IntegerBernsteinCertificates.seedAlphaPoly t := by
  norm_num [seedV, seedVp, seedVpp, seedSlope, seedConcavity, seedP, seedNegQ, seedDet, seedAlphaPoly, B, K, seedC, seedR, IntegerBernsteinCertificates.seedAlphaPoly]
  ring

theorem seedAlphaPoly_positive {t : ℝ} (ht : t ∈ Icc 0 seedT) :
    0 < seedAlphaPoly t := by
  rw [seedAlphaPoly_integer_certificate_eq]
  exact IntegerBernsteinCertificates.seedAlphaPoly_pos (by simpa [seedT] using ht)

def commonVp (t : ℝ) : ℝ := (-8668/3125)*t^0 + (15879/6250)*t^1 + (-4971/1250)*t^2 + (2777/625)*t^3 + (-29807/4000)*t^4 + (16917/2000)*t^5 + (-566461/100000)*t^6

def commonVpp (t : ℝ) : ℝ := (15879/6250)*t^0 + (-4971/625)*t^1 + (8331/625)*t^2 + (-29807/1000)*t^3 + (16917/400)*t^4 + (-1699383/50000)*t^5

def commonSlope (t : ℝ) : ℝ := commonV t+t*commonVp t

def commonConcavity (t : ℝ) : ℝ := -(3*commonV t*commonVp t+
  t*((commonVp t)^2+commonV t*commonVpp t))

def commonP (t : ℝ) : ℝ := -2*(1-t^2)*commonV t*commonSlope t+
  K*(1-t^2)+2*t^2*(commonV t)^2-commonR*t*commonV t

def commonNegQ (t : ℝ) : ℝ := commonR*commonV t*commonSlope t+
  (commonC*K+4/commonC)*t*commonV t

def commonDet (t : ℝ) : ℝ := (commonP t)^2-(1-t^2)*(commonNegQ t)^2

def commonAlphaPoly (t : ℝ) : ℝ := 1-t^2-commonC^2*t^2*(commonV t)^2

theorem commonV_integer_certificate_eq (t : ℝ) :
    commonV t = IntegerBernsteinCertificates.commonV t := by
  norm_num [commonV, commonVp, commonVpp, commonSlope, commonConcavity, commonP, commonNegQ, commonDet, commonAlphaPoly, B, K, commonC, commonR, IntegerBernsteinCertificates.commonV]
  ring

theorem commonV_positive {t : ℝ} (ht : t ∈ Icc 0 commonT) :
    0 < commonV t := by
  rw [commonV_integer_certificate_eq]
  exact IntegerBernsteinCertificates.commonV_pos (by simpa [commonT] using ht)

theorem commonSlope_integer_certificate_eq (t : ℝ) :
    commonSlope t = IntegerBernsteinCertificates.commonSlope t := by
  norm_num [commonV, commonVp, commonVpp, commonSlope, commonConcavity, commonP, commonNegQ, commonDet, commonAlphaPoly, B, K, commonC, commonR, IntegerBernsteinCertificates.commonSlope]
  ring

theorem commonSlope_positive {t : ℝ} (ht : t ∈ Icc 0 commonT) :
    0 < commonSlope t := by
  rw [commonSlope_integer_certificate_eq]
  exact IntegerBernsteinCertificates.commonSlope_pos (by simpa [commonT] using ht)

theorem commonConcavity_integer_certificate_eq (t : ℝ) :
    commonConcavity t = IntegerBernsteinCertificates.commonConcavity t := by
  norm_num [commonV, commonVp, commonVpp, commonSlope, commonConcavity, commonP, commonNegQ, commonDet, commonAlphaPoly, B, K, commonC, commonR, IntegerBernsteinCertificates.commonConcavity]
  ring

theorem commonConcavity_positive {t : ℝ} (ht : t ∈ Icc 0 commonT) :
    0 < commonConcavity t := by
  rw [commonConcavity_integer_certificate_eq]
  exact IntegerBernsteinCertificates.commonConcavity_pos (by simpa [commonT] using ht)

theorem commonP_integer_certificate_eq (t : ℝ) :
    commonP t = IntegerBernsteinCertificates.commonP t := by
  norm_num [commonV, commonVp, commonVpp, commonSlope, commonConcavity, commonP, commonNegQ, commonDet, commonAlphaPoly, B, K, commonC, commonR, IntegerBernsteinCertificates.commonP]
  ring

theorem commonP_positive {t : ℝ} (ht : t ∈ Icc 0 commonT) :
    0 < commonP t := by
  rw [commonP_integer_certificate_eq]
  exact IntegerBernsteinCertificates.commonP_pos (by simpa [commonT] using ht)

theorem commonNegQ_integer_certificate_eq (t : ℝ) :
    commonNegQ t = IntegerBernsteinCertificates.commonNegQ t := by
  norm_num [commonV, commonVp, commonVpp, commonSlope, commonConcavity, commonP, commonNegQ, commonDet, commonAlphaPoly, B, K, commonC, commonR, IntegerBernsteinCertificates.commonNegQ]
  ring

theorem commonNegQ_positive {t : ℝ} (ht : t ∈ Icc 0 commonT) :
    0 < commonNegQ t := by
  rw [commonNegQ_integer_certificate_eq]
  exact IntegerBernsteinCertificates.commonNegQ_pos (by simpa [commonT] using ht)

theorem commonDet_integer_certificate_eq (t : ℝ) :
    commonDet t = IntegerBernsteinCertificates.commonDet t := by
  norm_num [commonV, commonVp, commonVpp, commonSlope, commonConcavity, commonP, commonNegQ, commonDet, commonAlphaPoly, B, K, commonC, commonR, IntegerBernsteinCertificates.commonDet]
  ring

theorem commonDet_positive {t : ℝ} (ht : t ∈ Icc 0 commonT) :
    0 < commonDet t := by
  rw [commonDet_integer_certificate_eq]
  exact IntegerBernsteinCertificates.commonDet_pos (by simpa [commonT] using ht)

theorem commonAlphaPoly_integer_certificate_eq (t : ℝ) :
    commonAlphaPoly t = IntegerBernsteinCertificates.commonAlphaPoly t := by
  norm_num [commonV, commonVp, commonVpp, commonSlope, commonConcavity, commonP, commonNegQ, commonDet, commonAlphaPoly, B, K, commonC, commonR, IntegerBernsteinCertificates.commonAlphaPoly]
  ring

theorem commonAlphaPoly_positive {t : ℝ} (ht : t ∈ Icc 0 commonT) :
    0 < commonAlphaPoly t := by
  rw [commonAlphaPoly_integer_certificate_eq]
  exact IntegerBernsteinCertificates.commonAlphaPoly_pos (by simpa [commonT] using ht)

end VariableAlpha24

#print axioms VariableAlpha24.seedV_positive

#print axioms VariableAlpha24.seedSlope_positive

#print axioms VariableAlpha24.seedConcavity_positive

#print axioms VariableAlpha24.seedP_positive

#print axioms VariableAlpha24.seedNegQ_positive

#print axioms VariableAlpha24.seedDet_positive

#print axioms VariableAlpha24.seedAlphaPoly_positive

#print axioms VariableAlpha24.commonV_positive

#print axioms VariableAlpha24.commonSlope_positive

#print axioms VariableAlpha24.commonConcavity_positive

#print axioms VariableAlpha24.commonP_positive

#print axioms VariableAlpha24.commonNegQ_positive

#print axioms VariableAlpha24.commonDet_positive

#print axioms VariableAlpha24.commonAlphaPoly_positive
