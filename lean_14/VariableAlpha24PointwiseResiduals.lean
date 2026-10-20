import SquareRootResidualAlgebra
import VariableAlpha24BernsteinData

/-! Literal variable-alpha differential residuals of the certified rational
seed/common branches. Endpoint t=0 is intentionally handled separately. -/
noncomputable section
open Set
namespace VariableAlpha24
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def seedAlphaAt (t : ℝ) : ℝ := 1-seedC*t*seedV t/Real.sqrt (1-t^2)
def commonAlphaAt (t : ℝ) : ℝ := 1-commonC*t*commonV t/Real.sqrt (1-t^2)

 theorem seed_alpha_mem_unit {t : ℝ} (ht : 0<t) (htT : t ≤ seedT) :
    seedAlphaAt t∈Ioo (0:ℝ) 1 := by
  have hi : t∈Icc 0 seedT := ⟨ht.le,htT⟩
  exact alpha_mem_unit_of_polynomial
    (parameterized_z_positive ht.le htT seedT_range.2) seedC_positive ht
    (seedV_positive hi) (seedAlphaPoly_positive hi)

 theorem common_alpha_mem_unit {t : ℝ} (ht : 0<t) (htT : t ≤ commonT) :
    commonAlphaAt t∈Ioo (0:ℝ) 1 := by
  have hi : t∈Icc 0 commonT := ⟨ht.le,htT⟩
  exact alpha_mem_unit_of_polynomial
    (parameterized_z_positive ht.le htT commonT_range.2) commonC_positive ht
    (commonV_positive hi) (commonAlphaPoly_positive hi)

 theorem seed_sqrt_residual_positive {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ seedT) :
    0<seedP t-Real.sqrt (1-t^2)*seedNegQ t := by
  have hi : t∈Icc 0 seedT := ⟨ht,htT⟩
  exact sqrt_residual_positive (parameterized_z_positive ht htT seedT_range.2)
    (seedP_positive hi) (seedNegQ_positive hi) (seedDet_positive hi)

 theorem common_sqrt_residual_positive {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ commonT) :
    0<commonP t-Real.sqrt (1-t^2)*commonNegQ t := by
  have hi : t∈Icc 0 commonT := ⟨ht,htT⟩
  exact sqrt_residual_positive (parameterized_z_positive ht htT commonT_range.2)
    (commonP_positive hi) (commonNegQ_positive hi) (commonDet_positive hi)

 theorem seed_differential_residual_identity {t : ℝ} (ht : 0<t) (htT : t ≤ seedT) :
    seedAlphaAt t*(9*B/2)*(1-t^2)-
      (6*(4/(1-seedAlphaAt t)-2)-4)*(t^2*(seedV t)^2)+
      (17*(1-t^2)+seedR*Real.sqrt (1-t^2))*(-(seedV t*seedSlope t))=
      seedP t-Real.sqrt (1-t^2)*seedNegQ t := by
  have hi : t∈Icc 0 seedT := ⟨ht.le,htT⟩
  have he := variable_alpha_residual_identity
    (z:=1-t^2) (c:=seedC) (t:=t) (v:=seedV t) (s:=seedSlope t)
    (p:=9*B/2) (C:=24) (D:=16) (R:=seedR) (r0:=0) (a:=17)
    (parameterized_z_positive ht.le htT seedT_range.2)
    (ne_of_gt seedC_positive) (ne_of_gt ht) (ne_of_gt (seedV_positive hi))
  convert he using 1 <;> dsimp [seedAlphaAt,seedP,seedNegQ] <;> ring

 theorem common_differential_residual_identity {t : ℝ} (ht : 0<t) (htT : t ≤ commonT) :
    commonAlphaAt t*K*(1-t^2)-
      (4/(1-commonAlphaAt t)-2)*(t^2*(commonV t)^2)-
      commonR*Real.sqrt (t^2*(commonV t)^2)+
      (2*(1-t^2)+commonR*Real.sqrt (1-t^2))*(-(commonV t*commonSlope t))=
      commonP t-Real.sqrt (1-t^2)*commonNegQ t := by
  have hi : t∈Icc 0 commonT := ⟨ht.le,htT⟩
  have hv : 0<commonV t := commonV_positive hi
  have hs : Real.sqrt (t^2*(commonV t)^2)=t*commonV t := by
    rw [←mul_pow]
    exact Real.sqrt_sq (mul_nonneg ht.le hv.le)
  rw [hs]
  have he := variable_alpha_residual_identity
    (z:=1-t^2) (c:=commonC) (t:=t) (v:=commonV t) (s:=commonSlope t)
    (p:=K) (C:=4) (D:=2) (R:=commonR) (r0:=commonR) (a:=2)
    (parameterized_z_positive ht.le htT commonT_range.2)
    (ne_of_gt commonC_positive) (ne_of_gt ht) (ne_of_gt hv)
  convert he using 1 <;> dsimp [commonAlphaAt,commonP,commonNegQ] <;> ring

 theorem seed_differential_residual_positive {t : ℝ} (ht : 0<t) (htT : t ≤ seedT) :
    0<seedAlphaAt t*(9*B/2)*(1-t^2)-
      (6*(4/(1-seedAlphaAt t)-2)-4)*(t^2*(seedV t)^2)+
      (17*(1-t^2)+seedR*Real.sqrt (1-t^2))*(-(seedV t*seedSlope t)) := by
  rw [seed_differential_residual_identity ht htT]
  exact seed_sqrt_residual_positive ht.le htT

 theorem common_differential_residual_positive {t : ℝ} (ht : 0<t) (htT : t ≤ commonT) :
    0<commonAlphaAt t*K*(1-t^2)-
      (4/(1-commonAlphaAt t)-2)*(t^2*(commonV t)^2)-
      commonR*Real.sqrt (t^2*(commonV t)^2)+
      (2*(1-t^2)+commonR*Real.sqrt (1-t^2))*(-(commonV t*commonSlope t)) := by
  rw [common_differential_residual_identity ht htT]
  exact common_sqrt_residual_positive ht.le htT

end VariableAlpha24
#print axioms VariableAlpha24.seed_alpha_mem_unit
#print axioms VariableAlpha24.common_alpha_mem_unit
#print axioms VariableAlpha24.seed_differential_residual_positive
#print axioms VariableAlpha24.common_differential_residual_positive
