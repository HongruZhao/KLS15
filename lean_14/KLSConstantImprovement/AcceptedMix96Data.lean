import KLSConstantImprovement.QuarticM48Profile20261020Data
import KLSConstantImprovement.QuarticM32Profile20261020Data

/-! A nonnegative mixture of two frozen raw budgets (both actual-law chains must be accepted by the merger), with the positive
post-head remainder discarded after rank96. This is scalar data only. -/
noncomputable section
namespace KLSConstantImprovement.AcceptedMix96Data
set_option maxHeartbeats 3000000

def K : ℝ := 1216280801173157/100000000000000
def L : ℝ := 122144150200807/10000000000000
def a : ℝ := 1/32
def C : ℝ := 29154132685465397/160000000000000000
def p : ℝ := 1281084000000000/1216280801173157
def tau : ℝ := 1/2
def tTail : ℝ := 126653986822869/100000000000000
def rawMix (d : ℕ) : ℝ := QuarticM48Profile20261020Data.t d+
  a*QuarticM32Profile20261020Data.t d*(K/L)^d
def t (d : ℕ) : ℝ := if d ≤ 96 then rawMix d else tTail

theorem K_positive : 0 < K := by norm_num [K]
theorem L_positive : 0 < L := by norm_num [L]
theorem K_eq : K=QuarticM48Profile20261020Data.K := by norm_num [K,QuarticM48Profile20261020Data.K]
theorem L_eq : L=QuarticM32Profile20261020Data.K := by norm_num [L,QuarticM32Profile20261020Data.K]
theorem C_eq : C=QuarticM48Profile20261020Data.C+a*QuarticM32Profile20261020Data.C := by
  norm_num [C,a,QuarticM48Profile20261020Data.C,QuarticM32Profile20261020Data.C]

theorem rawMix_ge_base (d : ℕ) (hd : 2 ≤ d) :
    QuarticM48Profile20261020Data.t d ≤ rawMix d := by
  have he : 0 ≤ a*QuarticM32Profile20261020Data.t d*(K/L)^d :=
    mul_nonneg (mul_nonneg (by norm_num [a])
      (QuarticM32Profile20261020Data.t_positive d hd).le)
      (pow_nonneg (div_nonneg K_positive.le L_positive.le) d)
  dsimp only [rawMix]
  linarith

theorem rawMix_tail_floor (d : ℕ) (hd : 48 ≤ d) : tTail ≤ rawMix d := by
  calc
    tTail = QuarticM48Profile20261020Data.tTail := by norm_num [tTail,QuarticM48Profile20261020Data.tTail]
    _ = QuarticM48Profile20261020Data.t d := (QuarticM48Profile20261020Data.t_eq_tail d hd).symm
    _ ≤ rawMix d := rawMix_ge_base d (by omega)

theorem t_le_rawMix (d : ℕ) (hd : 2 ≤ d) : t d ≤ rawMix d := by
  by_cases he : d ≤ 96
  · simpa only [t,if_pos he] using (le_refl (rawMix d))
  · rw [t,if_neg he]
    exact rawMix_tail_floor d (by omega)

theorem t_floor (d : ℕ) (hd : 2 ≤ d) : tau ≤ t d := by
  by_cases he : d ≤ 96
  · rw [t,if_pos he]
    calc
      tau = QuarticM48Profile20261020Data.tau := by norm_num [tau,QuarticM48Profile20261020Data.tau]
      _ ≤ QuarticM48Profile20261020Data.t d := QuarticM48Profile20261020Data.t_floor d hd
      _ ≤ rawMix d := rawMix_ge_base d hd
  · rw [t,if_neg he]
    norm_num [tau,tTail]

theorem t_positive (d : ℕ) (hd : 2 ≤ d) : 0 < t d := by
  have he := t_floor d hd
  norm_num [tau] at he
  linarith

theorem t_eq_tail (d : ℕ) (hd : 97 ≤ d) : t d=tTail := by
  simp only [t,if_neg (show ¬d ≤ 96 by omega)]

theorem exact_endpoint : 1+K*p=(345271/25000 : ℝ) := by norm_num [K,p]
def pLoose : ℝ := (1281085/100000)/K

theorem exact_endpoint_loose : 1+K*pLoose=(276217/20000 : ℝ) := by
  norm_num [pLoose,K]

end KLSConstantImprovement.AcceptedMix96Data
#print axioms KLSConstantImprovement.AcceptedMix96Data.t_le_rawMix
#print axioms KLSConstantImprovement.AcceptedMix96Data.t_floor
#print axioms KLSConstantImprovement.AcceptedMix96Data.t_positive
#print axioms KLSConstantImprovement.AcceptedMix96Data.t_eq_tail
