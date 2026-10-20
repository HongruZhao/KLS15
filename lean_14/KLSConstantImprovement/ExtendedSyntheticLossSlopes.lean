import KLSConstantImprovement.SyntheticGeneratorLossLower

/-! Exact low-branch slope table, degrees3..64.  Every entry is proved
by a rational discriminant inequality.  Maximality is checked separately
in the reproducible exact report; this module only proves safe slopes.
This isolated source draft has not been compiled by its author. -/
noncomputable section
namespace KLSConstantImprovement.ExtendedSyntheticLossSlopes
open KLSBelow25.PairProjection
open KLSConstantImprovement.SyntheticGeneratorLossLower
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
open KLSConstantImprovement.PositiveEnergyWeightedGenerator

def lowL (d : ℕ) : ℝ :=
  4*(d : ℝ)^2+8*(d : ℝ)*((d : ℝ)-2)/(3*((d : ℝ)-1))
def lowB (d : ℕ) : ℝ :=
  2*(d : ℝ)^2+(d : ℝ)+8*(d : ℝ)*((d : ℝ)-2)/(3*((d : ℝ)-1))-1

theorem low_branch_le (d : ℕ) (hd : 3 ≤ d) (a : ℝ) :
    lowL d/(1-a)-lowB d ≤ unreservedG d a := by
  have hh := unreservedG_lower_low d hd a
  convert hh using 1 <;>
    unfold lowL lowB leadingNoiseCoefficient positiveNoiseCoefficient <;> ring

theorem generic_slope (d : ℕ) (hd : 3 ≤ d) (m : ℝ) (hm : 0 < m)
    (hdisc : (m-lowB d)^2 ≤ 4*m*(lowL d-lowB d)) (a : ℝ) (ha : a < 1) :
    m*a ≤ unreservedG d a := by
  exact (slope_of_discriminant ha hm (by nlinarith only [hdisc])).trans
    (low_branch_le d hd a)

def slope (d : ℕ) : ℝ :=
  if d=2 then 45 else
  if d=3 then 106 else
  if d=4 then 190 else
  if d=5 then 298 else
  if d=6 then 428 else
  if d=7 then 582 else
  if d=8 then 759 else
  if d=9 then 959 else
  if d=10 then 1183 else
  if d=11 then 1430 else
  if d=12 then 1700 else
  if d=13 then 1994 else
  if d=14 then 2311 else
  if d=15 then 2651 else
  if d=16 then 3015 else
  if d=17 then 3401 else
  if d=18 then 3812 else
  if d=19 then 4245 else
  if d=20 then 4702 else
  if d=21 then 5182 else
  if d=22 then 5685 else
  if d=23 then 6212 else
  if d=24 then 6762 else
  if d=25 then 7335 else
  if d=26 then 7932 else
  if d=27 then 8552 else
  if d=28 then 9195 else
  if d=29 then 9862 else
  if d=30 then 10552 else
  if d=31 then 11265 else
  if d=32 then 12001 else
  if d=33 then 12761 else
  if d=34 then 13544 else
  if d=35 then 14351 else
  if d=36 then 15181 else
  if d=37 then 16034 else
  if d=38 then 16910 else
  if d=39 then 17810 else
  if d=40 then 18733 else
  if d=41 then 19679 else
  if d=42 then 20649 else
  if d=43 then 21642 else
  if d=44 then 22658 else
  if d=45 then 23698 else
  if d=46 then 24761 else
  if d=47 then 25847 else
  if d=48 then 26956 else
  if d=49 then 28089 else
  if d=50 then 29245 else
  if d=51 then 30425 else
  if d=52 then 31628 else
  if d=53 then 32854 else
  if d=54 then 34103 else
  if d=55 then 35376 else
  if d=56 then 36672 else
  if d=57 then 37991 else
  if d=58 then 39334 else
  if d=59 then 40700 else
  if d=60 then 42089 else
  if d=61 then 43502 else
  if d=62 then 44938 else
  if d=63 then 46397 else
  if d=64 then 47880 else
  0

theorem slope_positive (d : ℕ) (hd : 2 ≤ d) (hD : d ≤ 64) : 0 < slope d := by
  interval_cases d <;> norm_num [slope]

theorem slope_discriminant (d : ℕ) (hd : 3 ≤ d) (hD : d ≤ 64) :
    (slope d-lowB d)^2 ≤ 4*slope d*(lowL d-lowB d) := by
  interval_cases d <;> norm_num [slope,lowL,lowB]

theorem table_slope (d : ℕ) (hd : 2 ≤ d) (hD : d ≤ 64) (a : ℝ) (ha : a < 1) :
    slope d*a ≤ unreservedG d a := by
  by_cases hd2 : d=2
  · subst d
    simpa only [slope,ite_true] using slope_two a ha
  · exact generic_slope d (by omega) (slope d) (slope_positive d hd hD)
      (slope_discriminant d (by omega) hD) a ha

theorem table_effective_slope {P : Parameters} {H A B : ℝ}
    (h : RawCubicQuarticWeightedBudget.ScalarCertificate P H A B)
    (d : ℕ) (hd : 2 ≤ d) (hD : d ≤ 64) :
    slope d*P.alpha d ≤
      generatorLoss P.K P.young P.t P.alpha P.theta P.lambda d+1+
        TriplePositiveEnergyWeightedBudget.cost P d :=
  (table_slope d hd hD (P.alpha d) (h.alpha_lt_one d hd)).trans
    (effective_loss_lower h d hd)

end KLSConstantImprovement.ExtendedSyntheticLossSlopes
#print axioms KLSConstantImprovement.ExtendedSyntheticLossSlopes.generic_slope
#print axioms KLSConstantImprovement.ExtendedSyntheticLossSlopes.table_slope
#print axioms KLSConstantImprovement.ExtendedSyntheticLossSlopes.table_effective_slope
