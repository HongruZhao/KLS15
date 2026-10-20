import KLSConstantImprovement.LongPrefixCubicBellmanData
import KLSConstantImprovement.CorrelatedCubicRationalTangents2388

/-! A sharper cubic tangent pays a smaller budget in the already proved six
stage Bellman certificate. The original all-rank weighted profile and each
square identity are reused unchanged; only the valid tangent and endpoint
budget change. -/
noncomputable section
open scoped BigOperators
open Set
namespace KLSConstantImprovement.Seed2388BellmanData
open PositiveFiniteHeadBellman QuadraticCapBellmanCertificates WeightedOrbitBellmanTail
open KLSBelow25
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def K : ℝ := 12453922967/976562500
def C : ℝ := 544214142208406583/10000000000000000000
def p : ℝ := 20929161/20000000
def originalC : ℝ := 5074295116709/100000000000000
abbrev tau := LongPrefixCubicBellmanData.tau
abbrev t := LongPrefixCubicBellmanData.t
abbrev ratioUpper := LongPrefixCubicBellmanData.ratioUpper
abbrev A := LongPrefixCubicBellmanData.A
abbrev chord := LongPrefixCubicBellmanData.chord
abbrev baseW := LongPrefixCubicBellmanData.baseW
abbrev w := LongPrefixCubicBellmanData.w
abbrev line := LongPrefixCubicBellmanData.line
abbrev contact := LongPrefixCubicBellmanData.contact
abbrev multiplier := LongPrefixCubicBellmanData.multiplier
abbrev domainTerm := LongPrefixCubicBellmanData.domainTerm
abbrev dualWeight := LongPrefixCubicBellmanData.dualWeight
abbrev dualMultiplier := LongPrefixCubicBellmanData.dualMultiplier
def dualT : ℝ := 644792251093/1000000000000
def dualHeight : ℝ := 1055785727663/50000000000000
def dualPoint : ℝ := dualT^2*(CreationSeed2388.seedV dualT)^2

theorem t_positive (d : ℕ) (hd : 2 ≤ d) : 0<t d := LongPrefixCubicBellmanData.t_positive d hd
theorem t_floor (d : ℕ) (hd : 2 ≤ d) : tau ≤ t d := LongPrefixCubicBellmanData.t_floor d hd
theorem A_nonneg : 0 ≤ A := LongPrefixCubicBellmanData.A_nonneg
theorem ratioUpper_positive : 0<ratioUpper := LongPrefixCubicBellmanData.ratioUpper_positive
theorem p_positive : 0<p := by norm_num [p]
theorem p_interval : 1 ≤ p ∧ p ≤ ratioUpper := by
  norm_num [p,ratioUpper,LongPrefixCubicBellmanData.ratioUpper,LongPrefixCubicBellmanData.K]
theorem w_tail (i : ℕ) (hi : 6 ≤ i) : w i=tau := LongPrefixCubicBellmanData.w_tail i hi
theorem w_nonneg (i : ℕ) : 0 ≤ w i := LongPrefixCubicBellmanData.w_nonneg i
theorem baseW_le_t (i : ℕ) : baseW i ≤ t (i+2) := LongPrefixCubicBellmanData.baseW_le_t i
theorem line_slope_nonneg (i : ℕ) (hi : i<7) : 0 ≤ (line i).slope :=
  LongPrefixCubicBellmanData.line_slope_nonneg i hi
theorem line_at_one (i : ℕ) (hi : i<7) : (line i).eval 1 ≤ 0 :=
  LongPrefixCubicBellmanData.line_at_one i hi
theorem stage_certificate (i : ℕ) (hi : i<6) :
    StageCertificate (w i) ratioUpper (capChord A ratioUpper) (line i) (line (i+1)) :=
  LongPrefixCubicBellmanData.stage_certificate i hi
theorem terminal_line (r : ℝ) : (line 6).eval r=tau*(r-1) :=
  LongPrefixCubicBellmanData.terminal_line r
theorem strict_budget : C<p*(line 0).positive p := by
  have hh : C<p*(line 0).eval p := by
    norm_num [C,p,line,LongPrefixCubicBellmanData.line,Affine.eval]
  exact hh.trans_le (mul_le_mul_of_nonneg_left (le_max_right 0 ((line 0).eval p)) p_positive.le)

theorem dualPoint_mem : dualPoint∈Icc (0 : ℝ) 1 := by
  norm_num [dualPoint,dualT,CreationSeed2388.seedV]
theorem dual_weight_le : dualWeight ≤ CreationSeed2388.supportWeight dualPoint/K := by
  unfold dualPoint
  rw [CreationSeed2388.supportWeight_polynomial_parameter
    (by norm_num [dualT] : 0 ≤ dualT)
    (by norm_num [dualT,CreationSeed2388.seedT] : dualT<CreationSeed2388.seedT)
    dualPoint_mem.2]
  norm_num [dualWeight,LongPrefixCubicBellmanData.dualWeight,K,dualT,CreationSeed2388.B,
    CreationSeed2388.seedV,CreationSeed2388.seedSlope,CreationSeed2388.seedVp]
theorem dual_height_le : CreationSeed2388.supportIntercept dualPoint/K^3 ≤ dualHeight := by
  unfold dualPoint
  rw [CreationSeed2388.supportIntercept_polynomial_parameter
    (by norm_num [dualT] : 0 ≤ dualT)
    (by norm_num [dualT,CreationSeed2388.seedT] : dualT<CreationSeed2388.seedT)
    dualPoint_mem.2]
  norm_num [dualHeight,K,dualT,CreationSeed2388.B,
    CreationSeed2388.seedV,CreationSeed2388.seedSlope,CreationSeed2388.seedVp]
theorem augmentation_identity (c : ℕ→ℝ) (N : ℕ) :
    spend w c (N+2)=spend baseW c (N+2)+dualMultiplier*(dualWeight*c 0+c 1) :=
  LongPrefixCubicBellmanData.augmentation_identity c N

theorem augmented_budget (c : ℕ→ℝ) (hc : ∀ i,0 ≤ c i)
    (hbudget : ∀ N,spend (fun i=>t (i+2)) c N ≤ originalC)
    (hdual : dualWeight*c 0+c 1 ≤ dualHeight) : ∀ N,spend w c N ≤ C := by
  intro N
  have hm : spend w c N ≤ spend w c (N+2) := by
    unfold spend
    rw [Finset.sum_range_add]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => mul_nonneg (w_nonneg _) (hc _))
  have hb : spend baseW c (N+2) ≤ originalC := by
    apply (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (baseW_le_t i) (hc i))).trans
    exact hbudget (N+2)
  have hd := mul_le_mul_of_nonneg_left hdual
    (by norm_num [dualMultiplier,LongPrefixCubicBellmanData.dualMultiplier] : 0 ≤ dualMultiplier)
  calc
    spend w c N ≤ spend w c (N+2) := hm
    _ = spend baseW c (N+2)+dualMultiplier*(dualWeight*c 0+c 1) := augmentation_identity c N
    _  ≤  originalC+dualMultiplier*dualHeight := add_le_add hb hd
    _ = C := by norm_num [originalC,dualMultiplier,LongPrefixCubicBellmanData.dualMultiplier,dualHeight,C]

end KLSConstantImprovement.Seed2388BellmanData
#print axioms KLSConstantImprovement.Seed2388BellmanData.stage_certificate
#print axioms KLSConstantImprovement.Seed2388BellmanData.strict_budget
#print axioms KLSConstantImprovement.Seed2388BellmanData.dualPoint_mem
#print axioms KLSConstantImprovement.Seed2388BellmanData.dual_weight_le
#print axioms KLSConstantImprovement.Seed2388BellmanData.dual_height_le
#print axioms KLSConstantImprovement.Seed2388BellmanData.augmented_budget
