import KLSConstantImprovement.ActualConstantTailFamilyFloor

/-! Pointwise necessary degree inequalities for the actual generator
family, without eventual constancy of alpha, Young, or energy weights.
Only the finite reserved prefix is removed. These feed a separate
subexponential contraction obstruction; they assert no KLS lower bound. -/
noncomputable section
namespace KLSConstantImprovement.ActualSubexponentialTailDegree
open KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget

def critical : ℝ := 6+4*Real.sqrt 2
def noiseScale (a : ℝ) : ℝ := 4/(1-a)-2
def noiseRefund (a : ℝ) : ℝ := 4*a/(3*(1-a))

theorem noiseScale_ge_two {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1) :
    2 ≤ noiseScale a := by
  have hden : 0 < 1-a := by linarith
  have hh : 4 ≤ 4/(1-a) := (le_div_iff₀ hden).mpr (by linarith)
  unfold noiseScale
  linarith

theorem noiseScale_ge_critical {a : ℝ} (ha : a < 1) :
    critical*a ≤ noiseScale a := by
  have hden : 0 < 1-a := by linarith
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hid : (noiseScale a-critical*a)*(1-a)=
      ((2+Real.sqrt 2)*a-Real.sqrt 2)^2 := by
    unfold noiseScale critical
    field_simp [ne_of_gt hden]
    ring_nf
    simp only [hs]
    ring
  by_contra hn
  have hneg : noiseScale a-critical*a < 0 := by linarith
  have hp := mul_neg_of_neg_of_pos hneg hden
  rw [hid] at hp
  linarith [sq_nonneg ((2+Real.sqrt 2)*a-Real.sqrt 2)]

theorem residual_loss_identity {a : ℝ} (ha : a < 1) (d : ℕ) (hd : 3 ≤ d) :
    generalResidualGeneratorLoss a d=noiseScale a*(d : ℝ)^2-(d : ℝ)+
      2*noiseRefund a*(d : ℝ)*((d : ℝ)-2)/((d : ℝ)-1) := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  unfold noiseScale noiseRefund generalResidualGeneratorLoss generalResidualA
  field_simp [show 1-a≠0 by linarith,show (d : ℝ)-1≠0 by linarith]
  ring

theorem residual_loss_lower {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1)
    (d : ℕ) (hd : 3 ≤ d) :
    noiseScale a*(d : ℝ)*((d : ℝ)-1) ≤ generalResidualGeneratorLoss a d := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hscale := noiseScale_ge_two ha0 ha
  have hden : 0 < 1-a := by linarith
  have hdm : 0 < (d : ℝ)-1 := by linarith
  have hdm2 : 0 ≤ (d : ℝ)-2 := by linarith
  have hrefund : 0 ≤ noiseRefund a := by unfold noiseRefund; positivity
  have he : 0 ≤ 2*noiseRefund a*(d : ℝ)*((d : ℝ)-2)/((d : ℝ)-1) := by positivity
  rw [residual_loss_identity ha d hd]
  nlinarith [mul_nonneg (by linarith : 0 ≤ noiseScale a-1)
    (by linarith : 0 ≤ (d : ℝ))]

/-- Actual all-rank positivity forces two coupled one-degree contractions.
Alpha, Young, and t may vary at every degree. -/
theorem degree_contractions (P : Parameters) (hK : 0 < P.K) (hC : 0 ≤ P.C)
    (hyall : ∀ b,2 ≤ b → 0 < P.young b)
    (htall : ∀ b,2 ≤ b → 0 < P.t b)
    (d : ℕ) (hd : 4 ≤ d) (ha0 : 0 ≤ P.alpha d) (ha : P.alpha d < 1)
    (hth : P.theta d=0) (hthnext : P.theta (d+1)=0)
    (hl : P.lambda d=0) (hlprev : P.lambda (d-1)=0)
    (hzeta : P.zeta d=0) (hzetaprev : P.zeta (d-2)=0)
    (hcoef : 0 ≤ coefficient P d) :
    critical*(1-1/(d : ℝ))*(P.t d*P.alpha d) ≤ P.K*(P.t (d-1)*P.alpha (d-1)) ∧
      2*(1-1/(d : ℝ))*P.t d ≤ P.K*(P.t (d-1)*P.alpha (d-1)) := by
  have hd4 : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have htd : 0 < P.t d := htall d (by omega)
  have hraw := ActualConstantTailFamilyFloor.raw_first_cost_nonneg P d hd
    hyall htall hth hlprev hzetaprev
  have hcharge : tripleHarmonicNeighborCharge P.K P.young P.zeta d=0 := by
    simp [tripleHarmonicNeighborCharge,hzeta]
  have hcost : 0 ≤ TriplePositiveEnergyWeightedGenerator.cost
      P.K P.C P.young P.t P.theta P.lambda P.zeta d := by
    unfold TriplePositiveEnergyWeightedGenerator.cost
    rw [if_pos (by omega : 3 ≤ d),hcharge]
    have hm : 0 ≤ (P.K*P.C/P.young d)*(d : ℝ)^2 :=
      mul_nonneg (div_nonneg (mul_nonneg hK.le hC) (hyall d (by omega)).le)
        (sq_nonneg _)
    simp only [mul_zero,add_zero]
    linarith
  have hgen := (residual_loss_lower ha0 ha d (by omega)).trans
    (ActualConstantTailFamilyFloor.generator_loss_lower P ha d (by omega)
      rfl hthnext hl)
  have hinc : noiseScale (P.alpha d)*(d : ℝ)*((d : ℝ)-1) ≤
      PositiveEnergyWeightedGenerator.incoming P.K P.t P.alpha d := by
    unfold coefficient TriplePositiveEnergyWeightedGenerator.coefficient at hcoef
    linarith
  have hh := mul_le_mul_of_nonneg_right hinc htd.le
  have hid : PositiveEnergyWeightedGenerator.incoming P.K P.t P.alpha d*P.t d=
      P.K*(P.t (d-1)*P.alpha (d-1))*(d : ℝ)^2 := by
    unfold PositiveEnergyWeightedGenerator.incoming
    field_simp [ne_of_gt htd] <;> ring
  rw [hid] at hh
  have hdivide := div_le_div_of_nonneg_right hh (sq_nonneg (d : ℝ))
  have hbound : noiseScale (P.alpha d)*(1-1/(d : ℝ))*P.t d ≤
      P.K*(P.t (d-1)*P.alpha (d-1)) := by
    convert hdivide using 1 <;> field_simp [show (d : ℝ)≠0 by linarith] <;> ring
  have hfactor : 0 ≤ (1-1/(d : ℝ))*P.t d := by
    have hdiv : 1/(d : ℝ) ≤ 1 := (div_le_iff₀ (by linarith : 0 < (d : ℝ))).mpr (by linarith)
    exact mul_nonneg (by linarith) htd.le
  have hc := mul_le_mul_of_nonneg_right (noiseScale_ge_critical ha) hfactor
  have ht := mul_le_mul_of_nonneg_right (noiseScale_ge_two ha0 ha) hfactor
  constructor
  · nlinarith only [hc,hbound]
  · nlinarith only [ht,hbound]

end KLSConstantImprovement.ActualSubexponentialTailDegree
#print axioms KLSConstantImprovement.ActualSubexponentialTailDegree.noiseScale_ge_critical
#print axioms KLSConstantImprovement.ActualSubexponentialTailDegree.residual_loss_identity
#print axioms KLSConstantImprovement.ActualSubexponentialTailDegree.degree_contractions
