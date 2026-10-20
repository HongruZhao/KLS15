import ThetaWeightedTriangleYoung
import DegreeYoungDrift

/-! A selective use of the exact size-two second-factor square.  The
full joint bound is kept and the literal selected square is retained on
the left; no upper estimate for that square is subtracted. -/
noncomputable section
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def selectiveTriangleFraction (lambda : ℕ → ℝ) (d a : ℕ) : ℝ :=
  if a = 2 then 1-lambda (d-1) else 1

def selectiveDegreePrefix (s theta lambda : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 2 (d-1), s (d-a+1) * (thetaTriangleCoefficient theta d a)^2 /
    selectiveTriangleFraction lambda d a

theorem selectiveDegreePrefix_eq (s theta lambda : ℕ → ℝ) {d : ℕ} (hd : 3 ≤ d) :
    selectiveDegreePrefix s theta lambda d = properYoungPrefix s d-s (d-1) +
      s (d-1)*(1-theta d)^2/(1-lambda (d-1)) := by
  classical
  have hmem : 2 ∈ Finset.Icc 2 (d-1) := by simp only [Finset.mem_Icc]; omega
  have he : (∑ a ∈ Finset.Icc 2 (d-1), s (d-a+1) * (thetaTriangleCoefficient theta d a)^2 /
      selectiveTriangleFraction lambda d a) =
      ∑ a ∈ Finset.Icc 2 (d-1), (s (d-a+1) + if a = 2 then
        s (d-1)*(1-theta d)^2/(1-lambda (d-1))-s (d-1) else 0) := by
    apply Finset.sum_congr rfl
    intro a ha
    by_cases ha2 : a = 2
    · subst a
      have hsub : d-2+1 = d-1 := by omega
      simp only [thetaTriangleCoefficient,selectiveTriangleFraction,ite_true,hsub]
      ring
    · simp [thetaTriangleCoefficient,selectiveTriangleFraction,ha2]
  unfold selectiveDegreePrefix
  rw [he,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',hmem,ite_true]
  have hp : (∑ a ∈ Finset.Icc 2 (d-1), s (d-a+1)) = properYoungPrefix s d := by
    unfold properYoungPrefix
    apply Finset.sum_bij (fun a _ => d-a+1)
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      omega
    · intro a ha b hb he
      simp only [Finset.mem_Icc] at ha hb
      omega
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      refine ⟨d-b+1,?_,?_⟩
      · simp only [Finset.mem_Icc]
        omega
      · omega
    · intro a ha
      rfl
  rw [hp]
  ring

theorem coupled_triangle_selective_budget_young (N : ℕ) (P : ℕ → ℝ)
    (Q : ℕ → ℕ → ℝ) (s theta lambda : ℕ → ℝ) {C K : ℝ}
    (hK : 0 ≤ K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (hlambda : ∀ b, 2 ≤ b → lambda b < 1)
    (hjoint : ∀ b ∈ Finset.Icc 2 N,
      (∑ a ∈ Finset.Icc 2 (N-1), (Q a b)^2) ≤ C*(P b)^2) :
    2*Real.sqrt K*(∑ d ∈ Finset.Icc 3 N, ∑ a ∈ Finset.Icc 2 (d-1),
      thetaTriangleCoefficient theta d a*(P d/(d : ℝ))*Q a (d-a+1)) +
      (∑ d ∈ Finset.Icc 3 N, (lambda (d-1)*K/s (d-1))*(Q 2 (d-1))^2) ≤
      (∑ d ∈ Finset.Icc 3 N, selectiveDegreePrefix s theta lambda d*(P d/(d : ℝ))^2) +
      ∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(P b)^2 := by
  classical
  have hp : ∀ p ∈ coupledDriftPairs N, 2 ≤ p.1-p.2+1 := by
    intro p hp
    obtain ⟨hd,ha⟩ := Finset.mem_sigma.mp hp
    simp only [Finset.mem_Icc] at hd ha
    omega
  have hfpos : ∀ p ∈ coupledDriftPairs N, 0 < selectiveTriangleFraction lambda p.1 p.2 := by
    intro p hmem
    unfold selectiveTriangleFraction
    split_ifs with h2
    · have hd := (Finset.mem_Icc.mp (Finset.mem_sigma.mp hmem).1).1
      have h := hlambda (p.1-1) (by omega)
      linarith
    · norm_num
  have hy := Finset.sum_le_sum (s := coupledDriftPairs N) (fun p hmem =>
    sqrt_weighted_young hK
      (div_pos (hs _ (hp p hmem)) (hfpos p hmem))
      (thetaTriangleCoefficient theta p.1 p.2*(P p.1/(p.1 : ℝ)))
      (Q p.2 (p.1-p.2+1)))
  have he : (∑ p ∈ coupledDriftPairs N, 2*Real.sqrt K *
      (thetaTriangleCoefficient theta p.1 p.2*(P p.1/(p.1 : ℝ))) *
        Q p.2 (p.1-p.2+1)) =
      2*Real.sqrt K*(∑ d ∈ Finset.Icc 3 N, ∑ a ∈ Finset.Icc 2 (d-1),
        thetaTriangleCoefficient theta d a*(P d/(d : ℝ))*Q a (d-a+1)) := by
    rw [coupledDriftPairs,Finset.sum_sigma,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hfirst : (∑ p ∈ coupledDriftPairs N,
      (s (p.1-p.2+1)/selectiveTriangleFraction lambda p.1 p.2) *
        (thetaTriangleCoefficient theta p.1 p.2*(P p.1/(p.1 : ℝ)))^2) =
      ∑ d ∈ Finset.Icc 3 N, selectiveDegreePrefix s theta lambda d*(P d/(d : ℝ))^2 := by
    rw [coupledDriftPairs,Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro d hd
    unfold selectiveDegreePrefix
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hsecond : (∑ p ∈ coupledDriftPairs N,
      (K/(s (p.1-p.2+1)/selectiveTriangleFraction lambda p.1 p.2)) *
        (Q p.2 (p.1-p.2+1))^2) =
      (∑ p ∈ coupledDriftPairs N, (K/s (p.1-p.2+1)) *
        (Q p.2 (p.1-p.2+1))^2) -
      ∑ d ∈ Finset.Icc 3 N, (lambda (d-1)*K/s (d-1))*(Q 2 (d-1))^2 := by
    have hterm : (∑ p ∈ coupledDriftPairs N,
        (K/(s (p.1-p.2+1)/selectiveTriangleFraction lambda p.1 p.2)) *
          (Q p.2 (p.1-p.2+1))^2) =
        ∑ p ∈ coupledDriftPairs N, ((K/s (p.1-p.2+1)) *
          (Q p.2 (p.1-p.2+1))^2 - if p.2 = 2 then
            (lambda (p.1-1)*K/s (p.1-1))*(Q 2 (p.1-1))^2 else 0) := by
      apply Finset.sum_congr rfl
      intro p hmem
      by_cases h2 : p.2 = 2
      · have hd := (Finset.mem_Icc.mp (Finset.mem_sigma.mp hmem).1).1
        have hsub : p.1-p.2+1 = p.1-1 := by omega
        simp only [selectiveTriangleFraction,ite_eq_left h2,hsub]
        rw [h2]
        field_simp
      · simp [selectiveTriangleFraction,h2]
    rw [hterm,Finset.sum_sub_distrib]
    congr 1
    rw [coupledDriftPairs,Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro d hd
    have h2 : 2 ∈ Finset.Icc 2 (d-1) := by
      simp only [Finset.mem_Icc] at hd ⊢
      omega
    simp only [Finset.sum_ite_eq',h2,ite_true]
  rw [he,Finset.sum_add_distrib,hfirst,hsecond] at hy
  have hj := coupled_triangle_second_factor_weighted N P Q (fun b => K/s b)
    (fun b hb => div_nonneg hK (hs b (Finset.mem_Icc.mp hb).1).le) hjoint
  have hj' : (∑ p ∈ coupledDriftPairs N, (K/s (p.1-p.2+1)) *
      (Q p.2 (p.1-p.2+1))^2) ≤ ∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(P b)^2 := by
    convert hj using 1
    apply Finset.sum_congr rfl
    intro b hb
    ring
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.selectiveDegreePrefix_eq
#print axioms KLS.DeterministicBridgeNext.coupled_triangle_selective_budget_young
