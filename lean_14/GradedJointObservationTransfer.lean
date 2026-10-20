import GradedPowerObservation

/-! Joint bounds for adjoint observation blocks pass to the genuine
Hilbert direct sum. Degree shifts preserve orthogonality exactly. -/
noncomputable section
namespace KLSBelow25.GradedHilbert
open ContinuousLinearMap InnerProductSpace
open scoped ENNReal BigOperators
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {G E : ℕ→Type*}
  [∀r,NormedAddCommGroup (G r)] [∀r,InnerProductSpace ℝ (G r)] [∀r,CompleteSpace (G r)]
  [∀r,NormedAddCommGroup (E r)] [∀r,InnerProductSpace ℝ (E r)] [∀r,CompleteSpace (E r)]
  (J : ∀r,G (r+1)→L[ℝ]G r) (L : ∀r,E r→L[ℝ]G r)
  {CJ CL : ℝ} (hCJ : 0≤CJ) (hJ : ∀r,‖J r‖≤CJ) (hCL : 0≤CL) (hL : ∀r,‖L r‖≤CL)

lemma power_observation_single_add (d r : ℕ) (y : E (r+d)) :
    (((shift J hCJ hJ)^d).comp (diagonal L hCL hL)) (lp.single 2 (r+d) y)=
      lp.single 2 r (powerObservationBlock J L hCJ hJ hCL hL d r y) := by
  apply lp.ext
  funext s
  rw [power_observation_apply]
  by_cases hs : s=r
  · subst s; simp
  · have hsd : s+d≠r+d := fun he => hs (Nat.add_right_cancel he)
    simp [hs]

lemma power_observation_adjoint_add (d r : ℕ) (f : lp G 2) :
    ((((shift J hCJ hJ)^d).comp (diagonal L hCL hL)).adjoint f) (r+d)=
      (powerObservationBlock J L hCJ hJ hCL hL d r).adjoint (f r) := by
  apply ext_inner_right ℝ
  intro y
  have he := adjoint_inner_left (((shift J hCJ hJ)^d).comp (diagonal L hCL hL))
    (lp.single 2 (r+d) y) f
  rw [lp.inner_single_right,power_observation_single_add,lp.inner_single_right] at he
  exact he.trans (adjoint_inner_left _ y (f r)).symm

lemma power_observation_adjoint_lt (d k : ℕ) (hk : k<d) (f : lp G 2) :
    ((((shift J hCJ hJ)^d).comp (diagonal L hCL hL)).adjoint f) k=0 := by
  apply ext_inner_right ℝ
  intro y
  have he := adjoint_inner_left (((shift J hCJ hJ)^d).comp (diagonal L hCL hL))
    (lp.single 2 k y) f
  rw [lp.inner_single_right] at he
  have hz : (((shift J hCJ hJ)^d).comp (diagonal L hCL hL)) (lp.single 2 k y)=0 := by
    apply lp.ext
    funext r
    rw [power_observation_apply]
    have hr : r+d≠k := by omega
    simp [hr]
  simpa [hz] using he

theorem norm_power_observation_adjoint_sq (d : ℕ) (f : lp G 2) :
    ‖(((shift J hCJ hJ)^d).comp (diagonal L hCL hL)).adjoint f‖^2=
      ∑'r,‖(powerObservationBlock J L hCJ hJ hCL hL d r).adjoint (f r)‖^2 := by
  let y := (((shift J hCJ hJ)^d).comp (diagonal L hCL hL)).adjoint f
  have he := (l2_summable_sq y).sum_add_tsum_nat_add d
  have hz : (∑k∈Finset.range d,‖y k‖^2)=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [show y k=0 from power_observation_adjoint_lt J L hCJ hJ hCL hL d k
      (Finset.mem_range.mp hk) f]
    simp
  rw [hz,zero_add] at he
  rw [l2_norm_sq,←he]
  apply tsum_congr
  intro r
  rw [show y (r+d)=(powerObservationBlock J L hCJ hJ hCL hL d r).adjoint (f r) from
    power_observation_adjoint_add J L hCJ hJ hCL hL d r f]

lemma summable_power_observation_adjoint_blocks (d : ℕ) (f : lp G 2) :
    Summable (fun r => ‖(powerObservationBlock J L hCJ hJ hCL hL d r).adjoint (f r)‖^2) := by
  have hs : Summable (fun r => ‖((((shift J hCJ hJ)^d).comp (diagonal L hCL hL)).adjoint f) (r+d)‖^2) :=
    (l2_summable_sq ((((shift J hCJ hJ)^d).comp (diagonal L hCL hL)).adjoint f)).comp_injective
      (fun a b h => Nat.add_right_cancel h)
  simpa only [power_observation_adjoint_add] using hs

/-- A common finite sum bound on every actual rank block is a bound on
the same finite sum of full adjoint observations. -/
theorem weighted_joint_adjoint_observation_le_of_blocks (s : Finset ℕ) (w : ℕ→ℝ)
    {C : ℝ} (_hC : 0≤C)
    (hblocks : ∀r (v : G r), ∑d∈s,w d*‖(powerObservationBlock J L hCJ hJ hCL hL d r).adjoint v‖^2≤C*‖v‖^2)
    (f : lp G 2) :
    ∑d∈s,w d*‖(((shift J hCJ hJ)^d).comp (diagonal L hCL hL)).adjoint f‖^2≤C*‖f‖^2 := by
  have hs (d : ℕ) : Summable (fun r => w d*‖(powerObservationBlock J L hCJ hJ hCL hL d r).adjoint (f r)‖^2) :=
    (summable_power_observation_adjoint_blocks J L hCJ hJ hCL hL d f).mul_left _
  calc
    _ = ∑d∈s,∑'r,w d*‖(powerObservationBlock J L hCJ hJ hCL hL d r).adjoint (f r)‖^2 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [norm_power_observation_adjoint_sq,tsum_mul_left]
    _ = ∑'r,∑d∈s,w d*‖(powerObservationBlock J L hCJ hJ hCL hL d r).adjoint (f r)‖^2 :=
      (Summable.tsum_finsetSum (fun d _ => hs d)).symm
    _ ≤ ∑'r,C*‖f r‖^2 := by
      apply Summable.tsum_le_tsum (fun r => hblocks r (f r))
      · clear hblocks
        induction s using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih =>
          simp only [Finset.sum_insert ha]
          exact (hs a).add ih
      · exact (l2_summable_sq f).mul_left _
    _ = _ := by rw [tsum_mul_left,←l2_norm_sq]

end KLSBelow25.GradedHilbert
end
#print axioms KLSBelow25.GradedHilbert.weighted_joint_adjoint_observation_le_of_blocks
