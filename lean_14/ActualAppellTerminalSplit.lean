import ActualAppellRemainderBounds
import ActualAppellLinearDirection
import FullClassAppellStationarity

/-! The terminal cumulant in the genuine Appell drift is exactly the
linear-test coefficient. The remaining terms are precisely the lower-degree
subset contractions, with no change of normalization. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem actualAppellFirst_coordinate_projection
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (hiso : IsIsotropic μ) (f : Lp ℝ 2 μ) (i : Fin n) :
    actualAppellCoefficient μ f 1 (fun _ => i) = affineProjectionVector hiso f i := by
  rw [actualAppellCoefficient_one_of_isotropic hLC hiso (Lp.memLp f),
    show affineProjectionVector hiso f i = inner ℝ (isotropicAffineCoordinate hiso (some i)) f from rfl,
    inner_isotropicAffineCoordinate]
  apply integral_congr_ae (.of_forall fun x => ?_)
  simp only [affineCoordinateFunction,Option.elim_some]
  ring

 theorem fullClassAppellTensor_one_norm_sq
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (hiso : IsIsotropic μ) (f : Lp ℝ 2 μ) :
    ‖fullClassAppellTensor 1 f‖^2 = ‖affineProjectionVector hiso f‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  change (∑ a : Fin 1 → Fin n, (actualAppellCoefficient μ f 1 a)^2) = _
  have he (a : Fin 1 → Fin n) : a = fun _ => a 0 := by funext j; exact congrArg a (Subsingleton.elim j 0)
  have hc (a : Fin 1 → Fin n) : actualAppellCoefficient μ f 1 a = affineProjectionVector hiso f (a 0) := by
    rw [he a]
    exact actualAppellFirst_coordinate_projection hLC hiso f (a 0)
  simp_rw [hc]
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)) _ _ (fun _ => rfl)

 theorem fullClassAppellTensor_one_norm_sq_le
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (hiso : IsIsotropic μ) (f : Lp ℝ 2 μ) :
    ‖fullClassAppellTensor 1 f‖^2 ≤ ‖f‖^2 := by
  rw [fullClassAppellTensor_one_norm_sq hLC hiso]
  exact affineProjectionVector_norm_sq_le_full hiso f

 theorem actualSubsetAppellContraction_univ
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (hiso : IsIsotropic μ) (f : Lp ℝ 2 μ) (d : ℕ) (a : Fin d → Fin n) :
    actualSubsetAppellContraction μ f d Finset.univ a =
      actualAppellCoefficient μ (fun x => inner ℝ x (affineProjectionVector hiso f)) d a := by
  classical
  obtain ⟨r,hr,hD,h1⟩ := exists_common_local_exponential_domains hLC (Lp.memLp f)
  have hA := contDiffOn_actualDampedAverage hD h1 (show (0 : ℝ) ≤ 0 from le_rfl)
  have h0 : (0 : Space n) ∈ ball 0 r := by simpa using hr
  rw [actualAppellCoefficient_inner_eq_cumulant hLC,cumulantTensor_snoc_coordinate_sum]
  unfold actualSubsetAppellContraction
  simp only [Finset.mem_univ,decide_true,Bool.not_true,maskedDirections_all,
    maskedDirections_none,List.nil_append]
  apply Finset.sum_congr rfl
  intro i hi
  have hc : listCumulant μ (List.ofFn (fun j => EuclideanSpace.single (a j) 1)++
      [EuclideanSpace.single i 1]) = cumulantTensor μ (d+1)
      (Fin.snoc (fun j => EuclideanSpace.single (a j) 1) (EuclideanSpace.single i 1)) := by
    rw [listCumulant_eq_local_word hLC]
    have hh := local_word_ofFn isOpen_ball (contDiffOn_logLaplace_of_local h1)
      (Fin.snoc (fun j => EuclideanSpace.single (a j) 1) (EuclideanSpace.single i 1)) h0
    simpa only [List.ofFn_succ_last,Fin.snoc_castSucc,Fin.snoc_last,cumulantTensor] using hh
  have ha : directionalWordDerivative (actualDampedAverage μ f 0) [EuclideanSpace.single i 1] 0 =
      affineProjectionVector hiso f i := by
    rw [actualDampedAverage_zero_eq_tilt_average]
    have hh := actualAppellFirst_coordinate_projection hLC hiso f i
    simpa only [actualAppellCoefficient,iteratedFDeriv_one_apply,
      directionalWordDerivative_cons,directionalWordDerivative_nil,EuclideanSpace.basisFun_apply] using hh
  rw [hc,ha]
  simp only [EuclideanSpace.basisFun_apply]
  ring

 theorem actualAppellLowerDriftTensor_terminal_split
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (hiso : IsIsotropic μ) (f : Lp ℝ 2 μ) {d : ℕ} (hd : 2 ≤ d) :
    actualAppellLowerDriftTensor μ f d =
      actualAppellCoefficient μ (fun x => inner ℝ x (affineProjectionVector hiso f)) d+
        actualAppellProperRemainder μ f d := by
  classical
  funext a
  change (∑ S : Finset (Fin d), if 2 ≤ S.card then actualSubsetAppellContraction μ f d S a else 0) = _
  have he (S : Finset (Fin d)) :
      (if 2 ≤ S.card then actualSubsetAppellContraction μ f d S a else 0) =
      (if S=Finset.univ then actualSubsetAppellContraction μ f d Finset.univ a else 0)+
      (if 2 ≤ S.card ∧ S.card ≤ d-1 then actualSubsetAppellContraction μ f d S a else 0) := by
    by_cases hS : S=Finset.univ
    · subst S
      simp only [Finset.card_univ,Fintype.card_fin,hd,ite_true]
      have hn : ¬ d ≤ d-1 := by omega
      simp [hn]
    · have hlt : S.card < d := by
        have hle : S.card ≤ d := by simpa using Finset.card_le_univ S
        have hne : S.card ≠ d := by
          intro hh
          apply hS
          exact Finset.eq_univ_of_card S (by simpa using hh)
        omega
      by_cases hp : 2 ≤ S.card <;> simp [hS,hp,show S.card ≤ d-1 by omega]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [actualSubsetAppellContraction_univ hLC hiso]
  simp only [Pi.add_apply,actualAppellProperRemainder,Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  split_ifs <;> rfl

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualAppellLowerDriftTensor_terminal_split
#print axioms KLS.DeterministicBridgeIntegration.fullClassAppellTensor_one_norm_sq_le
