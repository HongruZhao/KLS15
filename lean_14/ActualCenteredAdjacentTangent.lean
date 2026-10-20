import ActualJointTangentL2Bound
import ActualWeightedAppellCentering

/-! The genuine attained adjacent-energy quotient supports every original law,
and its constant invariance improves the supporting mass to actual variance. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25 KLS.TensorEnergy
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

 theorem actual_joint_all_law_tangent_bound {n k : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) {h : ℝ} (hh : 0 < h)
    (hunit : ‖f‖=1) {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ (Icc 0 1) φ)
    (hφpos : ∀ u ∈ Icc (0 : ℝ) 1, 0 < φ u)
    (hprevious : ∀ (ν : Measure (Space n)), admissibleMeasure ν → ∀ g : Space n → ℝ,
      MemLp g 2 ν → actualAppellEnergy ν g k ≤ h*(∫ x, (g x)^2 ∂ν))
    {d : ℝ} (hd : HasDerivAt φ d (‖fullClassAppellTensor k f‖^2/h))
    (hmax : ∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν:Measure (Space n)))
      (g : Lp ℝ 2 (ν:Measure (Space n))),
      coefficientQuotient (fullClassAppellLinearMap hν.logConcave k)
        (fullClassAppellLinearMap hν.logConcave (k+1)) h φ g ≤
      coefficientQuotient (fullClassAppellLinearMap hμ.logConcave k)
        (fullClassAppellLinearMap hμ.logConcave (k+1)) h φ f) :
    let X := ‖fullClassAppellTensor (k+1) f‖^2
    let u := ‖fullClassAppellTensor k f‖^2/h
    let w := -(X/φ u)*(d/h)
    let lam := (X/φ u)*(φ u-u*d)
    ∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν:Measure (Space n)))
      (g : Lp ℝ 2 (ν:Measure (Space n))),
      ‖fullClassAppellTensor (k+1) g‖^2+w*‖fullClassAppellTensor k g‖^2 ≤ lam*‖g‖^2 := by
  dsimp only
  let X := ‖fullClassAppellTensor (k+1) f‖^2
  let u := ‖fullClassAppellTensor k f‖^2/h
  let w := -(X/φ u)*(d/h)
  let lam := (X/φ u)*(φ u-u*d)
  have hf : f ≠ 0 := by
    intro he
    simp only [he,norm_zero] at hunit
    norm_num at hunit
  have hu : u ∈ Icc (0 : ℝ) 1 := by
    simpa only [hunit,one_pow,mul_one] using actualAppell_ratio_mem_Icc hμ hh hprevious f hf
  intro ν hν g
  by_cases hg : g=0
  · have hzj : fullClassAppellTensor (k+1) (0 : Lp ℝ 2 (ν:Measure (Space n)))=0 :=
      (fullClassAppellLinearMap hν.logConcave (k+1)).map_zero
    have hzk : fullClassAppellTensor k (0 : Lp ℝ 2 (ν:Measure (Space n)))=0 :=
      (fullClassAppellLinearMap hν.logConcave k).map_zero
    simp only [hg,hzj,hzk,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,add_zero,le_refl]
  have hratio := actualAppell_ratio_mem_Icc hν hh hprevious g hg
  have hm := hmax ν hν g
  unfold coefficientQuotient at hm
  change ‖fullClassAppellTensor (k+1) g‖^2/
    (‖g‖^2*φ (‖fullClassAppellTensor k g‖^2/(h*‖g‖^2))) ≤
    X/(‖f‖^2*φ (‖fullClassAppellTensor k f‖^2/(h*‖f‖^2))) at hm
  rw [hunit,one_pow,mul_one,one_mul] at hm
  have hb := concave_quotient_tangent_bound hφ hφpos hu hratio hd hh
    (sq_pos_of_pos (norm_pos_iff.mpr hg)) (sq_nonneg ‖fullClassAppellTensor (k+1) f‖) hm
  change ‖fullClassAppellTensor (k+1) g‖^2+w*‖fullClassAppellTensor k g‖^2 ≤ lam*‖g‖^2
  dsimp only [w,lam] at ⊢
  linarith

theorem actualAppellEnergy_sub_const {n d : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (c : ℝ) (hd : d≠0) :
    actualAppellEnergy μ (fun x => f x-c) d=actualAppellEnergy μ f d := by
  unfold actualAppellEnergy
  apply Finset.sum_congr rfl
  intro a ha
  rw [actualAppellCoefficient_sub_const hLC hf c hd]

theorem actual_two_rank_global_variance_bound {n k j : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ) (hk : k≠0) (hj : j≠0)
    (w lam : ℝ)
    (hglobal : ∀ g : Lp ℝ 2 μ,actualAppellEnergy μ g j+w*actualAppellEnergy μ g k≤lam*‖g‖^2)
    (f : Lp ℝ 2 μ) :
    actualAppellEnergy μ f j+w*actualAppellEnergy μ f k≤
      lam*(‖f‖^2-(∫ x,f x ∂μ)^2) := by
  have he (d : ℕ) (hd : d≠0) : actualAppellEnergy μ (CenteredL2.center μ f) d=
      actualAppellEnergy μ f d := by
    rw [actualAppellEnergy_congr_ae (CenteredL2.center_ae μ f)]
    exact actualAppellEnergy_sub_const hLC (Lp.memLp f) _ hd
  have hb := hglobal (CenteredL2.center μ f)
  rw [he j hj,he k hk,CenteredL2.norm_center_sq] at hb
  exact hb


theorem actual_two_rank_tilt_family_variance_bound {n k j : ℕ}
    {μ : ProbabilityMeasure (Space n)} (hμ : admissibleMeasure (μ : Measure (Space n)))
    (hk : k≠0) (hj : j≠0) (p : MvPolynomial (Fin n) ℝ) (w lam : ℝ)
    (hglobal : ∀ (ν : ProbabilityMeasure (Space n)) (hν : admissibleMeasure (ν : Measure (Space n)))
      (g : Lp ℝ 2 (ν : Measure (Space n))),
      actualAppellEnergy (ν : Measure (Space n)) g j+w*actualAppellEnergy (ν : Measure (Space n)) g k
        ≤lam*‖g‖^2) :
    ∃ r : ℝ, 0<r ∧ ∀ z : Space n, ‖z‖ ≤ r → ∀ s : ℝ, 0 ≤ s →
      actualCovarianceAppellEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
        (polynomialEval p) j+w*actualCovarianceAppellEnergy
          (actualDampedTiltLaw (μ : Measure (Space n)) z s) (polynomialEval p) k ≤
      lam*((∫ x, (polynomialEval p x)^2 ∂actualDampedTiltLaw (μ : Measure (Space n)) z s)-
        actualCovarianceAppellEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
          (polynomialEval p) 0) := by
  obtain ⟨r,hr,hfamily⟩ := exists_local_actual_damped_whitening hμ
  refine ⟨r,hr,?_⟩
  intro z hz s hs
  obtain ⟨hprob,hsupp,hpos,hadm⟩ := hfamily z hz s hs
  letI : IsProbabilityMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s) := hprob
  have hLC := actualDampedTiltLaw_logConcave hμ z hs
  have hf := polynomialEval_memLp_two hLC p
  let ν : ProbabilityMeasure (Space n) := ⟨_,hadm.isProb⟩
  let g := (actual_whitening_test_memLp hpos hf).toLp
    (fun y => polynomialEval p ((actualWhiteningEquiv
      (actualDampedTiltLaw (μ : Measure (Space n)) z s) hpos).symm y))
  have hg : (g : Space n → ℝ) =ᵐ[whitenedMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s)]
      fun y => polynomialEval p ((actualWhiteningEquiv
        (actualDampedTiltLaw (μ : Measure (Space n)) z s) hpos).symm y) :=
    (actual_whitening_test_memLp hpos hf).coeFn_toLp
  have hn : ‖g‖^2=∫ x, (polynomialEval p x)^2 ∂actualDampedTiltLaw (μ : Measure (Space n)) z s := by
    rw [actualLp_norm_sq_eq_integral]
    calc
      _ = ∫ y, (polynomialEval p ((actualWhiteningEquiv
          (actualDampedTiltLaw (μ : Measure (Space n)) z s) hpos).symm y))^2
          ∂whitenedMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s) :=
        integral_congr_ae (hg.fun_comp (fun t : ℝ => t^2))
      _ = _ := actual_whitening_test_L2_energy _ hpos _
  have hmean : (∫ x,g x ∂whitenedMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s))^2 =
      actualCovarianceAppellEnergy (actualDampedTiltLaw (μ : Measure (Space n)) z s)
        (polynomialEval p) 0 := by
    rw [←actualCovarianceAppellEnergy_zero_eq_mean_sq,
      actualCovarianceAppellEnergy_isotropic hadm.isotropic,
      actualAppellEnergy_congr_ae hg,actualAppellEnergy_whitening hLC hpos hf]
  have hm := actual_two_rank_global_variance_bound hadm.logConcave hk hj w lam (hglobal ν hadm) g
  change actualAppellEnergy (whitenedMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s)) g j+
      w*actualAppellEnergy (whitenedMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s)) g k ≤
      lam*(‖g‖^2-(∫ x,g x ∂whitenedMeasure (actualDampedTiltLaw (μ : Measure (Space n)) z s))^2) at hm
  rw [actualAppellEnergy_congr_ae hg,actualAppellEnergy_whitening hLC hpos hf,
    actualAppellEnergy_congr_ae hg,actualAppellEnergy_whitening hLC hpos hf,hn,hmean] at hm
  exact hm

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_joint_all_law_tangent_bound

#print axioms KLS.DeterministicBridgeNext.actual_two_rank_tilt_family_variance_bound
