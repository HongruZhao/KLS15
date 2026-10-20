import BoundaryApproximateEigenvectors
import ApproximateEigenObservation
import SpectralPowerEnvelope
import HilbertApproximateEigenLower
import Mathlib

/-! The concrete spectral part of manuscript Lemma 7.1, under its exact
scalar nonlinear quadratic comparison. This comparison is an explicit
hypothesis, not an axiom or an actual-law assertion. -/
noncomputable section
open Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal
namespace KLSBelow25
variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem observation_norm_convergent_subsequence (Q : H →L[ℂ] E) (v : ℕ → H)
    (hunit : ∀ n, ‖v n‖=1) :
    ∃ p ∈ Icc (0 : ℝ) ‖Q‖, ∃ f : ℕ → ℕ, StrictMono f ∧
      Tendsto (fun n => ‖Q (v (f n))‖) atTop (𝓝 p) := by
  have hbounded : ∀ n, ‖Q (v n)‖ ∈ Icc (0 : ℝ) ‖Q‖ := by
    intro n
    refine ⟨norm_nonneg _,?_⟩
    have hn := Q.le_opNorm (v n)
    simpa only [hunit n,mul_one] using hn
  simpa only [Function.comp_def] using isCompact_Icc.tendsto_subseq hbounded

theorem approximate_eigenvector_norm_tendsto (T : H →L[ℂ] H) (z : ℂ) (v : ℕ → H)
    (hunit : ∀ n, ‖v n‖=1)
    (hres : Tendsto (fun n => T (v n)-z • v n) atTop (𝓝 0)) :
    Tendsto (fun n => ‖T (v n)‖) atTop (𝓝 ‖z‖) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hzero : Tendsto (fun n => ‖T (v n)-z • v n‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hres.norm
  apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hzero
  simpa only [Real.dist_eq, norm_smul,hunit n,mul_one] using
    abs_norm_sub_norm_le (T (v n)) (z • v n)

theorem nonlinear_comparison_limit (T : H →L[ℂ] H) (Q : H →L[ℂ] E)
    (z : ℂ) (v : ℕ → H) {a p : ℝ} (ha : 0 < a)
    (hunit : ∀ n, ‖v n‖=1)
    (hres : Tendsto (fun n => T (v n)-z • v n) atTop (𝓝 0))
    (hplimit : Tendsto (fun n => ‖Q (v n)‖) atTop (𝓝 p))
    (hlower : ∀ n, ‖z‖ ≤ ‖ContinuousLinearMap.adjoint T (v n)‖+
      ‖T (v n)-z • v n‖)
    (hcomparison : ∀ x : H, ‖x‖=1 →
      ‖ContinuousLinearMap.adjoint T x‖^2 ≤
        (‖T x‖^2+‖Q x‖^2)/(1+a*(‖T x‖^2+‖Q x‖^2))) :
    ‖z‖^2 ≤ (‖z‖^2+p^2)/(1+a*(‖z‖^2+p^2)) := by
  have hT := approximate_eigenvector_norm_tendsto T z v hunit hres
  have he : Tendsto (fun n => ‖T (v n)-z • v n‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hres.norm
  let S : ℕ → ℝ := fun n => ‖T (v n)‖^2+‖Q (v n)‖^2
  have hS : Tendsto S atTop (𝓝 (‖z‖^2+p^2)) := hT.pow 2 |>.add (hplimit.pow 2)
  have hden : 0 < 1+a*(‖z‖^2+p^2) := by positivity
  have hfrac : Tendsto (fun n => S n/(1+a*S n)) atTop
      (𝓝 ((‖z‖^2+p^2)/(1+a*(‖z‖^2+p^2)))) :=
    hS.div (tendsto_const_nhds.add (hS.const_mul a)) (ne_of_gt hden)
  have hright : Tendsto (fun n => S n/(1+a*S n)+
      2*‖ContinuousLinearMap.adjoint T‖*‖T (v n)-z • v n‖+
      ‖T (v n)-z • v n‖^2) atTop
      (𝓝 ((‖z‖^2+p^2)/(1+a*(‖z‖^2+p^2)))) := by
    simpa only [mul_zero,zero_pow (by omega : 2 ≠ 0),add_zero] using
      (hfrac.add (he.const_mul (2*‖ContinuousLinearMap.adjoint T‖))).add (he.pow 2)
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds hright
  intro n
  have hbound := (ContinuousLinearMap.adjoint T).le_opNorm (v n)
  rw [hunit n,mul_one] at hbound
  have hsq := (sq_le_sq₀ (norm_nonneg z)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (hlower n)
  have hcomp := hcomparison (v n) (hunit n)
  have herror := mul_nonneg (norm_nonneg (T (v n)-z • v n)) (sub_nonneg.mpr hbound)
  dsimp [S]
  nlinarith

theorem spectralRadius_le_of_scalar_comparison (T : H →L[ℂ] H) (Q : H →L[ℂ] E)
    {a C K : ℝ} (ha : 0 < a) (hK : 0 < K) (m₀ : ℕ)
    (hcomparison : ∀ x : H, ‖x‖=1 →
      ‖ContinuousLinearMap.adjoint T x‖^2 ≤
        (‖T x‖^2+‖Q x‖^2)/(1+a*(‖T x‖^2+‖Q x‖^2)))
    (hobs : ∀ m, m₀ ≤ m → ‖Q.comp (T^m)‖^2 ≤ C*K^m) :
    spectralRadius ℂ T ≤ ENNReal.ofReal (Real.sqrt K) := by
  obtain ⟨z,hz,hzradius,v,hunit,hres⟩ := exists_maximal_modulus_approximate_eigenvectors T
  have hzsq : ‖z‖^2 ≤ K := by
    by_cases hz0 : ‖z‖=0
    · rw [hz0]
      simpa using hK.le
    have hzs : 0 < ‖z‖^2 := sq_pos_of_ne_zero hz0
    obtain ⟨p,hp,f,hf,hplimit⟩ := observation_norm_convergent_subsequence Q v hunit
    let w : ℕ → H := fun n => v (f n)
    have hwunit : ∀ n, ‖w n‖=1 := fun n => hunit (f n)
    have hwres : Tendsto (fun n => T (w n)-z • w n) atTop (𝓝 0) :=
      hres.comp hf.tendsto_atTop
    have hlimit := nonlinear_comparison_limit T Q z w ha hwunit hwres hplimit
      (fun n => adjoint_unit_residual_lower T z (w n) (hwunit n))
      hcomparison
    have hpmass := ApproximateEigenObservation.curvature_limit_positive ha hzs
      (sq_nonneg p) hlimit
    have hppos : 0 < p := by nlinarith [hp.1]
    exact ApproximateEigenObservation.approximate_eigenvalue_sq_le T Q z w p C K m₀
      hppos hK hwunit hwres hplimit hobs
  have hnorm : ‖z‖ ≤ Real.sqrt K := (Real.le_sqrt (norm_nonneg z) hK.le).mpr hzsq
  rw [← hzradius,← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hnorm

theorem power_envelope_of_scalar_comparison (T : H →L[ℂ] H) (Q : H →L[ℂ] E)
    {a C K : ℝ} (ha : 0 < a) (hK : 0 < K) (m₀ : ℕ)
    (hcomparison : ∀ x : H, ‖x‖=1 →
      ‖ContinuousLinearMap.adjoint T x‖^2 ≤
        (‖T x‖^2+‖Q x‖^2)/(1+a*(‖T x‖^2+‖Q x‖^2)))
    (hobs : ∀ m, m₀ ≤ m → ‖Q.comp (T^m)‖^2 ≤ C*K^m) :
    ∀ rho : ℝ, 1 < rho → ∃ M : ℝ, ∀ n : ℕ, ‖T^n‖^2 ≤ M*(K*rho)^n := by
  exact squared_power_envelope_of_spectralRadius_le T hK
    (spectralRadius_le_of_scalar_comparison T Q ha hK m₀ hcomparison hobs)

#print axioms spectralRadius_le_of_scalar_comparison
#print axioms power_envelope_of_scalar_comparison
end KLSBelow25
