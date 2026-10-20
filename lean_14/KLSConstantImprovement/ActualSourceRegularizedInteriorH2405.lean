import KLSConstantImprovement.ActualSourceRegularizedLocalEquation405
import EllipticPdes.Regularity.Localise.LocalOp
import EllipticPdes.Regularity.Local.InteriorH2
import EllipticPdes.Embedding.GagliardoNirenberg

/-!
Local second weak derivatives of the actual regularized scalar inverse.
Only the metric is regularized. The unchanged source density is C1, so
exp(-phi) J is a C1 principal coefficient. A compact coefficient blend
pays the bounded global hypotheses of the retained interior H2 theorem.
No classical representative or second-order domain is assumed.
-/
noncomputable section
open MeasureTheory Set Filter Matrix Metric InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceRegularizedInteriorH2405
open KLS ActualBoundedCanonicalSource ActualSourceMetricRegularization405
open ActualSourceInverseMetricRegularization405 ActualSourceRegularizedEnergyForm405
open ActualSourceRegularizedLocalEquation405
open EllipticPdes.Sobolev EllipticPdes.Embedding EllipticPdes.Regularity
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_regularizedDensity_principal (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ P : PrincipalOn n (ball (0 : Space n) R) 1,
      P.a = regularizedDensityCoefficient d k ε := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Space n) R).bddAbove_image
    d.source_C1.continuous.continuousOn
  let c : ℝ := (4 / d.targetConvexityConstant + ε)⁻¹
  have hc : 0 < c := by
    have hκ := d.target_convexity_pos
    dsimp [c]
    positivity
  refine ⟨{
    a := regularizedDensityCoefficient d k ε
    lam := Real.exp (-M) * c
    lam_pos := mul_pos (Real.exp_pos _) hc
    contDiffOn := fun i j => (regularizedDensityCoefficient_contDiff d k hε i j).contDiffOn
    elliptic := ?_
  }, rfl⟩
  filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx a
  have hρ : Real.exp (-M) ≤ Real.exp (-d.potential x) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (hM (mem_image_of_mem _ (ball_subset_closedBall hx)))
  have hq : c * ∑ i : Fin n, (a i)^2 ≤
      ∑ i : Fin n, ∑ j : Fin n, regularizedMetricInverse d k ε x i j * a i * a j := by
    have h := (regularizedMetricInverse_quadratic_bounds d k hε x a).1
    rw [← matrix_quadratic_sum_eq_dotProduct] at h
    simpa only [c, dotProduct, pow_two] using h
  have hq0 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      regularizedMetricInverse d k ε x i j * a i * a j :=
    (mul_nonneg hc.le (Finset.sum_nonneg (s := Finset.univ)
      (f := fun i : Fin n => (a i)^2) (fun i _ => sq_nonneg (a i)))).trans hq
  calc
    (Real.exp (-M) * c) * ∑ i : Fin n, (a i)^2 =
        Real.exp (-M) * (c * ∑ i : Fin n, (a i)^2) := by ring
    _ ≤ Real.exp (-M) * (∑ i : Fin n, ∑ j : Fin n,
        regularizedMetricInverse d k ε x i j * a i * a j) :=
      mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
    _ ≤ Real.exp (-d.potential x) * (∑ i : Fin n, ∑ j : Fin n,
        regularizedMetricInverse d k ε x i j * a i * a j) :=
      mul_le_mul_of_nonneg_right hρ hq0
    _ = ∑ i : Fin n, ∑ j : Fin n, regularizedDensityCoefficient d k ε x i j * a i * a j := by
      simp only [regularizedDensityCoefficient, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The actual density coefficient has a globally bounded C1 elliptic
extension around every compact set, with zero lower-order coefficients. -/
theorem exists_regularizedDensity_localOp (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) {E : Set (Space n)} (hE : IsCompact E) :
    ∃ (Ω : Set (Space n)) (Op : FullEllipticOp n), IsOpen Ω ∧ E ⊆ Ω ∧
      IsCompact (closure Ω) ∧ Nonempty (IsC1Coeff Op.toEllipticCoeff) ∧
      (∀ x ∈ Ω, Op.a x = regularizedDensityCoefficient d k ε x) ∧
      (∀ x, Op.b x = 0) ∧ (∀ x, Op.c x = 0) := by
  obtain ⟨R, _, hER⟩ := hE.isBounded.subset_ball_lt 0 (0 : Space n)
  obtain ⟨P, hPa⟩ := exists_regularizedDensity_principal d k hε R
  obtain ⟨χ, hχ, hχ01, Ω, hΩo, hEΩ, hclΩ, hΩ1⟩ :=
    exists_cutoff_interior_one isOpen_ball hE hER
  let Op : FullEllipticOp n := blendOp P isOpen_ball hχ hχ01
    (fun _ _ => 0) (fun _ => 0) (Bs := 0) (Cs := 0) le_rfl le_rfl
    (fun _ => measurable_const) measurable_const
    (fun _ => Eventually.of_forall fun _ => by simp)
    (Eventually.of_forall fun _ => by simp)
  obtain ⟨hC⟩ := P.nonempty_isCkCoeff isOpen_ball hχ Op.toEllipticCoeff rfl (k := 1) le_rfl
  refine ⟨Ω, Op, hΩo, hEΩ, hχ.2.1.of_isClosed_subset isClosed_closure hclΩ,
    ⟨hC.toIsC1Coeff le_rfl⟩, ?_, (fun _ => rfl), (fun _ => rfl)⟩
  intro x hx
  funext i j
  change P.aT χ x i j = regularizedDensityCoefficient d k ε x i j
  rw [P.aT_eq_of_eq_one (hΩ1 x hx), hPa]

/-- Every ordinary gradient coordinate of the actual inverse has an
actual L2 weak derivative on each compact region. This theorem assumes
only the natural L2 forcing and its mean-zero normalization. -/
theorem regularizedOrdinaryInverse_local_second_weak_derivative
    (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ) {ε : ℝ} (hε : 0 < ε)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    {E : Set (Space n)} (hE : IsCompact E) (i j : Fin n) :
    ∃ w : Lp ℝ 2 (volume.restrict E), ∀ ψ : Space n → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ E →
      (∫ x in E, weightedH1Derivative d.potential i
        (regularizedOrdinaryInverse d hn k hε g) x * coordinateDerivative ψ j x) =
        -(∫ x in E, w x * ψ x) := by
  cases n with
  | zero => omega
  | succ m =>
    let U := regularizedOrdinaryInverse d hn k hε g
    obtain ⟨Ω, Op, hΩo, hEΩ, hΩc, ⟨hC1⟩, hA, hb, hc⟩ :=
      exists_regularizedDensity_localOp d k hε hE
    have hu : MemLp (weightedH1Value d.potential U) 2 (volume.restrict Ω) :=
      (weightedH1Value_memLp_restrict d.source_C1.continuous U hΩc).mono_measure
        (Measure.restrict_mono_set volume subset_closure)
    have hp (a : Fin (m + 1)) : MemLp (weightedH1Derivative d.potential a U)
        2 (volume.restrict Ω) :=
      (weightedH1Derivative_memLp_restrict d.source_C1.continuous U a hΩc).mono_measure
        (Measure.restrict_mono_set volume subset_closure)
    have hf : MemLp (fun x => Real.exp (-d.potential x) * g x) 2 (volume.restrict Ω) :=
      (regularizedDensityForcing_local_L2 d g hΩc).mono_measure
        (Measure.restrict_mono_set volume subset_closure)
    have hwg : HasWeakGradOn Ω (weightedH1Value d.potential U)
        (fun a => weightedH1Derivative d.potential a U) :=
      HasWeakGradOn.mono (subset_univ Ω) (regularizedOrdinaryInverse_hasWeakGradOn d hn k hε g)
    have hsol : LocalWeakSol Ω Op.a Op.b Op.c (fun x => Real.exp (-d.potential x) * g x)
        (weightedH1Value d.potential U) (fun a => weightedH1Derivative d.potential a U) := by
      apply LocalWeakSol.congr hΩo.measurableSet
        (fun x hx => (hA x hx).symm) (fun x _ => (hb x).symm) (fun x _ => (hc x).symm)
        (fun _ _ => rfl)
      exact LocalWeakSol.mono (subset_univ Ω)
        (regularizedOrdinaryInverse_localWeakSol d hn k hε g hg)
    let W : H1amb Ω := WithLp.toLp 2 (Fin.cons
      (hu.toLp (weightedH1Value d.potential U))
      (fun a => (hp a).toLp (weightedH1Derivative d.potential a U)))
    have hW : IsLocalWeakSolution Op Ω W (hf.toLp (fun x => Real.exp (-d.potential x) * g x)) :=
      isLocalWeakSolution_of_localWeakSol Op hu hp hf hwg hsol
    obtain ⟨_, _, hH2⟩ := interior_H2_estimate_W12 Op hΩo hC1 hE hEΩ
    obtain ⟨w, hw, _⟩ := hH2 W (hf.toLp (fun x => Real.exp (-d.potential x) * g x)) hW j i
    refine ⟨w, ?_⟩
    intro ψ hψ hψc hψE
    have he := hw ψ hψ hψc hψE
    have hrep : (restrictL2 (Ω := E) (extendL2 hΩo.measurableSet (W i.succ)) : Space (m + 1) → ℝ)
        =ᵐ[volume.restrict E] weightedH1Derivative d.potential i U := by
      apply (coeFn_restrictL2_extendL2_of_subset hΩo.measurableSet hE.measurableSet hEΩ (W i.succ)).trans
      have hpE := ae_restrict_of_ae_restrict_of_subset hEΩ (hp i).coeFn_toLp
      exact hpE
    have hl : (∫ x in E, restrictL2 (Ω := E)
        (extendL2 hΩo.measurableSet (W i.succ)) x * partialD j ψ x) =
        ∫ x in E, weightedH1Derivative d.potential i U x * coordinateDerivative ψ j x := by
      exact integral_congr_ae (hrep.fun_mul EventuallyEq.rfl)
    rwa [hl] at he

end KLSConstantImprovement.ActualSourceRegularizedInteriorH2405
#print axioms KLSConstantImprovement.ActualSourceRegularizedInteriorH2405.exists_regularizedDensity_principal
#print axioms KLSConstantImprovement.ActualSourceRegularizedInteriorH2405.exists_regularizedDensity_localOp
#print axioms KLSConstantImprovement.ActualSourceRegularizedInteriorH2405.regularizedOrdinaryInverse_local_second_weak_derivative
