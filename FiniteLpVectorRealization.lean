import TensorMaximalHodgeCoercivity
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! The actual isometric realization of a finite family of scalar L²
classes as one Euclidean-valued L² class, for simultaneous a.e. limits. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter
open scoped Topology BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {μ : Measure α}

abbrev FiniteScalarLp (ι : Type*) [Fintype ι] (μ : Measure α) :=
  PiLp 2 (fun _ : ι => Lp ℝ 2 μ)

def finiteLpVectorFunction (F : FiniteScalarLp ι μ) (x : α) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => F i x)

lemma finiteLpVectorFunction_memLp (F : FiniteScalarLp ι μ) :
    MemLp (finiteLpVectorFunction F) 2 μ :=
  MemLp.of_eval_piLp (fun i => Lp.memLp (F i))

def finiteLpVector (F : FiniteScalarLp ι μ) : Lp (EuclideanSpace ℝ ι) 2 μ :=
  (finiteLpVectorFunction_memLp F).toLp (finiteLpVectorFunction F)

lemma finiteLpVector_ae (F : FiniteScalarLp ι μ) :
    (finiteLpVector F : α → EuclideanSpace ℝ ι)=ᵐ[μ] finiteLpVectorFunction F :=
  (finiteLpVectorFunction_memLp F).coeFn_toLp

lemma finiteLpVector_add (F G : FiniteScalarLp ι μ) :
    finiteLpVector (F+G)=finiteLpVector F+finiteLpVector G := by
  apply Lp.ext
  have hs : ∀ᵐ x ∂μ, ∀ i, (F i+G i) x=F i x+G i x :=
    ae_all_iff.mpr (fun i => Lp.coeFn_add (F i) (G i))
  filter_upwards [finiteLpVector_ae (F+G),finiteLpVector_ae F,finiteLpVector_ae G,
    Lp.coeFn_add (finiteLpVector F) (finiteLpVector G),hs] with x hfg hf hg hadd hsx
  rw [hfg,hadd]
  change finiteLpVectorFunction (F+G) x=finiteLpVector F x+finiteLpVector G x
  rw [hf,hg]
  apply PiLp.ext
  intro i
  exact hsx i

lemma finiteLpVector_smul (c : ℝ) (F : FiniteScalarLp ι μ) :
    finiteLpVector (c • F)=c • finiteLpVector F := by
  apply Lp.ext
  have hs : ∀ᵐ x ∂μ, ∀ i, (c • F i) x=c • F i x :=
    ae_all_iff.mpr (fun i => Lp.coeFn_smul c (F i))
  filter_upwards [finiteLpVector_ae (c • F),finiteLpVector_ae F,
    Lp.coeFn_smul c (finiteLpVector F),hs] with x hcf hf hsmul hsx
  rw [hcf,hsmul]
  change finiteLpVectorFunction (c • F) x=c • finiteLpVector F x
  rw [hf]
  apply PiLp.ext
  intro i
  exact hsx i

lemma finiteLpVector_norm_sq (F : FiniteScalarLp ι μ) :
    ‖finiteLpVector F‖^2=‖F‖^2 := by
  have hsq (i : ι) : Integrable (fun x => (F i x)^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs] using
      (Lp.memLp (F i)).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hi (i : ι) : ‖F i‖^2=∫ x, (F i x)^2 ∂μ := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [RCLike.inner_apply,conj_trivial,pow_two]
  rw [←real_inner_self_eq_norm_sq,L2.inner_def,PiLp.norm_sq_eq_of_L2]
  simp_rw [hi]
  rw [←integral_finsetSum Finset.univ (fun i _ => hsq i)]
  apply integral_congr_ae
  filter_upwards [finiteLpVector_ae F] with x hx
  rw [hx,PiLp.inner_apply]
  simp only [finiteLpVectorFunction,PiLp.toLp_apply,RCLike.inner_apply,conj_trivial,pow_two]

def finiteLpVectorLinearIsometry : FiniteScalarLp ι μ →ₗᵢ[ℝ] Lp (EuclideanSpace ℝ ι) 2 μ where
  toFun := finiteLpVector
  map_add' := finiteLpVector_add
  map_smul' := finiteLpVector_smul
  norm_map' F := by
    change ‖finiteLpVector F‖=‖F‖
    nlinarith [finiteLpVector_norm_sq F,norm_nonneg (finiteLpVector F),norm_nonneg F]

/-- A norm-convergent finite scalar L² family has one common subsequence
converging in every literal coordinate almost everywhere. -/
theorem finiteLp_exists_subsequence_ae
    {F : ℕ → FiniteScalarLp ι μ} {f : FiniteScalarLp ι μ}
    (ht : Tendsto F atTop (𝓝 f)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ᵐ x ∂μ, ∀ i,
      Tendsto (fun k => F (s k) i x) atTop (𝓝 (f i x)) := by
  have hv : Tendsto (fun k => finiteLpVector (F k)) atTop (𝓝 (finiteLpVector f)) :=
    finiteLpVectorLinearIsometry.continuous.continuousAt.tendsto.comp ht
  obtain ⟨s,hs,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ k, finiteLpVector (F (s k)) x=finiteLpVectorFunction (F (s k)) x :=
    ae_all_iff.mpr (fun k => finiteLpVector_ae (F (s k)))
  refine ⟨s,hs,?_⟩
  filter_upwards [hae,hall,finiteLpVector_ae f] with x hx hallx hfx
  intro i
  have h := (PiLp.proj 2 (fun _ : ι => ℝ) i : EuclideanSpace ℝ ι →L[ℝ] ℝ).continuous.continuousAt.tendsto.comp hx
  simp only [hallx,hfx] at h
  change Tendsto (fun k => F (s k) i x) atTop (𝓝 (f i x)) at h
  exact h

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.finiteLpVectorLinearIsometry
#print axioms KLS.DeterministicBridgeIntegration.finiteLp_exists_subsequence_ae
