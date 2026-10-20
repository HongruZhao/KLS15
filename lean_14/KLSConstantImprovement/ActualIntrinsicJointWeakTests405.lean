import KLSConstantImprovement.ActualLocalWeakVectorChain405
import KLSConstantImprovement.ActualSmoothScalarTruncation405
import KLSConstantImprovement.ActualBoundedSourceCalculus
import KLSConstantImprovement.ActualSourceRawHessianEvolution405
import KLSConstantImprovement.ActualBoundedRawMetricDomain
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Actual joint (u,H) intrinsic matrix tests. Positive square-root
regularization makes the denominator smooth even off the positive cone.
A concrete compact cutoff in all joint variables makes the function globally
Lipschitz, so the genuine multivariate weak chain rule applies to the actual
raw derivatives Du and N. No classical derivative of H is substituted for N.
This file supplies fixed-parameter tests; it asserts no uniform limit bound. -/
noncomputable section
open MeasureTheory Set Filter Matrix Metric
open scoped BigOperators Topology ContDiff ENNReal NNReal
namespace KLSConstantImprovement.ActualIntrinsicJointWeakTests405
open KLS ActualBoundedCanonicalSource ActualLocalWeakVectorChain405
open ActualVectorDifferential405 ActualSmoothScalarTruncation405
open ActualBoundedRawMetricDomain ActualSourceRawHessianEvolution405 ActualSourceHessianEvolution405
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

abbrev JointIndex (n : ℕ) := Sum (Fin n) (Fin n × Fin n)

def jointMass (v : JointIndex n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, v (.inl i) * v (.inr (i,j)) * v (.inl j)

def jointBump (k : ℕ) (v : JointIndex n → ℝ) : ℝ :=
  ∏ a : JointIndex n, scalarBump (cutoffScale k * v a)

theorem jointBump_contDiff (k : ℕ) : ContDiff ℝ 1 (jointBump (n := n) k) := by
  unfold jointBump
  apply contDiff_prod
  intro a _
  exact scalarBump.contDiff.comp (contDiff_const.mul (contDiff_apply ℝ ℝ a))

theorem jointBump_compact (k : ℕ) : HasCompactSupport (jointBump (n := n) k) := by
  apply (isCompact_closedBall (0 : JointIndex n → ℝ) (2 / cutoffScale k)).of_isClosed_subset
    (isClosed_tsupport _)
  apply closure_minimal _ isClosed_closedBall
  intro v hv
  change ‖v - 0‖ ≤ 2 / cutoffScale k
  rw [sub_zero]
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (by norm_num) (cutoffScale_pos k).le : 0 ≤ 2 / cutoffScale k)).mpr
  intro a
  have hprod : jointBump k v ≠ 0 := hv
  change (∏ a : JointIndex n, scalarBump (cutoffScale k * v a)) ≠ 0 at hprod
  have ha : scalarBump (cutoffScale k * v a) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod) a (Finset.mem_univ a)
  have hn : ‖cutoffScale k * v a‖ < 2 := by
    by_contra h
    apply ha
    apply scalarBump.zero_of_le_dist
    simpa only [scalarBump, dist_zero_right] using le_of_not_gt h
  rw [norm_mul, Real.norm_of_nonneg (cutoffScale_pos k).le] at hn
  exact (le_div_iff₀ (cutoffScale_pos k)).mpr (by nlinarith)

def intrinsicJointDenom (δ ε : ℝ) (v : JointIndex n → ℝ) : ℝ :=
  1 + δ * Real.sqrt (jointMass v ^ 2 + ε ^ 2)

def intrinsicJointMatrixEntry (δ ε : ℝ) (k : ℕ) (i j : Fin n)
    (v : JointIndex n → ℝ) : ℝ :=
  jointBump k v * (v (.inl i) * v (.inl j) / intrinsicJointDenom δ ε v)

theorem intrinsicJointDenom_positive {δ ε : ℝ} (hδ : 0 ≤ δ)
    (v : JointIndex n → ℝ) : 0 < intrinsicJointDenom δ ε v := by
  unfold intrinsicJointDenom
  positivity

theorem intrinsicJointMatrixEntry_contDiff {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε)
    (k : ℕ) (i j : Fin n) : ContDiff ℝ 1 (intrinsicJointMatrixEntry δ ε k i j) := by
  have hm : ContDiff ℝ 1 (jointMass : (JointIndex n → ℝ) → ℝ) := by
    unfold jointMass
    fun_prop
  have hr : ContDiff ℝ 1 (fun v : JointIndex n → ℝ => Real.sqrt (jointMass v ^ 2 + ε ^ 2)) :=
    ((hm.pow 2).add contDiff_const).sqrt (fun v => by nlinarith [sq_nonneg (jointMass v)])
  have hd : ContDiff ℝ 1 (intrinsicJointDenom δ ε : (JointIndex n → ℝ) → ℝ) :=
    contDiff_const.add (contDiff_const.mul hr)
  exact (jointBump_contDiff k).mul
    (((contDiff_apply ℝ ℝ (.inl i)).mul (contDiff_apply ℝ ℝ (.inl j))).div hd
      (fun v => (intrinsicJointDenom_positive hδ v).ne'))

theorem intrinsicJointMatrixEntry_compact (δ ε : ℝ) (k : ℕ) (i j : Fin n) :
    HasCompactSupport (intrinsicJointMatrixEntry δ ε k i j) :=
  (jointBump_compact k).mul_right

theorem intrinsicJointMatrixEntry_lipschitz {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε)
    (k : ℕ) (i j : Fin n) :
    ∃ L : ℝ≥0, LipschitzWith L (intrinsicJointMatrixEntry δ ε k i j) :=
  ContDiff.lipschitzWith_of_hasCompactSupport (intrinsicJointMatrixEntry_compact δ ε k i j)
    (intrinsicJointMatrixEntry_contDiff hδ hε k i j) (by norm_num)

def sourceJointValue (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (a : JointIndex n) (x : Space n) : ℝ :=
  Sum.elim (fun i => u i x) (fun ij => coordinateHessian d.potential x ij.1 ij.2) a

def sourceJointDerivative (d : SourceData μ) (Du : Fin n → Fin n → Space n → ℝ)
    (a : JointIndex n) (b : Fin n) (x : Space n) : ℝ :=
  Sum.elim (fun i => Du i b x) (fun ij => d.third x b ij.1 ij.2) a

def intrinsicSourceTest (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (δ ε : ℝ) (k : ℕ) (i j : Fin n) (x : Space n) : ℝ :=
  intrinsicJointMatrixEntry δ ε k i j (fun a => sourceJointValue d u a x)

def intrinsicSourceDerivative (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (Du : Fin n → Fin n → Space n → ℝ) (δ ε : ℝ) (k : ℕ)
    (i j b : Fin n) (x : Space n) : ℝ :=
  ∑ a : JointIndex n, vectorPartial (intrinsicJointMatrixEntry δ ε k i j) a
    (fun c => sourceJointValue d u c x) * sourceJointDerivative d Du a b x

theorem actual_intrinsic_joint_weak_domains (d : SourceData μ)
    {u : Fin n → Space n → ℝ} {Du : Fin n → Fin n → Space n → ℝ}
    (hu : ∀ i E, IsCompact E → MemLp (u i) 2 (volume.restrict E))
    (hDu : ∀ i b E, IsCompact E → MemLp (Du i b) 2 (volume.restrict E))
    (hw : ∀ i b, HasLocalWeakCoordinateDerivative (u i) (Du i b) b)
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) (k : ℕ) (i j : Fin n) :
    (∀ E, IsCompact E → MemLp (intrinsicSourceTest d u δ ε k i j) 2 (volume.restrict E)) ∧
      (∀ b E, IsCompact E → MemLp (intrinsicSourceDerivative d u Du δ ε k i j b) 2
        (volume.restrict E)) ∧
      ∀ b, HasLocalWeakCoordinateDerivative (intrinsicSourceTest d u δ ε k i j)
        (intrinsicSourceDerivative d u Du δ ε k i j b) b := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hf (a : JointIndex n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (sourceJointValue d u a) 2 (volume.restrict E) := by
    cases a with
    | inl i => exact hu i E hE
    | inr ij =>
        exact KLS.MemLp.restrict_volume_of_potentialMeasure
          (d.hessian_entry_memLp ij.1 ij.2 2) d.source_C1.continuous hE
  have hF (a : JointIndex n) (b : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (sourceJointDerivative d Du a b) 2 (volume.restrict E) := by
    cases a with
    | inl i => exact hDu i b E hE
    | inr ij => exact d.third_local_L2 b ij.1 ij.2 E hE
  have hW (a : JointIndex n) (b : Fin n) : HasLocalWeakCoordinateDerivative
      (sourceJointValue d u a) (sourceJointDerivative d Du a b) b := by
    cases a with
    | inl i => exact hw i b
    | inr ij => exact d.third_weak_derivative b ij.1 ij.2
  obtain ⟨L, hL⟩ := intrinsicJointMatrixEntry_lipschitz hδ hε k i j
  have hη := intrinsicJointMatrixEntry_contDiff hδ hε k i j
  have hzero : intrinsicJointMatrixEntry δ ε k i j 0 = 0 := by
    simp only [intrinsicJointMatrixEntry, Pi.zero_apply, zero_mul, zero_div, mul_zero]
  refine ⟨fun E hE => hL.comp_memLp hzero (MemLp.of_eval fun a => hf a E hE), ?_, ?_⟩
  · intro b E hE
    exact vector_composed_derivative_local_L2 hf (fun a => hF a b) hη hL E hE
  · intro b
    exact local_vector_chain hf (fun a => hF a b) (fun a => hW a b) hη hL

end KLSConstantImprovement.ActualIntrinsicJointWeakTests405
#print axioms KLSConstantImprovement.ActualIntrinsicJointWeakTests405.jointBump_compact
#print axioms KLSConstantImprovement.ActualIntrinsicJointWeakTests405.intrinsicJointMatrixEntry_contDiff
#print axioms KLSConstantImprovement.ActualIntrinsicJointWeakTests405.intrinsicJointMatrixEntry_lipschitz
#print axioms KLSConstantImprovement.ActualIntrinsicJointWeakTests405.actual_intrinsic_joint_weak_domains
