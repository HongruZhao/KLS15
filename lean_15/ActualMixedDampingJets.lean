import ActualNormalizedDampingCommutation
import ActualAppellFiniteMoments
import Mathlib

/-! Genuine mixed normalized jets of the damped actual expectation.
Faà di Bruno expresses each mixed jet using finitely many actual raw
jets, so their proved right derivatives imply right differentiability
of every mixed normalized coefficient. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

 def actualDampedMixedJet (μ : Measure (Space n)) (f : Space n → ℝ)
    (d : ℕ) (s : ℝ) (m : Fin d → Space n) : ℝ :=
  iteratedFDeriv ℝ d (actualDampedAverage μ f s) 0 m

 theorem actualDampedMixedJet_finite_formula
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r)
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r) (hr : 0 < r)
    {s : ℝ} (hs : 0 ≤ s) (d : ℕ) (m : Fin d → Space n) :
    actualDampedMixedJet μ f d s m =
      ∑ c : OrderedFinpartition d,
        iteratedFDeriv ℝ c.length scalarRatio
          (actualDampedNumerator μ f s 0,actualDampedNumerator μ (fun _ => 1) s 0)
          (fun j =>
            (iteratedFDeriv ℝ (c.partSize j) (actualDampedNumerator μ f s) 0
              (fun i => m (c.emb j i)),
             iteratedFDeriv ℝ (c.partSize j) (actualDampedNumerator μ (fun _ => 1) s) 0
              (fun i => m (c.emb j i)))) := by
  let P : Space n → ℝ × ℝ := fun z =>
    (actualDampedNumerator μ f s z,actualDampedNumerator μ (fun _ => 1) s z)
  have hN := contDiffAt_actualDampedNumerator_zero hf hr hs
  have hZ := contDiffAt_actualDampedNumerator_zero h1 hr hs
  have hP : ContDiffAt ℝ (⊤ : ℕ∞) P 0 := hN.prodMk hZ
  have hR : ContDiffAt ℝ (⊤ : ℕ∞) scalarRatio (P 0) :=
    scalarRatio_contDiffAt _ _ (actualDampedNumerator_one_zero_pos h1 hr hs).ne'
  change iteratedFDeriv ℝ d (scalarRatio ∘ P) 0 m = _
  rw [iteratedFDeriv_comp hR hP (by simp)]
  simp only [FormalMultilinearSeries.taylorComp,ContinuousMultilinearMap.sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,ftaylorSeries,
    OrderedFinpartition.applyOrderedFinpartition_apply]
  apply Finset.sum_congr rfl
  intro c hc
  congr 1
  funext j
  dsimp [P]
  rw [iteratedFDeriv_prodMk hN hZ (by simp)]
  rfl

 theorem differentiableWithinAt_actualDampedMixedJet
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (m : Fin d → Space n) :
    DifferentiableWithinAt ℝ (fun s : ℝ => actualDampedMixedJet μ f d s m) (Ici 0) 0 := by
  obtain ⟨r,hr,hD,h1D⟩ := exists_common_local_exponential_domains hLC hf
  have h1L : MemLp (fun _ : Space n => (1 : ℝ)) 2 μ := memLp_const 1
  have hraw (k : ℕ) (v : Fin k → Space n) :=
    (hasDerivWithinAt_damped_laplace_jet hLC hf k v).differentiableWithinAt
  have hzraw (k : ℕ) (v : Fin k → Space n) :=
    (hasDerivWithinAt_damped_laplace_jet hLC h1L k v).differentiableWithinAt
  have hbase : DifferentiableWithinAt ℝ
      (fun s : ℝ => (actualDampedNumerator μ f s 0,actualDampedNumerator μ (fun _ => 1) s 0))
      (Ici 0) 0 := by
    simpa using (hraw 0 Fin.elim0).prodMk (hzraw 0 Fin.elim0)
  have hratio : ContDiffAt ℝ (⊤ : ℕ∞) scalarRatio
      (actualDampedNumerator μ f 0 0,actualDampedNumerator μ (fun _ => 1) 0 0) :=
    scalarRatio_contDiffAt _ _ (by simp [actualDampedNumerator])
  have hsum : DifferentiableWithinAt ℝ
      (fun s : ℝ => ∑ c : OrderedFinpartition d,
        iteratedFDeriv ℝ c.length scalarRatio
          (actualDampedNumerator μ f s 0,actualDampedNumerator μ (fun _ => 1) s 0)
          (fun j =>
            (iteratedFDeriv ℝ (c.partSize j) (actualDampedNumerator μ f s) 0
              (fun i => m (c.emb j i)),
             iteratedFDeriv ℝ (c.partSize j) (actualDampedNumerator μ (fun _ => 1) s) 0
              (fun i => m (c.emb j i))))) (Ici 0) 0 := by
    apply DifferentiableWithinAt.fun_sum
    intro c hc
    have hratio' : ContDiffAt ℝ (c.length+1) scalarRatio
        (actualDampedNumerator μ f 0 0,actualDampedNumerator μ (fun _ => 1) 0 0) :=
      hratio.of_le (by simp)
    have houter := hratio'.differentiableAt_iteratedFDeriv
      (m := c.length) (Nat.cast_lt.mpr c.length.lt_succ_self)
    have ho := houter.hasFDerivAt.comp_hasFDerivWithinAt 0 hbase.hasFDerivWithinAt
    exact (ho.continuousMultilinearMap_apply (fun j =>
      ((hraw _ (fun i => m (c.emb j i))).prodMk
        (hzraw _ (fun i => m (c.emb j i)))).hasFDerivWithinAt)).differentiableWithinAt
  apply hsum.congr
  · intro s hs
    exact actualDampedMixedJet_finite_formula hD h1D hr hs d m
  · exact actualDampedMixedJet_finite_formula hD h1D hr (show (0 : ℝ) ≤ 0 from le_rfl) d m

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualDampedMixedJet_finite_formula
#print axioms KLS.DeterministicBridgeIntegration.differentiableWithinAt_actualDampedMixedJet
