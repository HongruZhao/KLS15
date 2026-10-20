import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Encodable.Basic

/-! A single further subsequence gives pointwise almost-everywhere
convergence for every member of a countable strongly convergent L2 family.
The extraction imposes a summable error rate simultaneously on each finite
initial set of coordinates; the null set is common to all coordinates. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace KLSConstantImprovement.ActualCountableLpAesubsequence405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem exists_nat_Lp_common_ae_subsequence
    (F : ℕ → ℕ → Lp ℝ 2 μ) (g : ℕ → Lp ℝ 2 μ)
    (hlim : ∀ i, Tendsto (fun k => F k i) atTop (𝓝 (g i))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ᵐ x ∂μ, ∀ i, Tendsto (fun k => F (σ k) i x) atTop (𝓝 (g i x)) := by
  let V (m : ℕ) : Set ℕ := {k | ∀ i : Fin (m+1),
    ‖F k i-g i‖ ≤ (1/2 : ℝ)^m}
  have hV (m : ℕ) : V m ∈ (atTop : Filter ℕ) := by
    change ∀ᶠ k in atTop, ∀ i : Fin (m+1), ‖F k i-g i‖ ≤ (1/2 : ℝ)^m
    rw [eventually_all]
    intro i
    have ht : Tendsto (fun k => ‖F k i-g i‖) atTop (𝓝 (0 : ℝ)) := by
      simpa only [sub_self, norm_zero] using ((hlim i).sub (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => g i) atTop (𝓝 (g i)))).norm
    exact (ht.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < (1/2 : ℝ)^m))).mono
      fun _ hk => hk.le
  obtain ⟨σ, hσ, hσV⟩ := Filter.Tendsto.subseq_mem hV
    (tendsto_id : Tendsto (id : ℕ → ℕ) atTop atTop)
  have hgeo : Summable (fun k : ℕ => (1/2 : ℝ)^k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum (i : ℕ) : Summable (fun k => ‖F (σ k) i-g i‖) := by
    apply Summable.of_norm_bounded_eventually_nat hgeo
    filter_upwards [eventually_ge_atTop i] with k hik
    have hb := hσV k (⟨i, Nat.lt_succ_of_le hik⟩ : Fin (k+1))
    simpa only [id_eq, norm_norm] using hb
  have hsumE (i : ℕ) :
      (∑' k, eLpNorm ((F (σ k) i-g i : Lp ℝ 2 μ) : X → ℝ) 2 μ) ≠ ∞ := by
    simpa only [← Lp.enorm_def] using
      (tsum_enorm_ne_top_iff_summable_norm.mpr (hsum i))
  have hp (i : ℕ) : ∀ᵐ x ∂μ, Summable
      (fun k => ‖(F (σ k) i-g i : Lp ℝ 2 μ) x‖) :=
    summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ENNReal) ≤ 2) (hsumE i)
  have hc (i : ℕ) : ∀ᵐ x ∂μ, ∀ k,
      (F (σ k) i-g i : Lp ℝ 2 μ) x = F (σ k) i x-g i x :=
    ae_all_iff.mpr fun k => Lp.coeFn_sub (F (σ k) i) (g i)
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [ae_all_iff.mpr hp, ae_all_iff.mpr hc] with x hx hcx
  intro i
  have hs : Summable (fun k => ‖F (σ k) i x-g i x‖) := by
    simpa only [hcx i] using hx i
  have hz : Tendsto (fun k => F (σ k) i x-g i x) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hs.tendsto_atTop_zero
  simpa only [zero_add, sub_add_cancel] using hz.add_const (g i x)

theorem exists_countable_Lp_common_ae_subsequence
    {ι : Type*} [Countable ι]
    (F : ℕ → ι → Lp ℝ 2 μ) (g : ι → Lp ℝ 2 μ)
    (hlim : ∀ i, Tendsto (fun k => F k i) atTop (𝓝 (g i))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ᵐ x ∂μ, ∀ i, Tendsto (fun k => F (σ k) i x) atTop (𝓝 (g i x)) := by
  classical
  letI : Encodable ι := Encodable.ofCountable ι
  let F' (k j : ℕ) : Lp ℝ 2 μ :=
    match Encodable.decode (α := ι) j with
    | none => 0
    | some i => F k i
  let g' (j : ℕ) : Lp ℝ 2 μ :=
    match Encodable.decode (α := ι) j with
    | none => 0
    | some i => g i
  have ht (j : ℕ) : Tendsto (fun k => F' k j) atTop (𝓝 (g' j)) := by
    cases hj : Encodable.decode (α := ι) j with
    | none => simpa only [F', g', hj] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Lp ℝ 2 μ)) atTop (𝓝 0))
    | some i => simpa only [F', g', hj] using hlim i
  obtain ⟨σ, hσ, hae⟩ := exists_nat_Lp_common_ae_subsequence F' g' ht
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hae] with x hx
  intro i
  simpa only [F', g', Encodable.encodek] using hx (Encodable.encode i)

end KLSConstantImprovement.ActualCountableLpAesubsequence405
#print axioms KLSConstantImprovement.ActualCountableLpAesubsequence405.exists_nat_Lp_common_ae_subsequence
#print axioms KLSConstantImprovement.ActualCountableLpAesubsequence405.exists_countable_Lp_common_ae_subsequence
