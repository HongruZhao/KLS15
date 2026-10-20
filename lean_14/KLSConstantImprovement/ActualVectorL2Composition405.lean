import KLSConstantImprovement.ActualRawWeakScalarChain405
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Genuine finite-vector L2 approximation and Lipschitz composition.
This supplies a single common a.e. mollifier subsequence for every
coordinate before a multivariate weak chain rule is passed to the limit. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal NNReal
namespace KLSConstantImprovement.ActualVectorL2Composition405
open KLS
variable {n : ℕ} {ρ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem lipschitz_comp_strong_L2_vector
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {η : E → F} {L : ℝ≥0} (hη : LipschitzWith L η) (hη0 : η 0 = 0)
    {f : ℕ → Space n → E} {u : Space n → E}
    (hf : ∀ k, MemLp (f k) 2 ρ) (hu : MemLp u 2 ρ)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 ρ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm ((η ∘ f k) - (η ∘ u)) 2 ρ) atTop (𝓝 0) := by
  have hF := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hconv
  have ht := (hη.continuous_compLp hη0).continuousAt.tendsto.comp hF
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun k => η ∘ f k)
    (fun k => hη.comp_memLp hη0 (hf k)) (η ∘ u) (hη.comp_memLp hη0 hu)).mp
  have hrep {g : Space n → E} (hg : MemLp g 2 ρ) :
      (hη.comp_memLp hη0 hg).toLp (η ∘ g) = hη.compLp hη0 (hg.toLp g) := by
    apply Lp.ext
    filter_upwards [(hη.comp_memLp hη0 hg).coeFn_toLp,
      hη.coeFn_compLp hη0 (hg.toLp g), hg.coeFn_toLp] with x hx hy hz
    change (hη.comp_memLp hη0 hg).toLp (η ∘ g) x = hη.compLp hη0 (hg.toLp g) x
    rw [hx, hy]
    change η (g x) = η ((hg.toLp g) x)
    rw [hz]
  have heq : (fun k => (hη.comp_memLp hη0 (hf k)).toLp (η ∘ f k)) =
      hη.compLp hη0 ∘ (fun k => (hf k).toLp (f k)) := by
    funext k
    exact hrep (hf k)
  rw [heq, hrep hu]
  exact ht

theorem finite_vector_strong_L2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℕ → ι → Space n → ℝ} {u : ι → Space n → ℝ}
    (hf : ∀ k j, MemLp (f k j) 2 ρ) (hu : ∀ j, MemLp (u j) 2 ρ)
    (hconv : ∀ j, Tendsto (fun k => eLpNorm (f k j - u j) 2 ρ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm
      ((fun x j => f k j x) - (fun x j => u j x)) 2 ρ) atTop (𝓝 0) := by
  let v (k : ℕ) (j : ι) (x : Space n) : ι → ℝ := Pi.single j (f k j x - u j x)
  have hsingle (j : ι) : LipschitzWith 1 (fun t : ℝ => (Pi.single j t : ι → ℝ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [dist_eq_norm, dist_eq_norm]
    have he : (Pi.single j s : ι → ℝ) - Pi.single j t = Pi.single j (s - t) := by
      ext a
      by_cases ha : a = j <;> simp [ha]
    rw [he, Pi.norm_single]
    simp
  have hv (k : ℕ) (j : ι) : MemLp (v k j) 2 ρ :=
    (hsingle j).comp_memLp (by ext a; simp) ((hf k j).sub (hu j))
  have hn (k : ℕ) (j : ι) : eLpNorm (v k j) 2 ρ = eLpNorm (f k j - u j) 2 ρ := by
    apply eLpNorm_congr_norm_ae (hv k j).aestronglyMeasurable
      ((hf k j).sub (hu j)).aestronglyMeasurable
    exact Eventually.of_forall fun x => Pi.norm_single _
  have heq (k : ℕ) : ((fun x j => f k j x) - (fun x j => u j x)) = ∑ j, v k j := by
    funext x j
    simp only [Pi.sub_apply, Finset.sum_apply, v]
    simp
  have hb (k : ℕ) : eLpNorm
      ((fun x j => f k j x) - (fun x j => u j x)) 2 ρ ≤
      ∑ j, eLpNorm (f k j - u j) 2 ρ := by
    rw [heq]
    calc
      _ ≤ ∑ j, eLpNorm (v k j) 2 ρ := eLpNorm_sum_le (by norm_num)
      _ = _ := Finset.sum_congr rfl fun j _ => hn k j
  have ht : Tendsto (fun k => ∑ j, eLpNorm (f k j - u j) 2 ρ) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => hconv j)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le) hb

theorem exists_common_vector_subsequence {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℕ → ι → Space n → ℝ} {u : ι → Space n → ℝ}
    (hf : ∀ k j, MemLp (f k j) 2 ρ) (hu : ∀ j, MemLp (u j) 2 ρ)
    (hconv : ∀ j, Tendsto (fun k => eLpNorm (f k j - u j) 2 ρ) atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ᵐ x ∂ρ,
      Tendsto (fun k j => f (s k) j x) atTop (𝓝 (fun j => u j x)) := by
  have hm : TendstoInMeasure ρ (fun k x j => f k j x) atTop (fun x j => u j x) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (finite_vector_strong_L2 hf hu hconv)
  exact hm.exists_seq_tendsto_ae

end KLSConstantImprovement.ActualVectorL2Composition405

#print axioms KLSConstantImprovement.ActualVectorL2Composition405.lipschitz_comp_strong_L2_vector
#print axioms KLSConstantImprovement.ActualVectorL2Composition405.finite_vector_strong_L2
#print axioms KLSConstantImprovement.ActualVectorL2Composition405.exists_common_vector_subsequence
