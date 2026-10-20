import FirstOrderMatrixCutoff
import FirstOrderMatrixSmoothing

/-! Actual maximal first-order matrix domains with a continuous zeroth
order drift. The cutoff and smoothing statements assume only the combined
distributional equation, rather than coordinate Sobolev regularity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {ι ρ : Type*} [Fintype ι] [Fintype ρ]
  [DecidableEq ι] [DecidableEq ρ]

def matrixZeroth (B : ρ → ι → Space n → ℝ) (f : ι → Space n → ℝ)
    (a : ρ) (x : Space n) : ℝ := ∑ j, B a j x * f j x

def matrixFirstOrder (A : ρ → Fin n → ι → ℝ)
    (B : ρ → ι → Space n → ℝ) (f : ι → Space n → ℝ) (a : ρ) (x : Space n) : ℝ :=
  matrixDifferential A f a x + matrixZeroth B f a x

def HasWeakMatrixFirstOrder (A : ρ → Fin n → ι → ℝ)
    (B : ρ → ι → Space n → ℝ) (f : ι → Space n → ℝ) (g : ρ → Space n → ℝ) : Prop :=
  HasWeakMatrixDerivative A f (fun a x => g a x - matrixZeroth B f a x)

lemma matrixZeroth_cutoff (B : ρ → ι → Space n → ℝ)
    (χ : Space n → ℝ) (f : ι → Space n → ℝ) (a : ρ) (x : Space n) :
    matrixZeroth B (fun j y => χ y * f j y) a x = χ x * matrixZeroth B f a x := by
  simp only [matrixZeroth, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem HasWeakMatrixFirstOrder.cutoff
    {A : ρ → Fin n → ι → ℝ} {B : ρ → ι → Space n → ℝ}
    {f : ι → Space n → ℝ} {g : ρ → Space n → ℝ}
    (h : HasWeakMatrixFirstOrder A B f g)
    (hf : ∀ j, LocallyIntegrable (f j) volume)
    (hg : ∀ a, LocallyIntegrable (fun x => g a x - matrixZeroth B f a x) volume)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    HasWeakMatrixFirstOrder A B (fun j x => χ x * f j x)
      (fun a x => χ x * g a x + matrixCutoffError A χ f a x) := by
  have ht := HasWeakMatrixDerivative.cutoff h hf hg hχ hc
  have he : (fun a x => (χ x * g a x + matrixCutoffError A χ f a x) -
      matrixZeroth B (fun j y => χ y * f j y) a x) =
      (fun a x => χ x * (g a x - matrixZeroth B f a x) + matrixCutoffError A χ f a x) := by
    funext a x
    rw [matrixZeroth_cutoff]
    ring
  unfold HasWeakMatrixFirstOrder
  rw [he]
  exact ht

lemma memLp_continuous_mul_compact {φ f b : Space n → ℝ}
    (hb : Continuous b) (hf : MemLp f 2 (potentialMeasure φ))
    (hc : HasCompactSupport f) : MemLp (fun x => b x * f x) 2 (potentialMeasure φ) := by
  obtain ⟨χ, hχ, hχc, hone⟩ := exists_smooth_compact_one_on_compact hc
  have hm : MemLp (fun x => (b x * χ x) * f x) 2 (potentialMeasure φ) :=
    ((hb.mul hχ.continuous).memLp_top_of_hasCompactSupport
    hχc.mul_left (potentialMeasure φ)).mul hf
  apply (memLp_congr_ae ?_).mp hm
  exact Eventually.of_forall fun x => by
    change (b x * χ x) * f x = b x * f x
    by_cases hx : x ∈ tsupport f
    · rw [hone x hx, mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]

lemma matrixZeroth_memLp_compact {φ : Space n → ℝ}
    {B : ρ → ι → Space n → ℝ} {f : ι → Space n → ℝ}
    (hB : ∀ a j, Continuous (B a j))
    (hf : ∀ j, MemLp (f j) 2 (potentialMeasure φ))
    (hc : ∀ j, HasCompactSupport (f j)) (a : ρ) :
    MemLp (matrixZeroth B f a) 2 (potentialMeasure φ) :=
  memLp_finsetSum Finset.univ (fun j _ => memLp_continuous_mul_compact (hB a j) (hf j) (hc j))

lemma matrixZeroth_hasCompactSupport (B : ρ → ι → Space n → ℝ)
    {f : ι → Space n → ℝ} (hc : ∀ j, HasCompactSupport (f j)) (a : ρ) :
    HasCompactSupport (matrixZeroth B f a) :=
  compactSupport_finsetSum Finset.univ (fun j _ => (hc j).mul_left)

lemma matrix_l2_add_limit {μ : Measure (Space n)}
    {f g : ℕ → Space n → ℝ} {u v : Space n → ℝ}
    (hf : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0))
    (hg : Tendsto (fun k => eLpNorm (g k - v) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm ((f k + g k) - (u + v)) 2 μ) atTop (𝓝 0) := by
  have he (k : ℕ) : (f k + g k) - (u + v) = (f k - u) + (g k - v) := by
    funext x; simp only [Pi.sub_apply, Pi.add_apply]; ring
  simp_rw [he]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hf.add hg) (fun _ => bot_le)
    (fun k => eLpNorm_add_le (by norm_num))

lemma matrix_l2_sum_limit {μ : Measure (Space n)} {τ : Type*} [DecidableEq τ]
    (s : Finset τ) {f : τ → ℕ → Space n → ℝ} {u : τ → Space n → ℝ}
    (h : ∀ i ∈ s, Tendsto (fun k => eLpNorm (f i k - u i) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm ((∑ i ∈ s, f i k) - ∑ i ∈ s, u i) 2 μ) atTop (𝓝 0) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact matrix_l2_add_limit (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- Strong compact graph approximation for the full first-order expression,
including a drift which is only locally bounded by continuity. -/
theorem HasWeakMatrixFirstOrder.compact_smoothing
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {A : ρ → Fin n → ι → ℝ} {B : ρ → ι → Space n → ℝ}
    {f : ι → Space n → ℝ} {g : ρ → Space n → ℝ}
    (h : HasWeakMatrixFirstOrder A B f g) (hB : ∀ a j, Continuous (B a j))
    (hf : ∀ j, MemLp (f j) 2 (potentialMeasure φ)) (hfc : ∀ j, HasCompactSupport (f j))
    (hg : ∀ a, MemLp (g a) 2 (potentialMeasure φ)) (hgc : ∀ a, HasCompactSupport (g a))
    (a : ρ) :
    Tendsto (fun k => eLpNorm
      (fun x => matrixFirstOrder A B (fun j => mollify k (f j)) a x - g a x)
        2 (potentialMeasure φ)) atTop (𝓝 0) := by
  have hprincipal := HasWeakMatrixDerivative.compact_smoothing hφ h hf hfc
    (fun b => (hg b).sub (matrixZeroth_memLp_compact hB hf hfc b))
    (fun b => (hgc b).sub (matrixZeroth_hasCompactSupport B hfc b)) a
  have hzeroth := matrix_l2_sum_limit Finset.univ (fun j _ =>
    eLpNorm_continuous_mul_compact_mollify_sub_potential_tendsto_zero hφ (hB a j) (hf j) (hfc j))
  have ht := matrix_l2_add_limit hprincipal hzeroth
  convert ht using 1
  funext k
  congr 1
  funext x
  simp only [matrixFirstOrder, matrixZeroth, Pi.sub_apply, Pi.add_apply,
    Finset.sum_apply, Finset.sum_const_zero]
  ring

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.HasWeakMatrixFirstOrder.cutoff
#print axioms KLS.DeterministicBridgeIntegration.HasWeakMatrixFirstOrder.compact_smoothing
