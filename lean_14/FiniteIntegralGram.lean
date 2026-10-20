import FiniteGramRowBound

/-! A finite observation bound for actual L² functions, obtained from the
absolute row sums of their actual integral Gram matrix. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace KLSImprovement.FiniteIntegralGram
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem observation_le_of_integral_gram_rows {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) (p : ι → Ω → ℝ)
    (hp : ∀ i, MemLp (p i) 2 μ) {C : ℝ} (hC : 0<C)
    (hrow : ∀ i, ∑ j, |∫ x, p i x*p j x ∂μ| ≤ C)
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∑ i, (∫ x, f x*p i x ∂μ)^2) ≤ C*(∫ x, (f x)^2 ∂μ) := by
  classical
  let c : ι → ℝ := fun i => ∫ x, f x*p i x ∂μ
  let S := ∑ i, (c i)^2
  let P : Ω → ℝ := fun x => ∑ i, c i*p i x
  have hP : MemLp P 2 μ := memLp_finsetSum _ (fun i _ => (hp i).const_mul (c i))
  have hff := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hPP := (memLp_two_iff_integrable_sq hP.aestronglyMeasurable).mp hP
  have hfP : Integrable (fun x => f x*P x) μ := hf.integrable_mul hP
  have hpair : (∫ x, f x*P x ∂μ)=S := by
    change (∫ x, f x*(∑ i,c i*p i x) ∂μ)=_
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ =>
      ((hf.integrable_mul (hp i)).const_mul (c i)).congr
        (.of_forall (fun x => by simp only [Pi.mul_apply];ring)))]
    apply Finset.sum_congr rfl
    intro i _
    have he : (fun x => f x*(c i*p i x))=(fun x => c i*(f x*p i x)) := by
      funext x
      ring
    rw [he,integral_const_mul]
    change c i*c i=(c i)^2
    ring
  have hgram : (∫ x, (P x)^2 ∂μ)=
      ∑ i, ∑ j, c i*c j*(∫ x,p i x*p j x ∂μ) := by
    have he : (fun x => (P x)^2)=
        (fun x => ∑ i, ∑ j, c i*c j*(p i x*p j x)) := by
      funext x
      dsimp [P]
      simp_rw [pow_two,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hij (i j : ι) : Integrable (fun x => c i*c j*(p i x*p j x)) μ :=
      ((hp i).integrable_mul (hp j)).const_mul (c i*c j)
    have hi (i : ι) : Integrable (fun x => ∑ j,c i*c j*(p i x*p j x)) μ :=
      integrable_finsetSum _ (fun j _ => hij i j)
    rw [he, integral_finsetSum _ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hij i j)]
    simp only [integral_const_mul]
  have hbound : (∫ x, (P x)^2 ∂μ)≤C*S := by
    rw [hgram]
    apply KLSImprovement.FiniteGram.symmetric_abs_row_quadratic_bound _ _ hrow c
    intro i j
    apply integral_congr_ae
    exact .of_forall (fun _ => mul_comm _ _)
  have hn : 0≤∫ x,(C*f x-P x)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have he : (fun x => (C*f x-P x)^2)=
      (fun x => C^2*(f x)^2-2*C*(f x*P x)+(P x)^2) := by
    funext x
    ring
  rw [he,integral_add (f := fun x => C^2*(f x)^2-2*C*(f x*P x))
    (g := fun x => (P x)^2) ((hff.const_mul _).sub (hfP.const_mul _)) hPP,
    integral_sub (f := fun x => C^2*(f x)^2) (g := fun x => 2*C*(f x*P x))
    (hff.const_mul _) (hfP.const_mul _),integral_const_mul,
    integral_const_mul,hpair] at hn
  change S≤C*(∫ x,(f x)^2 ∂μ)
  apply (mul_le_mul_iff_right₀ hC).mp
  nlinarith

end KLSImprovement.FiniteIntegralGram
#print axioms KLSImprovement.FiniteIntegralGram.observation_le_of_integral_gram_rows
