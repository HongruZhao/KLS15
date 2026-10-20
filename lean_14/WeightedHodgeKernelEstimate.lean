import WeightedHodgeMollification
import WeightedLocalMollificationLimit

/-! The compact Hodge estimate passes to actual weighted-L² fields with
zero distributional curl and weighted divergence by concrete mollification.
No common-core density is a premise. -/
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ}

private theorem l2_sub_limit {μ : Measure (Space n)}
    {f g : ℕ → Space n → ℝ} {u v : Space n → ℝ}
    (hf : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0))
    (hg : Tendsto (fun k => eLpNorm (g k - v) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm ((f k - g k) - (u - v)) 2 μ) atTop (𝓝 0) := by
  have he (k : ℕ) : (f k - g k) - (u - v) = (f k - u) + -(g k - v) := by
    funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]; ring
  simp_rw [he]
  have hb (k : ℕ) : eLpNorm ((f k - u) + -(g k - v)) 2 μ ≤
      eLpNorm (f k - u) 2 μ + eLpNorm (g k - v) 2 μ := by
    simpa only [eLpNorm_neg] using
      (eLpNorm_add_le (f := f k - u) (g := -(g k - v)) (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hf.add hg) (fun _ => bot_le) hb

private theorem l2_add_limit {μ : Measure (Space n)}
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

private theorem l2_sum_limit {μ : Measure (Space n)} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {f : ι → ℕ → Space n → ℝ} {u : ι → Space n → ℝ}
    (h : ∀ i ∈ s, Tendsto (fun k => eLpNorm (f i k - u i) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm ((∑ i ∈ s, f i k) - ∑ i ∈ s, u i) 2 μ) atTop (𝓝 0) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact l2_add_limit (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma weightedVectorDivergence_mul {φ χ : Space n → ℝ}
    {F : Fin n → Space n → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hF : ∀ i, ContDiff ℝ 1 (F i)) (x : Space n) :
    weightedVectorDivergence φ (fun i y => χ y * F i y) x =
      χ x * weightedVectorDivergence φ F x +
        ∑ i, coordinateDerivative χ i x * F i x := by
  simp only [weightedVectorDivergence, weightedDerivativeTest, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinateDerivative_mul (hχ.differentiable (by norm_num) x)
    ((hF i).differentiable (by norm_num) x)]
  ring

lemma vectorCurl_mul {χ : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    (i j : Fin n) (x : Space n) :
    vectorCurl (fun i y => χ y * F i y) i j x =
      χ x * vectorCurl F i j x + coordinateDerivative χ i x * F j x -
        coordinateDerivative χ j x * F i x := by
  unfold vectorCurl
  rw [coordinateDerivative_mul (hχ.differentiable (by norm_num) x)
    ((hF j).differentiable (by norm_num) x),
    coordinateDerivative_mul (hχ.differentiable (by norm_num) x)
    ((hF i).differentiable (by norm_num) x)]
  ring

/-- Actual cutoff energy estimate for every weighted-L² field with zero
weighted divergence and ordinary distributional curl. The field itself
need not have any pre-existing first weak derivative. -/
theorem weightedHodge_kernel_cutoff_estimate {φ χ : Space n → ℝ}
    {F : Fin n → Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hFlocal : ∀ i K, IsCompact K → MemLp (F i) 2 (volume.restrict K))
    (hcurl : DistributionallyCurlFree F) (hdiv : WeakWeightedDivergenceFree φ F)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    κ * (∑ i, ∫ x, (χ x * F i x) ^ 2 ∂potentialMeasure φ) ≤
      (∫ x, (∑ i, coordinateDerivative χ i x * F i x) ^ 2 ∂potentialMeasure φ) +
      (1 / 2 : ℝ) * (∑ i, ∑ j, ∫ x,
        (coordinateDerivative χ i x * F j x - coordinateDerivative χ j x * F i x) ^ 2
          ∂potentialMeasure φ) := by
  have hloc (i : Fin n) := locallyIntegrable_of_memLp_two_on_compacts (hFlocal i)
  have hm (k : ℕ) (i : Fin n) := mollify_contDiff (hloc i) k
  have hdχ (i : Fin n) : Continuous (coordinateDerivative χ i) :=
    (contDiff_coordinateDerivative hχ (m := 0) (by simp) i).continuous
  have hflux (i : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (vectorDriftFlux φ F i) 2 (volume.restrict K) :=
    memLp_mul_continuous_on_compact hK (hFlocal i K hK)
      (contDiff_coordinateDerivative hφ (m := 0) (by simp) i).continuous
  let A : ℕ → Fin n → Space n → ℝ := fun k i x => χ x * mollify k (F i) x
  let D : ℕ → Fin n → Space n → ℝ := fun k i x =>
    χ x * mollify k (vectorDriftFlux φ F i) x -
      (χ x * coordinateDerivative φ i x) * mollify k (F i) x +
      coordinateDerivative χ i x * mollify k (F i) x
  let d : Fin n → Space n → ℝ := fun i x => coordinateDerivative χ i x * F i x
  let B : ℕ → Fin n → Fin n → Space n → ℝ := fun k i j x =>
    coordinateDerivative χ i x * mollify k (F j) x -
      coordinateDerivative χ j x * mollify k (F i) x
  let b : Fin n → Fin n → Space n → ℝ := fun i j x =>
    coordinateDerivative χ i x * F j x - coordinateDerivative χ j x * F i x
  have hAconv (i : Fin n) : Tendsto
      (fun k => eLpNorm (A k i - fun x => χ x * F i x) 2 (potentialMeasure φ)) atTop (𝓝 0) :=
    eLpNorm_compact_mul_mollify_sub_potential_tendsto_zero hφ.continuous hχ.continuous hc
      (hFlocal i)
  have hDconv (i : Fin n) : Tendsto
      (fun k => eLpNorm (D k i - d i) 2 (potentialMeasure φ)) atTop (𝓝 0) := by
    have h1 := eLpNorm_compact_mul_mollify_sub_potential_tendsto_zero hφ.continuous
      hχ.continuous hc (hflux i)
    have h2 := eLpNorm_compact_mul_mollify_sub_potential_tendsto_zero hφ.continuous
      (hχ.continuous.mul (contDiff_coordinateDerivative hφ (m := 0) (by simp) i).continuous)
      hc.mul_right (hFlocal i)
    have h3 := eLpNorm_compact_mul_mollify_sub_potential_tendsto_zero hφ.continuous
      (hdχ i) (hasCompactSupport_coordinateDerivative hc i) (hFlocal i)
    have he := l2_add_limit (l2_sub_limit h1 h2) h3
    convert he using 1
    funext k
    apply congrArg (fun f : Space n → ℝ => eLpNorm f 2 (potentialMeasure φ))
    funext x
    dsimp [D, d, vectorDriftFlux]
    ring
  have hBconv (i j : Fin n) : Tendsto
      (fun k => eLpNorm (B k i j - b i j) 2 (potentialMeasure φ)) atTop (𝓝 0) :=
    l2_sub_limit
      (eLpNorm_compact_mul_mollify_sub_potential_tendsto_zero hφ.continuous
        (hdχ i) (hasCompactSupport_coordinateDerivative hc i) (hFlocal j))
      (eLpNorm_compact_mul_mollify_sub_potential_tendsto_zero hφ.continuous
        (hdχ j) (hasCompactSupport_coordinateDerivative hc j) (hFlocal i))
  have hA2 (k : ℕ) (i : Fin n) : MemLp (A k i) 2 (potentialMeasure φ) :=
    memLp_of_continuous_hasCompactSupport hφ.continuous
      (hχ.continuous.mul (hm k i).continuous) hc.mul_right
  have ha2 (i : Fin n) : MemLp (fun x => χ x * F i x) 2 (potentialMeasure φ) :=
    memLp_compact_mul_local_potential hφ.continuous hχ.continuous hc (hFlocal i)
  have hD2 (k : ℕ) (i : Fin n) : MemLp (D k i) 2 (potentialMeasure φ) := by
    exact ((memLp_of_continuous_hasCompactSupport hφ.continuous
      (hχ.continuous.mul (mollify_contDiff (locallyIntegrable_of_memLp_two_on_compacts
        (hflux i)) k).continuous) hc.mul_right).sub
      (memLp_of_continuous_hasCompactSupport hφ.continuous
        ((hχ.continuous.mul (contDiff_coordinateDerivative hφ (m := 0) (by simp) i).continuous).mul
          (hm k i).continuous) hc.mul_right.mul_right)).add
      (memLp_of_continuous_hasCompactSupport hφ.continuous
        ((hdχ i).mul (hm k i).continuous) (hasCompactSupport_coordinateDerivative hc i).mul_right)
  have hd2 (i : Fin n) : MemLp (d i) 2 (potentialMeasure φ) :=
    memLp_compact_mul_local_potential hφ.continuous (hdχ i)
      (hasCompactSupport_coordinateDerivative hc i) (hFlocal i)
  have hB2 (k : ℕ) (i j : Fin n) : MemLp (B k i j) 2 (potentialMeasure φ) :=
    (memLp_of_continuous_hasCompactSupport hφ.continuous
      ((hdχ i).mul (hm k j).continuous) (hasCompactSupport_coordinateDerivative hc i).mul_right).sub
    (memLp_of_continuous_hasCompactSupport hφ.continuous
      ((hdχ j).mul (hm k i).continuous) (hasCompactSupport_coordinateDerivative hc j).mul_right)
  have hb2 (i j : Fin n) : MemLp (b i j) 2 (potentialMeasure φ) :=
    (memLp_compact_mul_local_potential hφ.continuous (hdχ i)
      (hasCompactSupport_coordinateDerivative hc i) (hFlocal j)).sub
    (memLp_compact_mul_local_potential hφ.continuous (hdχ j)
      (hasCompactSupport_coordinateDerivative hc j) (hFlocal i))
  have hleft : Tendsto (fun k => κ * (∑ i, ∫ x, (A k i x) ^ 2 ∂potentialMeasure φ))
      atTop (𝓝 (κ * (∑ i, ∫ x, (χ x * F i x) ^ 2 ∂potentialMeasure φ))) := by
    apply Tendsto.const_mul κ
    apply tendsto_finsetSum Finset.univ
    intro i _
    exact tendsto_integral_sq_of_eLpNorm_sub_tendsto_zero
      (fun k => hA2 k i) (ha2 i) (hAconv i)
  have hDsum : Tendsto (fun k => eLpNorm ((∑ i, D k i) - ∑ i, d i)
      2 (potentialMeasure φ)) atTop (𝓝 0) :=
    l2_sum_limit Finset.univ (fun i _ => hDconv i)
  have hDsum2 (k : ℕ) : MemLp (∑ i, D k i) 2 (potentialMeasure φ) :=
    memLp_finsetSum' Finset.univ (f := fun i => D k i) (fun i _ => hD2 k i)
  have hdsum2 : MemLp (∑ i, d i) 2 (potentialMeasure φ) :=
    memLp_finsetSum' Finset.univ (f := d) (fun i _ => hd2 i)
  have hrightD : Tendsto (fun k => ∫ x, (∑ i, D k i x) ^ 2 ∂potentialMeasure φ)
      atTop (𝓝 (∫ x, (∑ i, d i x) ^ 2 ∂potentialMeasure φ)) := by
    have ht := tendsto_integral_sq_of_eLpNorm_sub_tendsto_zero
      (f := fun k => ∑ i, D k i) (g := ∑ i, d i) hDsum2 hdsum2 hDsum
    simpa only [Finset.sum_apply] using ht
  have hrightB : Tendsto (fun k => (1 / 2 : ℝ) *
      (∑ i, ∑ j, ∫ x, (B k i j x) ^ 2 ∂potentialMeasure φ)) atTop
      (𝓝 ((1 / 2 : ℝ) * (∑ i, ∑ j, ∫ x, (b i j x) ^ 2 ∂potentialMeasure φ))) := by
    apply Tendsto.const_mul (1 / 2 : ℝ)
    apply tendsto_finsetSum Finset.univ
    intro i _
    apply tendsto_finsetSum Finset.univ
    intro j _
    exact tendsto_integral_sq_of_eLpNorm_sub_tendsto_zero
      (fun k => hB2 k i j) (hb2 i j) (hBconv i j)
  have he (k : ℕ) : κ * (∑ i, ∫ x, (A k i x) ^ 2 ∂potentialMeasure φ) ≤
      (∫ x, (∑ i, D k i x) ^ 2 ∂potentialMeasure φ) +
        (1 / 2 : ℝ) * (∑ i, ∑ j, ∫ x, (B k i j x) ^ 2 ∂potentialMeasure φ) := by
    have hb := integral_weightedHodge_core_L2_bound (hφ.of_le (by simp))
      (fun i => (hχ.mul (hm k i)).of_le (by simp)) (fun _ => hc.mul_right) hlower
    change κ * (∑ i, ∫ x, (A k i x) ^ 2 ∂potentialMeasure φ) ≤
      (∫ x, (weightedVectorDivergence φ (A k) x) ^ 2 ∂potentialMeasure φ) +
        (1 / 2 : ℝ) * (∑ i, ∑ j, ∫ x, (vectorCurl (A k) i j x) ^ 2
          ∂potentialMeasure φ) at hb
    have hDpoint (x : Space n) : weightedVectorDivergence φ (A k) x = ∑ i, D k i x := by
      rw [weightedVectorDivergence_mul (hχ.of_le (by simp))
        (fun i => (hm k i).of_le (by simp)), hdiv.mollify hφ hloc]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [D]; ring
    have hBpoint (i j : Fin n) (x : Space n) : vectorCurl (A k) i j x = B k i j x := by
      rw [vectorCurl_mul (hχ.of_le (by simp)) (fun i => (hm k i).of_le (by simp)),
        hcurl.mollify hloc, mul_zero, zero_add]
    simpa only [hDpoint, hBpoint] using hb
  have hfinal := le_of_tendsto_of_tendsto hleft (hrightD.add hrightB) (Eventually.of_forall he)
  simpa only [A, d, b, Finset.sum_apply] using hfinal

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.weightedHodge_kernel_cutoff_estimate
