import CompactWeakDerivativeTempered

/-! Literal distributional product derivatives of compact localizations of
the weighted tensor primitive tower. Every right-hand term is genuine L². -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators SchwartzMap LineDeriv
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n s : ℕ} {φ : Space n → ℝ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem realMemLpToComplex_add_of_ae
    {f a b : Space n → ℝ} (hf : MemLp f 2 volume) (ha : MemLp a 2 volume) (hb : MemLp b 2 volume)
    (he : f =ᵐ[volume] fun x => a x+b x) :
    (realMemLpToComplex hf : 𝓢'(Space n,ℂ)) =
      (realMemLpToComplex ha : 𝓢'(Space n,ℂ))+(realMemLpToComplex hb : 𝓢'(Space n,ℂ)) := by
  have hLp : realMemLpToComplex hf = realMemLpToComplex ha+realMemLpToComplex hb := by
    apply Lp.ext
    filter_upwards [realMemLpToComplex_coe hf,realMemLpToComplex_coe ha,
      realMemLpToComplex_coe hb,Lp.coeFn_add (realMemLpToComplex ha) (realMemLpToComplex hb),he]
      with x hx hxa hxb hsum hfabc
    rw [hsum,Pi.add_apply,hx,hxa,hxb,hfabc,Complex.ofReal_add]
  rw [hLp]
  exact map_add (Lp.toTemperedDistributionCLM ℂ volume 2) _ _

 def compactWeightedTempered (hφ : Continuous φ) {χ : Space n → ℝ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (u : Lp ℝ 2 (potentialMeasure φ)) : 𝓢'(Space n,ℂ) :=
    realMemLpToComplex (memLp_compact_mul_weighted_to_volume hφ hχ hc u)

 theorem compactWeightedTempered_memSobolev_zero (hφ : Continuous φ) {χ : Space n → ℝ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (u : Lp ℝ 2 (potentialMeasure φ)) :
    TemperedDistribution.MemSobolev 0 2 (compactWeightedTempered hφ hχ hc u) := by
  apply TemperedDistribution.memSobolev_zero_iff.mpr
  exact ⟨_,rfl⟩

 theorem compactTensorWordTempered_lineDeriv (hφ : ContDiff ℝ 1 φ)
    (U : (k : ℕ) → OrderedTensorField φ k)
    (hgraph : ∀ k, k < s → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
      finitePrimitiveValue (OrderedTensorIndex n k) V = U k ∧
        ∀ I i, weightedH1Derivative φ i (V I) = U (k + 1) (Fin.cons i I))
    (L : List (Fin n)) (hL : L.length < s) (i : Fin n)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    ∂_{EuclideanSpace.single i (1 : ℝ)}
      (compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U L)) =
      compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U (i::L))+
      compactWeightedTempered hφ.continuous
        (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
        (hasCompactSupport_coordinateDerivative hc i) (tensorWordLp U L) := by
  obtain ⟨hf,g,hg,hweak⟩ := tensorWordLp_compact_product hφ U hgraph L hL i hχ hc
  have hfzero : ∀ᵐ x ∂(volume : Measure (Space n)), x ∉ tsupport χ →
      χ x*tensorWordLp U L x = 0 := by
    filter_upwards with x hx
    rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
  have hgzero : ∀ᵐ x ∂(volume : Measure (Space n)), x ∉ tsupport χ → g x = 0 := by
    filter_upwards [hg] with x hx hxout
    rw [hx,image_eq_zero_of_notMem_tsupport hxout,
      show coordinateDerivative χ i x = 0 from image_eq_zero_of_notMem_tsupport
        (fun hi => hxout (tsupport_coordinateDerivative_subset χ i hi))]
    ring
  have htemp := lineDeriv_realMemLpToComplex_of_compact_weak_derivative hf hweak hc hfzero hgzero
  have hdχ := (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
  have h1 := memLp_compact_mul_weighted_to_volume hφ.continuous hχ.continuous hc (tensorWordLp U (i::L))
  have h2 := memLp_compact_mul_weighted_to_volume hφ.continuous hdχ
    (hasCompactSupport_coordinateDerivative hc i) (tensorWordLp U L)
  exact htemp.trans (realMemLpToComplex_add_of_ae (Lp.memLp g) h1 h2 hg)

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.compactTensorWordTempered_lineDeriv
