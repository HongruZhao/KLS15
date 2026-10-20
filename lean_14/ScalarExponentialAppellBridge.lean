import ActualProductAdmissible
import ActualAppellFiniteMoments
import ActualAppellAffineTransport
import ActualAppellMoments

/-! The original normalized tilt derivatives for the actual one-dimensional
rate-one exponential. The moment generating function is used only on a
neighborhood of zero, so no global Laplace integrability is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Metric
open scoped BigOperators ContDiff Topology
namespace KLSImprovement.ScalarExponentialBridge
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSImprovement.ProductAdmissible KLSImprovement.ExponentialMoments
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def scalarEmbed : ℝ ≃L[ℝ] Space 1 :=
  (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm

@[simp] theorem scalarEmbed_apply (s : ℝ) (i : Fin 1) : scalarEmbed s i = s := by
  rfl

theorem scalarEmbed_one : scalarEmbed 1 = EuclideanSpace.single (0 : Fin 1) 1 := by
  ext i
  fin_cases i
  simp [scalarEmbed_apply]

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

local instance : IsProbabilityMeasure (rawEuclideanProduct 1) := by
  unfold rawEuclideanProduct
  exact (Measure.isProbabilityMeasure_map_iff
    (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurable.aemeasurable).mpr inferInstance

theorem raw_eq_scalar_map : rawEuclideanProduct 1=(expMeasure 1).map scalarEmbed := by
  let q := MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)
  have hq : KLSImprovement.ProductPolynomial.product 1=(expMeasure 1).map q.symm := by
    have hp := (measurePreserving_piUnique (fun _ : Fin 1 => expMeasure 1)).map_eq
    change (KLSImprovement.ProductPolynomial.product 1).map q=expMeasure 1 at hp
    rw [←hp,Measure.map_map q.symm.measurable q.measurable]
    have he : (q.symm ∘ q)=id := by
      funext x
      exact q.symm_apply_apply x
    rw [he,Measure.map_id]
  unfold rawEuclideanProduct
  rw [hq,Measure.map_map (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurable q.symm.measurable]
  rfl

theorem raw_partition (s : ℝ) (hs : s < 1) :
    (∫ x : Space 1, Real.exp (inner ℝ (scalarEmbed s) x)
      ∂rawEuclideanProduct 1) = 1/(1-s) := by
  unfold rawEuclideanProduct
  rw [integral_map (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurable.aemeasurable
    (by fun_prop)]
  have he : (fun y : Fin 1 → ℝ => Real.exp
      (inner ℝ (scalarEmbed s) (WithLp.toLp 2 y))) =
      (fun y => Real.exp (s*y 0)) := by
    funext y
    congr 1
    simp [PiLp.inner_apply, scalarEmbed_apply, mul_comm]
  change (∫ y : Fin 1 → ℝ, Real.exp
    (inner ℝ (scalarEmbed s) (WithLp.toLp 2 y)) ∂KLSImprovement.ProductPolynomial.product 1) = _
  rw [he]
  rw [KLSImprovement.ProductPolynomial.product, integral_comp_eval
    (μ := fun _ : Fin 1 => expMeasure 1) (i := (0 : Fin 1))
    (f := fun y : ℝ => Real.exp (s*y)) (by fun_prop)]
  exact (expMeasure_one_exponential_moment s hs).2

theorem iteratedDeriv_embed (F : Space 1 → ℝ) (m : ℕ) :
    iteratedDeriv m (F ∘ scalarEmbed) 0 =
      iteratedFDeriv ℝ m F 0 (fun _ => EuclideanSpace.single (0 : Fin 1) 1) := by
  have h := scalarEmbed.iteratedFDerivWithin_comp_right F
    (s := Set.univ) uniqueDiffOn_univ (x := 0) (by simp) m
  have hv := congrArg (fun T => T (fun _ => (1 : ℝ))) h
  simpa only [Set.preimage_univ, iteratedFDerivWithin_univ, map_zero,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, scalarEmbed_one,
    ContinuousLinearEquiv.coe_coe,
    ←iteratedDeriv_eq_iteratedFDeriv] using hv

def numerator (f : Space 1 → ℝ) (s : ℝ) : ℝ :=
  tiltNumerator (rawEuclideanProduct 1) (fun _ => 0) f (scalarEmbed s)

theorem numerator_smooth {f : Space 1 → ℝ}
    (hf : MemLp f 2 (rawEuclideanProduct 1)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (numerator f) 0 := by
  obtain ⟨r,hr,hfD,_⟩ := exists_common_local_exponential_domains
    (rawEuclideanProduct_logConcave 1) hf
  have hN := (contDiffOn_tiltNumerator_of_localNormExponentialDomain hfD).contDiffAt
    (isOpen_ball.mem_nhds (show (0 : Space 1) ∈ Metric.ball 0 r by simpa using hr))
  unfold numerator
  simpa only [Function.comp_def] using
    hN.comp (f := (scalarEmbed : ℝ → Space 1)) (0 : ℝ)
      (scalarEmbed.contDiff.contDiffAt)

theorem numerator_derivative {f : Space 1 → ℝ}
    (hf : MemLp f 2 (rawEuclideanProduct 1)) (m : ℕ) :
    iteratedDeriv m (numerator f) 0 =
      ∫ x : Space 1, f x*(x 0)^m ∂rawEuclideanProduct 1 := by
  change iteratedDeriv m ((tiltNumerator (rawEuclideanProduct 1)
    (fun _ => 0) f) ∘ scalarEmbed) 0 = _
  rw [iteratedDeriv_embed]
  obtain ⟨r,hr,hfD,_⟩ := exists_common_local_exponential_domains
    (rawEuclideanProduct_logConcave 1) hf
  rw [iteratedFDeriv_tiltNumerator_moment_of_local hfD (by simpa using hr)]
  simp [EuclideanSpace.inner_single_right]

theorem derivative_linear_factor {N : ℝ → ℝ}
    (hN : ContDiffAt ℝ (⊤ : ℕ∞) N 0) (m : ℕ) :
    iteratedDeriv (m+1) (fun s => (1-s)*N s) 0 =
      iteratedDeriv (m+1) N 0-((m:ℝ)+1)*iteratedDeriv m N 0 := by
  have hn : ContDiffAt ℝ (m+1) N 0 := hN.of_le (by simp)
  have hm : ContDiffAt ℝ (m+1) (fun s : ℝ => s*N s) 0 :=
    contDiffAt_id.mul hn
  have he : (fun s : ℝ => (1-s)*N s) = N-(fun s => s*N s) := by
    funext s
    simp only [Pi.sub_apply]
    ring
  rw [he, iteratedDeriv_sub hn hm]
  rw [iteratedDeriv_fun_mul (by fun_prop) hn]
  simp [iteratedDeriv_fun_id_zero, Finset.sum_ite_eq', Nat.cast_add,
    Nat.cast_one]

theorem raw_average_near_zero (f : Space 1 → ℝ) :
    (fun s => ∫ x, f x ∂exponentialTilt (rawEuclideanProduct 1) (scalarEmbed s))
      =ᶠ[𝓝 0] (fun s => (1-s)*numerator f s) := by
  filter_upwards [eventually_lt_nhds (by norm_num : (0 : ℝ)<1)] with s hs
  change tiltAverage (rawEuclideanProduct 1)
    (fun x => inner ℝ (scalarEmbed s) x) f = _
  rw [tiltAverage_eq_ratio]
  change (∫ x : Space 1, f x*Real.exp (inner ℝ (scalarEmbed s) x)
    ∂rawEuclideanProduct 1) /
    (∫ x : Space 1, Real.exp (inner ℝ (scalarEmbed s) x)
    ∂rawEuclideanProduct 1) = _
  rw [raw_partition s hs]
  simp only [numerator, tiltNumerator, zero_add]
  field_simp

theorem raw_coefficient_moment_formula {f : Space 1 → ℝ}
    (hf : MemLp f 2 (rawEuclideanProduct 1)) (m : ℕ) :
    actualAppellCoefficient (rawEuclideanProduct 1) f (m+1) (fun _ => 0) =
      (∫ x : Space 1, f x*(x 0)^(m+1) ∂rawEuclideanProduct 1)-
      ((m:ℝ)+1)*(∫ x : Space 1, f x*(x 0)^m ∂rawEuclideanProduct 1) := by
  unfold actualAppellCoefficient
  rw [←iteratedDeriv_embed]
  change iteratedDeriv (m+1)
    (fun s => ∫ x, f x ∂exponentialTilt (rawEuclideanProduct 1) (scalarEmbed s)) 0 = _
  rw [(raw_average_near_zero f).iteratedDeriv_eq (m+1),
    derivative_linear_factor (numerator_smooth hf),
    numerator_derivative hf, numerator_derivative hf]

theorem raw_coordinate_power_memLp (m : ℕ) :
    MemLp (fun x : Space 1 => (x 0)^m) 2 (rawEuclideanProduct 1) := by
  apply ((rawEuclideanProduct_logConcave 1).memLp_two_norm_pow m).mono' (by fun_prop)
  exact .of_forall (fun x => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le x 0) m)

theorem raw_actual_Appell_coefficient {f : Space 1 → ℝ}
    (hf : MemLp f 2 (rawEuclideanProduct 1)) (m : ℕ) :
    actualAppellCoefficient (rawEuclideanProduct 1) f (m+1) (fun _ => 0) =
      ∫ x : Space 1, f x*KLSImprovement.Exponential.appell m (x 0)
        ∂rawEuclideanProduct 1 := by
  rw [raw_coefficient_moment_formula hf]
  have h₁ := hf.integrable_mul (raw_coordinate_power_memLp (m+1))
  have h₀ := hf.integrable_mul (raw_coordinate_power_memLp m)
  have he : (fun x : Space 1 => f x*KLSImprovement.Exponential.appell m (x 0)) =
      (fun x => f x*(x 0)^(m+1)-((m:ℝ)+1)*(f x*(x 0)^m)) := by
    funext x
    unfold KLSImprovement.Exponential.appell
    ring
  rw [he, integral_sub (f := fun x : Space 1 => f x*(x 0)^(m+1))
    (g := fun x : Space 1 => ((m:ℝ)+1)*(f x*(x 0)^m))
    h₁ (h₀.const_mul _), integral_const_mul]

theorem centered_raw_average (f : Space 1 → ℝ) :
    (fun z => ∫ x,f x ∂exponentialTilt
      (KLSImprovement.ActualProductCumulants.centeredProductMeasure 1) z)=
    (fun z => ∫ x,f (centerAffine 1 x) ∂exponentialTilt (rawEuclideanProduct 1) z) := by
  funext z
  have h := actual_tilt_average_affine_transport (rawEuclideanProduct 1)
    (centerAffine 1) (fun x => f (centerAffine 1 x)) z
  rw [←centeredProduct_eq_raw_map] at h
  have he : (centerAffine 1).toContinuousAffineMap.contLinear.adjoint =
      ContinuousLinearMap.id ℝ (Space 1) := by
    change (ContinuousLinearMap.id ℝ (Space 1)).adjoint = _
    simp
  simpa only [ContinuousAffineEquiv.apply_symm_apply,he,
    ContinuousLinearMap.id_apply] using h

theorem centered_actual_Appell_coefficient {f : Space 1 → ℝ}
    (hf : MemLp f 2 (KLSImprovement.ActualProductCumulants.centeredProductMeasure 1))
    (m : ℕ) :
    actualAppellCoefficient (KLSImprovement.ActualProductCumulants.centeredProductMeasure 1)
      f (m+1) (fun _ => 0) =
      ∫ x : Space 1, f x*KLSImprovement.Exponential.appell m (x 0+1)
        ∂KLSImprovement.ActualProductCumulants.centeredProductMeasure 1 := by
  have hfmap : MemLp f 2 ((rawEuclideanProduct 1).map (centerAffine 1)) := by
    rwa [←centeredProduct_eq_raw_map]
  have hfm := hfmap.comp_of_map (centerAffine 1).continuous.measurable.aemeasurable
  change MemLp (fun x => f (centerAffine 1 x)) 2 (rawEuclideanProduct 1) at hfm
  unfold actualAppellCoefficient
  rw [centered_raw_average]
  change actualAppellCoefficient (rawEuclideanProduct 1)
    (fun x => f (centerAffine 1 x)) (m+1) (fun _ => 0) = _
  rw [raw_actual_Appell_coefficient hfm,centeredProduct_eq_raw_map]
  change _=(∫ x : Space 1, f x*KLSImprovement.Exponential.appell m (x 0+1)
    ∂(rawEuclideanProduct 1).map (centerAffine 1).toHomeomorph)
  rw [(centerAffine 1).toHomeomorph.isClosedEmbedding.integral_map]
  apply integral_congr_ae
  exact .of_forall (fun x => by
    have he : (centerAffine 1 x) 0+1=x 0 := by
      change (-1:ℝ)+x 0+1=x 0
      ring
    change f (centerAffine 1 x)*KLSImprovement.Exponential.appell m (x 0)=
      f (centerAffine 1 x)*KLSImprovement.Exponential.appell m ((centerAffine 1 x) 0+1)
    rw [he])

end KLSImprovement.ScalarExponentialBridge

#print axioms KLSImprovement.ScalarExponentialBridge.raw_partition
#print axioms KLSImprovement.ScalarExponentialBridge.numerator_derivative
#print axioms KLSImprovement.ScalarExponentialBridge.raw_actual_Appell_coefficient
#print axioms KLSImprovement.ScalarExponentialBridge.centered_actual_Appell_coefficient
