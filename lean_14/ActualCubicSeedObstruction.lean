import ScalarQuadraticCubicJoint
import ActualScalarCriticalObservation
import ActualProductCubicCap
import GenericVariableBarrierAssembly

/-! The genuine scalar exponential rules out cap six for every normalized
strictly decreasing cubic seed. The sharp scalar joint replacement is proved
through the original normalized tilt-derivative coefficient definition. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace KLSImprovement.CubicSeedObstruction
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSImprovement.ActualProductCumulants KLSImprovement.ProductAdmissible
open KLSImprovement.Exponential KLSImprovement.ExponentialCriticalGram
open KLSImprovement.ScalarExponentialBridge KLSImprovement.ActualScalarCritical
open KLSImprovement.ProductCubic KLSImprovement.ScalarJoint
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure (centeredProductMeasure 1) :=
  centeredProduct_isProbability 1
local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

/-- A sharp joint inequality for the actual original scalar coefficients. -/
theorem actual_scalar_quadratic_cubic_joint_budget {f : Space 1→ℝ}
    (hf : MemLp f 2 (centeredProductMeasure 1)) :
    (actualAppellCoefficient (centeredProductMeasure 1) f 2 (fun _=>0))^2/8+
      (actualAppellCoefficient (centeredProductMeasure 1) f 3 (fun _=>0)-
        (9/2:ℝ)*actualAppellCoefficient (centeredProductMeasure 1) f 2 (fun _=>0))^2/54≤
          ∫ x,(f x)^2 ∂centeredProductMeasure 1 := by
  rw [original_coefficient_eq_scalar_integral hf 1,
    original_coefficient_eq_scalar_integral hf 2,centered_integral]
  exact scalar_quadratic_cubic_joint_budget (pullback_memLp hf)

def cubicWitness (x : Space 1) : ℝ := appell 2 (x 0+1)

theorem cubicWitness_memLp : MemLp cubicWitness 2 (centeredProductMeasure 1) := by
  have he : cubicWitness=(fun x:Space 1=>
      isotropicCubicKernel (fun _:Fin 3=>(0:Fin 1)) (fun i=>x i)) := by
    funext x
    norm_num [cubicWitness,appell,isotropicCubicKernel]
    ring
  rw [he]
  exact isotropicCubicKernel_memLp _

theorem pullback_cubicWitness : pullback cubicWitness=appell 2 := by
  funext y
  change appell 2 ((-1:ℝ)+y+1)=appell 2 y
  congr 1
  ring

theorem cubicWitness_square :
    (∫ x,(cubicWitness x)^2 ∂centeredProductMeasure 1)=216 := by
  rw [centered_integral]
  change (∫ y,(pullback cubicWitness y)^2 ∂expMeasure 1)=216
  rw [pullback_cubicWitness,integral_appell_sq]
  norm_num

theorem cubicWitness_coefficient_two :
    actualAppellCoefficient (centeredProductMeasure 1) cubicWitness 2 (fun _=>0)=36 := by
  rw [original_coefficient_eq_scalar_integral cubicWitness_memLp 1,
    pullback_cubicWitness,integral_appell_mul]
  norm_num

theorem cubicWitness_coefficient_three :
    actualAppellCoefficient (centeredProductMeasure 1) cubicWitness 3 (fun _=>0)=216 := by
  rw [original_coefficient_eq_scalar_integral cubicWitness_memLp 2,
    pullback_cubicWitness,integral_appell_mul]
  norm_num

theorem cubicWitness_energy_two :
    actualAppellEnergy (centeredProductMeasure 1) cubicWitness 2=1296 := by
  rw [original_energy_one,cubicWitness_coefficient_two]
  norm_num

theorem cubicWitness_energy_three :
    actualAppellEnergy (centeredProductMeasure 1) cubicWitness 3=46656 := by
  rw [original_energy_one,cubicWitness_coefficient_three]
  norm_num

theorem actual_scalar_joint_budget_is_sharp :
    (actualAppellCoefficient (centeredProductMeasure 1) cubicWitness 2 (fun _=>0))^2/8+
      (actualAppellCoefficient (centeredProductMeasure 1) cubicWitness 3 (fun _=>0)-
        (9/2:ℝ)*actualAppellCoefficient (centeredProductMeasure 1) cubicWitness 2
          (fun _=>0))^2/54=
      ∫ x,(cubicWitness x)^2 ∂centeredProductMeasure 1 := by
  rw [cubicWitness_coefficient_two,cubicWitness_coefficient_three,cubicWitness_square]
  norm_num

def unitWitness (x : Space 1) : ℝ := cubicWitness x/Real.sqrt 216

theorem unitWitness_memLp : MemLp unitWitness 2 (centeredProductMeasure 1) := by
  change MemLp (fun x=>cubicWitness x/Real.sqrt 216) 2 (centeredProductMeasure 1)
  simpa only [div_eq_mul_inv] using
    cubicWitness_memLp.mul_const (Real.sqrt 216)⁻¹

theorem unitWitness_square :
    (∫ x,(unitWitness x)^2 ∂centeredProductMeasure 1)=1 := by
  simp_rw [unitWitness,div_pow]
  rw [integral_div,Real.sq_sqrt (by norm_num : (0:ℝ)≤216),cubicWitness_square]
  norm_num

theorem unitWitness_coefficient (m : ℕ) :
    actualAppellCoefficient (centeredProductMeasure 1) unitWitness (m+1) (fun _=>0)=
      actualAppellCoefficient (centeredProductMeasure 1) cubicWitness (m+1) (fun _=>0)/
        Real.sqrt 216 := by
  rw [original_coefficient_eq_scalar_integral unitWitness_memLp m,
    original_coefficient_eq_scalar_integral cubicWitness_memLp m]
  change (∫ y,(cubicWitness (scalarCenter y)/Real.sqrt 216)*appell m y ∂expMeasure 1)=_
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div]
  rfl

theorem unitWitness_energy_two :
    actualAppellEnergy (centeredProductMeasure 1) unitWitness 2=6 := by
  rw [original_energy_one,unitWitness_coefficient 1,cubicWitness_coefficient_two,
    div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤216)]
  norm_num

theorem unitWitness_energy_three :
    actualAppellEnergy (centeredProductMeasure 1) unitWitness 3=216 := by
  rw [original_energy_one,unitWitness_coefficient 2,cubicWitness_coefficient_three,
    div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤216)]
  norm_num

def unitWitnessLp : Lp ℝ 2 (centeredProductMeasure 1) := unitWitness_memLp.toLp unitWitness

theorem unitWitnessLp_norm : ‖unitWitnessLp‖=1 := by
  have hsq : ‖unitWitnessLp‖^2=1 := by
    rw [actualLp_norm_sq_eq_integral]
    have he : (∫ x,(unitWitnessLp x)^2 ∂centeredProductMeasure 1)=
        ∫ x,(unitWitness x)^2 ∂centeredProductMeasure 1 := by
      apply integral_congr_ae
      exact unitWitness_memLp.coeFn_toLp.mono (fun x hx=>congrArg (fun a:ℝ=>a^2) hx)
    rw [he,unitWitness_square]
  nlinarith [norm_nonneg unitWitnessLp]

theorem unitWitnessLp_energy (m : ℕ) :
    actualAppellEnergy (centeredProductMeasure 1) unitWitnessLp m=
      actualAppellEnergy (centeredProductMeasure 1) unitWitness m :=
  actualAppellEnergy_congr_ae unitWitness_memLp.coeFn_toLp

/-- Necessary constraint for any original-interface seed on unit L² tests. -/
theorem unit_seed_requires_product_constraint (B : ℝ) (φ : ℝ→ℝ)
    (hseed : ∀ f : Lp ℝ 2 (centeredProductMeasure 1), ‖f‖=1 →
      actualAppellEnergy (centeredProductMeasure 1) f 3≤
        36*B*φ (actualAppellEnergy (centeredProductMeasure 1) f 2/8)) :
    6≤B*φ (3/4:ℝ) := by
  have h := hseed unitWitnessLp unitWitnessLp_norm
  rw [unitWitnessLp_energy,unitWitnessLp_energy,
    unitWitness_energy_three,unitWitness_energy_two] at h
  norm_num at h
  nlinarith

/-- A cap-six decreasing seed already fails for the actual scalar exponential. -/
theorem decreasing_cap_six_seed_is_false (φ : ℝ→ℝ) (hφ : φ (3/4:ℝ)<1) :
    ¬(∀ f : Lp ℝ 2 (centeredProductMeasure 1), ‖f‖=1 →
      actualAppellEnergy (centeredProductMeasure 1) f 3≤
        36*6*φ (actualAppellEnergy (centeredProductMeasure 1) f 2/8)) := by
  intro hseed
  have h := unit_seed_requires_product_constraint 6 φ hseed
  nlinarith

/-- Every barrier shape currently used in the seed architecture forces B>6,
regardless of how its polynomial certificate is chosen. -/
theorem existing_barrier_shape_forces_cap_strictly_above_six
    (b : ScalarVariableBarrierShape) (B : ℝ)
    (hseed : ∀ f : Lp ℝ 2 (centeredProductMeasure 1), ‖f‖=1 →
      actualAppellEnergy (centeredProductMeasure 1) f 3≤
        36*B*b.phi (actualAppellEnergy (centeredProductMeasure 1) f 2/8)) : 6<B := by
  have hs : StrictAntiOn b.phi (Icc (0:ℝ) 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) b.continuous
    intro u hu
    exact b.derivative_negative u (interior_subset hu)
  have hφ : b.phi (3/4:ℝ)<1 := by
    have h := hs (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1)
      (by norm_num : (3/4:ℝ)∈Icc (0:ℝ) 1) (by norm_num : (0:ℝ)<3/4)
    rwa [b.zero] at h
  have hp : 0≤b.phi (3/4:ℝ) := (b.positive _ (by norm_num)).le
  have hn := unit_seed_requires_product_constraint B b.phi hseed
  by_contra h
  have hb : B≤6 := le_of_not_gt h
  have hm := mul_le_mul_of_nonneg_right hb hp
  nlinarith

end KLSImprovement.CubicSeedObstruction
#print axioms KLSImprovement.CubicSeedObstruction.actual_scalar_quadratic_cubic_joint_budget
#print axioms KLSImprovement.CubicSeedObstruction.actual_scalar_joint_budget_is_sharp
#print axioms KLSImprovement.CubicSeedObstruction.unitWitnessLp_norm
#print axioms KLSImprovement.CubicSeedObstruction.unit_seed_requires_product_constraint
#print axioms KLSImprovement.CubicSeedObstruction.decreasing_cap_six_seed_is_false
#print axioms KLSImprovement.CubicSeedObstruction.existing_barrier_shape_forces_cap_strictly_above_six
