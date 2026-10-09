import QuinticInterval24886
import QuinticScalarCertificate

/-! The scalar inverse barrier is an actual smooth function, not a choice of
unrelated inverse values.  This file does not assert the Appell induction or
the Poincare endpoint. -/
noncomputable section
open Filter Set
open scoped Topology
namespace Quintic24886

def branch : Set ℝ := Ioo (29 / 50) (101 / 100)

theorem Wpp_positive_of_nonpos {v : ℝ} (hv : -1 ≤ v) (hv0 : v ≤ 0) :
    0 < Wpp v := by
  have hp : (-v) ^ 3 ≤ (1 : ℝ) ^ 3 := by
    gcongr <;> linarith
  have hsq : 0 ≤ v ^ 2 := sq_nonneg v
  norm_num [Wpp, kappa] at *
  nlinarith

theorem Upp_negative_extended {z : ℝ}
    (hz : z ∈ Icc (29 / 50) (101 / 100)) : Upp z < 0 := by
  by_cases hz1 : z ≤ 1
  · exact Upp_negative_on_interval ⟨hz.1, hz1⟩
  · have hx0 : x z ≤ 0 := by unfold x L; linarith
    have hxlo : -1 ≤ x z := by unfold x L; linarith [hz.2]
    have h := Wpp_positive_of_nonpos hxlo hx0
    norm_num [Upp, P, Q, L]
    nlinarith

theorem Up_strictAntiOn_extended :
    StrictAntiOn Up (Icc (29 / 50) (101 / 100)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact (continuous_iff_continuousAt.mpr
      (fun z => (hasDerivAt_Up z).continuousAt)).continuousOn
  · intro z hz
    rw [(hasDerivAt_Up z).deriv]
    exact Upp_negative_extended (interior_subset hz)

theorem Up_negative_extended {z : ℝ}
    (hz : z ∈ Icc (29 / 50) (101 / 100)) : Up z < 0 := by
  have h := Up_strictAntiOn_extended.antitoneOn
    (show (29 / 50 : ℝ) ∈ Icc (29 / 50) (101 / 100) by norm_num) hz hz.1
  exact lt_of_le_of_lt h barrier_endpoint_derivative_negative

theorem U_strictAntiOn_extended :
    StrictAntiOn U (Icc (29 / 50) (101 / 100)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact (continuous_iff_continuousAt.mpr
      (fun z => (hasDerivAt_U z).continuousAt)).continuousOn
  · intro z hz
    rw [(hasDerivAt_U z).deriv]
    exact Up_negative_extended (interior_subset hz)

theorem analyticAt_U (z : ℝ) : AnalyticAt ℝ U z := by
  unfold U W x
  fun_prop

def phi (u : ℝ) : ℝ := by
  classical
  exact if h : ∃ z ∈ branch, U z = u then Classical.choose h else 1

theorem phi_spec {u : ℝ} (hu : ∃ z ∈ branch, U z = u) :
    phi u ∈ branch ∧ U (phi u) = u := by
  simp only [phi, dite_eq_left hu]
  exact Classical.choose_spec hu

theorem phi_eq_of_root {u z : ℝ} (hz : z ∈ branch) (heq : U z = u) :
    phi u = z := by
  have hp := phi_spec ⟨z, hz, heq⟩
  apply U_strictAntiOn_extended.injOn
    (Ioo_subset_Icc_self hp.1) (Ioo_subset_Icc_self hz)
  exact hp.2.trans heq.symm

theorem phi_branch_of_unit {u : ℝ} (hu : u ∈ Icc 0 1) :
    phi u ∈ Icc (29 / 50) 1 ∧ U (phi u) = u := by
  obtain ⟨z, ⟨hz, heq⟩, _⟩ := U_branch_has_all_values u hu
  have hzlo : (29 / 50 : ℝ) < z := by
    by_contra hn
    have he : z = 29 / 50 := le_antisymm (not_lt.mp hn) hz.1
    rw [he] at heq
    linarith [barrier_endpoint_above_one, hu.2]
  have hzb : z ∈ branch := ⟨hzlo, by linarith [hz.2]⟩
  rw [phi_eq_of_root hzb heq]
  exact ⟨hz, heq⟩

theorem phi_zero : phi 0 = 1 :=
  phi_eq_of_root (by norm_num [branch]) barrier_at_one

/-- Every inverse value on the open branch agrees locally with a single
analytic inverse. This includes neighborhoods of u=0 and u=1. -/
theorem analyticAt_phi_of_root {u z : ℝ}
    (hz : z ∈ branch) (heq : U z = u) : AnalyticAt ℝ phi u := by
  have hne : deriv U z ≠ 0 := by
    rw [(hasDerivAt_U z).deriv]
    exact ne_of_lt (Up_negative_extended (Ioo_subset_Icc_self hz))
  let ha := analyticAt_U z
  let g := ha.hasStrictDerivAt.localInverse U (deriv U z) z hne
  have hg : AnalyticAt ℝ g (U z) := ha.analyticAt_localInverse hne
  have hgz : g (U z) = z :=
    (ha.hasStrictDerivAt.eventually_left_inverse hne).self_of_nhds
  have hmem : ∀ᶠ v in 𝓝 (U z), g v ∈ branch := by
    apply hg.continuousAt.eventually
    exact isOpen_Ioo.mem_nhds (hgz.symm ▸ hz)
  have hright : ∀ᶠ v in 𝓝 (U z), U (g v) = v :=
    ha.hasStrictDerivAt.eventually_right_inverse hne
  have hevent : g =ᶠ[𝓝 (U z)] phi := by
    filter_upwards [hmem, hright] with v hv hUv
    exact (phi_eq_of_root hv hUv).symm
  rw [← heq]
  exact hg.congr hevent

theorem analyticAt_phi {u : ℝ} (hu : u ∈ Icc 0 1) :
    AnalyticAt ℝ phi u := by
  have hp := phi_branch_of_unit hu
  have hlo : (29 / 50 : ℝ) < phi u := by
    by_contra hn
    have he : phi u = 29 / 50 := le_antisymm (not_lt.mp hn) hp.1.1
    rw [he] at hp
    linarith [hp.2, barrier_endpoint_above_one, hu.2]
  exact analyticAt_phi_of_root ⟨hlo, by linarith [hp.1.2]⟩ hp.2

theorem contDiffOn_phi : ContDiffOn ℝ (⊤ : ℕ∞) phi (Icc 0 1) := by
  intro u hu
  exact (analyticAt_phi hu).contDiffAt.contDiffWithinAt

theorem hasDerivAt_phi_of_root {u z : ℝ} (hz : z ∈ branch) (heq : U z = u) :
    HasDerivAt phi (Up z)⁻¹ u := by
  have hne : deriv U z ≠ 0 := by
    rw [(hasDerivAt_U z).deriv]
    exact ne_of_lt (Up_negative_extended (Ioo_subset_Icc_self hz))
  let ha := analyticAt_U z
  let g := ha.hasStrictDerivAt.localInverse U (deriv U z) z hne
  have hg : HasDerivAt g (deriv U z)⁻¹ (U z) :=
    (ha.hasStrictDerivAt.to_localInverse hne).hasDerivAt
  have hgz : g (U z) = z :=
    (ha.hasStrictDerivAt.eventually_left_inverse hne).self_of_nhds
  have hmem : ∀ᶠ v in 𝓝 (U z), g v ∈ branch := by
    apply hg.continuousAt.eventually
    exact isOpen_Ioo.mem_nhds (hgz.symm ▸ hz)
  have hright : ∀ᶠ v in 𝓝 (U z), U (g v) = v :=
    ha.hasStrictDerivAt.eventually_right_inverse hne
  have hevent : phi =ᶠ[𝓝 (U z)] g := by
    filter_upwards [hmem, hright] with v hv hUv
    exact phi_eq_of_root hv hUv
  have hret := hg.congr_of_eventuallyEq hevent
  rw [heq, (hasDerivAt_U z).deriv] at hret
  exact hret

theorem eventually_root_exists {u z : ℝ} (hz : z ∈ branch) (heq : U z = u) :
    ∀ᶠ v in 𝓝 u, ∃ y ∈ branch, U y = v := by
  have hne : deriv U z ≠ 0 := by
    rw [(hasDerivAt_U z).deriv]
    exact ne_of_lt (Up_negative_extended (Ioo_subset_Icc_self hz))
  let ha := analyticAt_U z
  let g := ha.hasStrictDerivAt.localInverse U (deriv U z) z hne
  have hg : AnalyticAt ℝ g (U z) := ha.analyticAt_localInverse hne
  have hgz : g (U z) = z :=
    (ha.hasStrictDerivAt.eventually_left_inverse hne).self_of_nhds
  have hmem : ∀ᶠ v in 𝓝 (U z), g v ∈ branch := by
    apply hg.continuousAt.eventually
    exact isOpen_Ioo.mem_nhds (hgz.symm ▸ hz)
  have hright : ∀ᶠ v in 𝓝 (U z), U (g v) = v :=
    ha.hasStrictDerivAt.eventually_right_inverse hne
  rw [← heq]
  filter_upwards [hmem, hright] with v hv hUv
  exact ⟨g v, hv, hUv⟩

theorem phi_open_branch_of_unit {u : ℝ} (hu : u ∈ Icc 0 1) : phi u ∈ branch := by
  have hp := phi_branch_of_unit hu
  have hlo : (29 / 50 : ℝ) < phi u := by
    by_contra hn
    have he : phi u = 29 / 50 := le_antisymm (not_lt.mp hn) hp.1.1
    rw [he] at hp
    linarith [hp.2, barrier_endpoint_above_one, hu.2]
  exact ⟨hlo, by linarith [hp.1.2]⟩

theorem hasDerivAt_phi {u : ℝ} (hu : u ∈ Icc 0 1) :
    HasDerivAt phi (Up (phi u))⁻¹ u :=
  hasDerivAt_phi_of_root (phi_open_branch_of_unit hu) (phi_branch_of_unit hu).2

theorem hasDerivAt_deriv_phi {u : ℝ} (hu : u ∈ Icc 0 1) :
    HasDerivAt (deriv phi) (-Upp (phi u) / (Up (phi u)) ^ 3) u := by
  have hp := phi_branch_of_unit hu
  have hne := ne_of_lt (Up_negative_on_interval hp.1)
  have hf := ((hasDerivAt_Up (phi u)).comp u (hasDerivAt_phi hu)).inv hne
  have hevent : deriv phi =ᶠ[𝓝 u] (fun v => (Up (phi v))⁻¹) := by
    filter_upwards [eventually_root_exists (phi_open_branch_of_unit hu) hp.2] with v hv
    have hvp := phi_spec hv
    exact (hasDerivAt_phi_of_root hvp.1 hvp.2).deriv
  convert hf.congr_of_eventuallyEq hevent using 1
  simp only [Function.comp_apply]
  field_simp [hne]

theorem deriv_phi_negative {u : ℝ} (hu : u ∈ Icc 0 1) : deriv phi u < 0 := by
  rw [(hasDerivAt_phi hu).deriv]
  exact inv_lt_zero.mpr (Up_negative_on_interval (phi_branch_of_unit hu).1)

theorem deriv2_phi_negative {u : ℝ} (hu : u ∈ Icc 0 1) : deriv (deriv phi) u < 0 := by
  rw [(hasDerivAt_deriv_phi hu).deriv]
  have hup := Up_negative_on_interval (phi_branch_of_unit hu).1
  have hupp := Upp_negative_on_interval (phi_branch_of_unit hu).1
  have hcube : Up (phi u) ^ 3 < 0 := by nlinarith [sq_pos_of_neg hup]
  exact div_neg_of_pos_of_neg (neg_pos.mpr hupp) hcube

theorem phi_strictAntiOn : StrictAntiOn phi (Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · intro u hu
    exact (analyticAt_phi hu).continuousAt.continuousWithinAt
  · intro u hu
    exact deriv_phi_negative (interior_subset hu)

theorem phi_strictConcaveOn : StrictConcaveOn ℝ (Icc 0 1) phi := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
  · intro u hu
    exact (analyticAt_phi hu).continuousAt.continuousWithinAt
  · intro u hu
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
      deriv2_phi_negative (interior_subset hu)

def phiMargin (u : ℝ) : ℝ :=
  (-deriv phi u / phi u) * (alpha * K * phi u - A * u - r * Real.sqrt u) -
    2 - r / Real.sqrt (phi u)

theorem phiMargin_eq {u : ℝ} (hu : u ∈ Icc 0 1) :
    phiMargin u = limitingMargin (phi u) := by
  have hp := phi_branch_of_unit hu
  rw [phiMargin, (hasDerivAt_phi hu).deriv, limitingMargin, hp.2]
  ring

theorem phiMargin_positive {u : ℝ} (hu : u ∈ Icc 0 1) : 0 < phiMargin u := by
  rw [phiMargin_eq hu]
  exact limitingMargin_positive (phi_branch_of_unit hu).1

theorem continuousOn_phiMargin : ContinuousOn phiMargin (Icc 0 1) := by
  have hphi : ContinuousOn phi (Icc 0 1) := contDiffOn_phi.continuousOn
  have hup : ContinuousOn (fun u => Up (phi u)) (Icc 0 1) :=
    (continuous_iff_continuousAt.mpr
      (fun z => (hasDerivAt_Up z).continuousAt)).comp_continuousOn hphi
  have hphine : ∀ u ∈ Icc (0 : ℝ) 1, phi u ≠ 0 := by
    intro u hu
    exact ne_of_gt (by linarith [(phi_branch_of_unit hu).1.1])
  have hupne : ∀ u ∈ Icc (0 : ℝ) 1, Up (phi u) ≠ 0 := by
    intro u hu
    exact ne_of_lt (Up_negative_on_interval (phi_branch_of_unit hu).1)
  have hcont : ContinuousOn (fun u =>
      (-1 / (phi u * Up (phi u))) *
        (alpha * K * phi u - A * u - r * Real.sqrt u) -
      2 - r / Real.sqrt (phi u)) (Icc 0 1) := by
    apply ContinuousOn.sub
    · have hq : ContinuousOn (fun u => -1 / (phi u * Up (phi u))) (Icc 0 1) :=
        continuousOn_const.div (hphi.mul hup)
          (fun u hu => mul_ne_zero (hphine u hu) (hupne u hu))
      have hpoly : ContinuousOn
          (fun u => alpha * K * phi u - A * u - r * Real.sqrt u) (Icc 0 1) :=
        ((hphi.const_mul (alpha * K)).sub (continuousOn_id.const_mul A)).sub
          (Real.continuous_sqrt.continuousOn.const_mul r)
      exact (hq.mul hpoly).sub continuousOn_const
    · apply continuousOn_const.div (Real.continuous_sqrt.comp_continuousOn hphi)
      intro u hu
      exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [(phi_branch_of_unit hu).1.1]))
  apply hcont.congr
  intro u hu
  rw [phiMargin_eq hu, limitingMargin, (phi_branch_of_unit hu).2]

theorem exists_uniform_phiMargin :
    ∃ eta : ℝ, 0 < eta ∧ ∀ u ∈ Icc (0 : ℝ) 1, eta ≤ phiMargin u := by
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn
    (by exact ⟨0, by norm_num⟩ : (Icc (0 : ℝ) 1).Nonempty) continuousOn_phiMargin
  exact ⟨phiMargin u, phiMargin_positive hu, fun v hv => hmin hv⟩

#print axioms analyticAt_phi
#print axioms contDiffOn_phi
#print axioms hasDerivAt_phi
#print axioms hasDerivAt_deriv_phi
#print axioms phi_strictConcaveOn
#print axioms exists_uniform_phiMargin
end Quintic24886
