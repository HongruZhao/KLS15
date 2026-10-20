import Mathlib

/-! A genuine C1 inverse barrier, including neighborhoods of both closed
induction endpoints. No analytic or C-infinity inverse is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace KLSBelow25
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

 structure DescendingC1Barrier where
  left : ℝ
  right : ℝ
  U : ℝ → ℝ
  Up : ℝ → ℝ
  left_positive : 0 < left
  left_lt_one : left < 1
  one_lt_right : 1 < right
  continuous : ContinuousOn U (Icc left 1)
  strictDerivative : ∀ z ∈ Ioo left right, HasStrictDerivAt U (Up z) z
  derivative_negative : ∀ z ∈ Ioo left right, Up z < 0
  derivative_antitone : AntitoneOn Up (Icc left 1)
  zero : U 1 = 0
  endpoint : 1 < U left

namespace DescendingC1Barrier
variable (b : DescendingC1Barrier)

def branch : Set ℝ := Ioo b.left b.right

 theorem strictAntiOn_U : StrictAntiOn b.U b.branch := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
  · intro z hz
    exact (b.strictDerivative z hz).hasDerivAt.continuousAt.continuousWithinAt
  · intro z hz
    have hmem : z ∈ b.branch := interior_subset hz
    rw [(b.strictDerivative z hmem).hasDerivAt.deriv]
    exact b.derivative_negative z hmem

def phi (u : ℝ) : ℝ := by
  classical
  exact if h : ∃ z ∈ b.branch, b.U z=u then Classical.choose h else 1

 theorem phi_spec {u : ℝ} (hu : ∃ z ∈ b.branch, b.U z=u) :
    b.phi u ∈ b.branch ∧ b.U (b.phi u)=u := by
  simp only [phi,dite_eq_left hu]
  exact Classical.choose_spec hu

 theorem phi_eq_of_root {u z : ℝ} (hz : z ∈ b.branch) (heq : b.U z=u) :
    b.phi u=z := by
  have hp := b.phi_spec ⟨z,hz,heq⟩
  exact b.strictAntiOn_U.injOn hp.1 hz (hp.2.trans heq.symm)

 theorem phi_branch_of_unit {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    b.phi u ∈ Ioc b.left 1 ∧ b.U (b.phi u)=u := by
  have hlo : b.U 1 ≤ u := by rw [b.zero];exact hu.1
  have hhi : u ≤ b.U b.left := hu.2.trans b.endpoint.le
  obtain ⟨z,hz,heq⟩ := intermediate_value_Icc' b.left_lt_one.le b.continuous ⟨hlo,hhi⟩
  have hzlo : b.left < z := by
    by_contra hn
    have he : z=b.left := le_antisymm (not_lt.mp hn) hz.1
    rw [he] at heq
    linarith [b.endpoint,hu.2]
  have hzb : z ∈ b.branch := ⟨hzlo,hz.2.trans_lt b.one_lt_right⟩
  rw [b.phi_eq_of_root hzb heq]
  exact ⟨⟨hzlo,hz.2⟩,heq⟩

 theorem phi_open_branch {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    b.phi u ∈ b.branch := by
  have hp := b.phi_branch_of_unit hu
  exact ⟨hp.1.1,hp.1.2.trans_lt b.one_lt_right⟩

 theorem phi_zero : b.phi 0=1 :=
  b.phi_eq_of_root ⟨b.left_lt_one,b.one_lt_right⟩ b.zero

 theorem hasDerivAt_phi_of_root {u z : ℝ} (hz : z ∈ b.branch) (heq : b.U z=u) :
    HasDerivAt b.phi (b.Up z)⁻¹ u := by
  have hne := ne_of_lt (b.derivative_negative z hz)
  let hd := b.strictDerivative z hz
  let g := hd.localInverse b.U (b.Up z) z hne
  have hg : HasDerivAt g (b.Up z)⁻¹ (b.U z) := (hd.to_localInverse hne).hasDerivAt
  have hgz : g (b.U z)=z := (hd.eventually_left_inverse hne).self_of_nhds
  have hmem : ∀ᶠ v in 𝓝 (b.U z), g v ∈ b.branch := by
    apply hg.continuousAt.eventually
    exact isOpen_Ioo.mem_nhds (hgz.symm ▸ hz)
  have hright : ∀ᶠ v in 𝓝 (b.U z), b.U (g v)=v := hd.eventually_right_inverse hne
  have hevent : b.phi =ᶠ[𝓝 (b.U z)] g := by
    filter_upwards [hmem,hright] with v hv hUv
    exact b.phi_eq_of_root hv hUv
  have hr := hg.congr_of_eventuallyEq hevent
  rwa [heq] at hr

 theorem hasDerivAt_phi {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    HasDerivAt b.phi (b.Up (b.phi u))⁻¹ u :=
  b.hasDerivAt_phi_of_root (b.phi_open_branch hu) (b.phi_branch_of_unit hu).2

 theorem continuousOn_phi : ContinuousOn b.phi (Icc (0 : ℝ) 1) := by
  intro u hu
  exact (b.hasDerivAt_phi hu).continuousAt.continuousWithinAt

 theorem phi_positive {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : 0 < b.phi u :=
  b.left_positive.trans (b.phi_branch_of_unit hu).1.1

 theorem deriv_phi_negative {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : deriv b.phi u < 0 := by
  rw [(b.hasDerivAt_phi hu).deriv]
  exact inv_lt_zero.mpr (b.derivative_negative _ (b.phi_open_branch hu))

 theorem strictAntiOn_phi : StrictAntiOn b.phi (Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact b.continuousOn_phi
  · intro u hu
    exact b.deriv_phi_negative (interior_subset hu)

 theorem antitoneOn_deriv_phi : AntitoneOn (deriv b.phi) (Icc (0 : ℝ) 1) := by
  intro u hu v hv huv
  rw [(b.hasDerivAt_phi hu).deriv,(b.hasDerivAt_phi hv).deriv]
  apply (inv_le_inv_of_neg (b.derivative_negative _ (b.phi_open_branch hv))
    (b.derivative_negative _ (b.phi_open_branch hu))).mpr
  have hpu := b.phi_branch_of_unit hu
  have hpv := b.phi_branch_of_unit hv
  exact b.derivative_antitone ⟨hpv.1.1.le,hpv.1.2⟩ ⟨hpu.1.1.le,hpu.1.2⟩
    (b.strictAntiOn_phi.antitoneOn hu hv huv)

 theorem concaveOn_phi : ConcaveOn ℝ (Icc (0 : ℝ) 1) b.phi := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc _ _) b.continuousOn_phi
  · intro u hu
    exact (b.hasDerivAt_phi (interior_subset hu)).differentiableAt.differentiableWithinAt
  · exact b.antitoneOn_deriv_phi.mono interior_subset

end DescendingC1Barrier
end KLSBelow25
#print axioms KLSBelow25.DescendingC1Barrier.hasDerivAt_phi
#print axioms KLSBelow25.DescendingC1Barrier.concaveOn_phi
