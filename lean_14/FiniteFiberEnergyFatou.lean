import FiniteLpVectorRealization

/-! Nonnegative fiber energies pass from an actual joint graph core to
its closure by one common a.e. subsequence and Fatou. No bounded curvature
or uniform coefficient estimate is needed in this passage. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter
open scoped Topology BigOperators ENNReal
namespace KLS.DeterministicBridgeIntegration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {α ι G : Type*} [MeasurableSpace α] [Fintype ι] {μ : Measure α}
variable [NormedAddCommGroup G]

theorem finiteFiberEnergy_lintegral_le_of_graph_closure
    (Q : α → EuclideanSpace ℝ ι → ℝ)
    (hQc : ∀ x, Continuous (Q x))
    (hQm : ∀ F : FiniteScalarLp ι μ,
      AEMeasurable (fun x => ENNReal.ofReal (Q x (finiteLpVectorFunction F x))) μ)
    {S : Set (FiniteScalarLp ι μ × G)} {p : FiniteScalarLp ι μ × G}
    (hp : p ∈ closure S)
    (hS : ∀ z ∈ S, (∫⁻ x, ENNReal.ofReal (Q x (finiteLpVectorFunction z.1 x)) ∂μ) ≤
      ENNReal.ofReal (‖z.2‖^2)) :
    (∫⁻ x, ENNReal.ofReal (Q x (finiteLpVectorFunction p.1 x)) ∂μ) ≤
      ENNReal.ofReal (‖p.2‖^2) := by
  obtain ⟨z,hz,ht⟩ := mem_closure_iff_seq_limit.mp hp
  have ht1 : Tendsto (fun k => (z k).1) atTop (𝓝 p.1) :=
    continuous_fst.continuousAt.tendsto.comp ht
  obtain ⟨s,hs,hae⟩ := finiteLp_exists_subsequence_ae ht1
  have hpoint : ∀ᵐ x ∂μ, Tendsto
      (fun k => ENNReal.ofReal (Q x (finiteLpVectorFunction (z (s k)).1 x))) atTop
      (𝓝 (ENNReal.ofReal (Q x (finiteLpVectorFunction p.1 x)))) := by
    filter_upwards [hae] with x hx
    have hv : Tendsto (fun k => finiteLpVectorFunction (z (s k)).1 x) atTop
        (𝓝 (finiteLpVectorFunction p.1 x)) :=
      (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hx)
    exact ENNReal.tendsto_ofReal ((hQc x).continuousAt.tendsto.comp hv)
  have hupper : Tendsto (fun k => ENNReal.ofReal (‖(z (s k)).2‖^2)) atTop
      (𝓝 (ENNReal.ofReal (‖p.2‖^2))) :=
    ENNReal.tendsto_ofReal ((continuous_snd.norm.pow 2).continuousAt.tendsto.comp
      (ht.comp hs.tendsto_atTop))
  calc
    _ = ∫⁻ x, liminf (fun k => ENNReal.ofReal
        (Q x (finiteLpVectorFunction (z (s k)).1 x))) atTop ∂μ :=
      lintegral_congr_ae (hpoint.mono (fun x hx => hx.liminf_eq.symm))
    _ ≤ liminf (fun k => ∫⁻ x, ENNReal.ofReal
        (Q x (finiteLpVectorFunction (z (s k)).1 x)) ∂μ) atTop :=
      lintegral_liminf_le' (fun k => hQm (z (s k)).1)
    _ ≤ liminf (fun k => ENNReal.ofReal (‖(z (s k)).2‖^2)) atTop :=
      Filter.liminf_le_liminf (Eventually.of_forall (fun k => hS (z (s k)) (hz (s k))))
    _ = _ := hupper.liminf_eq

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.finiteFiberEnergy_lintegral_le_of_graph_closure
