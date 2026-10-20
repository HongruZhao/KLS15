import Mathlib

/-! Hilbert graph-core consequences of dense shifted compact range.
The actual regular-source shifted Caccioppoli proof, closed Dirichlet
operator and positivity are paper inputs. This neither asserts a core
on a boundary moment map nor supplies a numerical response estimate. -/
noncomputable section
open Filter Topology
namespace KLSConstantImprovement.RegularSourceShiftedGraphCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem positive_shifted_coercivity (v av : E)
    (hPositive : 0 ≤ inner ℝ v av) : ‖v‖ ≤ ‖av+v‖ := by
  have hSquare : ‖v‖^2 ≤ ‖av+v‖^2 := by
    rw [norm_add_sq_real]
    have hc := real_inner_comm av v
    have ha := sq_nonneg ‖av‖
    nlinarith
  have h1 := norm_nonneg v
  have h2 := norm_nonneg (av+v)
  nlinarith

theorem shifted_convergence_implies_graph_convergence
    (u au : ℕ → E) (v av : E)
    (hPositive : ∀ n, 0 ≤ inner ℝ (u n-v) (au n-av))
    (hShift : Tendsto (fun n => au n+u n) atTop (𝓝 (av+v))) :
    Tendsto u atTop (𝓝 v) ∧ Tendsto au atTop (𝓝 av) := by
  have hs : Tendsto (fun n => (au n+u n)-(av+v)) atTop (𝓝 (0:E)) := by
    simpa using hShift.sub_const (av+v)
  have hBound (n : ℕ) : ‖u n-v‖ ≤ ‖(au n+u n)-(av+v)‖ := by
    have hc := positive_shifted_coercivity (u n-v) (au n-av) (hPositive n)
    convert hc using 1 <;> congr 1 <;> abel
  have hd := squeeze_zero_norm hBound (by simpa using hs.norm)
  have hu : Tendsto u atTop (𝓝 v) := by
    simpa using hd.add_const v
  refine ⟨hu, ?_⟩
  simpa using hShift.sub hu

theorem dense_shifted_range_gives_graph_approximation
    {C : Type*} (inc op : C → E) (v av : E)
    (hDense : DenseRange (fun c => op c+inc c))
    (hPositive : ∀ c, 0 ≤ inner ℝ (inc c-v) (op c-av)) :
    ∃ seq : ℕ → C, Tendsto (fun n => inc (seq n)) atTop (𝓝 v) ∧
      Tendsto (fun n => op (seq n)) atTop (𝓝 av) := by
  obtain ⟨b, hb, ht⟩ := mem_closure_iff_seq_limit.mp (hDense (av+v))
  choose seq hseq using hb
  have heq : (fun n => op (seq n)+inc (seq n)) = b := by
    funext n
    exact hseq n
  have hShift : Tendsto (fun n => op (seq n)+inc (seq n)) atTop (𝓝 (av+v)) := by
    rw [heq]
    exact ht
  exact ⟨seq, shifted_convergence_implies_graph_convergence
    (fun n => inc (seq n)) (fun n => op (seq n)) v av
    (fun n => hPositive (seq n)) hShift⟩

end KLSConstantImprovement.RegularSourceShiftedGraphCore

#print axioms KLSConstantImprovement.RegularSourceShiftedGraphCore.positive_shifted_coercivity
#print axioms KLSConstantImprovement.RegularSourceShiftedGraphCore.shifted_convergence_implies_graph_convergence
#print axioms KLSConstantImprovement.RegularSourceShiftedGraphCore.dense_shifted_range_gives_graph_approximation
