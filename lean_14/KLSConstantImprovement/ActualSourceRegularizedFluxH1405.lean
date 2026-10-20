import KLSConstantImprovement.ActualSourceRegularizedGradientH1405
import KLS.LocalWeakFiniteProduct
import KLS.WeakMomentLocalEssentialBounds

/-!
The actual regularized inverse flux and its genuine weak Jacobian.
The local Hessian is constructed by the preceding actual H2/gluing
proof, and multiplication by the actual smooth inverse metric pays the
flux product rule. Values are globally L2 for each positive epsilon;
Jacobian entries are locally L2. No connection tensor product is assumed.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceRegularizedFluxH1405
open KLS ActualBoundedCanonicalSource ActualSourceMetricRegularization405
open ActualSourceInverseMetricRegularization405 ActualSourceRegularizedEnergyForm405
open ActualSourceRegularizedGradientH1405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def regularizedWeakFlux (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (i : Fin n) (x : Space n) : ℝ :=
  ∑ a : Fin n, regularizedMetricInverse d k ε x i a *
    weightedH1Derivative d.potential a (regularizedOrdinaryInverse d hn k hε g) x

def regularizedFluxDerivative (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : Fin n → Fin n → Space n → ℝ) (i j : Fin n) (x : Space n) : ℝ :=
  ∑ a : Fin n,
    (coordinateDerivative (fun y => regularizedMetricInverse d k ε y i a) j x *
      weightedH1Derivative d.potential a (regularizedOrdinaryInverse d hn k hε g) x +
        regularizedMetricInverse d k ε x i a * D a j x)

theorem regularizedWeakFlux_memLp (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential)) (i : Fin n) :
    MemLp (regularizedWeakFlux d hn k hε g i) 2 (potentialMeasure d.potential) := by
  exact memLp_finsetSum Finset.univ fun a _ =>
    (regularizedMetricInverse_entry_memLp_top d k hε i a (potentialMeasure d.potential)).mul (Lp.memLp _)

theorem regularizedFluxDerivative_local_L2 (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : Fin n → Fin n → Space n → ℝ)
    (hD : ∀ a j E, IsCompact E → MemLp (D a j) 2 (volume.restrict E))
    (i j : Fin n) {E : Set (Space n)} (hE : IsCompact E) :
    MemLp (regularizedFluxDerivative d hn k hε g D i j) 2 (volume.restrict E) := by
  let U := regularizedOrdinaryInverse d hn k hε g
  have hJ (a : Fin n) : ContDiff ℝ 1 (fun x => regularizedMetricInverse d k ε x i a) :=
    (contDiff_pi.mp (contDiff_pi.mp (regularizedMetricInverse_contDiff d k hε) i) a).of_le (by simp)
  apply memLp_finsetSum Finset.univ
  intro a _
  have hDJtop := memLp_continuous_top_on_compact
    (contDiff_coordinateDerivative (hJ a) (m := 0) (by norm_num) j).continuous hE
  have hJtop := memLp_continuous_top_on_compact (hJ a).continuous hE
  have hp := weightedH1Derivative_memLp_restrict d.source_C1.continuous U a hE
  exact (hDJtop.mul hp).add (hJtop.mul (hD a j E hE))

theorem regularizedWeakFlux_hasLocalWeakDerivative (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : Fin n → Fin n → Space n → ℝ)
    (hD : ∀ a j E, IsCompact E → MemLp (D a j) 2 (volume.restrict E))
    (hw : ∀ a j, HasLocalWeakCoordinateDerivative
      (weightedH1Derivative d.potential a (regularizedOrdinaryInverse d hn k hε g)) (D a j) j)
    (i j : Fin n) :
    HasLocalWeakCoordinateDerivative (regularizedWeakFlux d hn k hε g i)
      (regularizedFluxDerivative d hn k hε g D i j) j := by
  let U := regularizedOrdinaryInverse d hn k hε g
  let f (a : Fin n) (x : Space n) := regularizedMetricInverse d k ε x i a * weightedH1Derivative d.potential a U x
  let F (a : Fin n) (x : Space n) :=
    coordinateDerivative (fun y => regularizedMetricInverse d k ε y i a) j x * weightedH1Derivative d.potential a U x +
      regularizedMetricInverse d k ε x i a * D a j x
  have hJ (a : Fin n) : ContDiff ℝ 1 (fun x => regularizedMetricInverse d k ε x i a) :=
    (contDiff_pi.mp (contDiff_pi.mp (regularizedMetricInverse_contDiff d k hε) i) a).of_le (by simp)
  have hp (a : Fin n) : ∀ E : Set (Space n), IsCompact E →
      MemLp (weightedH1Derivative d.potential a U) 2 (volume.restrict E) :=
    fun E hE => weightedH1Derivative_memLp_restrict d.source_C1.continuous U a hE
  have hJtop (a : Fin n) : ∀ E : Set (Space n), IsCompact E →
      MemLp (fun x => regularizedMetricInverse d k ε x i a) ∞ (volume.restrict E) :=
    fun E hE => memLp_continuous_top_on_compact (hJ a).continuous hE
  have hDJtop (a : Fin n) : ∀ E : Set (Space n), IsCompact E →
      MemLp (coordinateDerivative (fun y => regularizedMetricInverse d k ε y i a) j)
        ∞ (volume.restrict E) := fun E hE => memLp_continuous_top_on_compact
      (contDiff_coordinateDerivative (hJ a) (m := 0) (by norm_num) j).continuous hE
  have hf2 (a : Fin n) : ∀ E : Set (Space n), IsCompact E → MemLp (f a) 2 (volume.restrict E) :=
    fun E hE => (hJtop a E hE).mul (hp a E hE)
  have hF2 (a : Fin n) : ∀ E : Set (Space n), IsCompact E → MemLp (F a) 2 (volume.restrict E) :=
    fun E hE => ((hDJtop a E hE).mul (hp a E hE)).add ((hJtop a E hE).mul (hD a j E hE))
  have hfw (a : Fin n) : HasLocalWeakCoordinateDerivative (f a) (F a) j :=
    (hasLocalWeakCoordinateDerivative_of_contDiff (hJ a) j).mul (hw a j)
      (memLp_two_on_compacts_of_top (hJtop a)) (hp a)
      (memLp_two_on_compacts_of_top (hDJtop a)) (hD a j)
  exact hasLocalWeakCoordinateDerivative_finset_sum Finset.univ
    (fun a _ => hfw a)
    (fun a _ => locallyIntegrable_of_memLp_two_on_compacts (hf2 a))
    (fun a _ => locallyIntegrable_of_memLp_two_on_compacts (hF2 a))

/-- All scalar-Hessian and vector-Jacobian witnesses are constructed from
the actual inverse and their genuine weak derivative identities. -/
theorem exists_regularizedWeakFlux_rawH1 (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0) :
    ∃ D : Fin n → Fin n → Space n → ℝ,
      (∀ a j E, IsCompact E → MemLp (D a j) 2 (volume.restrict E)) ∧
      (∀ a j, HasLocalWeakCoordinateDerivative
        (weightedH1Derivative d.potential a (regularizedOrdinaryInverse d hn k hε g)) (D a j) j) ∧
      (∀ᵐ x ∂(volume : Measure (Space n)), ∀ a j, D a j x = D j a x) ∧
      (∀ i j E, IsCompact E →
        MemLp (regularizedFluxDerivative d hn k hε g D i j) 2 (volume.restrict E)) ∧
      (∀ i j, HasLocalWeakCoordinateDerivative (regularizedWeakFlux d hn k hε g i)
        (regularizedFluxDerivative d hn k hε g D i j) j) := by
  obtain ⟨D, hD, hw, hs⟩ := exists_regularizedOrdinaryGradient_rawH1 d hn k hε g hg
  exact ⟨D, hD, hw, hs, (fun i j _ hE => regularizedFluxDerivative_local_L2 d hn k hε g D hD i j hE),
    (fun i j => regularizedWeakFlux_hasLocalWeakDerivative d hn k hε g D hD hw i j)⟩

end KLSConstantImprovement.ActualSourceRegularizedFluxH1405
#print axioms KLSConstantImprovement.ActualSourceRegularizedFluxH1405.regularizedWeakFlux_memLp
#print axioms KLSConstantImprovement.ActualSourceRegularizedFluxH1405.regularizedFluxDerivative_local_L2
#print axioms KLSConstantImprovement.ActualSourceRegularizedFluxH1405.regularizedWeakFlux_hasLocalWeakDerivative
#print axioms KLSConstantImprovement.ActualSourceRegularizedFluxH1405.exists_regularizedWeakFlux_rawH1
