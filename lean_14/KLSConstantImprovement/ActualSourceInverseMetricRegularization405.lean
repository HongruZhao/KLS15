import KLSConstantImprovement.ActualSourceMetricRegularization405
import KLS.WeightedEnergyCoercivity
import KLS.MatrixInverseCoercivity
import KLS.MatrixEntrySmooth
import KLS.MatrixInverseSqrtLipschitz

/-!
The actual inverse of the regularized metric. Its global bounds, local
bounds uniform in both regularization parameters, smoothness and actual
almost-everywhere limit follow from the constructed canonical source.
The source measure is unchanged throughout.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceInverseMetricRegularization405
open KLS ActualBoundedCanonicalSource ActualSourceMetricRegularization405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

private lemma matrixAction_toLp_quadratic (M : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) :
    inner ℝ (WithLp.toLp 2 a : Space n) (matrixAction M (WithLp.toLp 2 a)) =
      a ⬝ᵥ (M *ᵥ a) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    matrixAction_apply, PiLp.toLp_apply, dotProduct, Matrix.mulVec]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private lemma norm_toLp_sq_eq_dotProduct (a : Fin n → ℝ) :
    ‖(WithLp.toLp 2 a : Space n)‖ ^ 2 = a ⬝ᵥ a := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.toLp_apply, dotProduct]

/-- A positive matrix with a quadratic upper bound has the same bound on
all its entries. No dimension factor or simultaneous diagonalization is used. -/
theorem matrix_entry_abs_le_of_quadratic_upper
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) {C : ℝ}
    (hupper : ∀ a : Fin n → ℝ, a ⬝ᵥ (A *ᵥ a) ≤ C * (a ⬝ᵥ a)) (i j : Fin n) :
    |A i j| ≤ C := by
  classical
  have hdiag (k : Fin n) : A k k ≤ C := by
    simpa only [single_dotProduct, one_mul, Matrix.mulVec_single_one,
      Matrix.col_apply, Pi.single_eq_same, mul_one] using hupper (Pi.single k 1)
  have hs : A j i = A i j := (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian).apply i j
  have hp := hA.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have hm := hA.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp only [star_trivial, Matrix.mulVec_add, add_dotProduct, dotProduct_add,
    Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply, hs] at hp
  simp only [star_trivial, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
    Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply, hs] at hm
  exact abs_le.mpr ⟨by linarith [hdiag i, hdiag j], by linarith [hdiag i, hdiag j]⟩

def regularizedMetricInverse (d : SourceData μ) (k : ℕ) (ε : ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ := (regularizedMetricHessian d k ε x)⁻¹

theorem regularizedMetricInverse_posDef (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (x : Space n) : (regularizedMetricInverse d k ε x).PosDef :=
  (regularizedMetricHessian_posDef d k hε x).inv

theorem regularizedMetricInverse_contDiff (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ (⊤ : ℕ∞) (regularizedMetricInverse d k ε) := by
  apply contDiff_inverse_of_entries
  · intro i j
    exact contDiff_pi.mp (contDiff_pi.mp (regularizedMetricHessian_contDiff d k ε) i) j
  · intro x
    exact (regularizedMetricHessian_posDef d k hε x).det_pos.ne'

/-- Both reciprocal quadratic bounds are consequences of the actual
constructed Hessian bounds. -/
theorem regularizedMetricInverse_quadratic_bounds (d : SourceData μ)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) (x : Space n) (a : Fin n → ℝ) :
    (4 / d.targetConvexityConstant + ε)⁻¹ * (a ⬝ᵥ a) ≤
        a ⬝ᵥ (regularizedMetricInverse d k ε x *ᵥ a) ∧
      a ⬝ᵥ (regularizedMetricInverse d k ε x *ᵥ a) ≤ ε⁻¹ * (a ⬝ᵥ a) := by
  let H := regularizedMetricHessian d k ε x
  let K : ℝ := 4 / d.targetConvexityConstant + ε
  have hH : H.PosDef := regularizedMetricHessian_posDef d k hε x
  have hK : 0 < K := by
    have hκ := d.target_convexity_pos
    dsimp [K]
    positivity
  have hlo (b : Fin n → ℝ) : ε * (b ⬝ᵥ b) ≤ b ⬝ᵥ (H *ᵥ b) := by
    have hb := (regularizedMetricHessian_quadratic_bounds d k ε x (WithLp.toLp 2 b)).1
    simpa only [H, norm_toLp_sq_eq_dotProduct, matrixAction_toLp_quadratic] using hb
  have hup : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - H).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact (Matrix.isHermitian_one.smul (IsSelfAdjoint.all K)).sub hH.isHermitian
    intro b
    have hb := (regularizedMetricHessian_quadratic_bounds d k ε x (WithLp.toLp 2 b)).2
    have hquad : b ⬝ᵥ (H *ᵥ b) ≤ K * (b ⬝ᵥ b) := by
      simpa only [H, K, norm_toLp_sq_eq_dotProduct, matrixAction_toLp_quadratic] using hb
    simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] using
      sub_nonneg.mpr hquad
  have hlow := (inverse_lower_of_posDef_upper hH hK hup).dotProduct_mulVec_nonneg a
  have hlow' : K⁻¹ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (H⁻¹ *ᵥ a) := by
    simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      sub_nonneg] using hlow
  exact ⟨hlow', matrix_inverse_quadratic_le_of_lower_bound hH hε hlo a⟩

theorem regularizedMetricInverse_entry_bound (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (x : Space n) (i j : Fin n) :
    |regularizedMetricInverse d k ε x i j| ≤ ε⁻¹ :=
  matrix_entry_abs_le_of_quadratic_upper (regularizedMetricInverse_posDef d k hε x).posSemidef
    (fun a => (regularizedMetricInverse_quadratic_bounds d k hε x a).2) i j

theorem regularizedMetricInverse_entry_memLp_top (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (i j : Fin n) (ν : Measure (Space n)) :
    MemLp (fun x => regularizedMetricInverse d k ε x i j) ∞ ν := by
  apply memLp_top_of_bound
    (contDiff_pi.mp (contDiff_pi.mp (regularizedMetricInverse_contDiff d k hε) i) j).continuous.aestronglyMeasurable
    ε⁻¹
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using regularizedMetricInverse_entry_bound d k hε x i j

/-- Every compact inverse bound is independent of both regularization
parameters. This is the bound needed when removing regularization locally. -/
theorem regularizedMetricInverse_compact_entry_bound (d : SourceData μ)
    {E : Set (Space n)} (hE : IsCompact E) :
    ∃ B : ℝ, 0 < B ∧ ∀ k ε, 0 < ε → ∀ x ∈ E, ∀ i j,
      |regularizedMetricInverse d k ε x i j| ≤ B := by
  obtain ⟨m, hm, hlow⟩ := regularizedMetricHessian_compact_lower d hE
  refine ⟨m⁻¹, inv_pos.mpr hm, ?_⟩
  intro k ε hε x hx i j
  apply matrix_entry_abs_le_of_quadratic_upper (regularizedMetricInverse_posDef d k hε x).posSemidef
  intro a
  apply matrix_inverse_quadratic_le_of_lower_bound (regularizedMetricHessian_posDef d k hε x) hm
  intro b
  have hb := hlow k ε hε.le x hx (WithLp.toLp 2 b)
  simpa only [norm_toLp_sq_eq_dotProduct, matrixAction_toLp_quadratic] using hb

theorem regularizedMetricInverse_tendsto_ae (d : SourceData μ) :
    ∀ᵐ x ∂(volume : Measure (Space n)),
      Tendsto (fun k => regularizedMetricInverse d k (cutoffScale k) x)
        atTop (𝓝 (coordinateHessian d.potential x)⁻¹) := by
  filter_upwards [regularizedMetricHessian_tendsto_ae d, d.hessian_ae] with x hx hpos
  exact (matrix_inverse_continuousAt_posDef hpos.1).tendsto.comp hx

end KLSConstantImprovement.ActualSourceInverseMetricRegularization405
#print axioms KLSConstantImprovement.ActualSourceInverseMetricRegularization405.matrix_entry_abs_le_of_quadratic_upper
#print axioms KLSConstantImprovement.ActualSourceInverseMetricRegularization405.regularizedMetricInverse_posDef
#print axioms KLSConstantImprovement.ActualSourceInverseMetricRegularization405.regularizedMetricInverse_contDiff
#print axioms KLSConstantImprovement.ActualSourceInverseMetricRegularization405.regularizedMetricInverse_quadratic_bounds
#print axioms KLSConstantImprovement.ActualSourceInverseMetricRegularization405.regularizedMetricInverse_entry_bound
#print axioms KLSConstantImprovement.ActualSourceInverseMetricRegularization405.regularizedMetricInverse_entry_memLp_top
#print axioms KLSConstantImprovement.ActualSourceInverseMetricRegularization405.regularizedMetricInverse_compact_entry_bound
#print axioms KLSConstantImprovement.ActualSourceInverseMetricRegularization405.regularizedMetricInverse_tendsto_ae
