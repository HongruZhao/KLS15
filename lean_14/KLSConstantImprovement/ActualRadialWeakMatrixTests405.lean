import KLSConstantImprovement.ActualLocalWeakVectorChain405
import KLSConstantImprovement.ActualRadialMatrixLipschitz405
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Actual radial bounded matrix products of a raw local H1 vector.
The derivative is computed from the genuine raw derivatives. Matrix
curvature remains a single radial contraction throughout. -/
noncomputable section
open Matrix MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace KLSConstantImprovement.ActualRadialWeakMatrixTests405
open KLS ActualVectorDifferential405 ActualLocalWeakVectorChain405
open ActualRadialMatrixCalculus405 ActualRadialMatrixLipschitz405
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def radialRawDerivative (δ : ℝ) (i j : ι) (u F : ι → Space n → ℝ) (x : Space n) : ℝ :=
  (F i x * u j x + u i x * F j x) / radialDenom δ (fun k => u k x) -
    (2 * δ * u i x * u j x * (∑ k, u k x * F k x)) / radialDenom δ (fun k => u k x) ^ 2

theorem radial_raw_derivative_eq_chain {δ : ℝ} (hδ : 0 ≤ δ) (i j : ι)
    (u F : ι → Space n → ℝ) (x : Space n) :
    (∑ k, vectorPartial (radialMatrixEntry δ i j) k (fun a => u a x) * F k x) =
      radialRawDerivative δ i j u F x := by
  rw [← fderiv_eq_sum_vectorPartial, radialMatrixEntry_differential hδ]
  rfl

theorem radial_matrix_weak_derivative {δ : ℝ} (hδ : 0 < δ) (i j : ι)
    {u F : ι → Space n → ℝ} {a : Fin n}
    (hu : ∀ k E, IsCompact E → MemLp (u k) 2 (volume.restrict E))
    (hF : ∀ k E, IsCompact E → MemLp (F k) 2 (volume.restrict E))
    (hW : ∀ k, HasLocalWeakCoordinateDerivative (u k) (F k) a) :
    HasLocalWeakCoordinateDerivative (fun x => radialMatrixEntry δ i j (fun k => u k x))
      (radialRawDerivative δ i j u F) a := by
  have hw := local_vector_chain hu hF hW (radialMatrixEntry_contDiff hδ.le i j)
    (radialMatrixEntry_lipschitz hδ i j)
  exact hw.congr_ae (Eventually.of_forall fun _ => rfl)
    (Eventually.of_forall fun x => radial_raw_derivative_eq_chain hδ.le i j u F x)

theorem radial_matrix_derivative_local_L2 {δ : ℝ} (hδ : 0 < δ) (i j : ι)
    {u F : ι → Space n → ℝ}
    (hu : ∀ k E, IsCompact E → MemLp (u k) 2 (volume.restrict E))
    (hF : ∀ k E, IsCompact E → MemLp (F k) 2 (volume.restrict E))
    (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (radialRawDerivative δ i j u F) 2 (volume.restrict E) := by
  have hm := vector_composed_derivative_local_L2 hu hF
    (radialMatrixEntry_contDiff hδ.le i j) (radialMatrixEntry_lipschitz hδ i j) E hE
  exact (memLp_congr_ae (Eventually.of_forall fun x =>
    radial_raw_derivative_eq_chain hδ.le i j u F x)).mp hm

theorem radial_matrix_value_local_L2 {δ : ℝ} (hδ : 0 < δ) (i j : ι)
    {u : ι → Space n → ℝ}
    (hu : ∀ k E, IsCompact E → MemLp (u k) 2 (volume.restrict E))
    (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (fun x => radialMatrixEntry δ i j (fun k => u k x)) 2 (volume.restrict E) :=
  (radialMatrixEntry_lipschitz hδ i j).comp_memLp (radialMatrixEntry_zero δ i j)
    (MemLp.of_eval fun k => hu k E hE)

def radialMatrix (δ : ℝ) (v : ι → ℝ) : Matrix ι ι ℝ := fun i j => radialMatrixEntry δ i j v

theorem radialMatrix_eq_smul (δ : ℝ) (v : ι → ℝ) :
    radialMatrix δ v = (radialDenom δ v)⁻¹ • Matrix.vecMulVec v v := by
  ext i j
  simp only [radialMatrix, radialMatrixEntry, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
    div_eq_mul_inv]
  ring

theorem radialMatrix_positive {δ : ℝ} (hδ : 0 ≤ δ) (v : ι → ℝ) :
    (radialMatrix δ v).PosSemidef := by
  rw [radialMatrix_eq_smul]
  have hp : (Matrix.vecMulVec v v).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star v
  exact hp.smul (inv_nonneg.mpr (radialDenom_positive hδ v).le)

theorem radial_curvature_contraction (δ : ℝ) (v : ι → ℝ) (Γ : Matrix ι ι ℝ) :
    (Γ * radialMatrix δ v).trace = (v ⬝ᵥ (Γ *ᵥ v)) / radialDenom δ v := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, radialMatrix, radialMatrixEntry,
    dotProduct, Matrix.mulVec, Finset.mul_sum, div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem radial_curvature_nonnegative {δ : ℝ} (hδ : 0 ≤ δ)
    (v : ι → ℝ) (Γ : Matrix ι ι ℝ) (hΓ : Γ.PosSemidef) :
    0 ≤ (Γ * radialMatrix δ v).trace := by
  rw [radial_curvature_contraction]
  exact div_nonneg (by simpa only [star_trivial] using hΓ.dotProduct_mulVec_nonneg v)
    (radialDenom_positive hδ v).le

theorem radial_matrix_tendsto {α : Type*} {l : Filter α} {δ : α → ℝ}
    (hδ : Tendsto δ l (𝓝 0)) (i j : ι) (v : ι → ℝ) :
    Tendsto (fun a => radialMatrixEntry (δ a) i j v) l (𝓝 (v i * v j)) := by
  have hd : Tendsto (fun a => radialDenom (δ a) v) l (𝓝 (1 : ℝ)) := by
    simpa only [radialDenom, zero_mul, add_zero] using
      tendsto_const_nhds.add (hδ.mul_const (radialSquare v))
  convert (show Tendsto (fun _ : α => v i * v j) l (𝓝 (v i * v j)) from
    tendsto_const_nhds).div hd one_ne_zero using 1 <;>
    simp only [radialMatrixEntry, Pi.div_apply, div_one] <;> rfl

end KLSConstantImprovement.ActualRadialWeakMatrixTests405

#print axioms KLSConstantImprovement.ActualRadialWeakMatrixTests405.radial_matrix_weak_derivative
#print axioms KLSConstantImprovement.ActualRadialWeakMatrixTests405.radial_matrix_derivative_local_L2
#print axioms KLSConstantImprovement.ActualRadialWeakMatrixTests405.radialMatrix_positive
#print axioms KLSConstantImprovement.ActualRadialWeakMatrixTests405.radial_curvature_contraction
#print axioms KLSConstantImprovement.ActualRadialWeakMatrixTests405.radial_matrix_tendsto
