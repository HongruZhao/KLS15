import ActualAppellMoments
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Exact algebraic and positive-matrix core of the convex-potential first
variation at the product exponential. The analytic density/whitening
derivative and integration-by-parts correspondence are not assumed proved
by this module; they are stated mathematically in the companion note. -/
noncomputable section
open MeasureTheory Matrix Polynomial
open scoped BigOperators
namespace KLSImprovement.ProductFirstVariation
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def influence (y : ℝ) : ℝ := y^6-6*y^5+9*y^4-684*y^2+1152*y
def curvatureWeight (y : ℝ) : ℝ := y^6+6*y^5+39*y^4+192*y^3
def extraWeight (y : ℝ) : ℝ := 3*y^3*(2*y^2+13*y+64)

theorem influence_whitening_correction (y : ℝ) :
    influence y=(y^3-3*y^2)^2-216-216*(y-1)-684*((y-1)^2-1) := by
  unfold influence
  ring

theorem curvatureWeight_decomposition (y : ℝ) :
    curvatureWeight y=y^3*y^3+extraWeight y := by
  unfold curvatureWeight extraWeight
  ring

theorem extraWeight_nonneg {y : ℝ} (hy : 0≤y) : 0≤extraWeight y := by
  unfold extraWeight
  positivity

def influencePoly : Polynomial ℝ := X^6-C 6*X^5+C 9*X^4-C 684*X^2+C 1152*X
def curvaturePoly : Polynomial ℝ := X^6+C 6*X^5+C 39*X^4+C 192*X^3

/-- The exact twice-integrated exponential-density identity. -/
theorem exponential_kernel_differential_identity :
    curvaturePoly.derivative.derivative-C 2*curvaturePoly.derivative+
      curvaturePoly=influencePoly := by
  norm_num [curvaturePoly,influencePoly,Polynomial.derivative_add,
    Polynomial.derivative_sub,Polynomial.derivative_mul,Polynomial.derivative_pow]
  simp only [Polynomial.C_ofNat]
  ring

theorem curvaturePoly_boundary : curvaturePoly.eval 0=0 ∧curvaturePoly.derivative.eval 0=0 := by
  norm_num [curvaturePoly,Polynomial.derivative_add,Polynomial.derivative_mul,
    Polynomial.derivative_pow]

def cubicWeights {ι : Type*} [DecidableEq ι] (y : ι→ℝ) : Matrix ι ι ℝ :=
  diagonal (fun i=>(y i)^3)
def curvatureGram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι→ℝ) (H : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (cubicWeights y)ᴴ*H*cubicWeights y+
    diagonal (fun i=>extraWeight (y i)*H i i)

/-- Convexity supplies a positive Hessian. The extra diagonal weight is
nonnegative on the positive orthant, so the whole derivative core is PSD. -/
theorem curvatureGram_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {y : ι→ℝ} (hy : ∀ i,0≤y i) {H : Matrix ι ι ℝ} (hH : H.PosSemidef) :
    (curvatureGram y H).PosSemidef := by
  apply (hH.conjTranspose_mul_mul_same (cubicWeights y)).add
  exact Matrix.PosSemidef.diagonal (fun i=>mul_nonneg (extraWeight_nonneg (hy i)) hH.diag_nonneg)

theorem curvatureGram_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι→ℝ) (H : Matrix ι ι ℝ) (i j : ι) :
    curvatureGram y H i j=(y i)^3*(y j)^3*H i j+
      (if i=j then extraWeight (y i)*H i i else 0) := by
  simp only [curvatureGram,cubicWeights,diagonal_conjTranspose,star_trivial,
    Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.add_apply,Matrix.diagonal_apply]
  ring

theorem curvatureGram_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι→ℝ) (H : Matrix ι ι ℝ) (i : ι) :
    curvatureGram y H i i=curvatureWeight (y i)*H i i := by
  simp only [curvatureGram_apply,↓reduceIte]
  rw [curvatureWeight_decomposition]
  ring

theorem curvatureGram_off_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι→ℝ) (H : Matrix ι ι ℝ) (i j : ι) (hij : i≠j) :
    curvatureGram y H i j=(y i)^3*(y j)^3*H i j := by
  rw [curvatureGram_apply,ite_eq_right hij,add_zero]

theorem negative_curvature_quadratic_nonpos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {y : ι→ℝ} (hy : ∀ i,0≤y i) {H : Matrix ι ι ℝ} (hH : H.PosSemidef) (a : ι→ℝ) :
    -(a ⬝ᵥ (curvatureGram y H *ᵥ a))≤0 := by
  have h:=(curvatureGram_posSemidef hy hH).dotProduct_mulVec_nonneg a
  simpa only [star_trivial,neg_nonpos] using h

/-- Integral positivity core only: the theorem's integrand is explicitly
the negative curvature expression, not an assumed actual Gram derivative. -/
theorem negative_curvature_integral_nonpos {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (μ : Measure Ω) (y : Ω→ι→ℝ)
    (H : Ω→Matrix ι ι ℝ) (hy : ∀ x i,0≤y x i) (hH : ∀ x,(H x).PosSemidef) (a : ι→ℝ) :
    (∫ x,-(a ⬝ᵥ (curvatureGram (y x) (H x) *ᵥ a)) ∂μ)≤0 := by
  exact integral_nonpos (fun x=>negative_curvature_quadratic_nonpos (hy x) (hH x) a)

end KLSImprovement.ProductFirstVariation
#print axioms KLSImprovement.ProductFirstVariation.exponential_kernel_differential_identity
#print axioms KLSImprovement.ProductFirstVariation.curvatureGram_posSemidef
#print axioms KLSImprovement.ProductFirstVariation.negative_curvature_integral_nonpos
