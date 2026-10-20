import KLSConstantImprovement.ActualFixedTensorDeficit

/-! Literal coordinate expansion of the actual fixed-tensor tilt Hessian.
All derivatives are justified on the law's local exponential domain.
-/
noncomputable section
open MeasureTheory Matrix Set Filter Metric
open scoped BigOperators ContDiff Topology
namespace KLSConstantImprovement.ActualDeficitHessianExpansion
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open ActualFixedTensorDeficit
variable {n : ℕ}
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem hessian_eq_iterated {f : Space n→ℝ} (hf : ContDiffAt ℝ 2 f 0) (i j : Fin n) :
    coordinateHessian f 0 i j=iteratedFDeriv ℝ 2 f 0 ![e i,e j] := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) 0 :=
    (hf.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  rw [coordinateHessian_eq_fderiv_fderiv hd,iteratedFDeriv_two_apply]
  rfl

theorem hessian_sum {ι : Type*} [Fintype ι] {f : ι→Space n→ℝ}
    (hf : ∀ k,ContDiffAt ℝ 2 (f k) 0) (i j : Fin n) :
    coordinateHessian (fun θ=>∑ k,f k θ) 0 i j=∑ k,coordinateHessian (f k) 0 i j := by
  rw [hessian_eq_iterated (ContDiffAt.sum fun k _=>hf k),
    iteratedFDeriv_fun_sum_apply (fun k _=>hf k),_root_.sum_apply]
  exact Finset.sum_congr rfl fun k _=>(hessian_eq_iterated (hf k) i j).symm

theorem hessian_const_mul {f : Space n→ℝ} (hf : ContDiffAt ℝ 2 f 0)
    (c : ℝ) (i j : Fin n) :
    coordinateHessian (fun θ=>c*f θ) 0 i j=c*coordinateHessian f 0 i j := by
  have hs:ContDiffAt ℝ 2 (fun θ=>c*f θ) 0 := contDiffAt_const.mul hf
  rw [hessian_eq_iterated hs]
  change iteratedFDeriv ℝ 2 (c • f) 0 ![e i,e j]=_
  rw [iteratedFDeriv_const_smul_apply hf]
  simp only [ContinuousMultilinearMap.smul_apply,smul_eq_mul]
  rw [←hessian_eq_iterated hf]

theorem hessian_sub {f g : Space n→ℝ} (hf : ContDiffAt ℝ 2 f 0)
    (hg : ContDiffAt ℝ 2 g 0) (i j : Fin n) :
    coordinateHessian (fun θ=>f θ-g θ) 0 i j=
      coordinateHessian f 0 i j-coordinateHessian g 0 i j := by
  rw [hessian_eq_iterated (hf.sub hg)]
  change iteratedFDeriv ℝ 2 (f-g) 0 ![e i,e j]=_
  rw [iteratedFDeriv_sub_apply hf hg]
  simp only [ContinuousMultilinearMap.sub_apply]
  rw [←hessian_eq_iterated hf,←hessian_eq_iterated hg]

theorem hessian_fourfold_sum {f : Fin n→Fin n→Fin n→Fin n→Space n→ℝ}
    (hf : ∀ a b c d,ContDiffAt ℝ 2 (f a b c d) 0) (i j : Fin n) :
    coordinateHessian (fun θ=>∑ a,∑ b,∑ c,∑ d,f a b c d θ) 0 i j=
      ∑ a,∑ b,∑ c,∑ d,coordinateHessian (f a b c d) 0 i j := by
  rw [hessian_sum (fun a=>ContDiffAt.sum fun b _=>
    ContDiffAt.sum fun c _=>ContDiffAt.sum fun d _=>hf a b c d)]
  apply Finset.sum_congr rfl
  intro a _
  rw [hessian_sum (fun b=>ContDiffAt.sum fun c _=>ContDiffAt.sum fun d _=>hf a b c d)]
  apply Finset.sum_congr rfl
  intro b _
  rw [hessian_sum (fun c=>ContDiffAt.sum fun d _=>hf a b c d)]
  apply Finset.sum_congr rfl
  intro c _
  exact hessian_sum (hf a b c) i j

def hessianEntry (μ : Measure (Space n)) (i j a b c d : Fin n) : ℝ :=
  6*(actualFourthCumulantArray μ i j a c*(if b=d then 1 else 0)+
    actualThirdCubicArray μ j a c*actualThirdCubicArray μ i b d+
    actualThirdCubicArray μ i a c*actualThirdCubicArray μ j b d+
    (if a=c then 1 else 0)*actualFourthCumulantArray μ i j b d)-
    cumulantJet μ [i,j,a,b,c,d] 0

theorem fixedTensorDeficit_hessian {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (B C : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    coordinateHessian (fixedTensorDeficit μ B C) 0 i j=
      ∑ a,∑ b,∑ c,∑ d,B a b*C c d*hessianEntry μ i j a b c d := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨r,hr,h1⟩:=hμ.logConcave.exists_localNormExponentialDomain_one
  have hz:(0 : Space n)∈ball 0 r := by simpa using hr
  have hj (is : List (Fin n)) : ContDiffAt ℝ 2 (cumulantJet μ is) 0 :=
    ((cumulantJet_contDiffOn h1 is).contDiffAt (isOpen_ball.mem_nhds hz)).of_le (by simp)
  have hc (a b : Fin n) : ContDiffAt ℝ 2 (covarianceJet μ a b) 0 := hj [a,b]
  have he (a b c d : Fin n) : ContDiffAt ℝ 2
      (fun θ=>6*covarianceJet μ a c θ*covarianceJet μ b d θ-cumulantJet μ [a,b,c,d] θ) 0 :=
    ((contDiffAt_const.mul (hc a c)).mul (hc b d)).sub (hj [a,b,c,d])
  unfold fixedTensorDeficit
  rw [hessian_fourfold_sum (fun a b c d=>contDiffAt_const.mul (he a b c d))]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  rw [hessian_const_mul (he a b c d),hessian_sub]
  · have hm:(fun θ=>6*covarianceJet μ a c θ*covarianceJet μ b d θ)=
        fun θ=>6*(covarianceJet μ a c θ*covarianceJet μ b d θ) := by funext θ;ring
    rw [hm,hessian_const_mul ((hc a c).mul (hc b d)),covariance_product_hessian hμ,
      hessian_cumulantJet]
    rfl
  · exact (contDiffAt_const.mul (hc a c)).mul (hc b d)
  · exact hj [a,b,c,d]

theorem contractedDeficitHessian_expansion {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : KLSBelow25.CubicSymmetricNoise.Array3 (Fin n)) :
    contractedDeficitHessian μ T=
      ∑ i,∑ j,∑ a,∑ b,∑ c,∑ d,T i a b*T j c d*hessianEntry μ i j a b c d := by
  unfold contractedDeficitHessian
  simp_rw [fixedTensorDeficit_hessian hμ]

end KLSConstantImprovement.ActualDeficitHessianExpansion
#print axioms KLSConstantImprovement.ActualDeficitHessianExpansion.hessian_fourfold_sum
#print axioms KLSConstantImprovement.ActualDeficitHessianExpansion.fixedTensorDeficit_hessian
#print axioms KLSConstantImprovement.ActualDeficitHessianExpansion.contractedDeficitHessian_expansion
