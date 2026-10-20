import KLSConstantImprovement.ActualDeficitHessianExpansion

/-! Linear and zero-mean product identities for locally smooth coordinate
words. These require only an open neighborhood of the evaluation point. -/
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology
namespace KLSConstantImprovement.LocalWordLinear
open KLS KLS.DeterministicBridgeIntegration
open ActualFixedTensorDeficit
variable {n : ℕ}
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem word_add {f g : Space n→ℝ} {U : Set (Space n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    {x : Space n} (hx : x∈U) (vs : List (Space n)) :
    directionalWordDerivative (fun z=>f z+g z) vs x=
      directionalWordDerivative f vs x+directionalWordDerivative g vs x := by
  have ha:=local_word_ofFn hU (hf.add hg) vs.get hx
  have hb:=local_word_ofFn hU hf vs.get hx
  have hc:=local_word_ofFn hU hg vs.get hx
  simp only [List.ofFn_get] at ha hb hc
  rw [ha]
  change iteratedFDeriv ℝ vs.length (f+g) x vs.get=_
  rw [iteratedFDeriv_add_apply ((hf.contDiffAt (hU.mem_nhds hx)).of_le (by simp))
    ((hg.contDiffAt (hU.mem_nhds hx)).of_le (by simp))]
  simp only [_root_.add_apply]
  rw [hb,hc]

theorem word_sub {f g : Space n→ℝ} {U : Set (Space n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    {x : Space n} (hx : x∈U) (vs : List (Space n)) :
    directionalWordDerivative (fun z=>f z-g z) vs x=
      directionalWordDerivative f vs x-directionalWordDerivative g vs x := by
  have ha:=local_word_ofFn hU (hf.sub hg) vs.get hx
  have hb:=local_word_ofFn hU hf vs.get hx
  have hc:=local_word_ofFn hU hg vs.get hx
  simp only [List.ofFn_get] at ha hb hc
  rw [ha]
  change iteratedFDeriv ℝ vs.length (f-g) x vs.get=_
  rw [iteratedFDeriv_sub_apply ((hf.contDiffAt (hU.mem_nhds hx)).of_le (by simp))
    ((hg.contDiffAt (hU.mem_nhds hx)).of_le (by simp))]
  simp only [_root_.sub_apply]
  rw [hb,hc]

theorem word_const_mul {f : Space n→ℝ} {U : Set (Space n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) {x : Space n} (hx : x∈U)
    (c : ℝ) (vs : List (Space n)) :
    directionalWordDerivative (fun z=>c*f z) vs x=c*directionalWordDerivative f vs x := by
  have hs:ContDiffOn ℝ (⊤ : ℕ∞) (fun z=>c*f z) U := contDiffOn_const.mul hf
  have ha:=local_word_ofFn hU hs vs.get hx
  have hb:=local_word_ofFn hU hf vs.get hx
  simp only [List.ofFn_get] at ha hb
  rw [ha]
  change iteratedFDeriv ℝ vs.length (c • f) x vs.get=_
  rw [iteratedFDeriv_const_smul_apply ((hf.contDiffAt (hU.mem_nhds hx)).of_le (by simp))]
  simp only [_root_.smul_apply,smul_eq_mul]
  rw [hb]

theorem word_sum {ι : Type*} [Fintype ι] {f : ι→Space n→ℝ}
    {U : Set (Space n)} (hU : IsOpen U)
    (hf : ∀ k,ContDiffOn ℝ (⊤ : ℕ∞) (f k) U) {x : Space n} (hx : x∈U)
    (vs : List (Space n)) :
    directionalWordDerivative (fun z=>∑ k,f k z) vs x=
      ∑ k,directionalWordDerivative (f k) vs x := by
  have hs:ContDiffOn ℝ (⊤ : ℕ∞) (fun z=>∑ k,f k z) U :=
    ContDiffOn.sum (s:=Finset.univ) fun k _=>hf k
  have ha:=local_word_ofFn hU hs vs.get hx
  simp only [List.ofFn_get] at ha
  rw [ha,iteratedFDeriv_fun_sum_apply (fun k _=>
    ((hf k).contDiffAt (hU.mem_nhds hx)).of_le (by simp)),_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hb:=local_word_ofFn hU (hf k) vs.get hx
  simpa only [List.ofFn_get] using hb.symm

theorem word_triple_product_zero {f g h : Space n→ℝ} {r : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (ball 0 r))
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (ball 0 r))
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h (ball 0 r)) (hr : 0<r)
    (hf0 : f 0=0) (hg0 : g 0=0) (hh0 : h 0=0) (i j k : Fin n) :
    directionalWordDerivative (fun z=>f z*g z*h z) [e i,e j,e k] 0=
      coordinateDerivative f i 0*coordinateDerivative g j 0*coordinateDerivative h k 0+
      coordinateDerivative f j 0*coordinateDerivative g i 0*coordinateDerivative h k 0+
      coordinateDerivative f i 0*coordinateDerivative g k 0*coordinateDerivative h j 0+
      coordinateDerivative f k 0*coordinateDerivative g i 0*coordinateDerivative h j 0+
      coordinateDerivative f j 0*coordinateDerivative g k 0*coordinateDerivative h i 0+
      coordinateDerivative f k 0*coordinateDerivative g j 0*coordinateDerivative h i 0 := by
  have hx:(0 : Space n)∈ball 0 r := by simpa using hr
  have hfa:ContDiffAt ℝ 2 f 0 := (hf.contDiffAt (isOpen_ball.mem_nhds hx)).of_le (by simp)
  have hga:ContDiffAt ℝ 2 g 0 := (hg.contDiffAt (isOpen_ball.mem_nhds hx)).of_le (by simp)
  have hD (a : Fin n) : coordinateDerivative (fun z=>f z*g z) a 0=0 := by
    rw [coordinateDerivative_mul (hfa.differentiableAt (by norm_num))
      (hga.differentiableAt (by norm_num))]
    simp [hf0,hg0]
  have hH (a b : Fin n) : coordinateHessian (fun z=>f z*g z) 0 a b=
      coordinateDerivative f b 0*coordinateDerivative g a 0+
      coordinateDerivative f a 0*coordinateDerivative g b 0 := by
    rw [coordinateHessian_mul_of_contDiffAt hfa hga]
    simp [hf0,hg0]
  have hp:=local_word_product_three isOpen_ball (hf.mul hg) hh hx (e i) (e j) (e k)
  change directionalWordDerivative (fun z=>f z*g z*h z) [e i,e j,e k] 0=
    directionalWordDerivative (fun z=>f z*g z) [e i,e j,e k] 0*h 0+
    coordinateHessian (fun z=>f z*g z) 0 i j*coordinateDerivative h k 0+
    coordinateHessian (fun z=>f z*g z) 0 i k*coordinateDerivative h j 0+
    coordinateDerivative (fun z=>f z*g z) i 0*coordinateHessian h 0 j k+
    coordinateHessian (fun z=>f z*g z) 0 j k*coordinateDerivative h i 0+
    coordinateDerivative (fun z=>f z*g z) j 0*coordinateHessian h 0 i k+
    coordinateDerivative (fun z=>f z*g z) k 0*coordinateHessian h 0 i j+
    (f 0*g 0)*directionalWordDerivative h [e i,e j,e k] 0 at hp
  rw [hh0,hf0,hg0,hD,hD,hD,hH,hH,hH] at hp
  simp only [mul_zero,zero_mul,add_zero,zero_add] at hp
  rw [hp]
  ring

end KLSConstantImprovement.LocalWordLinear
#print axioms KLSConstantImprovement.LocalWordLinear.word_add
#print axioms KLSConstantImprovement.LocalWordLinear.word_sub
#print axioms KLSConstantImprovement.LocalWordLinear.word_sum
#print axioms KLSConstantImprovement.LocalWordLinear.word_triple_product_zero
