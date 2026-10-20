import Mathlib.Analysis.Distribution.Sobolev

/-! Genuine tempered-distribution elliptic lifting for powers of the
Euclidean Laplacian. This is a tool for the local regularity step in the
projected-divergence density proof; it is not itself that density theorem. -/
noncomputable section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv Real ENNReal
namespace KLSBelow25
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem tempered_fourierMultiplier_add {g h : E → ℂ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) :
    fourierMultiplierCLM F (g+h)=fourierMultiplierCLM F g+fourierMultiplierCLM F h := by
  have hs : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      (if i=0 then g else h).HasTemperateGrowth := by
    intro i hi
    split_ifs <;> assumption
  change fourierMultiplierCLM F (fun x => g x+h x)=_
  simpa [Pi.add_apply] using fourierMultiplierCLM_sum F hs

theorem besselPotential_two_eq_laplacian (f : 𝓢'(E,F)) :
    besselPotential E F 2 f = f-((2*π : ℂ)^2)⁻¹ • Δ f := by
  have hC : (2*π : ℂ)^2 ≠ 0 := pow_ne_zero _ (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hb : besselPotential E F 2 =
      fourierMultiplierCLM F ((fun _ : E => (1 : ℂ))+
        (fun x : E => Complex.ofReal (‖x‖^2))) := by
    unfold besselPotential
    congr 1
    funext x
    simp
  rw [hb,tempered_fourierMultiplier_add (by fun_prop) (by fun_prop),
    ContinuousLinearMap.add_apply,fourierMultiplierCLM_const]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,one_smul]
  rw [laplacian_eq_fourierMultiplierCLM]
  rw [←Complex.coe_smul (-(2*π)^2 : ℝ),smul_smul]
  have hc : ((2*π : ℂ)^2)⁻¹ * (-(2*π : ℂ)^2) = -1 := by field_simp
  push_cast
  rw [hc,neg_one_smul,sub_neg_eq_add]

theorem tempered_sobolev_laplacian_lift {s : ℝ} {f : 𝓢'(E,F)}
    (hf : MemSobolev s 2 f) (hΔ : MemSobolev s 2 (Δ f)) :
    MemSobolev (s+2) 2 f := by
  have hb : MemSobolev s 2 (besselPotential E F 2 f) := by
    rw [besselPotential_two_eq_laplacian]
    exact hf.sub (hΔ.smul _)
  simpa only [add_comm s 2] using memSobolev_besselPotential_iff.mp hb

def iteratedTemperedLaplacian (q : ℕ) (f : 𝓢'(E,F)) : 𝓢'(E,F) :=
  (fun u : 𝓢'(E,F) => Δ u)^[q] f

theorem tempered_sobolev_polyharmonic_lift (q : ℕ) {s : ℝ} {f : 𝓢'(E,F)}
    (hf : MemSobolev (s+2*(q : ℝ)-2) 2 f)
    (hΔ : MemSobolev s 2 (iteratedTemperedLaplacian q f)) :
    MemSobolev (s+2*(q : ℝ)) 2 f := by
  induction q generalizing f with
  | zero => simpa [iteratedTemperedLaplacian] using hΔ
  | succ q ih =>
      have hf' : MemSobolev (s+2*(q : ℝ)) 2 f := by
        convert hf using 1 <;> push_cast <;> ring
      have hd' : MemSobolev (s+2*(q : ℝ)-2) 2 (Δ f) := hf'.laplacian
      have hit : iteratedTemperedLaplacian q (Δ f)=
          iteratedTemperedLaplacian (q+1) f := by
        exact (Function.iterate_succ_apply _ q f).symm
      have hhigh := ih hd' (hit ▸ hΔ)
      have hout := tempered_sobolev_laplacian_lift hf' hhigh
      convert hout using 1 <;> push_cast <;> ring

theorem tempered_sobolev_finset_sum {ι : Type*} (S : Finset ι)
    {s : ℝ} (f : ι → 𝓢'(E,F)) (hf : ∀ i ∈ S, MemSobolev s 2 (f i)) :
    MemSobolev s 2 (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact memSobolev_fun_zero E F s 2
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i S)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem tempered_sobolev_first_derivatives_lift {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {s : ℝ} {f : 𝓢'(E,F)}
    (hf : MemSobolev s 2 f) (hd : ∀ i, MemSobolev s 2 (∂_{b i} f)) :
    MemSobolev (s+1) 2 f := by
  have hΔ : MemSobolev (s-1) 2 (Δ f) := by
    rw [laplacian_eq_sum b]
    exact tempered_sobolev_finset_sum Finset.univ _ (fun i _ => (hd i).lineDerivOp)
  have hout := tempered_sobolev_laplacian_lift (hf.mono (by linarith : s-1 ≤ s)) hΔ
  convert hout using 1 <;> ring

def temperedCoordinateWord {ι : Type*} (b : ι → E) : List ι → 𝓢'(E,F) → 𝓢'(E,F)
  | [],f => f
  | i::I,f => ∂_{b i} (temperedCoordinateWord b I f)

theorem temperedCoordinateWord_append {ι : Type*} (b : ι → E)
    (I J : List ι) (f : 𝓢'(E,F)) :
    temperedCoordinateWord b (I++J) f=
      temperedCoordinateWord b I (temperedCoordinateWord b J f) := by
  induction I with
  | nil => rfl
  | cons i I ih => simp only [List.cons_append,temperedCoordinateWord,ih]

theorem tempered_sobolev_of_L2_coordinate_tower {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (q : ℕ) (f : 𝓢'(E,F))
    (hf : ∀ I : List ι, I.length ≤ q → MemSobolev 0 2 (temperedCoordinateWord b I f)) :
    MemSobolev (q : ℝ) 2 f := by
  induction q generalizing f with
  | zero => simpa only [temperedCoordinateWord,Nat.cast_zero] using hf [] (by simp)
  | succ q ih =>
      have hlow := ih f (fun I hI => hf I (by omega))
      have hd (i : ι) : MemSobolev (q : ℝ) 2 (∂_{b i} f) := by
        apply ih
        intro I hI
        have hh := hf (I++[i]) (by simp only [List.length_append,List.length_singleton]; omega)
        simpa only [temperedCoordinateWord_append,temperedCoordinateWord] using hh
      simpa only [Nat.cast_add,Nat.cast_one] using
        tempered_sobolev_first_derivatives_lift b hlow hd

end KLSBelow25
#print axioms KLSBelow25.besselPotential_two_eq_laplacian
#print axioms KLSBelow25.tempered_sobolev_polyharmonic_lift
#print axioms KLSBelow25.tempered_sobolev_of_L2_coordinate_tower
