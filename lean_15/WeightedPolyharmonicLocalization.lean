import SchwartzSobolevCommutators
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Local elliptic lifting for the actual ordered divergence-form
polyharmonic operator. Lower-order terms are controlled by explicitly
proved coordinate-word commutators; no elliptic regularity premise occurs. -/
noncomputable section
open MeasureTheory TemperedDistribution Set
open scoped ContDiff SchwartzMap LineDeriv Laplacian Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLSBelow25
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 theorem coordinateTemperedWord_cons (i : Fin n) (I : List (Fin n)) (u : 𝓢'(Space n,ℂ)) :
     coordinateTemperedWord (i::I) u=∂_{EuclideanSpace.single i (1 : ℝ)} (coordinateTemperedWord I u) := rfl

 theorem schwartz_lineDeriv_comm (ψ : 𝓢(Space n,ℂ)) (v w : Space n) :
     ∂_{v} (∂_{w} ψ)=∂_{w} (∂_{v} ψ) := by
   have h2 : ContDiff ℝ 2 (ψ : Space n → ℂ) := ψ.smooth 2
   have hd : Differentiable ℝ (fderiv ℝ (ψ : Space n → ℂ)) :=
     (h2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
   ext x
   change fderiv ℝ (fun y => fderiv ℝ (ψ : Space n → ℂ) y w) x v=
     fderiv ℝ (fun y => fderiv ℝ (ψ : Space n → ℂ) y v) x w
   rw [fderiv_clm_apply (hd x) (differentiableAt_const _),
     fderiv_clm_apply (hd x) (differentiableAt_const _)]
   simpa using (h2.contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num) |>.eq v w

 theorem tempered_lineDeriv_comm (u : 𝓢'(Space n,ℂ)) (v w : Space n) :
     ∂_{v} (∂_{w} u)=∂_{w} (∂_{v} u) := by
   ext ψ
   simp only [TemperedDistribution.lineDerivOp_apply_apply,
     LineDeriv.lineDerivOp_neg,map_neg,neg_neg]
   rw [schwartz_lineDeriv_comm]

 theorem coordinateTemperedWord_lineDeriv (I : List (Fin n)) (u : 𝓢'(Space n,ℂ)) (v : Space n) :
     coordinateTemperedWord I (∂_{v} u)=∂_{v} (coordinateTemperedWord I u) := by
   induction I with
   | nil => rfl
   | cons i I ih =>
     simp only [coordinateTemperedWord,temperedCoordinateWord] at ih ⊢
     rw [ih,tempered_lineDeriv_comm]

 theorem coordinateTemperedWord_sum {ι : Type*} (S : Finset ι)
     (f : ι → 𝓢'(Space n,ℂ)) (I : List (Fin n)) :
     coordinateTemperedWord I (∑ i ∈ S, f i)=∑ i ∈ S, coordinateTemperedWord I (f i) := by
   induction I with
   | nil => rfl
   | cons i I ih =>
     simp only [coordinateTemperedWord,temperedCoordinateWord] at ih ⊢
     rw [ih,LineDeriv.lineDerivOp_sum]

 theorem iteratedTemperedLaplacian_eq_ordered (q : ℕ) (u : 𝓢'(Space n,ℂ)) :
     iteratedTemperedLaplacian q u=
       ∑ I : Fin q → Fin n, coordinateTemperedWord (List.ofFn I++List.ofFn I) u := by
   induction q with
   | zero => simp [iteratedTemperedLaplacian,coordinateTemperedWord,temperedCoordinateWord]
   | succ q ih =>
     have hit : iteratedTemperedLaplacian (q+1) u=Δ (iteratedTemperedLaplacian q u) :=
       Function.iterate_succ_apply' _ q u
     rw [hit,TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin n) ℝ),ih]
     simp only [EuclideanSpace.basisFun_apply,LineDeriv.lineDerivOp_sum]
     rw [←(Fin.consEquiv (fun _ : Fin (q+1) => Fin n)).sum_comp
       (fun I : Fin (q+1) → Fin n => coordinateTemperedWord (List.ofFn I++List.ofFn I) u),
       Fintype.sum_prod_type]
     apply Finset.sum_congr rfl
     intro i hi
     apply Finset.sum_congr rfl
     intro I hI
     simp only [Fin.consEquiv_apply,List.ofFn_succ,Fin.tail_cons,Fin.cons_zero,Fin.cons_succ,List.cons_append,coordinateTemperedWord_cons]
     rw [coordinateTemperedWord_append,coordinateTemperedWord_append]
     change ∂_{EuclideanSpace.single i (1 : ℝ)}
         (∂_{EuclideanSpace.single i (1 : ℝ)}
           (coordinateTemperedWord (List.ofFn I) (coordinateTemperedWord (List.ofFn I) u)))=
       ∂_{EuclideanSpace.single i (1 : ℝ)}
         (coordinateTemperedWord (List.ofFn I)
           (∂_{EuclideanSpace.single i (1 : ℝ)} (coordinateTemperedWord (List.ofFn I) u)))
     rw [coordinateTemperedWord_lineDeriv]

 theorem wordMultiplierCommutator_memSobolev (s : ℕ) {u : 𝓢'(Space n,ℂ)}
     (hu : MemSobolev (s : ℝ) 2 u) (I J : List (Fin n)) (g : 𝓢(Space n,ℂ)) :
     MemSobolev ((s : ℝ)-(I.length : ℝ)-(J.length : ℝ)+1) 2
       (wordMultiplierCommutator I J g u) := by
   induction I with
   | nil =>
     simp only [wordMultiplierCommutator,coordinateTemperedWord,temperedCoordinateWord,
       List.nil_append,sub_self]
     exact memSobolev_fun_zero _ _ _ _
   | cons i I ih =>
     rw [wordMultiplierCommutator_cons]
     have h1 := ih.lineDerivOp (m := EuclideanSpace.single i (1 : ℝ))
     simp only [add_sub_cancel_right] at h1
     have h2 := schwartz_mul_coordinateWord_memSobolev s hu (I++J)
       (∂_{EuclideanSpace.single i (1 : ℝ)} g)
     have h2' : MemSobolev ((s : ℝ)-(I.length : ℝ)-(J.length : ℝ)) 2
         (TemperedDistribution.smulLeftCLM ℂ
           (∂_{EuclideanSpace.single i (1 : ℝ)} g : 𝓢(Space n,ℂ))
           (coordinateTemperedWord (I++J) u)) := by
       convert h2 using 1 <;> simp only [List.length_append,Nat.cast_add] <;> ring
     convert h1.add h2' using 1 <;> simp only [List.length_cons,Nat.cast_add,Nat.cast_one] <;> ring

 def weightedOrderedPolyharmonic (q : ℕ) (w : 𝓢(Space n,ℂ)) (u : 𝓢'(Space n,ℂ)) :
     𝓢'(Space n,ℂ) :=
   ∑ I : Fin q → Fin n, coordinateTemperedWord (List.ofFn I)
     (TemperedDistribution.smulLeftCLM ℂ w (coordinateTemperedWord (List.ofFn I) u))

 def schwartzProduct (a w : 𝓢(Space n,ℂ)) : 𝓢(Space n,ℂ) := SchwartzMap.smulLeftCLM ℂ a w

 theorem schwartzProduct_coe (a w : 𝓢(Space n,ℂ)) :
     (schwartzProduct a w : Space n → ℂ)=(w : Space n → ℂ)*(a : Space n → ℂ) := by
   funext x
   simp only [schwartzProduct,SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth,
     Pi.mul_apply,smul_eq_mul]
   ring

 theorem weighted_polyharmonic_commutator_memSobolev {q : ℕ} (hq : 1 ≤ q)
     {u : 𝓢'(Space n,ℂ)} (hu : MemSobolev ((q-1 : ℕ) : ℝ) 2 u)
     (a w : 𝓢(Space n,ℂ)) :
     MemSobolev (-(q : ℝ)) 2
       (TemperedDistribution.smulLeftCLM ℂ a (weightedOrderedPolyharmonic q w u)-
         TemperedDistribution.smulLeftCLM ℂ (schwartzProduct a w) (iteratedTemperedLaplacian q u)) := by
   have he : TemperedDistribution.smulLeftCLM ℂ a (weightedOrderedPolyharmonic q w u)-
       TemperedDistribution.smulLeftCLM ℂ (schwartzProduct a w) (iteratedTemperedLaplacian q u)=
     ∑ I : Fin q → Fin n, TemperedDistribution.smulLeftCLM ℂ a
       (wordMultiplierCommutator (List.ofFn I) (List.ofFn I) w u) := by
     rw [weightedOrderedPolyharmonic,iteratedTemperedLaplacian_eq_ordered,map_sum,map_sum,
       ←Finset.sum_sub_distrib]
     apply Finset.sum_congr rfl
     intro I hI
     rw [wordMultiplierCommutator,map_sub,
       TemperedDistribution.smulLeftCLM_smulLeftCLM_apply w.hasTemperateGrowth a.hasTemperateGrowth,
       ←schwartzProduct_coe]
   rw [he]
   apply tempered_sobolev_finset_sum Finset.univ _
   intro I hI
   have hh := schwartz_mul_wordCommutator_memSobolev (q-1) hu (List.ofFn I) (List.ofFn I) a w
   convert hh using 1 <;> simp only [List.length_ofFn,Nat.cast_sub hq,Nat.cast_one] <;> ring

 theorem polyharmonic_cutoff_commutator_memSobolev {q : ℕ} (hq : 1 ≤ q)
     {u : 𝓢'(Space n,ℂ)} (hu : MemSobolev ((q-1 : ℕ) : ℝ) 2 u) (ζ : 𝓢(Space n,ℂ)) :
     MemSobolev (-(q : ℝ)) 2
       (iteratedTemperedLaplacian q (TemperedDistribution.smulLeftCLM ℂ ζ u)-
         TemperedDistribution.smulLeftCLM ℂ ζ (iteratedTemperedLaplacian q u)) := by
   have he : iteratedTemperedLaplacian q (TemperedDistribution.smulLeftCLM ℂ ζ u)-
       TemperedDistribution.smulLeftCLM ℂ ζ (iteratedTemperedLaplacian q u)=
     ∑ I : Fin q → Fin n, wordMultiplierCommutator (List.ofFn I++List.ofFn I) [] ζ u := by
     rw [iteratedTemperedLaplacian_eq_ordered,iteratedTemperedLaplacian_eq_ordered,map_sum,
       ←Finset.sum_sub_distrib]
     simp only [wordMultiplierCommutator,List.append_nil,coordinateTemperedWord,temperedCoordinateWord]
   rw [he]
   apply tempered_sobolev_finset_sum Finset.univ _
   intro I hI
   have hh := wordMultiplierCommutator_memSobolev (q-1) hu (List.ofFn I++List.ofFn I) [] ζ
   convert hh using 1 <;> simp only [List.length_append,List.length_ofFn,List.length_nil,Nat.cast_zero,
     Nat.cast_add,Nat.cast_sub hq,Nat.cast_one] <;> ring

 theorem weighted_polyharmonic_local_lift {q : ℕ} (hq : 1 ≤ q)
     {u : 𝓢'(Space n,ℂ)} (hu : MemSobolev ((q-1 : ℕ) : ℝ) 2 u)
     (a w : 𝓢(Space n,ℂ))
     (hPDE : MemSobolev (-(q : ℝ)) 2
       (TemperedDistribution.smulLeftCLM ℂ a (weightedOrderedPolyharmonic q w u))) :
     MemSobolev (q : ℝ) 2 (TemperedDistribution.smulLeftCLM ℂ (schwartzProduct a w) u) := by
   let ζ := schwartzProduct a w
   have hc := weighted_polyharmonic_commutator_memSobolev hq hu a w
   have hh := polyharmonic_cutoff_commutator_memSobolev hq hu ζ
   have hΔ : MemSobolev (-(q : ℝ)) 2
       (iteratedTemperedLaplacian q (TemperedDistribution.smulLeftCLM ℂ ζ u)) := by
     have he : iteratedTemperedLaplacian q (TemperedDistribution.smulLeftCLM ℂ ζ u)=
         TemperedDistribution.smulLeftCLM ℂ a (weightedOrderedPolyharmonic q w u)-
           (TemperedDistribution.smulLeftCLM ℂ a (weightedOrderedPolyharmonic q w u)-
             TemperedDistribution.smulLeftCLM ℂ ζ (iteratedTemperedLaplacian q u))+
           (iteratedTemperedLaplacian q (TemperedDistribution.smulLeftCLM ℂ ζ u)-
             TemperedDistribution.smulLeftCLM ℂ ζ (iteratedTemperedLaplacian q u)) := by abel
     rw [he]
     exact (hPDE.sub hc).add hh
   have hlo := schwartz_mul_memSobolev_nat (q-1) hu ζ
   have hlow : MemSobolev (-(q : ℝ)+2*(q : ℝ)-2) 2
       (TemperedDistribution.smulLeftCLM ℂ ζ u) := hlo.mono (by simp only [Nat.cast_sub hq,Nat.cast_one]; linarith)
   have hout := tempered_sobolev_polyharmonic_lift q hlow hΔ
   convert hout using 1 <;> ring

 theorem weighted_polyharmonic_local_lift_of_zero {q : ℕ} (hq : 1 ≤ q)
     {u : 𝓢'(Space n,ℂ)} (hu : MemSobolev ((q-1 : ℕ) : ℝ) 2 u)
     (a w : 𝓢(Space n,ℂ))
     (hPDE : TemperedDistribution.smulLeftCLM ℂ a (weightedOrderedPolyharmonic q w u)=0) :
     MemSobolev (q : ℝ) 2 (TemperedDistribution.smulLeftCLM ℂ (schwartzProduct a w) u) :=
   weighted_polyharmonic_local_lift hq hu a w (hPDE ▸ memSobolev_fun_zero _ _ _ _)

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.weighted_polyharmonic_commutator_memSobolev
#print axioms KLS.DeterministicBridgeIntegration.polyharmonic_cutoff_commutator_memSobolev
#print axioms KLS.DeterministicBridgeIntegration.weighted_polyharmonic_local_lift
#print axioms KLS.DeterministicBridgeIntegration.weighted_polyharmonic_local_lift_of_zero
