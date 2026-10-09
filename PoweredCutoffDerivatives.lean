import HigherCutoffBounds

/-! Exact powered-cutoff derivative coefficients. The residual factor is a
polynomial differential expression; no quotient by the cutoff is used. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 def powerDerivativeCoefficient (η : Space n → ℝ) (p : ℕ) : List (Fin n) → Space n → ℝ
  | [] => fun _ => 1
  | i::L => fun x => ((p-L.length : ℕ) : ℝ)*coordinateDerivative η i x*
      powerDerivativeCoefficient η p L x+
      η x*coordinateDerivative (powerDerivativeCoefficient η p L) i x

 theorem powerDerivativeCoefficient_contDiff {η : Space n → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (p : ℕ) (L : List (Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (powerDerivativeCoefficient η p L) := by
  induction L with
  | nil => exact contDiff_const
  | cons i L ih =>
    exact ((contDiff_const.mul (contDiff_coordinateDerivative hη (m := (⊤ : ℕ∞)) (by simp) i)).mul ih).add
      (hη.mul (contDiff_coordinateDerivative ih (m := (⊤ : ℕ∞)) (by simp) i))

 theorem coordinateDerivative_nat_pow {η : Space n → ℝ}
    (hη : DifferentiableAt ℝ η x) (p : ℕ) (i : Fin n) :
    coordinateDerivative (fun y => (η y)^p) i x =
      (p : ℝ)*(η x)^(p-1)*coordinateDerivative η i x := by
  unfold coordinateDerivative
  rw [(hη.hasFDerivAt.pow p).fderiv]
  simp only [smul_apply,smul_eq_mul,nsmul_eq_mul]

 theorem coordinateWordDerivative_pow_factor {η : Space n → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (p : ℕ) (L : List (Fin n)) (hL : L.length ≤ p)
    (x : Space n) :
    coordinateWordDerivative (fun y => (η y)^p) L x =
      (η x)^(p-L.length)*powerDerivativeCoefficient η p L x := by
  induction L generalizing x with
  | nil => simp [coordinateWordDerivative,powerDerivativeCoefficient]
  | cons i L ih =>
    have hLp : L.length ≤ p := by simp only [List.length_cons] at hL; omega
    have he : coordinateWordDerivative (fun y => (η y)^p) L =
        fun y => (η y)^(p-L.length)*powerDerivativeCoefficient η p L y := funext (ih hLp)
    rw [coordinateWordDerivative_cons,he,
      coordinateDerivative_mul (f := fun y => (η y)^(p-L.length))
        (g := powerDerivativeCoefficient η p L) ((hη.differentiable (by simp) x).pow _)
        ((powerDerivativeCoefficient_contDiff hη p L).differentiable (by simp) x),
      coordinateDerivative_nat_pow (hη.differentiable (by simp) x)]
    have hp : p-L.length=(p-(i::L).length)+1 := by simp only [List.length_cons] at *; omega
    have hsub : p-L.length-1=p-(i::L).length := by omega
    rw [hsub,hp,pow_succ]
    simp only [powerDerivativeCoefficient]
    rw [hp]
    push_cast
    ring

 theorem powerDerivativeCoefficient_hasCompactSupport {η : Space n → ℝ}
    (hc : HasCompactSupport η) (p : ℕ) (L : List (Fin n)) (hL : L ≠ []) :
    HasCompactSupport (powerDerivativeCoefficient η p L) := by
  cases L with
  | nil => contradiction
  | cons i L =>
    exact (((hasCompactSupport_coordinateDerivative hc i).mul_left
      (f := fun _ => ((p-L.length : ℕ) : ℝ))).mul_right
      (f' := powerDerivativeCoefficient η p L)).add
      (hc.mul_right (f' := coordinateDerivative (powerDerivativeCoefficient η p L) i))

 theorem coordinateDerivative_comp_const_smul_smooth {f : Space n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) (i : Fin n) (x : Space n) :
    coordinateDerivative (fun y => f (c • y)) i x = c*coordinateDerivative f i (c • x) := by
  simpa only [coordinateWordDerivative, List.map_cons,List.map_nil,
    directionalWordDerivative_cons,directionalWordDerivative_nil,List.length_cons,List.length_nil,
    Nat.zero_add,pow_one,coordinateDerivative] using coordinateWordDerivative_comp_const_smul hf c [i] x

 theorem powerDerivativeCoefficient_comp_const_smul {η : Space n → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (p : ℕ) (L : List (Fin n)) (c : ℝ) (x : Space n) :
    powerDerivativeCoefficient (fun y => η (c • y)) p L x =
      c^L.length*powerDerivativeCoefficient η p L (c • x) := by
  induction L generalizing x with
  | nil => simp [powerDerivativeCoefficient]
  | cons i L ih =>
    have he : powerDerivativeCoefficient (fun y => η (c • y)) p L =
        fun y => c^L.length*powerDerivativeCoefficient η p L (c • y) := funext ih
    have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun y => powerDerivativeCoefficient η p L (c • y)) :=
      (powerDerivativeCoefficient_contDiff hη p L).comp (contDiff_id.const_smul c)
    have hd : coordinateDerivative (fun y => c^L.length*powerDerivativeCoefficient η p L (c • y)) i x =
        c^L.length*(c*coordinateDerivative (powerDerivativeCoefficient η p L) i (c • x)) := by
      unfold coordinateDerivative
      rw [(hcomp.differentiable (by simp) x).hasFDerivAt.const_mul (c^L.length) |>.fderiv]
      change c^L.length*coordinateDerivative (fun y => powerDerivativeCoefficient η p L (c • y)) i x = _
      rw [coordinateDerivative_comp_const_smul_smooth (powerDerivativeCoefficient_contDiff hη p L)]
      rfl
    simp only [powerDerivativeCoefficient,List.length_cons]
    rw [he,hd,coordinateDerivative_comp_const_smul_smooth hη,pow_succ]
    dsimp only
    ring

 def poweredCutoffResidual (η : Space n → ℝ) (q : ℕ) (L : List (Fin n)) (x : Space n) : ℝ :=
    (η x)^(q-L.length)*powerDerivativeCoefficient η (2*q) L x

 theorem coordinateWordDerivative_poweredCutoff {η : Space n → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (q : ℕ) (L : List (Fin n)) (hL : L.length ≤ q)
    (x : Space n) :
    coordinateWordDerivative (fun y => (η y)^(2*q)) L x =
      (η x)^q*poweredCutoffResidual η q L x := by
  rw [coordinateWordDerivative_pow_factor hη (2*q) L (by omega)]
  unfold poweredCutoffResidual
  have he : 2*q-L.length=q+(q-L.length) := by omega
  rw [he,pow_add]
  ring

 theorem smoothCutoff_poweredResidual_bound (q : ℕ) (L : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k x,
      ‖poweredCutoffResidual (smoothCutoff n k) q L x‖ ≤ cutoffScale k^L.length*C := by
  have hη : ContDiff ℝ (⊤ : ℕ∞) (unitCutoff n) := (unitCutoff n).contDiff
  have hQ := powerDerivativeCoefficient_contDiff hη (2*q) L
  have hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖powerDerivativeCoefficient (unitCutoff n) (2*q) L x‖ ≤ C := by
    by_cases hL : L=[]
    · subst L
      exact ⟨1,by norm_num,by simp [powerDerivativeCoefficient]⟩
    · obtain ⟨C,hC⟩ := (powerDerivativeCoefficient_hasCompactSupport (unitCutoff n).hasCompactSupport (2*q) L hL).exists_bound_of_continuous hQ.continuous
      exact ⟨C,(norm_nonneg _).trans (hC 0),hC⟩
  obtain ⟨C,hC,hb⟩ := hb
  refine ⟨C,hC,?_⟩
  intro k x
  have he : powerDerivativeCoefficient (smoothCutoff n k) (2*q) L x =
      cutoffScale k^L.length*powerDerivativeCoefficient (unitCutoff n) (2*q) L (cutoffScale k • x) :=
    powerDerivativeCoefficient_comp_const_smul hη (2*q) L (cutoffScale k) x
  have hnon : 0 ≤ smoothCutoff n k x := (unitCutoff n).nonneg
  have hone : smoothCutoff n k x ≤ 1 := (unitCutoff n).le_one
  unfold poweredCutoffResidual
  rw [norm_mul,he,norm_mul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hnon _),
    Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (cutoffScale_pos k).le _)]
  calc
    _ ≤ 1*(cutoffScale k^L.length*C) :=
      mul_le_mul (pow_le_one₀ hnon hone) (mul_le_mul_of_nonneg_left (hb _) (pow_nonneg (cutoffScale_pos k).le _))
        (mul_nonneg (pow_nonneg (cutoffScale_pos k).le _) (norm_nonneg _)) (by norm_num)
    _ = _ := one_mul _

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.coordinateWordDerivative_poweredCutoff
#print axioms KLS.DeterministicBridgeIntegration.smoothCutoff_poweredResidual_bound
