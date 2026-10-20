import PoweredCutoffDerivatives
import GlobalTensorCutoffLimit
import KLS.MaskedDirections

/-! L² control of the powered-cutoff Leibniz remainder. Only jets strictly
below the tested order are required to lie in global L². -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n q : ℕ} {μ : Measure (Space n)}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

lemma maskedDirections_complement_length_lt (I : Fin q → Fin n) (b : Fin q → Bool)
    (hb : b ≠ fun _ => false) :
    (maskedDirections I (fun i => !(b i))).length < q := by
  have hp := (KLS.maskedDirections_append_complement I b).length_eq
  simp only [List.length_append,List.length_ofFn] at hp
  have hn : maskedDirections I b ≠ [] := by
    intro he
    apply hb
    funext i
    exact (maskedDirections_eq_nil_iff I b).mp he i
  have hl := List.length_pos_iff.mpr hn
  omega

def cutoffResidualConstant (q : ℕ) (L : List (Fin n)) : ℝ :=
  Classical.choose (smoothCutoff_poweredResidual_bound q L)

lemma cutoffResidualConstant_nonneg (q : ℕ) (L : List (Fin n)) :
    0 ≤ cutoffResidualConstant q L :=
  (Classical.choose_spec (smoothCutoff_poweredResidual_bound q L)).1

lemma poweredCutoffResidual_bound (q : ℕ) (L : List (Fin n)) (k : ℕ) (x : Space n) :
    ‖poweredCutoffResidual (smoothCutoff n k) q L x‖ ≤
      cutoffScale k^L.length*cutoffResidualConstant q L :=
  (Classical.choose_spec (smoothCutoff_poweredResidual_bound q L)).2 k x

lemma poweredCutoffResidual_continuous (q : ℕ) (L : List (Fin n)) (k : ℕ) :
    Continuous (poweredCutoffResidual (smoothCutoff n k) q L) := by
  have hη : ContDiff ℝ (⊤ : ℕ∞) (smoothCutoff n k) :=
    (unitCutoff n).contDiff.comp (contDiff_id.const_smul _)
  exact (hη.continuous.pow _).mul (powerDerivativeCoefficient_contDiff hη _ _).continuous

def boundedMultiplierLp (a : Space n → ℝ) (ha : AEStronglyMeasurable a μ)
    (c : ℝ) (hb : ∀ x, ‖a x‖ ≤ c) (u : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  ((memLp_top_of_bound ha c (Eventually.of_forall hb)).mul (Lp.memLp u)).toLp
    (fun x => a x*u x)

lemma boundedMultiplierLp_coe (a : Space n → ℝ) (ha : AEStronglyMeasurable a μ)
    (c : ℝ) (hb : ∀ x, ‖a x‖ ≤ c) (u : Lp ℝ 2 μ) :
    (boundedMultiplierLp a ha c hb u : Space n → ℝ) =ᵐ[μ] fun x => a x*u x :=
  MemLp.coeFn_toLp _

lemma boundedMultiplierLp_norm_le (a : Space n → ℝ) (ha : AEStronglyMeasurable a μ)
    (c : ℝ) (hb : ∀ x, ‖a x‖ ≤ c) (u : Lp ℝ 2 μ) :
    ‖boundedMultiplierLp a ha c hb u‖ ≤ c*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedMultiplierLp_coe a ha c hb u] with x hx
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

/-- The error is defined directly, including at cutoff zeros. -/
def poweredTensorCutoffRemainder (J : List (Fin n) → Space n → ℝ)
    (q k : ℕ) (I : Fin q → Fin n) (x : Space n) : ℝ :=
  ∑ b : Fin q → Bool, if b = (fun _ => false) then 0 else
    poweredCutoffResidual (smoothCutoff n k) q (maskedDirections I b) x*
      J (maskedDirections I (fun i => !(b i))) x

def poweredTensorCutoffJet (J : List (Fin n) → Space n → ℝ)
    (q k : ℕ) (I : Fin q → Fin n) (x : Space n) : ℝ :=
  ∑ b : Fin q → Bool,
    coordinateWordDerivative (fun y => (smoothCutoff n k y)^(2*q)) (maskedDirections I b) x*
      J (maskedDirections I (fun i => !(b i))) x

lemma poweredTensorCutoffJet_split (J : List (Fin n) → Space n → ℝ)
    (q k : ℕ) (I : Fin q → Fin n) (x : Space n) :
    poweredTensorCutoffJet J q k I x =
      (smoothCutoff n k x)^(2*q)*J (List.ofFn I) x+
      (smoothCutoff n k x)^q*poweredTensorCutoffRemainder J q k I x := by
  classical
  have hη : ContDiff ℝ (⊤ : ℕ∞) (smoothCutoff n k) :=
    (unitCutoff n).contDiff.comp (contDiff_id.const_smul _)
  have he : (smoothCutoff n k x)^(2*q)*J (List.ofFn I) x =
    ∑ b : Fin q → Bool, if b = (fun _ => false) then
      (smoothCutoff n k x)^(2*q)*J (List.ofFn I) x else 0 := by simp
  rw [he]
  simp only [poweredTensorCutoffJet,poweredTensorCutoffRemainder,Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : b = fun _ => false
  · subst b
    simp [maskedDirections_false,maskedDirections_true,coordinateWordDerivative,
      directionalWordDerivative_nil]
  · rw [ite_eq_right hb,ite_eq_right hb,coordinateWordDerivative_poweredCutoff hη q _
      (maskedDirections_length_le I b)]
    ring

def poweredRemainderTermLp (J : List (Fin n) → Space n → ℝ)
    (hJ : ∀ L, L.length < q → MemLp (J L) 2 μ) (I : Fin q → Fin n)
    (k : ℕ) (b : Fin q → Bool) : Lp ℝ 2 μ :=
  if hb : b = (fun _ => false) then 0 else
    boundedMultiplierLp (poweredCutoffResidual (smoothCutoff n k) q (maskedDirections I b))
      (poweredCutoffResidual_continuous q _ k).aestronglyMeasurable
      (cutoffScale k^(maskedDirections I b).length*cutoffResidualConstant q (maskedDirections I b))
      (poweredCutoffResidual_bound q _ k)
      ((hJ _ (maskedDirections_complement_length_lt I b hb)).toLp _)

def poweredTensorCutoffRemainderLp (J : List (Fin n) → Space n → ℝ)
    (hJ : ∀ L, L.length < q → MemLp (J L) 2 μ) (I : Fin q → Fin n) (k : ℕ) : Lp ℝ 2 μ :=
  ∑ b : Fin q → Bool, poweredRemainderTermLp J hJ I k b

lemma poweredRemainderTermLp_coe (J : List (Fin n) → Space n → ℝ)
    (hJ : ∀ L, L.length < q → MemLp (J L) 2 μ) (I : Fin q → Fin n)
    (k : ℕ) (b : Fin q → Bool) :
    (poweredRemainderTermLp J hJ I k b : Space n → ℝ) =ᵐ[μ] fun x =>
      if b = (fun _ => false) then 0 else
        poweredCutoffResidual (smoothCutoff n k) q (maskedDirections I b) x*
          J (maskedDirections I (fun i => !(b i))) x := by
  classical
  by_cases hb : b = fun _ => false
  · simp only [poweredRemainderTermLp,dite_eq_left hb,ite_eq_left hb]
    exact Lp.coeFn_zero _ _ _
  · simp only [poweredRemainderTermLp,dite_eq_right hb,ite_eq_right hb]
    exact (boundedMultiplierLp_coe _ _ _ _ _).trans
      (EventuallyEq.rfl.fun_mul
        (hJ _ (maskedDirections_complement_length_lt I b hb)).coeFn_toLp)

lemma poweredTensorCutoffRemainderLp_coe (J : List (Fin n) → Space n → ℝ)
    (hJ : ∀ L, L.length < q → MemLp (J L) 2 μ) (I : Fin q → Fin n) (k : ℕ) :
    (poweredTensorCutoffRemainderLp J hJ I k : Space n → ℝ) =ᵐ[μ]
      poweredTensorCutoffRemainder J q k I := by
  classical
  apply (Lp.coeFn_finsetSum _ _).trans
  have hs := eventuallyEq_sum (s := Finset.univ) fun b _ => poweredRemainderTermLp_coe J hJ I k b
  filter_upwards [hs] with x hx
  simpa only [poweredTensorCutoffRemainder,Finset.sum_apply] using hx

lemma poweredRemainderTermLp_norm_tendsto_zero (J : List (Fin n) → Space n → ℝ)
    (hJ : ∀ L, L.length < q → MemLp (J L) 2 μ) (I : Fin q → Fin n)
    (b : Fin q → Bool) :
    Tendsto (fun k => ‖poweredRemainderTermLp J hJ I k b‖) atTop (𝓝 0) := by
  classical
  by_cases hb : b = fun _ => false
  · simp only [poweredRemainderTermLp,dite_eq_left hb,norm_zero]
    exact tendsto_const_nhds
  · have hn : (maskedDirections I b).length ≠ 0 := by
      intro he
      apply hb
      funext i
      exact (maskedDirections_eq_nil_iff I b).mp (List.length_eq_zero_iff.mp he) i
    let u := (hJ _ (maskedDirections_complement_length_lt I b hb)).toLp
      (J (maskedDirections I (fun i => !(b i))))
    have ht : Tendsto (fun k => cutoffScale k^(maskedDirections I b).length*
        cutoffResidualConstant q (maskedDirections I b)*‖u‖) atTop (𝓝 0) := by
      simpa only [zero_pow hn,zero_mul] using
        ((cutoffScale_tendsto_zero.pow (maskedDirections I b).length).mul_const (cutoffResidualConstant q (maskedDirections I b))).mul_const ‖u‖
    apply squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) ht
    simp only [poweredRemainderTermLp,dite_eq_right hb]
    exact boundedMultiplierLp_norm_le _ _ _ _ _

/-- The global error vanishes using only global L² lower jets, without
assuming global L² integrability of the top jet being tested. -/
theorem poweredTensorCutoffRemainderLp_norm_tendsto_zero
    (J : List (Fin n) → Space n → ℝ)
    (hJ : ∀ L, L.length < q → MemLp (J L) 2 μ) (I : Fin q → Fin n) :
    Tendsto (fun k => ‖poweredTensorCutoffRemainderLp J hJ I k‖) atTop (𝓝 0) := by
  classical
  have ht := tendsto_finsetSum Finset.univ (fun b _ =>
    poweredRemainderTermLp_norm_tendsto_zero J hJ I b)
  simp only [Finset.sum_const_zero] at ht
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun k => norm_sum_le _ _) ht

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.poweredTensorCutoffJet_split
#print axioms KLS.DeterministicBridgeIntegration.poweredTensorCutoffRemainderLp_norm_tendsto_zero
