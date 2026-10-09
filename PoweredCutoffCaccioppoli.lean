import PoweredTensorCutoffRemainder

/-! Caccioppoli's energy estimate from the literal powered-cutoff test.
The top jet is required only after compact multiplication. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n q : ℕ} {μ : Measure (Space n)}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def poweredCutoffTopTensor (J : List (Fin n) → Space n → ℝ) (q k : ℕ)
    (hTop : ∀ I : Fin q → Fin n,
      MemLp (fun x => (smoothCutoff n k x)^q*J (List.ofFn I) x) 2 μ) :
    PiLp 2 (fun _ : Fin q → Fin n => Lp ℝ 2 μ) :=
  WithLp.toLp 2 (fun I => (hTop I).toLp _)

def poweredCutoffErrorTensor (J : List (Fin n) → Space n → ℝ)
    (hJ : ∀ L, L.length < q → MemLp (J L) 2 μ) (k : ℕ) :
    PiLp 2 (fun _ : Fin q → Fin n => Lp ℝ 2 μ) :=
  WithLp.toLp 2 (fun I => poweredTensorCutoffRemainderLp J hJ I k)

lemma poweredCutoffErrorTensor_norm_tendsto_zero
    (J : List (Fin n) → Space n → ℝ)
    (hJ : ∀ L, L.length < q → MemLp (J L) 2 μ) :
    Tendsto (fun k => ‖poweredCutoffErrorTensor J hJ k‖) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mp
  have ht : Tendsto (fun k I => poweredTensorCutoffRemainderLp J hJ I k) atTop
      (𝓝 (fun _ => (0 : Lp ℝ 2 μ))) := by
    apply tendsto_pi_nhds.mpr
    intro I
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      (poweredTensorCutoffRemainderLp_norm_tendsto_zero J hJ I)
  have he := (PiLp.continuous_toLp 2 (fun _ : Fin q → Fin n => Lp ℝ 2 μ)).tendsto
      (fun _ => 0) |>.comp ht
  have hz : WithLp.toLp 2 (fun _ : Fin q → Fin n => (0 : Lp ℝ 2 μ)) =
      (0 : PiLp 2 (fun _ : Fin q → Fin n => Lp ℝ 2 μ)) := rfl
  rw [hz] at he
  exact he

lemma poweredCutoff_test_inner
    (J : List (Fin n) → Space n → ℝ)
    (hJ : ∀ L, L.length < q → MemLp (J L) 2 μ) (k : ℕ)
    (hTop : ∀ I : Fin q → Fin n,
      MemLp (fun x => (smoothCutoff n k x)^q*J (List.ofFn I) x) 2 μ) :
    inner ℝ (poweredCutoffTopTensor J q k hTop)
      (poweredCutoffTopTensor J q k hTop+poweredCutoffErrorTensor J hJ k) =
      ∑ I : Fin q → Fin n, ∫ x,
        J (List.ofFn I) x*poweredTensorCutoffJet J q k I x ∂μ := by
  classical
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro I _
  rw [L2.inner_def]
  apply integral_congr_ae
  have hA : (poweredCutoffTopTensor J q k hTop I : Space n → ℝ) =ᵐ[μ]
      fun x => (smoothCutoff n k x)^q*J (List.ofFn I) x := (hTop I).coeFn_toLp
  have hE := poweredTensorCutoffRemainderLp_coe J hJ I k
  have hplus := Lp.coeFn_add (poweredCutoffTopTensor J q k hTop I)
      (poweredCutoffErrorTensor J hJ k I)
  filter_upwards [hA,hE,hplus] with x hAx hEx hpx
  change inner ℝ (poweredCutoffTopTensor J q k hTop I x)
    ((poweredCutoffTopTensor J q k hTop I+poweredCutoffErrorTensor J hJ k I) x) = _
  rw [hpx]
  simp only [Pi.add_apply]
  rw [hAx]
  change inner ℝ ((smoothCutoff n k x)^q*J (List.ofFn I) x)
    ((smoothCutoff n k x)^q*J (List.ofFn I) x+
      poweredTensorCutoffRemainderLp J hJ I k x) = _
  rw [hEx,poweredTensorCutoffJet_split]
  simp only [RCLike.inner_apply,conj_trivial]
  have hp : (smoothCutoff n k x)^(2*q)=((smoothCutoff n k x)^q)^2 := by
    rw [Nat.mul_comm,pow_mul]
  rw [hp]
  ring

lemma norm_le_error_of_inner_test_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (A E : H) (h : inner ℝ A (A+E)=0) : ‖A‖ ≤ ‖E‖ := by
  rw [inner_add_right,real_inner_self_eq_norm_sq] at h
  have hc := abs_real_inner_le_norm A E
  have he : |inner ℝ A E|=‖A‖^2 := by
    rw [show inner ℝ A E= -(‖A‖^2) by linarith,abs_neg,abs_of_nonneg (sq_nonneg _)]
  rw [he] at hc
  by_cases hz : ‖A‖=0
  · rw [hz]
    exact norm_nonneg _
  · have hp : 0 < ‖A‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

/-- The energy bound uses the actual cutoff test, not a postulated norm
bound. Its right side is already proved to vanish from lower jets. -/
theorem poweredCutoff_caccioppoli
    (J : List (Fin n) → Space n → ℝ)
    (hJ : ∀ L, L.length < q → MemLp (J L) 2 μ) (k : ℕ)
    (hTop : ∀ I : Fin q → Fin n,
      MemLp (fun x => (smoothCutoff n k x)^q*J (List.ofFn I) x) 2 μ)
    (htest : (∑ I : Fin q → Fin n, ∫ x,
      J (List.ofFn I) x*poweredTensorCutoffJet J q k I x ∂μ)=0) :
    ‖poweredCutoffTopTensor J q k hTop‖ ≤ ‖poweredCutoffErrorTensor J hJ k‖ := by
  apply norm_le_error_of_inner_test_zero
  rw [poweredCutoff_test_inner J hJ k hTop,htest]

/-- All compactly truncated top-jet energies vanish, although no global
MemLp premise for the top jet occurs in this statement. -/
theorem poweredCutoffTopTensor_norm_tendsto_zero
    (J : List (Fin n) → Space n → ℝ)
    (hJ : ∀ L, L.length < q → MemLp (J L) 2 μ)
    (hTop : ∀ k (I : Fin q → Fin n),
      MemLp (fun x => (smoothCutoff n k x)^q*J (List.ofFn I) x) 2 μ)
    (htest : ∀ k, (∑ I : Fin q → Fin n, ∫ x,
      J (List.ofFn I) x*poweredTensorCutoffJet J q k I x ∂μ)=0) :
    Tendsto (fun k => ‖poweredCutoffTopTensor J q k (hTop k)‖) atTop (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _)
    (fun k => poweredCutoff_caccioppoli J hJ k (hTop k) (htest k))
    (poweredCutoffErrorTensor_norm_tendsto_zero J hJ)

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.poweredCutoff_caccioppoli
#print axioms KLS.DeterministicBridgeIntegration.poweredCutoffTopTensor_norm_tendsto_zero
