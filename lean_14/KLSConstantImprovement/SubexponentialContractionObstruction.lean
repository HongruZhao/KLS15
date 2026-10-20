import Mathlib

/-! Pure scalar obstruction to geometric contraction under a subexponential
inverse-weight bound. This draft has not been compiled. The actual generator
degree inequalities and the value of L are separate analytic inputs. -/
noncomputable section
open Filter
open scoped Topology
namespace KLSConstantImprovement.SubexponentialContractionObstruction

/-- A shifted polynomial-times-geometric upper bound contradicts a positive
weight floor after every exponential rescaling. No sign assumption on C or
on the low-rank values of t is needed. -/
theorem subexponential_lower_not_geometric_upper
    (t : ℕ → ℝ) (D : ℕ) (hD : 2 ≤ D) (q C : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hupper : ∀ n : ℕ,
      t (D+n) ≤ C*((D+n : ℕ) : ℝ)*q^n)
    (hsub : ∀ ρ : ℝ, 1 < ρ → ∃ τ : ℝ, 0 < τ ∧
      ∀ d : ℕ, 2 ≤ d → τ ≤ t d*ρ^d) :
    False := by
  let ρ : ℝ := (1+q)/(2*q)
  have hρ1 : 1 < ρ := by
    dsimp only [ρ]
    apply (lt_div_iff₀ (by positivity : 0 < 2*q)).2
    nlinarith only [hq1]
  have hρ0 : 0 < ρ := by linarith
  have hqρ : q*ρ=(1+q)/2 := by
    dsimp only [ρ]
    field_simp [ne_of_gt hq0] <;> ring
  have ha0 : 0 ≤ q*ρ := mul_nonneg hq0.le hρ0.le
  have ha1 : q*ρ < 1 := by
    rw [hqρ]
    nlinarith only [hq1]
  obtain ⟨τ,hτ,hfloor⟩ := hsub ρ hρ1
  have hbound (n : ℕ) :
      τ ≤ C*ρ^D*(((D : ℝ)+(n : ℝ))*(q*ρ)^n) := by
    calc
      τ ≤ t (D+n)*ρ^(D+n) := hfloor (D+n) (by omega)
      _ ≤ (C*((D+n : ℕ) : ℝ)*q^n)*ρ^(D+n) :=
        mul_le_mul_of_nonneg_right (hupper n) (pow_nonneg hρ0.le _)
      _ = C*ρ^D*(((D : ℝ)+(n : ℝ))*(q*ρ)^n) := by
        rw [pow_add,mul_pow]
        push_cast
        ring
  have hgeom : Tendsto (fun n : ℕ => (q*ρ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1
  have hlinear : Tendsto (fun n : ℕ => (n : ℝ)*(q*ρ)^n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_lt_one ha0 ha1
  have hsum : Tendsto
      (fun n : ℕ => ((D : ℝ)+(n : ℝ))*(q*ρ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero,←add_mul] using
      ((hgeom.const_mul (D : ℝ)).add hlinear)
  have hlim : Tendsto
      (fun n : ℕ => C*ρ^D*(((D : ℝ)+(n : ℝ))*(q*ρ)^n))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hsum.const_mul (C*ρ^D)
  obtain ⟨n,hn⟩ := (hlim.eventually (gt_mem_nhds hτ)).exists
  exact (not_lt_of_ge (hbound n)) hn

/-- Index-safe normalized version. The input v is u_d/d in the original
degree formulation. No nonnegativity assumption on v is required. -/
theorem le_of_normalized_degree_contractions
    (K L : ℝ) (hK : 0 < K) (hL : 0 < L)
    (v t : ℕ → ℝ) (D : ℕ) (hD : 2 ≤ D)
    (hsub : ∀ ρ : ℝ, 1 < ρ → ∃ τ : ℝ, 0 < τ ∧
      ∀ d : ℕ, 2 ≤ d → τ ≤ t d*ρ^d)
    (hcontract : ∀ d : ℕ, D ≤ d → L*v d ≤ K*v (d-1))
    (hobserve : ∀ d : ℕ, D ≤ d →
      2*t d ≤ K*(d : ℝ)*v (d-1)) :
    L ≤ K := by
  by_contra hKL
  have hKL' : K < L := lt_of_not_ge hKL
  let q : ℝ := K/L
  have hq0 : 0 < q := div_pos hK hL
  have hq1 : q < 1 := (div_lt_one hL).2 hKL'
  have hstep (d : ℕ) (hd : D ≤ d) : v d ≤ q*v (d-1) := by
    have hh : v d ≤ (K*v (d-1))/L :=
      (le_div_iff₀ hL).2 (by nlinarith only [hcontract d hd])
    calc
      v d ≤ (K*v (d-1))/L := hh
      _ = q*v (d-1) := by dsimp only [q]; ring
  have hdecay (n : ℕ) : v (D+n-1) ≤ q^n*v (D-1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hind : D+(n+1)-1=D+n := by omega
      rw [hind,pow_succ]
      calc
        v (D+n) ≤ q*v (D+n-1) := hstep (D+n) (by omega)
        _ ≤ q*(q^n*v (D-1)) := mul_le_mul_of_nonneg_left ih hq0.le
        _ = q^n*q*v (D-1) := by ring
  have hupper (n : ℕ) :
      t (D+n) ≤ ((K/2)*v (D-1))*((D+n : ℕ) : ℝ)*q^n := by
    have hh := hobserve (D+n) (by omega)
    have hpayment : t (D+n) ≤
        (K/2)*((D+n : ℕ) : ℝ)*v (D+n-1) := by
      nlinarith only [hh]
    have hm : 0 ≤ (K/2)*((D+n : ℕ) : ℝ) := by positivity
    calc
      t (D+n) ≤ (K/2)*((D+n : ℕ) : ℝ)*v (D+n-1) := hpayment
      _ ≤ (K/2)*((D+n : ℕ) : ℝ)*(q^n*v (D-1)) :=
        mul_le_mul_of_nonneg_left (hdecay n) hm
      _ = ((K/2)*v (D-1))*((D+n : ℕ) : ℝ)*q^n := by ring
  exact subexponential_lower_not_geometric_upper t D hD q
    ((K/2)*v (D-1)) hq0 hq1 hupper hsub

/-- Original degree inequalities, without assuming nonnegativity at ranks0/1
or modifying their values. The normalized sequence is v_d=u_d/d. -/
theorem le_of_degree_contractions
    (K L : ℝ) (hK : 0 < K) (hL : 0 < L)
    (u t : ℕ → ℝ) (D : ℕ) (hD : 2 ≤ D)
    (hsub : ∀ ρ : ℝ, 1 < ρ → ∃ τ : ℝ, 0 < τ ∧
      ∀ d : ℕ, 2 ≤ d → τ ≤ t d*ρ^d)
    (hcontract : ∀ d : ℕ, D ≤ d →
      L*(1-1/(d : ℝ))*u d ≤ K*u (d-1))
    (hobserve : ∀ d : ℕ, D ≤ d →
      2*(1-1/(d : ℝ))*t d ≤ K*u (d-1)) :
    L ≤ K := by
  let v : ℕ → ℝ := fun d => u d/(d : ℝ)
  apply le_of_normalized_degree_contractions K L hK hL v t D hD hsub
  · intro d hd
    have hd2 : 2 ≤ d := hD.trans hd
    have hd2r : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    have hd0 : 0 < (d : ℝ) := by linarith
    have hp0 : 0 < (d : ℝ)-1 := by linarith
    have hcast : ((d-1 : ℕ) : ℝ)=(d : ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      norm_num
    have hh := mul_le_mul_of_nonneg_right (hcontract d hd) hd0.le
    have hclear : L*((d : ℝ)-1)*u d ≤ K*(d : ℝ)*u (d-1) := by
      convert hh using 1 <;> field_simp [ne_of_gt hd0] <;> ring
    calc
      L*v d = (L*u d)/(d : ℝ) := by dsimp only [v]; ring
      _ ≤ (K*u (d-1))/((d : ℝ)-1) :=
        (div_le_div_iff₀ hd0 hp0).2 (by nlinarith only [hclear])
      _ = K*v (d-1) := by dsimp only [v]; rw [hcast]; ring
  · intro d hd
    have hd2 : 2 ≤ d := hD.trans hd
    have hd2r : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    have hd0 : 0 < (d : ℝ) := by linarith
    have hp0 : 0 < (d : ℝ)-1 := by linarith
    have hcast : ((d-1 : ℕ) : ℝ)=(d : ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      norm_num
    have hh := mul_le_mul_of_nonneg_right (hobserve d hd) hd0.le
    have hclear : 2*((d : ℝ)-1)*t d ≤ K*(d : ℝ)*u (d-1) := by
      convert hh using 1 <;> field_simp [ne_of_gt hd0] <;> ring
    calc
      2*t d ≤ (K*(d : ℝ)*u (d-1))/((d : ℝ)-1) :=
        (le_div_iff₀ hp0).2 (by nlinarith only [hclear])
      _ = K*(d : ℝ)*v (d-1) := by dsimp only [v]; rw [hcast]; ring

end KLSConstantImprovement.SubexponentialContractionObstruction

#print axioms KLSConstantImprovement.SubexponentialContractionObstruction.subexponential_lower_not_geometric_upper
#print axioms KLSConstantImprovement.SubexponentialContractionObstruction.le_of_normalized_degree_contractions
#print axioms KLSConstantImprovement.SubexponentialContractionObstruction.le_of_degree_contractions
