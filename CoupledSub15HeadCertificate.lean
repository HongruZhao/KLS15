import CoupledSub15HeadPolynomialCertificate
import SymmetricCenteredSeed245Inverse
noncomputable section
open Set
namespace KLSBelow25.CoupledEnergy.NumericsSub15
set_option maxHeartbeats 1500000
theorem correlated_head_margin {u : ℝ} (hu : u∈Icc (0 : ℝ) 1) :
    (c+head)*(2/K^2)*u+
      (c-coefficient 3)*(KLSBelow25.SymmetricCenteredSeed245.B/K^3)*KLSBelow25.SymmetricCenteredSeed245.seedPhi u<c*C := by
  have hr := KLSBelow25.SymmetricCenteredSeed245.seedParameter_range hu
  have hp := headPolynomial_positive (by simpa only [KLSBelow25.SymmetricCenteredSeed245.seedT] using hr)
  unfold headPolynomial at hp
  rw [←KLSBelow25.SymmetricCenteredSeed245.seedPhi_u_identity hu,←KLSBelow25.SymmetricCenteredSeed245.seedPhi_z_identity hu] at hp
  linarith

theorem crossing_impossible (M e2 e3 u : ℝ) (hu : u∈Icc (0 : ℝ) 1)
    (hM : C≤M) (he2 : e2≤(2/K^2)*u)
    (he3 : e3≤(KLSBelow25.SymmetricCenteredSeed245.B/K^3)*KLSBelow25.SymmetricCenteredSeed245.seedPhi u)
    (hgen : c*M-(c+head)*e2-(c-coefficient 3)*e3≤0) : False := by
  have hm := mul_le_mul_of_nonneg_left hM c_positive.le
  have h2 := mul_le_mul_of_nonneg_left he2 c_add_head_nonneg
  have h3 := mul_le_mul_of_nonneg_left he3 c_sub_coefficient_three_nonneg
  have hmargin := correlated_head_margin hu
  nlinarith

theorem finite_energy_head_reduction (e : ℕ → ℝ) (N : ℕ) (hN : 3≤N)
    (he : ∀ d∈Finset.Icc 4 N,0≤e d)
    (hgen : (∑ d∈Finset.Icc 3 N,coefficient d*e d)-head*e 2≤0) :
    c*(∑ d∈Finset.Icc 2 N,e d)-(c+head)*e 2-(c-coefficient 3)*e 3≤0 := by
  classical
  have htail : c*(∑ d∈Finset.Icc 4 N,e d)≤
      ∑ d∈Finset.Icc 4 N,coefficient d*e d := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun d hd =>
      mul_le_mul_of_nonneg_right (coefficient_lower d (Finset.mem_Icc.mp hd).1) (he d hd)
  have hset3 : Finset.Icc 3 N=insert 3 (Finset.Icc 4 N) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hset2 : Finset.Icc 2 N=insert 2 (Finset.Icc 3 N) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hn3 : 3∉Finset.Icc 4 N := by simp
  have hn2 : 2∉Finset.Icc 3 N := by simp
  rw [hset3,Finset.sum_insert hn3] at hgen
  rw [hset2,Finset.sum_insert hn2,hset3,Finset.sum_insert hn3]
  nlinarith

theorem finite_energy_sum_lt_budget (e : ℕ → ℝ) (N : ℕ) (hN : 3≤N)
    (he : ∀ d∈Finset.Icc 4 N,0≤e d) {u : ℝ} (hu : u∈Icc (0 : ℝ) 1)
    (he2 : e 2≤(2/K^2)*u)
    (he3 : e 3≤(KLSBelow25.SymmetricCenteredSeed245.B/K^3)*KLSBelow25.SymmetricCenteredSeed245.seedPhi u)
    (hgen : (∑ d∈Finset.Icc 3 N,coefficient d*e d)-head*e 2≤0) :
    (∑ d∈Finset.Icc 2 N,e d)<C := by
  by_contra hn
  exact crossing_impossible _ _ _ _ hu (le_of_not_gt hn) he2 he3
    (finite_energy_head_reduction e N hN he hgen)

end KLSBelow25.CoupledEnergy.NumericsSub15
#print axioms KLSBelow25.CoupledEnergy.NumericsSub15.finite_energy_sum_lt_budget
