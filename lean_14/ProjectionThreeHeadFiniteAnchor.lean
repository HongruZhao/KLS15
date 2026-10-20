import ProjectionThreeHeadFiniteChargeCost

/-! Finite anchor growth starting after three genuine initial head denominators.
Only explicitly proved finite-prefix floors are used. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.ProjectionSlackRatio

theorem finite_one_two_step_growth_three
    (z : ℕ → ℝ) (l V gamma : ℝ) (hl : 0<l) (hl1 : l ≤ 1)
    (hV : 0<V) (hgamma : 1 ≤ gamma) (hinit : V ≤ z 3)
    (hstep : ∀ m, 3 ≤ m → (∀ i, 3 ≤ i → i ≤ m → l*V ≤ z i) → V ≤ z m →
      l*z m ≤ z (m+1) ∧ (gamma*z m ≤ z (m+1) ∨ gamma^2*z m ≤ z (m+2))) :
    ∀ k,l*V*gamma^k ≤ z (k+4) := by
  have hh := finite_one_two_step_growth (fun i => z (i+1)) l V gamma hl hl1 hV hgamma
    (by simpa using hinit) (by
      intro m hm hfloor hanchor
      have hf : ∀ i, 3 ≤ i → i ≤ m+1 → l*V ≤ z i := by
        intro i hi him
        have hj : 2 ≤ i-1 := by omega
        have hji : i-1+1=i := by omega
        simpa only [hji] using hfloor (i-1) hj (by omega)
      simpa only [Nat.add_assoc,Nat.reduceAdd] using hstep (m+1) (by omega) hf hanchor)
  intro k
  simpa only [Nat.add_assoc,Nat.reduceAdd] using hh k

theorem finite_three_head_anchor_step
    (z rho d a : ℕ → ℝ) (p D l V eta w r B gamma : ℝ)
    (hl : 0 < l) (hV : 0 < V) (_heta0 : 0  ≤  eta) (heta1 : eta  ≤  1)
    (hw0 : 0 < w) (hw1 : w < 1) (hhalf : (1/2:ℝ)  ≤  l)
    (hB : 0  ≤  B) (hrdef : r=p-(1-eta)*D/l)
    (hBdef : B=D/l-(p-1)) (hlower : l  ≤  p-D/l)
    (hinterval : (1-w)*r/w  ≤  l) (hgamma : gamma  ≤  r)
    (hgain : gamma^2  ≤  r*(1-B))
    (hfirst : p  ≤  rho 0) (ha : ∀ m,0  ≤  a m) (hd : ∀ m, 0  ≤  d m)
    (hrec : ∀ m,rho (m+1)=rho m-d m+a m)
    (hpay : ∀ m, l  ≤  rho m → eta*d m  ≤  w*a m+(1-w)*a (m+1))
    (hzrec : ∀ m,z (m+1)=rho (m+1)*z m)
    (hcost : ∀ (N : ℕ), 3  ≤  N  →  (∀ (i : ℕ), 3  ≤  i  →  i < N  →  l*V  ≤  z i)  → 
      (∑i∈Finset.range N,d i)  ≤  D/l)
    (m : ℕ) (hm : 3  ≤  m) (hfloor : ∀ i, 3  ≤  i  →  i  ≤  m  →  l*V  ≤  z i)
    (hanchor : V  ≤  z m) :
    l*z m  ≤  z (m+1) ∧
      (gamma*z m  ≤  z (m+1) ∨ gamma^2*z m  ≤  z (m+2)) := by
  have hzm : 0  ≤  z m := le_trans hV.le hanchor
  have hc := hcost (m+1) (by omega) (fun i hi him=>hfloor i hi (by omega))
  have hrho : l  ≤  rho (m+1) :=
    hlower.trans (by linarith [ratio_lower_of_finite_cost rho d a p hfirst hrec ha (m+1)])
  have hzn : l*z m  ≤  z (m+1) := by
    rw [hzrec m]
    exact mul_le_mul_of_nonneg_right hrho hzm
  refine ⟨hzn,?_⟩
  by_cases hbig : r  ≤  rho (m+1)
  · left
    rw [hzrec m]
    exact mul_le_mul_of_nonneg_right (hgamma.trans hbig) hzm
  · right
    have hprefix (i : ℕ) (hi : i  ≤  m+1) : l  ≤  rho i := by
      have hs : (∑ j∈Finset.range i, d j)  ≤  ∑ j∈Finset.range (m+1), d j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi)
          (fun j _ _ => hd j)
      have hh := ratio_lower_of_finite_cost rho d a p hfirst hrec ha i
      linarith
    have hqn := corrected_potential_finite_prefix eta w rho d a hrec (m+1)
      (fun i hi => hpay i (hprefix i (by omega)))
    have hq : r  ≤  rho (m+1)+(1-w)*a (m+1) := by
      have hh := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr heta1)
      have ha0 : 0  ≤  (1-w)*a 0 := mul_nonneg (sub_pos.mpr hw1).le (ha 0)
      rw [hrdef]
      have hid : (1-eta)*(D/l)=(1-eta)*D/l := by ring
      rw [hid] at hh
      nlinarith
    have hnextfloor : l*V  ≤  z (m+1) := by
      have hh := mul_le_mul_of_nonneg_left hanchor hl.le
      exact hh.trans hzn
    have hcnext := hcost (m+2) (by omega) (by
      intro i hi him
      by_cases he : i=m+1
      · simpa [he] using hnextfloor
      · exact hfloor i hi (by omega))
    have hremain : d (m+1)  ≤  B+rho (m+1)-1 := by
      rw [Finset.sum_range_succ] at hcnext
      have hh := ratio_lower_of_finite_cost rho d a p hfirst hrec ha (m+1)
      rw [hBdef]
      linarith
    have hprod := two_step_growth_of_remaining_cost w r (rho (m+1)) (rho (m+2))
      (d (m+1)) B (a (m+1)) hw0 hw1 (le_of_not_ge hbig)
      (hhalf.trans hrho) hB (hinterval.trans hrho) (hrec (m+1)) hq hremain
    have hnorm : z (m+2)=(rho (m+1)*rho (m+2))*z m := by
      rw [hzrec (m+1),hzrec m]
      ring
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right (hgain.trans hprod) hzm

theorem finite_three_head_anchor_orbit_growth
    (z rho d a : ℕ → ℝ) (p D l V eta w r B gamma : ℝ)
    (hl : 0 < l) (hl1 : l  ≤  1) (hV : 0 < V)
    (heta0 : 0  ≤  eta) (heta1 : eta  ≤  1)
    (hw0 : 0 < w) (hw1 : w < 1) (hhalf : (1/2:ℝ)  ≤  l)
    (hB : 0  ≤  B) (hrdef : r=p-(1-eta)*D/l)
    (hBdef : B=D/l-(p-1)) (hlower : l  ≤  p-D/l)
    (hinterval : (1-w)*r/w  ≤  l) (hgamma : gamma  ≤  r)
    (hgamma1 : 1  ≤  gamma) (hgain : gamma^2  ≤  r*(1-B))
    (hfirst : p  ≤  rho 0) (ha : ∀ m, 0  ≤  a m) (hd : ∀ m, 0  ≤  d m)
    (hrec : ∀ m, rho (m+1)=rho m-d m+a m)
    (hpay : ∀ m, l  ≤  rho m → eta*d m  ≤  w*a m+(1-w)*a (m+1))
    (hzrec : ∀ m, z (m+1)=rho (m+1)*z m)
    (hcost : ∀ (N : ℕ), 3  ≤  N →
      (∀ (i : ℕ), 3  ≤  i → i < N → l*V  ≤  z i) →
      (∑ i∈Finset.range N,d i)  ≤  D/l)
    (hinit : V  ≤  z 3) :
    ∀ k, l*V*gamma^k  ≤  z (k+4) := by
  apply finite_one_two_step_growth_three z l V gamma hl hl1 hV hgamma1 hinit
  intro m hm hfloor hanchor
  exact finite_three_head_anchor_step z rho d a p D l V eta w r B gamma
    hl hV heta0 heta1 hw0 hw1 hhalf hB hrdef hBdef hlower hinterval
    hgamma hgain hfirst ha hd hrec hpay hzrec hcost m hm hfloor hanchor

end KLSBelow25.ProjectionSlackRatio
#print axioms KLSBelow25.ProjectionSlackRatio.finite_one_two_step_growth_three
#print axioms KLSBelow25.ProjectionSlackRatio.finite_three_head_anchor_step
#print axioms KLSBelow25.ProjectionSlackRatio.finite_three_head_anchor_orbit_growth
