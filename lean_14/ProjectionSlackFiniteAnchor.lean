import ProjectionSlackRatioPotential
import FiniteOneTwoStepGrowth

/-! Finite anchor bookkeeping for the projection-slack estimate.
Absolute charges and the first-two supporting line give the cost bound;
no globally growing orbit or vanishing terminal slack is assumed. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.ProjectionSlackRatio

 theorem head_tail_ratio_cost_le
    (l V p u H C c1 c2 tailC d1 d2 tailD : ℝ)
    (hl : 0 < l) (hl1 : l ≤ 1) (hV : 0 < V) (hp : 0 < p) (hu : 0 < u)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hbudget : c1+c2+tailC ≤ C)
    (hline : (1/p-1/V)*c1+(1/u-1/V)*c2 ≤ H)
    (hd1 : d1 ≤ c1/p) (hd2 : d2 ≤ c2/u)
    (htail : tailD ≤ tailC/(l*V)) :
    d1+d2+tailD ≤ (H+C/V)/l := by
  have h1 : l*d1 ≤ c1/p := (mul_le_mul_of_nonneg_left hd1 hl.le).trans
    (by nlinarith [div_nonneg hc1 hp.le])
  have h2 : l*d2 ≤ c2/u := (mul_le_mul_of_nonneg_left hd2 hl.le).trans
    (by nlinarith [div_nonneg hc2 hu.le])
  have he : l*(tailC/(l*V))=tailC/V := by field_simp
  have ht : l*tailD ≤ tailC/V := by
    simpa only [he] using mul_le_mul_of_nonneg_left htail hl.le
  have hb := div_le_div_of_nonneg_right hbudget hV.le
  have hid : (1/p-1/V)*c1+(1/u-1/V)*c2+(c1+c2+tailC)/V=
      c1/p+c2/u+tailC/V := by ring
  apply (le_div_iff₀ hl).mpr
  nlinarith

 theorem ratio_lower_of_finite_cost
    (rho d a : ℕ → ℝ) (p : ℝ) (hfirst : p ≤ rho 0)
    (hrec : ∀ m,rho (m+1)=rho m-d m+a m) (ha : ∀ m,0 ≤ a m) (N : ℕ) :
    p-(∑m∈Finset.range N,d m) ≤ rho N := by
  induction N with
  | zero => simpa using hfirst
  | succ N ih =>
    rw [Finset.sum_range_succ,hrec N]
    linarith [ha N]

 theorem two_step_growth_of_remaining_cost
    (w r rho rhoNext d B a : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (hrho : rho ≤ r) (hrhohalf : (1/2:ℝ) ≤ rho) (hB : 0 ≤ B)
    (hlower : (1-w)*r/w ≤ rho)
    (hrec : rhoNext=rho-d+a) (hpotential : r ≤ rho+(1-w)*a)
    (hremaining : d ≤ B+rho-1) :
    r*(1-B) ≤ rho*rhoNext := by
  have hh := corrected_potential_two_step w r rho rhoNext d a hw0 hw1
    (by linarith) hrho hlower hrec hpotential
  have hd := mul_le_mul_of_nonneg_left hremaining (by linarith : 0 ≤ rho)
  have hprod : 0 ≤ (r-rho)*(B+r+rho-1) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- Prefix telescoping needs payments only in the displayed finite prefix. -/
theorem corrected_potential_finite_prefix
    (eta w : ℝ) (rho d a : ℕ → ℝ)
    (hrec : ∀ m, rho (m+1)=rho m-d m+a m) (N : ℕ)
    (hpay : ∀ i, i < N → eta*d i ≤ w*a i+(1-w)*a (i+1)) :
    rho 0+(1-w)*a 0-(1-eta)*(∑ i∈Finset.range N,d i) ≤
      rho N+(1-w)*a N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hp := ih (fun i hi => hpay i (by omega))
    rw [Finset.sum_range_succ]
    have hh := corrected_potential_step eta w (rho N) (rho (N+1))
      (d N) (a N) (a (N+1)) (hrec N) (hpay N (by omega))
    nlinarith

/-- One finite anchor advances by one or two steps. `hcost` is the finite
ratio-cost consequence of actual absolute charges and head floors, not an
assumed eventual orbit bound. -/
theorem finite_anchor_step
    (z rho d a : ℕ → ℝ) (p D l V eta w r B gamma : ℝ)
    (hl : 0 < l) (hV : 0 < V) (_heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hw0 : 0 < w) (hw1 : w < 1) (hhalf : (1/2:ℝ) ≤ l)
    (hB : 0 ≤ B) (hrdef : r=p-(1-eta)*D/l)
    (hBdef : B=D/l-(p-1)) (hlower : l ≤ p-D/l)
    (hinterval : (1-w)*r/w ≤ l) (hgamma : gamma ≤ r)
    (hgain : gamma^2 ≤ r*(1-B))
    (hfirst : p ≤ rho 0) (ha : ∀ m,0 ≤ a m) (hd : ∀ m, 0 ≤ d m)
    (hrec : ∀ m,rho (m+1)=rho m-d m+a m)
    (hpay : ∀ m, l ≤ rho m → eta*d m ≤ w*a m+(1-w)*a (m+1))
    (hzrec : ∀ m,z (m+1)=rho (m+1)*z m)
    (hcost : ∀ (N : ℕ), 2 ≤ N  →  (∀ (i : ℕ), 2 ≤ i  →  i < N  →  l*V ≤ z i)  → 
      (∑i∈Finset.range N,d i) ≤ D/l)
    (m : ℕ) (hm : 2 ≤ m) (hfloor : ∀ i,2 ≤ i  →  i ≤ m  →  l*V ≤ z i)
    (hanchor : V ≤ z m) :
    l*z m ≤ z (m+1) ∧
      (gamma*z m ≤ z (m+1) ∨ gamma^2*z m ≤ z (m+2)) := by
  have hzm : 0 ≤ z m := le_trans hV.le hanchor
  have hc := hcost (m+1) (by omega) (fun i hi him=>hfloor i hi (by omega))
  have hrho : l ≤ rho (m+1) :=
    hlower.trans (by linarith [ratio_lower_of_finite_cost rho d a p hfirst hrec ha (m+1)])
  have hzn : l*z m ≤ z (m+1) := by
    rw [hzrec m]
    exact mul_le_mul_of_nonneg_right hrho hzm
  refine ⟨hzn,?_⟩
  by_cases hbig : r ≤ rho (m+1)
  · left
    rw [hzrec m]
    exact mul_le_mul_of_nonneg_right (hgamma.trans hbig) hzm
  · right
    have hprefix (i : ℕ) (hi : i ≤ m+1) : l ≤ rho i := by
      have hs : (∑ j∈Finset.range i, d j) ≤ ∑ j∈Finset.range (m+1), d j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi)
          (fun j _ _ => hd j)
      have hh := ratio_lower_of_finite_cost rho d a p hfirst hrec ha i
      linarith
    have hqn := corrected_potential_finite_prefix eta w rho d a hrec (m+1)
      (fun i hi => hpay i (hprefix i (by omega)))
    have hq : r ≤ rho (m+1)+(1-w)*a (m+1) := by
      have hh := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr heta1)
      have ha0 : 0 ≤ (1-w)*a 0 := mul_nonneg (sub_pos.mpr hw1).le (ha 0)
      rw [hrdef]
      have hid : (1-eta)*(D/l)=(1-eta)*D/l := by ring
      rw [hid] at hh
      nlinarith
    have hnextfloor : l*V ≤ z (m+1) := by
      have hh := mul_le_mul_of_nonneg_left hanchor hl.le
      exact hh.trans hzn
    have hcnext := hcost (m+2) (by omega) (by
      intro i hi him
      by_cases he : i=m+1
      · simpa [he] using hnextfloor
      · exact hfloor i hi (by omega))
    have hremain : d (m+1) ≤ B+rho (m+1)-1 := by
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

/-- Uniform exponential growth from finite absolute-charge bookkeeping and
conditional projection-slack payments. No future amplitude floor is assumed. -/
theorem finite_anchor_orbit_growth
    (z rho d a : ℕ → ℝ) (p D l V eta w r B gamma : ℝ)
    (hl : 0 < l) (hl1 : l ≤ 1) (hV : 0 < V)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hw0 : 0 < w) (hw1 : w < 1) (hhalf : (1/2:ℝ) ≤ l)
    (hB : 0 ≤ B) (hrdef : r=p-(1-eta)*D/l)
    (hBdef : B=D/l-(p-1)) (hlower : l ≤ p-D/l)
    (hinterval : (1-w)*r/w ≤ l) (hgamma : gamma ≤ r)
    (hgamma1 : 1 ≤ gamma) (hgain : gamma^2 ≤ r*(1-B))
    (hfirst : p ≤ rho 0) (ha : ∀ m, 0 ≤ a m) (hd : ∀ m, 0 ≤ d m)
    (hrec : ∀ m, rho (m+1)=rho m-d m+a m)
    (hpay : ∀ m, l ≤ rho m → eta*d m ≤ w*a m+(1-w)*a (m+1))
    (hzrec : ∀ m, z (m+1)=rho (m+1)*z m)
    (hcost : ∀ (N : ℕ), 2 ≤ N →
      (∀ (i : ℕ), 2 ≤ i → i < N → l*V ≤ z i) →
      (∑ i∈Finset.range N,d i) ≤ D/l)
    (hinit : V ≤ z 2) :
    ∀ k, l*V*gamma^k ≤ z (k+3) := by
  apply finite_one_two_step_growth z l V gamma hl hl1 hV hgamma1 hinit
  intro m hm hfloor hanchor
  exact finite_anchor_step z rho d a p D l V eta w r B gamma
    hl hV heta0 heta1 hw0 hw1 hhalf hB hrdef hBdef hlower hinterval
    hgamma hgain hfirst ha hd hrec hpay hzrec hcost m hm hfloor hanchor

end KLSBelow25.ProjectionSlackRatio
#print axioms KLSBelow25.ProjectionSlackRatio.head_tail_ratio_cost_le
#print axioms KLSBelow25.ProjectionSlackRatio.ratio_lower_of_finite_cost
#print axioms KLSBelow25.ProjectionSlackRatio.two_step_growth_of_remaining_cost
#print axioms KLSBelow25.ProjectionSlackRatio.finite_anchor_step

#print axioms KLSBelow25.ProjectionSlackRatio.finite_anchor_orbit_growth
