import ProjectionFiniteEarlyInitialization
noncomputable section
namespace KLSBelow25.ProjectionSlackRatio
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def thirdHeadInitialWeight (p r x₀ : ℝ) : ℝ := 4*r*p-r^2-4*r*x₀/p
def thirdHeadInitialBase (p r x₀ : ℝ) : ℝ := 2*r*p^3-r^2*p^2-2*r*x₀^2/p

/-- A quadratic-perspective tangent and a same-vector three-observation
supporting cap initialize the fourth normalized orbit value. -/
theorem normalized_early_three_observation_initialization
    (z c : ℕ → ℝ) {p u V W cap r x₀ H : ℝ}
    (hp : 0 < p) (hu : 0 < u) (hV : 0 < V) (hr : 0 ≤ r)
    (hucap : u ≤ p^2-cap) (hrcap : r ≤ 2*(p-cap/p))
    (hz0 : z 0=1) (hz1 : p ≤ z 1) (hc1 : 0 ≤ c 1) (hcap : c 1 ≤ cap)
    (hinit : V ≤ (p^2-c 1)*(p-c 1/p)-c 2)
    (hline : thirdHeadInitialWeight p r x₀*c 1+2*r*c 2+c 3 ≤ H)
    (hbase : W ≤ thirdHeadInitialBase p r x₀-H)
    (hrec : ∀ n, 0 < z n → 0 < z (n+1) →
      z (n+1)^2/z n-c (n+1) ≤ z (n+2)) :
    p ≤ z 1 ∧ u ≤ z 2 ∧ V ≤ z 3 ∧ W ≤ z 4 := by
  obtain ⟨hz1',hz2,hz3⟩ := normalized_early_correlated_initialization
    z c hp hu hucap hz0 hz1 hc1 hcap hinit hrec
  have hz1pos : 0 < z 1 := hp.trans_le hz1
  have hz2pos : 0 < z 2 := hu.trans_le hz2
  have hz3pos : 0 < z 3 := hV.trans_le hz3
  have hrec0 := hrec 0 (by simpa only [hz0] using (zero_lt_one : (0 : ℝ) < 1)) hz1pos
  rw [hz0,div_one] at hrec0
  have hz2raw : p^2-c 1 ≤ z 2 := by nlinarith [sq_nonneg (z 1-p)]
  have hcdiv : c 1/z 1 ≤ c 1/p := div_le_div_of_nonneg_left hc1 hp hz1
  have hratio : p-c 1/p ≤ z 2/z 1 := by
    apply (le_div_iff₀ hz1pos).mpr
    have hh := (div_le_iff₀ hz1pos).mp hcdiv
    nlinarith
  have hz3raw : (p-c 1/p)*z 2-c 2 ≤ z 3 := by
    have hm := mul_le_mul_of_nonneg_right hratio hz2pos.le
    have hh := hrec 1 hz1pos hz2pos
    have he : z 2^2/z 1=(z 2/z 1)*z 2 := by ring
    simp only [Nat.reduceAdd] at hh
    rw [he] at hh
    linarith only [hm,hh]
  have hq : r ≤ 2*(p-c 1/p) := by
    have hc := div_le_div_of_nonneg_right hcap hp.le
    linarith
  have hcoeff : 0 ≤ 2*r*(p-c 1/p)-r^2 := by nlinarith
  have hmid := mul_le_mul_of_nonneg_left hz3raw (by linarith : 0 ≤ 2*r)
  have hsub := mul_le_mul_of_nonneg_left hz2raw hcoeff
  have hpers : 2*r*z 3-r^2*z 2 ≤ z 3^2/z 2 := by
    apply (le_div_iff₀ hz2pos).mpr
    nlinarith only [sq_nonneg (z 3-r*z 2)]
  have hrec2 := hrec 2 hz2pos hz3pos
  have heq : (2*r*(p-c 1/p)-r^2)*(p^2-c 1)-2*r*c 2-c 3 =
      thirdHeadInitialBase p r x₀-thirdHeadInitialWeight p r x₀*c 1-
        2*r*c 2-c 3+(2*r/p)*(c 1-x₀)^2 := by
    dsimp only [thirdHeadInitialBase, thirdHeadInitialWeight]
    field_simp [hp.ne']
    ring
  have hs : 0 ≤ (2*r/p)*(c 1-x₀)^2 := by positivity
  refine ⟨hz1',hz2,hz3,?_⟩
  simp only [Nat.reduceAdd] at hrec2
  nlinarith only [hmid,hsub,hpers,hrec2,heq,hs,hline,hbase]

end KLSBelow25.ProjectionSlackRatio
#print axioms KLSBelow25.ProjectionSlackRatio.normalized_early_three_observation_initialization
