import Mathlib
noncomputable section
namespace KLSBelow25.ProjectionSlackRatio

theorem normalized_early_correlated_initialization
    (z c : ℕ → ℝ) {p u V cap : ℝ}
    (hp : 0<p) (hu : 0<u) (hucap : u≤p^2-cap)
    (hz0 : z 0=1) (hz1 : p≤z 1) (hc1 : 0≤c 1) (hcap : c 1≤cap)
    (hinit : V≤(p^2-c 1)*(p-c 1/p)-c 2)
    (hrec : ∀ n, 0<z n → 0<z (n+1) →
      z (n+1)^2/z n-c (n+1)≤z (n+2)) :
    p≤z 1 ∧ u≤z 2 ∧ V≤z 3 := by
  have hz1pos : 0<z 1 := hp.trans_le hz1
  have hrec0 := hrec 0 (by simpa only [hz0] using (zero_lt_one : (0:ℝ)<1)) hz1pos
  rw [hz0,div_one] at hrec0
  have hz2raw : p^2-c 1≤z 2 := by nlinarith [sq_nonneg (z 1-p)]
  have hz2u : u≤z 2 := by linarith
  have hz2pos : 0<z 2 := hu.trans_le hz2u
  have hqpos : 0≤p-c 1/p := by
    have hh : p*(p-c 1/p)=p^2-c 1 := by field_simp
    have hx : 0<p^2-c 1 := by linarith
    nlinarith
  have hcdiv : c 1/z 1≤c 1/p := div_le_div_of_nonneg_left hc1 hp hz1
  have hratio2 : p-c 1/p≤z 2/z 1 := by
    apply (le_div_iff₀ hz1pos).mpr
    have hh := (div_le_iff₀ hz1pos).mp hcdiv
    nlinarith
  have hrec1 := hrec 1 hz1pos hz2pos
  have he : z 2^2/z 1=(z 2/z 1)*z 2 := by ring
  rw [he] at hrec1
  have hm := mul_le_mul_of_nonneg_right hratio2 hz2pos.le
  have hm' := mul_le_mul_of_nonneg_left hz2raw hqpos
  exact ⟨hz1,hz2u,by nlinarith⟩

end KLSBelow25.ProjectionSlackRatio
#print axioms KLSBelow25.ProjectionSlackRatio.normalized_early_correlated_initialization
