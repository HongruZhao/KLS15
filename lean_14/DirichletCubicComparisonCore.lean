import ActualAppellMoments

/-! Algebraic comparison core of the Dirichlet cubic-cap proof. The
Dirichlet law, its moment formula, the gamma-product Gram bound, and their
original Appell correspondence are not formalized by this file. The
comparison premises are explicit; no universal log-concave claim follows. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace KLSImprovement.DirichletCubic
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def denominator (A : ℝ) : ℝ := (A+2)*(A+3)*(A+4)*(A+5)
def bFour (A : ℝ) : ℝ := A*(A+1)/((A+2)*(A+3))
def bSix (A : ℝ) : ℝ := A^2*(A+1)^2/denominator A
def cThree (A : ℝ) : ℝ := A*(A+1)/(A+2)^2
def delta (A : ℝ) : ℝ := bFour A-bSix A
def completion (A : ℝ) : ℝ := 2*bFour A-1-bSix A
def cNumerator (A : ℝ) : ℝ := 2*A^3-7*A^2-57*A-60
def deficitNumerator (A : ℝ) : ℝ :=
  28*A^6+28*A^5-1437*A^4-8462*A^3-20777*A^2-24120*A-10800

theorem denominator_pos {A : ℝ} (hA : 0<A) : 0<denominator A := by
  unfold denominator
  positivity

theorem coefficient_identities {A : ℝ} (hA : 0<A) :
    1-bFour A=(4*A+6)/((A+2)*(A+3)) ∧
    1-bSix A=(12*A^3+70*A^2+154*A+120)/denominator A ∧
    delta A=4*A*(A+1)*(2*A+5)/denominator A ∧
    cThree A-bSix A=
      3*A*(A+1)*(3*A^2+15*A+20)/((A+2)^2*(A+3)*(A+4)*(A+5)) ∧
    completion A=2*cNumerator A/denominator A := by
  have h2:(A+2)≠0 := by positivity
  have h3:(A+3)≠0 := by positivity
  have h4:(A+4)≠0 := by positivity
  have h5:(A+5)≠0 := by positivity
  dsimp [bFour,bSix,cThree,delta,completion,cNumerator,denominator]
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    ring
  constructor <;> field_simp <;> ring

theorem coefficient_bounds {A : ℝ} (hA : 0<A) :
    0≤bFour A ∧bFour A≤1 ∧0≤bSix A ∧bSix A≤1 ∧
      0≤delta A ∧bSix A≤cThree A := by
  obtain ⟨h4,h6,hd,hc,_⟩ := coefficient_identities hA
  have h4n:0≤bFour A := by unfold bFour;positivity
  have h6n:0≤bSix A := div_nonneg (by positivity) (denominator_pos hA).le
  have h4d:0≤1-bFour A := by rw [h4];positivity
  have h6d:0≤1-bSix A := by rw [h6];exact div_nonneg (by positivity) (denominator_pos hA).le
  have hdn:0≤delta A := by rw [hd];exact div_nonneg (by positivity) (denominator_pos hA).le
  have hcn:0≤cThree A-bSix A := by rw [hc];positivity
  exact ⟨h4n,by linarith,h6n,by linarith,hdn,by linarith⟩

theorem shifted_cNumerator (z : ℝ) :
    cNumerator (10+z)=2*z^3+53*z^2+403*z+670 := by
  unfold cNumerator
  ring

theorem shifted_deficitNumerator (z : ℝ) :
    deficitNumerator (10+z)=28*z^6+1708*z^5+41963*z^4+522058*z^3+
      3343163*z^2+9473740*z+5638300 := by
  unfold deficitNumerator
  ring

theorem large_completion_pos {A : ℝ} (hA : 10≤A) : 0<completion A := by
  have hAp:0<A := by linarith
  have hn:0<cNumerator A := by
    rw [show A=10+(A-10) by ring,shifted_cNumerator]
    have hz:0≤A-10 := by linarith
    positivity
  rw [(coefficient_identities hAp).2.2.2.2]
  exact div_pos (by positivity) (denominator_pos hAp)

theorem large_deficit_identity {A : ℝ} (hA : 10≤A) :
    216*(1-bSix A)-36*(delta A)^2/completion A=
      144*deficitNumerator A/(denominator A*cNumerator A) := by
  have hAp:0<A := by linarith
  have hD:denominator A≠0 := (denominator_pos hAp).ne'
  have hn:cNumerator A≠0 := by
    have hc:=large_completion_pos hA
    rw [(coefficient_identities hAp).2.2.2.2] at hc
    intro hz
    rw [hz,mul_zero,zero_div] at hc
    exact (lt_irrefl (0:ℝ)) hc
  rw [(coefficient_identities hAp).2.2.1,(coefficient_identities hAp).2.2.2.2]
  unfold bSix
  field_simp [hD,hn]
  unfold denominator cNumerator deficitNumerator
  ring

theorem large_comparison_ceiling {A : ℝ} (hA : 10≤A) :
    216*bSix A+36*(delta A)^2/completion A≤216 := by
  have hAp:0<A := by linarith
  have hn:0≤deficitNumerator A := by
    rw [show A=10+(A-10) by ring,shifted_deficitNumerator]
    have hz:0≤A-10 := by linarith
    positivity
  have hc:0≤cNumerator A := by
    rw [show A=10+(A-10) by ring,shifted_cNumerator]
    have hz:0≤A-10 := by linarith
    positivity
  have hgap:0≤216*(1-bSix A)-36*(delta A)^2/completion A := by
    rw [large_deficit_identity hA]
    exact div_nonneg (mul_nonneg (by norm_num) hn) (mul_nonneg (denominator_pos hAp).le hc)
  linarith

def squared {ι : Type*} [Fintype ι] (v : ι→ℝ) : ℝ := ∑ i,(v i)^2
def pairing {ι : Type*} [Fintype ι] (v w : ι→ℝ) : ℝ := ∑ i,v i*w i

theorem squared_nonneg {ι : Type*} [Fintype ι] (v : ι→ℝ) : 0≤ squared v :=
  Finset.sum_nonneg (fun _ _=>sq_nonneg _)

theorem cross_lower {ι : Type*} [Fintype ι] (v w : ι→ℝ) :
    -2*pairing v w≤ squared v+squared w := by
  have hs:0≤∑ i,(v i+w i)^2 := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have he:(∑ i,(v i+w i)^2)=squared v+2*pairing v w+squared w := by
    simp only [squared,pairing,show ∀ i,(v i+w i)^2=(v i)^2+2*(v i*w i)+(w i)^2 by intro i;ring,
      Finset.sum_add_distrib,Finset.mul_sum]
  rw [he] at hs
  linarith

theorem weighted_cross_completion {ι : Type*} [Fintype ι]
    (v w : ι→ℝ) {c d : ℝ} (hc : 0<c) :
    -36*d*pairing v w-9*c*squared v≤36*d^2/c*squared w := by
  have hs:0≤∑ i,(c*v i+2*d*w i)^2 := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have he:(∑ i,(c*v i+2*d*w i)^2)=
      c^2*squared v+4*c*d*pairing v w+4*d^2*squared w := by
    simp only [squared,pairing,
      show ∀ i,(c*v i+2*d*w i)^2=c^2*(v i)^2+(4*c*d)*(v i*w i)+(4*d^2)*(w i)^2
        by intro i;ring,
      Finset.sum_add_distrib,Finset.mul_sum]
  rw [he] at hs
  have h:= (le_div_iff₀ hc).mpr (show
      (-36*d*pairing v w-9*c*squared v)*c≤36*d^2*squared w by nlinarith)
  convert h using 1
  ring

def correctedGram {ι : Type*} [Fintype ι] (A Q s : ℝ) (t a : ι→ℝ) : ℝ :=
  bSix A*Q-36*delta A*pairing t a+
    9*(bSix A-2*bFour A+1)*squared t+4*(bSix A-cThree A)*s^2

/-- All comparison inputs are explicit. The actual Dirichlet moment and
gamma-product correspondences are additional analytic work. -/
theorem correctedGram_le_six {ι : Type*} [Fintype ι]
    {A F Q s : ℝ} (hA : 0<A) (hF : 0≤F) (hQ : Q≤216*F)
    (t a : ι→ℝ) (ha : squared a≤F) (ht : squared t≤(A+1)/3*F) :
    correctedGram A Q s t a≤216*F := by
  obtain ⟨h4n,h4,h6n,h6,hd,hc⟩:=coefficient_bounds hA
  have hp:4*(bSix A-cThree A)*s^2≤0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (by linarith)) (sq_nonneg _)
  have hQ':bSix A*Q≤216*bSix A*F := by nlinarith [mul_le_mul_of_nonneg_left hQ h6n]
  by_cases hsmall:A≤10
  · have ht':squared t≤(11/3:ℝ)*F := ht.trans (by nlinarith [mul_nonneg (by linarith : 0≤10-A) hF])
    have hcross:-36*delta A*pairing t a≤18*delta A*(squared t+squared a) := by
      nlinarith [mul_le_mul_of_nonneg_left (cross_lower t a) hd]
    have hac:18*delta A*squared a≤18*delta A*F := by nlinarith [mul_le_mul_of_nonneg_left ha hd]
    have htc:9*(1-bSix A)*squared t≤33*(1-bSix A)*F := by
      nlinarith [mul_le_mul_of_nonneg_left ht' (sub_nonneg.mpr h6)]
    have hcoeff:(33+165*bSix A+18*bFour A)*F≤216*F := by
      nlinarith [mul_le_mul_of_nonneg_right h6 hF,mul_le_mul_of_nonneg_right h4 hF]
    unfold correctedGram delta
    dsimp [delta] at hcross hac
    nlinarith [hQ',hcross,hac,htc,hp,hcoeff]
  · have hlarge:10≤A := (lt_of_not_ge hsmall).le
    have hcp:=large_completion_pos hlarge
    have hcross:=weighted_cross_completion t a (d:=delta A) hcp
    have hcoeffnonneg:0≤36*(delta A)^2/completion A := div_nonneg (by positivity) hcp.le
    have hac:=mul_le_mul_of_nonneg_left ha hcoeffnonneg
    have hbound:=mul_le_mul_of_nonneg_right (large_comparison_ceiling hlarge) hF
    unfold correctedGram
    dsimp [completion] at hcross hac hbound
    nlinarith [hQ',hcross,hac,hp,hbound]

end KLSImprovement.DirichletCubic
#print axioms KLSImprovement.DirichletCubic.large_deficit_identity
#print axioms KLSImprovement.DirichletCubic.large_comparison_ceiling
#print axioms KLSImprovement.DirichletCubic.correctedGram_le_six
