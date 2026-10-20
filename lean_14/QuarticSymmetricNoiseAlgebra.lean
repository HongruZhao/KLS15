import Mathlib

/-! Exact rank-three covariance-noise square completion, retaining the
full symmetry of the rank-four coefficient. All arrays are literal finite
real coordinates; the law-specific contraction bounds are separate. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.QuarticSymmetricNoise
variable {ι : Type*} [Fintype ι]

abbrev Array4 (ι : Type*) := ι → ι → ι → ι → ℝ
def quadSum (F : Array4 ι) : ℝ := ∑ i,∑ j,∑ k,∑ l,F i j k l
def square (U : Array4 ι) : ℝ := quadSum (fun i j k l => U i j k l^2)
def cross (U : Array4 ι) : ℝ := quadSum (fun i j k l => U i j k l*U i k j l)
def disjoint (U : Array4 ι) : ℝ := quadSum (fun i j k l => U i j k l*U k l i j)
def symPart (U : Array4 ι) : Array4 ι := fun i j k l => (1/2 : ℝ)*
  (U i j k l+U i k j l+U i l j k+U j k i l+U j l i k+U k l i j)
def noise (U W : Array4 ι) : ℝ := quadSum (fun i j k l =>
  W i j k l^2-2*W i j k l*(U i j k l+U i k j l+U i l j k)+
    (1/2 : ℝ)*(U i j k l+U i k j l+U i l j k)^2+
    (1/2 : ℝ)*(U i j k l^2+U i k j l^2+U i l j k^2))

theorem quadSum_swap12 (F : Array4 ι) :
    quadSum (fun i j k l => F j i k l)=quadSum F := Finset.sum_comm
theorem quadSum_swap23 (F : Array4 ι) :
    quadSum (fun i j k l => F i k j l)=quadSum F := by
  unfold quadSum
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm
theorem quadSum_swap34 (F : Array4 ι) :
    quadSum (fun i j k l => F i j l k)=quadSum F := by
  unfold quadSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm
theorem quadSum_pair_exchange (F : Array4 ι) :
    quadSum (fun i j k l => F k l i j)=quadSum F := by
  calc
    _=quadSum (fun i j k l => F j l i k) :=
      (quadSum_swap23 (fun i j k l => F k l i j)).symm
    _=quadSum (fun i j k l => F i l j k) :=
      (quadSum_swap12 (fun i j k l => F j l i k)).symm
    _=quadSum (fun i j k l => F i k j l) :=
      (quadSum_swap34 (fun i j k l => F i l j k)).symm
    _=quadSum F := quadSum_swap23 F

theorem quadSum_add (F G : Array4 ι) :
    quadSum (fun i j k l => F i j k l+G i j k l)=quadSum F+quadSum G := by
  simp only [quadSum,Finset.sum_add_distrib]
theorem quadSum_smul (a : ℝ) (F : Array4 ι) :
    quadSum (fun i j k l => a*F i j k l)=a*quadSum F := by
  simp only [quadSum,Finset.mul_sum]
theorem quadSum_neg (F : Array4 ι) :
    quadSum (fun i j k l => -F i j k l)= -quadSum F := by
  simp only [quadSum,Finset.sum_neg_distrib]

theorem weighted_swap12 (U W : Array4 ι)
    (hW : ∀ i j k l,W i j k l=W j i k l) :
    quadSum (fun i j k l => W i j k l*U j i k l)=
      quadSum (fun i j k l => W i j k l*U i j k l) := by
  rw [←quadSum_swap12 (fun i j k l => W i j k l*U j i k l)]
  congr 1
  funext i j k l
  rw [hW j i k l]
theorem weighted_swap23 (U W : Array4 ι)
    (hW : ∀ i j k l,W i j k l=W i k j l) :
    quadSum (fun i j k l => W i j k l*U i k j l)=
      quadSum (fun i j k l => W i j k l*U i j k l) := by
  rw [←quadSum_swap23 (fun i j k l => W i j k l*U i k j l)]
  congr 1
  funext i j k l
  rw [hW i k j l]
theorem weighted_swap34 (U W : Array4 ι)
    (hW : ∀ i j k l,W i j k l=W i j l k) :
    quadSum (fun i j k l => W i j k l*U i j l k)=
      quadSum (fun i j k l => W i j k l*U i j k l) := by
  rw [←quadSum_swap34 (fun i j k l => W i j k l*U i j l k)]
  congr 1
  funext i j k l
  rw [hW i j l k]
theorem weighted_pair_exchange (U W : Array4 ι)
    (hW12 : ∀ i j k l,W i j k l=W j i k l)
    (hW23 : ∀ i j k l,W i j k l=W i k j l)
    (hW34 : ∀ i j k l,W i j k l=W i j l k) :
    quadSum (fun i j k l => W i j k l*U k l i j)=
      quadSum (fun i j k l => W i j k l*U i j k l) := by
  rw [←quadSum_pair_exchange (fun i j k l => W i j k l*U k l i j)]
  congr 1
  funext i j k l
  rw [hW23 k l i j,hW12 k i l j,hW34 i k l j,hW23 i k j l]

omit [Fintype ι] in theorem symPart_swap12 (U : Array4 ι)
    (hU12 : ∀ i j k l,U i j k l=U j i k l)
    (hU34 : ∀ i j k l,U i j k l=U i j l k) (i j k l : ι) :
    symPart U i j k l=symPart U j i k l := by
  unfold symPart
  rw [hU12 j i k l,hU34 k l j i]
  ring
omit [Fintype ι] in theorem symPart_swap23 (U : Array4 ι)
    (hU12 : ∀ i j k l,U i j k l=U j i k l)
    (hU34 : ∀ i j k l,U i j k l=U i j l k) (i j k l : ι) :
    symPart U i j k l=symPart U i k j l := by
  unfold symPart
  rw [hU34 i l k j,hU12 k j i l]
  ring
omit [Fintype ι] in theorem symPart_swap34 (U : Array4 ι)
    (hU12 : ∀ i j k l,U i j k l=U j i k l)
    (hU34 : ∀ i j k l,U i j k l=U i j l k) (i j k l : ι) :
    symPart U i j k l=symPart U i j l k := by
  unfold symPart
  rw [hU34 i j l k,hU12 l k i j]
  ring

theorem symmetric_average_pairing (U W : Array4 ι)
    (hW12 : ∀ i j k l,W i j k l=W j i k l)
    (hW23 : ∀ i j k l,W i j k l=W i k j l)
    (hW34 : ∀ i j k l,W i j k l=W i j l k) :
    quadSum (fun i j k l => W i j k l*symPart U i j k l)=
      3*quadSum (fun i j k l => W i j k l*U i j k l) := by
  have h2 := weighted_swap23 U W hW23
  have h3 : quadSum (fun i j k l => W i j k l*U i l j k)=
      quadSum (fun i j k l => W i j k l*U i j k l) :=
    (weighted_swap34 (fun i j k l => U i k j l) W hW34).trans h2
  have h4 : quadSum (fun i j k l => W i j k l*U j k i l)=
      quadSum (fun i j k l => W i j k l*U i j k l) :=
    (weighted_swap12 (fun i j k l => U i k j l) W hW12).trans h2
  have h5 : quadSum (fun i j k l => W i j k l*U j l i k)=
      quadSum (fun i j k l => W i j k l*U i j k l) :=
    (weighted_swap12 (fun i j k l => U i l j k) W hW12).trans h3
  have h6 := weighted_pair_exchange U W hW12 hW23 hW34
  have he : quadSum (fun i j k l => W i j k l*symPart U i j k l)=
      (1/2 : ℝ)*(quadSum (fun i j k l => W i j k l*U i j k l)+
        quadSum (fun i j k l => W i j k l*U i k j l)+
        quadSum (fun i j k l => W i j k l*U i l j k)+
        quadSum (fun i j k l => W i j k l*U j k i l)+
        quadSum (fun i j k l => W i j k l*U j l i k)+
        quadSum (fun i j k l => W i j k l*U k l i j)) := by
    unfold symPart
    simp only [←quadSum_add,←quadSum_smul]
    congr 1
    funext i j k l
    ring
  rw [he,h2,h3,h4,h5,h6]
  ring

theorem symmetric_pairing (U W : Array4 ι)
    (hW12 : ∀ i j k l,W i j k l=W j i k l)
    (hW23 : ∀ i j k l,W i j k l=W i k j l)
    (hW34 : ∀ i j k l,W i j k l=W i j l k) :
    quadSum (fun i j k l => W i j k l*(U i j k l+U i k j l+U i l j k))=
      quadSum (fun i j k l => W i j k l*symPart U i j k l) := by
  rw [symmetric_average_pairing U W hW12 hW23 hW34]
  have h2 := weighted_swap23 U W hW23
  have h3 : quadSum (fun i j k l => W i j k l*U i l j k)=
      quadSum (fun i j k l => W i j k l*U i j k l) :=
    (weighted_swap34 (fun i j k l => U i k j l) W hW34).trans h2
  simp only [mul_add,quadSum_add,h2,h3]
  ring

theorem cross_third (U : Array4 ι)
    (hU34 : ∀ i j k l,U i j k l=U i j l k) :
    quadSum (fun i j k l => U i j k l*U i l j k)=cross U := by
  rw [←quadSum_swap34 (fun i j k l => U i j k l*U i l j k)]
  unfold cross
  congr 1
  funext i j k l
  rw [hU34 i j l k]
theorem cross_fourth (U : Array4 ι)
    (hU12 : ∀ i j k l,U i j k l=U j i k l) :
    quadSum (fun i j k l => U i j k l*U j k i l)=cross U := by
  rw [←quadSum_swap12 (fun i j k l => U i j k l*U j k i l)]
  unfold cross
  congr 1
  funext i j k l
  rw [hU12 j i k l]
theorem cross_fifth (U : Array4 ι)
    (hU12 : ∀ i j k l,U i j k l=U j i k l)
    (hU34 : ∀ i j k l,U i j k l=U i j l k) :
    quadSum (fun i j k l => U i j k l*U j l i k)=cross U := by
  rw [←quadSum_swap12 (fun i j k l => U i j k l*U j l i k)]
  have he : quadSum (fun i j k l => U j i k l*U i l j k)=
      quadSum (fun i j k l => U i j k l*U i l j k) := by
    congr 1
    funext i j k l
    rw [hU12 j i k l]
  exact he.trans (cross_third U hU34)

theorem self_average_pairing (U : Array4 ι)
    (hU12 : ∀ i j k l,U i j k l=U j i k l)
    (hU34 : ∀ i j k l,U i j k l=U i j l k) :
    quadSum (fun i j k l => U i j k l*symPart U i j k l)=
      (1/2 : ℝ)*(square U+4*cross U+disjoint U) := by
  have he : quadSum (fun i j k l => U i j k l*symPart U i j k l)=
      (1/2 : ℝ)*(square U+cross U+
        quadSum (fun i j k l => U i j k l*U i l j k)+
        quadSum (fun i j k l => U i j k l*U j k i l)+
        quadSum (fun i j k l => U i j k l*U j l i k)+disjoint U) := by
    unfold square cross disjoint symPart
    simp only [←quadSum_add,←quadSum_smul]
    congr 1
    funext i j k l
    ring
  rw [he,cross_third U hU34,cross_fourth U hU12,cross_fifth U hU12 hU34]
  ring

theorem symPart_square (U : Array4 ι)
    (hU12 : ∀ i j k l,U i j k l=U j i k l)
    (hU34 : ∀ i j k l,U i j k l=U i j l k) :
    square (symPart U)=(3/2 : ℝ)*square U+6*cross U+(3/2 : ℝ)*disjoint U := by
  have hh := symmetric_average_pairing U (symPart U)
    (symPart_swap12 U hU12 hU34) (symPart_swap23 U hU12 hU34)
    (symPart_swap34 U hU12 hU34)
  have he : quadSum (fun i j k l => symPart U i j k l*U i j k l)=
      quadSum (fun i j k l => U i j k l*symPart U i j k l) := by
    congr 1
    funext i j k l
    ring
  rw [he,self_average_pairing U hU12 hU34] at hh
  simp only [←pow_two] at hh
  change square (symPart U)=_ at hh
  linarith

theorem noise_eq (U W : Array4 ι)
    (hU34 : ∀ i j k l,U i j k l=U i j l k) :
    noise U W=square W-
      2*quadSum (fun i j k l => W i j k l*(U i j k l+U i k j l+U i l j k))+
      3*square U+3*cross U := by
  have hs2 : square (fun i j k l => U i k j l)=square U := quadSum_swap23 _
  have hs3 : square (fun i j k l => U i l j k)=square U :=
    (quadSum_swap34 (fun i j k l => U i k j l^2)).trans (quadSum_swap23 _)
  have hc23 : quadSum (fun i j k l => U i k j l*U i l j k)=cross U := by
    rw [←quadSum_swap23 (fun i j k l => U i k j l*U i l j k)]
    have he : quadSum (fun i j k l => U i j k l*U i l k j)=
        quadSum (fun i j k l => U i j k l*U i l j k) := by
      congr 1
      funext i j k l
      rw [hU34 i l k j]
    exact he.trans (cross_third U hU34)
  have he : noise U W=square W-
      2*quadSum (fun i j k l => W i j k l*(U i j k l+U i k j l+U i l j k))+
      square U+square (fun i j k l => U i k j l)+square (fun i j k l => U i l j k)+
      cross U+quadSum (fun i j k l => U i j k l*U i l j k)+
      quadSum (fun i j k l => U i k j l*U i l j k) := by
    unfold noise square cross
    simp only [sub_eq_add_neg,←quadSum_neg,←quadSum_add,←quadSum_smul]
    congr 1
    funext i j k l
    ring
  rw [he,hs2,hs3,cross_third U hU34,hc23]
  ring

theorem completion {β : ℝ} (hβ : β<1) (U W : Array4 ι)
    (hU12 : ∀ i j k l,U i j k l=U j i k l)
    (hU34 : ∀ i j k l,U i j k l=U i j l k)
    (hW12 : ∀ i j k l,W i j k l=W j i k l)
    (hW23 : ∀ i j k l,W i j k l=W i k j l)
    (hW34 : ∀ i j k l,W i j k l=W i j l k) :
    β*square W+(3-(3/2 : ℝ)/(1-β))*square U+
      (3-6/(1-β))*cross U-(3/2 : ℝ)/(1-β)*disjoint U≤noise U W := by
  have hpos : 0<1-β := by linarith
  have hsum : 0≤quadSum (fun i j k l => ((1-β)*W i j k l-symPart U i j k l)^2) := by
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have he : quadSum (fun i j k l => ((1-β)*W i j k l-symPart U i j k l)^2)=
      (1-β)^2*square W-2*(1-β)*
        quadSum (fun i j k l => W i j k l*symPart U i j k l)+square (symPart U) := by
    unfold square
    simp only [sub_eq_add_neg,←quadSum_neg,←quadSum_add,←quadSum_smul]
    congr 1
    funext i j k l
    ring
  rw [he,symPart_square U hU12 hU34] at hsum
  rw [noise_eq U W hU34,symmetric_pairing U W hW12 hW23 hW34]
  field_simp
  nlinarith

theorem lower_of_bounds {β E : ℝ} (hβ0 : (1 : ℝ)/2≤β) (hβ1 : β<1)
    (U W : Array4 ι)
    (hU12 : ∀ i j k l,U i j k l=U j i k l)
    (hU34 : ∀ i j k l,U i j k l=U i j l k)
    (hW12 : ∀ i j k l,W i j k l=W j i k l)
    (hW23 : ∀ i j k l,W i j k l=W i k j l)
    (hW34 : ∀ i j k l,W i j k l=W i j l k)
    (hQ : square U≤8*E) (hR : cross U≤4*E) (hS : disjoint U≤(16/3 : ℝ)*E) :
    β*square W-(44/(1-β)-36)*E≤noise U W := by
  have hc := completion hβ1 U W hU12 hU34 hW12 hW23 hW34
  have hpos : 0<1-β := by linarith
  have ha : 3-(3/2 : ℝ)/(1-β)≤0 := by
    apply sub_nonpos.mpr
    apply (le_div_iff₀ hpos).mpr
    linarith
  have hb : 3-6/(1-β)≤0 := by
    apply sub_nonpos.mpr
    apply (le_div_iff₀ hpos).mpr
    linarith
  have hs : -(3/2 : ℝ)/(1-β)≤0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hpos.le
  have hq := mul_le_mul_of_nonpos_left hQ ha
  have hr := mul_le_mul_of_nonpos_left hR hb
  have hd := mul_le_mul_of_nonpos_left hS hs
  simp only [neg_div,neg_mul] at hd
  have hid : (3-(3/2 : ℝ)/(1-β))*(8*E)+(3-6/(1-β))*(4*E)-
      (3/2 : ℝ)/(1-β)*((16/3 : ℝ)*E)= -(44/(1-β)-36)*E := by ring
  linarith

end KLSBelow25.QuarticSymmetricNoise
#print axioms KLSBelow25.QuarticSymmetricNoise.symPart_square
#print axioms KLSBelow25.QuarticSymmetricNoise.noise_eq
#print axioms KLSBelow25.QuarticSymmetricNoise.completion
#print axioms KLSBelow25.QuarticSymmetricNoise.lower_of_bounds
