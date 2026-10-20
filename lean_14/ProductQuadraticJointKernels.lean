import ProductCubicResidualRows

/-! The ordinary quadratic product family, and its exact orthogonality to
the complete residual cubic family. All indices are ordered. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.ProductJoint
open KLSImprovement.ProductCubic KLSImprovement.ProductPolynomial
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

def pairCount {n : ℕ} (I : Fin 2→Fin n) (i : Fin n) : ℕ :=
  ∑ a,if I a=i then 1 else 0
def pairSupport {n : ℕ} (I : Fin 2→Fin n) : Finset (Fin n) := {I 0,I 1}

@[simp] theorem pairCount_tuple {n : ℕ} (i j l : Fin n) :
    pairCount ![i,j] l=(if i=l then 1 else 0)+(if j=l then 1 else 0) := by
  rw [pairCount,Fin.sum_univ_two]
  simp

theorem pairCount_zero_of_not_mem {n : ℕ} (I : Fin 2→Fin n) {i : Fin n}
    (hi:i∉pairSupport I) : pairCount I i=0 := by
  have hI:I=![I 0,I 1] := by funext a;fin_cases a <;>simp
  have h0:I 0≠i := by intro he;apply hi;simp [pairSupport,he]
  have h1:I 1≠i := by intro he;apply hi;simp [pairSupport,he]
  rw [hI,pairCount_tuple]
  simp [h0,h1]

def pairBasis {n : ℕ} (I : Fin 2→Fin n) (y : Fin n→ℝ) : ℝ :=
  ∏ i,scalarAppell (pairCount I i) (y i)
def pairGram {n : ℕ} (I J : Fin 2→Fin n) : ℝ :=
  ∏ i,scalarKernel (pairCount I i) (pairCount J i)
def crossGram {n : ℕ} (I : Fin 2→Fin n) (J : Fin 3→Fin n) : ℝ :=
  ∏ i,mixedKernel (pairCount I i) (coordinateCount J i)

theorem pairBasis_memLp {n : ℕ} (I : Fin 2→Fin n) :
    MemLp (pairBasis I) 2 (product n) := by
  have hi : Integrable (pairBasis I) (product n) :=
    Integrable.fintype_prod (fun i=>scalarAppell_integrable _)
  apply (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mpr
  have h := Integrable.fintype_prod (fun i:Fin n=>
    (scalarAppell_memLp (pairCount I i)).integrable_sq)
  simpa only [pairBasis,Finset.prod_pow] using h

theorem pairGram_integral {n : ℕ} (I J : Fin 2→Fin n) :
    (∫ y,pairBasis I y*pairBasis J y ∂product n)=pairGram I J := by
  simp only [pairBasis,←Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (μ:=fun _:Fin n=>expMeasure 1)
    (fun i y=>scalarAppell (pairCount I i) y*scalarAppell (pairCount J i) y)

theorem crossGram_integral {n : ℕ} (I : Fin 2→Fin n) (J : Fin 3→Fin n) :
    (∫ y,pairBasis I y*residualBasis J y ∂product n)=crossGram I J := by
  simp only [pairBasis,residualBasis,←Finset.prod_mul_distrib]
  calc
    _ = ∏ i,∫ y,scalarAppell (pairCount I i) y*
        residualScalar (coordinateCount J i) y ∂expMeasure 1 :=
      integral_fintype_prod_eq_prod (μ:=fun _:Fin n=>expMeasure 1) _
    _ = _ := by simp only [mixedKernel_integral];rfl

def pairEquiv (n : ℕ) : (Fin 2→Fin n)≃Fin n×Fin n where
  toFun I := (I 0,I 1)
  invFun p := ![p.1,p.2]
  left_inv I := by funext a;fin_cases a <;>simp
  right_inv p := by simp

theorem sum_pairs {n : ℕ} (f : (Fin 2→Fin n)→ℝ) :
    (∑ I,f I)=∑ i,∑ j,f ![i,j] := by
  calc
    _ = ∑ p:Fin n×Fin n,f ![p.1,p.2] :=
      Fintype.sum_equiv (pairEquiv n) f _ (fun I=>by
        congr 1
        funext a
        fin_cases a <;>simp [pairEquiv])
    _ = _ := Fintype.sum_prod_type _

theorem restrict_pair_sum {n : ℕ} (s : Finset (Fin n)) (f : Fin n→Fin n→ℝ)
    (hz:∀ i j,i∉s∨j∉s→f i j=0) :
    (∑ i,∑ j,f i j)=∑ i∈s,∑ j∈s,f i j := by
  classical
  calc
    _ = ∑ i∈s,∑ j,f i j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      apply Finset.sum_eq_zero
      intro j _
      exact hz i j (Or.inl hi)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro j _ hj
      exact hz i j (Or.inr hj)

theorem pairGram_abs_row_restrict {n : ℕ} (I : Fin 2→Fin n) :
    (∑ J,|pairGram I J|)=∑ i∈pairSupport I,∑ j∈pairSupport I,
      |∏ l∈pairSupport I,scalarKernel (pairCount I l) (pairCount ![i,j] l)| := by
  classical
  have hout (i j : Fin n) (h:i∉pairSupport I∨j∉pairSupport I) :
      |pairGram I ![i,j]|=0 := by
    have hzero (k : Fin n) (hk:k∉pairSupport I) (hJ:0<pairCount ![i,j] k) :
        pairGram I ![i,j]=0 := by
      unfold pairGram
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      rw [pairCount_zero_of_not_mem I hk,scalarKernel_zero_left]
      rw [ite_eq_right hJ.ne']
    rcases h with hi|hj
    · rw [hzero i hi (by simp [pairCount_tuple]),abs_zero]
    · rw [hzero j hj (by simp [pairCount_tuple]),abs_zero]
  rw [sum_pairs,restrict_pair_sum (pairSupport I) _ hout]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro l _ hl
  have hil:i≠l := by intro he;exact hl (he ▸ hi)
  have hjl:j≠l := by intro he;exact hl (he ▸ hj)
  simp [pairCount_zero_of_not_mem I hl,pairCount_tuple,hil,hjl]

theorem pairGram_abs_row_le {n : ℕ} (I : Fin 2→Fin n) :
    (∑ J,|pairGram I J|)≤8 := by
  classical
  rw [pairGram_abs_row_restrict]
  have he:I=![I 0,I 1] := by funext a;fin_cases a <;>simp
  rw [he]
  by_cases h:I 0=I 1
  · norm_num [pairSupport,pairCount_tuple,h]
  · norm_num [pairSupport,pairCount_tuple,h,Ne.symm h,
      Finset.sum_insert,Finset.prod_insert]

theorem crossGram_abs_row_restrict {n : ℕ} (I : Fin 2→Fin n) :
    (∑ J,|crossGram I J|)=
      ∑ i∈pairSupport I,∑ j∈pairSupport I,∑ k∈pairSupport I,
        |∏ l∈pairSupport I,mixedKernel (pairCount I l) (coordinateCount ![i,j,k] l)| := by
  classical
  have hout (i j k : Fin n) (h:i∉pairSupport I∨j∉pairSupport I∨k∉pairSupport I) :
      |crossGram I ![i,j,k]|=0 := by
    have hz (a : Fin 3) (ha:(![i,j,k] a)∉pairSupport I) : crossGram I ![i,j,k]=0 := by
      unfold crossGram
      apply Finset.prod_eq_zero (Finset.mem_univ (![i,j,k] a))
      rw [pairCount_zero_of_not_mem I ha,mixedKernel_zero_left]
      rw [ite_eq_right (coordinateCount_pos_at ![i,j,k] a).ne']
    rcases h with hi|hj|hk
    · rw [hz 0 (by simpa using hi),abs_zero]
    · rw [hz 1 (by simpa using hj),abs_zero]
    · rw [hz 2 (by simpa using hk),abs_zero]
  rw [sum_triples,restrict_triple_sum (pairSupport I) _ hout]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro l _ hl
  have hil:i≠l := by intro he;exact hl (he ▸ hi)
  have hjl:j≠l := by intro he;exact hl (he ▸ hj)
  have hkl:k≠l := by intro he;exact hl (he ▸ hk)
  simp [pairCount_zero_of_not_mem I hl,coordinateCount_tuple,hil,hjl,hkl]

theorem crossGram_abs_row_zero {n : ℕ} (I : Fin 2→Fin n) :
    (∑ J,|crossGram I J|)=0 := by
  classical
  rw [crossGram_abs_row_restrict]
  have he:I=![I 0,I 1] := by funext a;fin_cases a <;>simp
  rw [he]
  by_cases h:I 0=I 1
  · norm_num [pairSupport,pairCount_tuple,coordinateCount_tuple,h]
  · norm_num [pairSupport,pairCount_tuple,coordinateCount_tuple,h,Ne.symm h,
      Finset.sum_insert,Finset.prod_insert]

theorem crossGram_zero {n : ℕ} (I : Fin 2→Fin n) (J : Fin 3→Fin n) :
    crossGram I J=0 := by
  have h := Finset.single_le_sum (fun K (_:K∈Finset.univ)=>abs_nonneg (crossGram I K))
    (Finset.mem_univ J)
  rw [crossGram_abs_row_zero] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

end KLSImprovement.ProductJoint
#print axioms KLSImprovement.ProductJoint.pairGram_abs_row_le
#print axioms KLSImprovement.ProductJoint.crossGram_abs_row_zero
#print axioms KLSImprovement.ProductJoint.crossGram_zero
