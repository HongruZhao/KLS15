import ProductCubicResidualKernels

/-! Exact ordered residual cubic Gram rows: 54, 12 and six. -/
noncomputable section
open scoped BigOperators
namespace KLSImprovement.ProductJoint
open KLSImprovement.ProductCubic
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem residualGram_abs_row_restrict {n : ℕ} (I : Fin 3→Fin n) :
    (∑ J,|residualGram I J|)=
      ∑ i∈coordinateSupport I,∑ j∈coordinateSupport I,∑ k∈coordinateSupport I,
        |∏ l∈coordinateSupport I,
          residualKernel (coordinateCount I l) (coordinateCount ![i,j,k] l)| := by
  classical
  rw [sum_triples]
  have hz:∀ i j k,i∉coordinateSupport I∨j∉coordinateSupport I∨k∉coordinateSupport I→
      |residualGram I ![i,j,k]|=0 := by
    intro i j k h
    rcases h with hi|hj|hk
    · rw [residualGram_zero_of_outside I ![i,j,k] 0 (by simpa using hi),abs_zero]
    · rw [residualGram_zero_of_outside I ![i,j,k] 1 (by simpa using hj),abs_zero]
    · rw [residualGram_zero_of_outside I ![i,j,k] 2 (by simpa using hk),abs_zero]
  rw [restrict_triple_sum (coordinateSupport I) _ hz]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  apply residualGram_restrict_product
  intro a
  fin_cases a <;> simpa using (by assumption : _)

theorem residualGram_abs_row_diagonal {n : ℕ} (i : Fin n) :
    (∑ J,|residualGram ![i,i,i] J|)=54 := by
  classical
  rw [residualGram_abs_row_restrict]
  norm_num [coordinateSupport,coordinateCount_tuple]

theorem residualGram_abs_row_pair {n : ℕ} (i j : Fin n) (hij:i≠j) :
    (∑ J,|residualGram ![i,i,j] J|)=12 := by
  classical
  rw [residualGram_abs_row_restrict]
  norm_num [coordinateSupport,coordinateCount_tuple,hij,Ne.symm hij,
    Finset.sum_insert,Finset.prod_insert]

theorem residualGram_abs_row_distinct {n : ℕ} (i j k : Fin n)
    (hij:i≠j) (hik:i≠k) (hjk:j≠k) :
    (∑ J,|residualGram ![i,j,k] J|)=6 := by
  classical
  rw [residualGram_abs_row_restrict]
  norm_num [coordinateSupport,coordinateCount_tuple,hij,Ne.symm hij,
    hik,Ne.symm hik,hjk,Ne.symm hjk,Finset.sum_insert,Finset.prod_insert]

theorem residualGram_abs_row_congr {n : ℕ} (I I' : Fin 3→Fin n)
    (hcount:∀ l,coordinateCount I l=coordinateCount I' l) :
    (∑ J,|residualGram I J|)=∑ J,|residualGram I' J| := by
  unfold residualGram
  simp_rw [hcount]

theorem residualGram_abs_row_tuple_le {n : ℕ} (i j k : Fin n) :
    (∑ J,|residualGram ![i,j,k] J|)≤54 := by
  by_cases hij:i=j
  · subst j
    by_cases hik:i=k
    · subst k
      rw [residualGram_abs_row_diagonal]
    · rw [residualGram_abs_row_pair i k hik]
      norm_num
  · by_cases hik:i=k
    · subst k
      rw [residualGram_abs_row_congr ![i,j,i] ![i,i,j] (fun l=>by
        simp only [coordinateCount_tuple]; omega),residualGram_abs_row_pair i j hij]
      norm_num
    · by_cases hjk:j=k
      · subst k
        rw [residualGram_abs_row_congr ![i,j,j] ![j,j,i] (fun l=>by
          simp only [coordinateCount_tuple]; omega),residualGram_abs_row_pair j i (Ne.symm hij)]
        norm_num
      · rw [residualGram_abs_row_distinct i j k hij hik hjk]
        norm_num

theorem residualGram_abs_row_le {n : ℕ} (I : Fin 3→Fin n) :
    (∑ J,|residualGram I J|)≤54 := by
  have he:I=![I 0,I 1,I 2] := by funext a;fin_cases a <;> simp
  simpa only [←he] using residualGram_abs_row_tuple_le (I 0) (I 1) (I 2)

end KLSImprovement.ProductJoint
#print axioms KLSImprovement.ProductJoint.residualGram_abs_row_diagonal
#print axioms KLSImprovement.ProductJoint.residualGram_abs_row_pair
#print axioms KLSImprovement.ProductJoint.residualGram_abs_row_distinct
#print axioms KLSImprovement.ProductJoint.residualGram_abs_row_le
