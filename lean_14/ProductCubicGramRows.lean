import ProductCubicKernels

/-! Exact covariance row sums for the full ordered cubic exponential family.
There are no dimension factors: the possible row sums are 216, 36 and 6. -/
noncomputable section
open scoped BigOperators
namespace KLSImprovement.ProductCubic
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def tripleEquiv (n : ℕ) : (Fin 3 → Fin n) ≃ Fin n × (Fin n × Fin n) where
  toFun I := (I 0,(I 1,I 2))
  invFun p := ![p.1,p.2.1,p.2.2]
  left_inv I := by funext a; fin_cases a <;> simp
  right_inv p := by simp

theorem sum_triples {n : ℕ} (f : (Fin 3 → Fin n) → ℝ) :
    (∑ I, f I)=∑ i,∑ j,∑ k,f ![i,j,k] := by
  calc
    _ = ∑ p:Fin n×(Fin n×Fin n),f ![p.1,p.2.1,p.2.2] :=
      Fintype.sum_equiv (tripleEquiv n) f
        (fun p=>f ![p.1,p.2.1,p.2.2]) (fun I=>by
          congr 1
          funext a
          fin_cases a <;> simp [tripleEquiv])
    _ = _ := by rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]

theorem restrict_triple_sum {n : ℕ} (s : Finset (Fin n))
    (f : Fin n→Fin n→Fin n→ℝ)
    (hz:∀ i j k,i∉s∨j∉s∨k∉s→f i j k=0) :
    (∑ i,∑ j,∑ k,f i j k)=∑ i∈s,∑ j∈s,∑ k∈s,f i j k := by
  classical
  calc
    _ = ∑ i∈s,∑ j,∑ k,f i j k := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      apply Finset.sum_eq_zero
      intro j _
      apply Finset.sum_eq_zero
      intro k _
      exact hz i j k (Or.inl hi)
    _ = ∑ i∈s,∑ j∈s,∑ k,f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro j _ hj
      apply Finset.sum_eq_zero
      intro k _
      exact hz i j k (Or.inr (Or.inl hj))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro k _ hk
      exact hz i j k (Or.inr (Or.inr hk))

theorem cubicGram_abs_row_restrict {n : ℕ} (I : Fin 3→Fin n) :
    (∑ J,|cubicGram I J|)=
      ∑ i∈coordinateSupport I,∑ j∈coordinateSupport I,∑ k∈coordinateSupport I,
        |∏ l∈coordinateSupport I,
          scalarKernel (coordinateCount I l) (coordinateCount ![i,j,k] l)| := by
  classical
  rw [sum_triples]
  have hz:∀ i j k,i∉coordinateSupport I∨j∉coordinateSupport I∨k∉coordinateSupport I→
      |cubicGram I ![i,j,k]|=0 := by
    intro i j k h
    rcases h with hi|hj|hk
    · rw [cubicGram_zero_of_outside I ![i,j,k] 0 (by simpa using hi),abs_zero]
    · rw [cubicGram_zero_of_outside I ![i,j,k] 1 (by simpa using hj),abs_zero]
    · rw [cubicGram_zero_of_outside I ![i,j,k] 2 (by simpa using hk),abs_zero]
  rw [restrict_triple_sum (coordinateSupport I) _ hz]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  apply cubicGram_restrict_product
  intro a
  fin_cases a <;> simpa using (by assumption : _)

@[simp] theorem coordinateCount_tuple {n : ℕ} (i j k l : Fin n) :
    coordinateCount ![i,j,k] l=
      (if i=l then 1 else 0)+(if j=l then 1 else 0)+(if k=l then 1 else 0) := by
  rw [coordinateCount,Fin.sum_univ_three]
  simp

theorem cubicGram_abs_row_diagonal {n : ℕ} (i : Fin n) :
    (∑ J,|cubicGram ![i,i,i] J|)=216 := by
  classical
  rw [cubicGram_abs_row_restrict]
  norm_num [coordinateSupport,coordinateCount_tuple]

theorem cubicGram_abs_row_pair {n : ℕ} (i j : Fin n) (hij:i≠j) :
    (∑ J,|cubicGram ![i,i,j] J|)=36 := by
  classical
  rw [cubicGram_abs_row_restrict]
  norm_num [coordinateSupport,coordinateCount_tuple,hij,Ne.symm hij,
    Finset.sum_insert,Finset.prod_insert]

theorem cubicGram_abs_row_distinct {n : ℕ} (i j k : Fin n)
    (hij:i≠j) (hik:i≠k) (hjk:j≠k) :
    (∑ J,|cubicGram ![i,j,k] J|)=6 := by
  classical
  rw [cubicGram_abs_row_restrict]
  norm_num [coordinateSupport,coordinateCount_tuple,hij,Ne.symm hij,
    hik,Ne.symm hik,hjk,Ne.symm hjk,Finset.sum_insert,Finset.prod_insert]

theorem cubicGram_abs_row_congr {n : ℕ} (I I' : Fin 3→Fin n)
    (hcount:∀ l,coordinateCount I l=coordinateCount I' l) :
    (∑ J,|cubicGram I J|)=∑ J,|cubicGram I' J| := by
  unfold cubicGram
  simp_rw [hcount]

theorem cubicGram_abs_row_tuple_le {n : ℕ} (i j k : Fin n) :
    (∑ J,|cubicGram ![i,j,k] J|)≤216 := by
  by_cases hij:i=j
  · subst j
    by_cases hik:i=k
    · subst k
      rw [cubicGram_abs_row_diagonal]
    · rw [cubicGram_abs_row_pair i k hik]
      norm_num
  · by_cases hik:i=k
    · subst k
      rw [cubicGram_abs_row_congr ![i,j,i] ![i,i,j] (fun l=>by
        simp only [coordinateCount_tuple]; omega),cubicGram_abs_row_pair i j hij]
      norm_num
    · by_cases hjk:j=k
      · subst k
        rw [cubicGram_abs_row_congr ![i,j,j] ![j,j,i] (fun l=>by
          simp only [coordinateCount_tuple]; omega),cubicGram_abs_row_pair j i (Ne.symm hij)]
        norm_num
      · rw [cubicGram_abs_row_distinct i j k hij hik hjk]
        norm_num

theorem cubicGram_abs_row_le {n : ℕ} (I : Fin 3→Fin n) :
    (∑ J,|cubicGram I J|)≤216 := by
  have he:I=![I 0,I 1,I 2] := by funext a;fin_cases a <;> simp
  simpa only [←he] using cubicGram_abs_row_tuple_le (I 0) (I 1) (I 2)

end KLSImprovement.ProductCubic
#print axioms KLSImprovement.ProductCubic.cubicGram_abs_row_diagonal
#print axioms KLSImprovement.ProductCubic.cubicGram_abs_row_pair
#print axioms KLSImprovement.ProductCubic.cubicGram_abs_row_distinct
#print axioms KLSImprovement.ProductCubic.cubicGram_abs_row_le
