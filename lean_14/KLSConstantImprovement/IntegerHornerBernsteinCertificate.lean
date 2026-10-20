import KLSConstantImprovement.IntegerListPolynomialCertificate

/-! A compositional integer Bernstein positivity certificate.

The numerical identity is still checked by ordinary kernel reduction.  This
backend computes a homogeneous Horner sum, multiplying only by linear factors,
rather than independently expanding every pair of affine powers.  It asserts
no KLS estimate or particular numerical certificate.
-/
namespace KLSConstantImprovement.IntegerHornerBernsteinCertificate

open KLSConstantImprovement.IntegerListPolynomialCertificate
open Set

theorem eval_append_zero (p : List ℤ) (t : ℝ) :
    eval (p ++ [0]) t = eval p t := by
  induction p with
  | nil => simp [eval]
  | cons a p ih => simp [eval, ih]

def homogeneousState (x y : List ℤ) : List ℤ → List ℤ × List ℤ
  | [] => ([1], [])
  | b :: bs =>
      let previous := homogeneousState x y bs
      (mulCoeff y previous.1,
       addCoeff (previous.1.map (fun a => b * a)) (mulCoeff x previous.2))

theorem eval_homogeneous_power (x y bs : List ℤ) (t : ℝ) :
    eval (homogeneousState x y bs).1 t = (eval y t) ^ bs.length := by
  induction bs with
  | nil => simp [homogeneousState, eval]
  | cons b bs ih =>
      change eval (mulCoeff y (homogeneousState x y bs).1) t =
        (eval y t) ^ (bs.length + 1)
      rw [eval_mulCoeff, ih, pow_succ]
      ring

theorem eval_homogeneous_sum_cons (x y : List ℤ) (b : ℤ) (bs : List ℤ) (t : ℝ) :
    eval (homogeneousState x y (b :: bs)).2 t =
      (b : ℝ) * (eval y t) ^ bs.length +
        eval x t * eval (homogeneousState x y bs).2 t := by
  change eval (addCoeff ((homogeneousState x y bs).1.map (fun a => b * a))
    (mulCoeff x (homogeneousState x y bs).2)) t = _
  rw [eval_addCoeff, eval_scaleCoeff, eval_mulCoeff, eval_homogeneous_power]

theorem eval_homogeneous_positive (x y bs : List ℤ) (t : ℝ)
    (hx : 0 ≤ eval x t) (hy : 0 ≤ eval y t)
    (hxy : 0 < eval x t + eval y t) :
    bs ≠ [] → (∀ b ∈ bs, (0 : ℤ) < b) →
      0 < eval (homogeneousState x y bs).2 t := by
  induction bs with
  | nil =>
      intro h _
      exact (h rfl).elim
  | cons b bs ih =>
      intro _ hb
      have hb0 : (0 : ℝ) < (b : ℝ) := by
        exact_mod_cast hb b (by simp)
      rw [eval_homogeneous_sum_cons]
      cases bs with
      | nil => simpa [homogeneousState, eval] using hb0
      | cons c cs =>
          have hs : 0 < eval (homogeneousState x y (c :: cs)).2 t :=
            ih (by simp) (fun a ha => hb a (List.mem_cons_of_mem b ha))
          have hfirst : 0 ≤ (b : ℝ) * (eval y t) ^ (c :: cs).length :=
            mul_nonneg hb0.le (pow_nonneg hy _)
          by_cases hypos : 0 < eval y t
          · exact add_pos_of_pos_of_nonneg
              (mul_pos hb0 (pow_pos hypos _)) (mul_nonneg hx hs.le)
          · have hxpos : 0 < eval x t := by linarith
            exact add_pos_of_nonneg_of_pos hfirst (mul_pos hxpos hs)

def bernsteinHornerCoeff (n : ℕ) (b : Fin (n + 1) → ℤ)
    (span slope offset : ℤ) : List ℤ :=
  (homogeneousState [-offset, slope] [span + offset, -slope] (List.ofFn b)).2

theorem eval_bernsteinHornerCoeff_positive
    (n : ℕ) (b : Fin (n + 1) → ℤ) (span slope offset : ℤ) (t : ℝ)
    (hspan : (0 : ℝ) < (span : ℝ)) (hb : ∀ i, (0 : ℤ) < b i)
    (ht : (slope : ℝ) * t - (offset : ℝ) ∈ Icc (0 : ℝ) (span : ℝ)) :
    0 < eval (bernsteinHornerCoeff n b span slope offset) t := by
  have hx : eval [-offset, slope] t = (slope : ℝ) * t - (offset : ℝ) := by
    simp [eval]
    ring
  have hy : eval [span + offset, -slope] t =
      (span : ℝ) - ((slope : ℝ) * t - (offset : ℝ)) := by
    simp [eval]
    ring
  apply eval_homogeneous_positive
  · simpa only [hx] using ht.1
  · rw [hy]
    linarith [ht.2]
  · rw [hx, hy]
    linarith
  · intro hempty
    have hlength := congrArg List.length hempty
    simpa using hlength
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hb i

end KLSConstantImprovement.IntegerHornerBernsteinCertificate

#print axioms KLSConstantImprovement.IntegerHornerBernsteinCertificate.eval_homogeneous_power
#print axioms KLSConstantImprovement.IntegerHornerBernsteinCertificate.eval_append_zero
#print axioms KLSConstantImprovement.IntegerHornerBernsteinCertificate.eval_homogeneous_sum_cons
#print axioms KLSConstantImprovement.IntegerHornerBernsteinCertificate.eval_homogeneous_positive
#print axioms KLSConstantImprovement.IntegerHornerBernsteinCertificate.eval_bernsteinHornerCoeff_positive
