import KLSConstantImprovement.ActualDeficitContraction

/-! Exact all-dimensional signed cumulant contractions of the cubic Gram
kernel. This module is finite algebra; the actual polynomial jet is linked
in the subsequent original-law variance module. -/
noncomputable section
open MeasureTheory Matrix Set Filter Metric
open scoped BigOperators ContDiff Topology
namespace KLSConstantImprovement.CubicCumulantContraction
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open ActualFixedTensorDeficit ActualDeficitTensorBounds ActualDeficitContraction
open KLSBelow25.CubicSymmetricNoise
variable {n : ℕ}
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
def δ (a b : Fin n) : ℝ := if a=b then 1 else 0
def contract (T : Array3 (Fin n)) (K : Fin n→Fin n→Fin n→Fin n→Fin n→Fin n→ℝ) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*K i j k a b c
theorem third_rotate (μ : Measure (Space n)) (i a b : Fin n) :
    actualThirdCubicArray μ i a b=actualThirdCubicArray μ a b i :=
  (actualThirdCumulant_cyclic μ i a b).trans (actualThirdCumulant_cyclic μ b i a)
theorem cumulantJet_perm_zero {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {vs ws : List (Fin n)} (hp : vs.Perm ws) : cumulantJet μ vs 0=cumulantJet μ ws 0 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨r,hr,h1⟩:=hμ.logConcave.exists_localNormExponentialDomain_one
  exact local_word_perm isOpen_ball (contDiffOn_logLaplace_of_local h1) (hp.map e)
    (show (0 : Space n)∈ball 0 r by simpa using hr)

private theorem reorderF0 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ k,∑ i,∑ j,∑ a,∑ b,∑ c,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ i,∑ k,∑ j,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ k,∑ i,∑ j,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_comm

def F0 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualFourthCumulantArray μ i j a b*δ k c)
theorem F0_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : F0 μ T=fourthContraction μ T := by
  classical
  unfold F0
  rw [reorderF0]
  calc
    _ = ∑ k,∑ i,∑ j,∑ a,∑ b,∑ c,T k i j*T c a b*(actualFourthCumulantArray μ i j a b*δ k c) := by
      apply Finset.sum_congr rfl;intro k _
      apply Finset.sum_congr rfl;intro i _
      apply Finset.sum_congr rfl;intro j _
      apply Finset.sum_congr rfl;intro a _
      apply Finset.sum_congr rfl;intro b _
      apply Finset.sum_congr rfl;intro c _
      rw [hT23 i j k,hT12 i k j,hT23 a b c,hT12 a c b]
    _ = fourthContraction μ T := by
      simp [δ,mul_ite]
      exact (fourthContraction_expanded hμ T hT23).symm

private theorem reorderF1 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ j,∑ i,∑ k,∑ a,∑ b,∑ c,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ j,∑ i,∑ k,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_comm

def F1 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualFourthCumulantArray μ i k a b*δ j c)
theorem F1_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : F1 μ T=fourthContraction μ T := by
  classical
  unfold F1
  rw [reorderF1]
  calc
    _ = ∑ j,∑ i,∑ k,∑ a,∑ b,∑ c,T j i k*T c a b*(actualFourthCumulantArray μ i k a b*δ j c) := by
      apply Finset.sum_congr rfl;intro j _
      apply Finset.sum_congr rfl;intro i _
      apply Finset.sum_congr rfl;intro k _
      apply Finset.sum_congr rfl;intro a _
      apply Finset.sum_congr rfl;intro b _
      apply Finset.sum_congr rfl;intro c _
      rw [hT12 i j k,hT23 a b c,hT12 a c b]
    _ = fourthContraction μ T := by
      simp [δ,mul_ite]
      exact (fourthContraction_expanded hμ T hT23).symm

private theorem reorderF2 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c := by rfl

def F2 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualFourthCumulantArray μ j k a b*δ i c)
theorem F2_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : F2 μ T=fourthContraction μ T := by
  classical
  unfold F2
  rw [reorderF2]
  calc
    _ = ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T c a b*(actualFourthCumulantArray μ j k a b*δ i c) := by
      apply Finset.sum_congr rfl;intro i _
      apply Finset.sum_congr rfl;intro j _
      apply Finset.sum_congr rfl;intro k _
      apply Finset.sum_congr rfl;intro a _
      apply Finset.sum_congr rfl;intro b _
      apply Finset.sum_congr rfl;intro c _
      rw [hT23 a b c,hT12 a c b]
    _ = fourthContraction μ T := by
      simp [δ,mul_ite]
      exact (fourthContraction_expanded hμ T hT23).symm

private theorem reorderF3 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ k,∑ i,∑ j,∑ a,∑ c,∑ b,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ i,∑ k,∑ j,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ k,∑ i,∑ j,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_comm
    _ = ∑ k,∑ i,∑ j,∑ a,∑ c,∑ b,G i j k a b c := by
      exact Finset.sum_congr rfl fun k _=>Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun a _=>Finset.sum_comm

def F3 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualFourthCumulantArray μ i j a c*δ k b)
theorem F3_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : F3 μ T=fourthContraction μ T := by
  classical
  unfold F3
  rw [reorderF3]
  calc
    _ = ∑ k,∑ i,∑ j,∑ a,∑ c,∑ b,T k i j*T b a c*(actualFourthCumulantArray μ i j a c*δ k b) := by
      apply Finset.sum_congr rfl;intro k _
      apply Finset.sum_congr rfl;intro i _
      apply Finset.sum_congr rfl;intro j _
      apply Finset.sum_congr rfl;intro a _
      apply Finset.sum_congr rfl;intro c _
      apply Finset.sum_congr rfl;intro b _
      rw [hT23 i j k,hT12 i k j,hT12 a b c]
    _ = fourthContraction μ T := by
      simp [δ,mul_ite]
      exact (fourthContraction_expanded hμ T hT23).symm

private theorem reorderF4 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ j,∑ i,∑ k,∑ a,∑ c,∑ b,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ j,∑ i,∑ k,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_comm
    _ = ∑ j,∑ i,∑ k,∑ a,∑ c,∑ b,G i j k a b c := by
      exact Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun k _=>Finset.sum_congr rfl fun a _=>Finset.sum_comm

def F4 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualFourthCumulantArray μ i k a c*δ j b)
theorem F4_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : F4 μ T=fourthContraction μ T := by
  classical
  unfold F4
  rw [reorderF4]
  calc
    _ = ∑ j,∑ i,∑ k,∑ a,∑ c,∑ b,T j i k*T b a c*(actualFourthCumulantArray μ i k a c*δ j b) := by
      apply Finset.sum_congr rfl;intro j _
      apply Finset.sum_congr rfl;intro i _
      apply Finset.sum_congr rfl;intro k _
      apply Finset.sum_congr rfl;intro a _
      apply Finset.sum_congr rfl;intro c _
      apply Finset.sum_congr rfl;intro b _
      rw [hT12 i j k,hT12 a b c]
    _ = fourthContraction μ T := by
      simp [δ,mul_ite]
      exact (fourthContraction_expanded hμ T hT23).symm

private theorem reorderF5 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ i,∑ j,∑ k,∑ a,∑ c,∑ b,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ i,∑ j,∑ k,∑ a,∑ c,∑ b,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun k _=>Finset.sum_congr rfl fun a _=>Finset.sum_comm

def F5 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualFourthCumulantArray μ j k a c*δ i b)
theorem F5_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : F5 μ T=fourthContraction μ T := by
  classical
  unfold F5
  rw [reorderF5]
  calc
    _ = ∑ i,∑ j,∑ k,∑ a,∑ c,∑ b,T i j k*T b a c*(actualFourthCumulantArray μ j k a c*δ i b) := by
      apply Finset.sum_congr rfl;intro i _
      apply Finset.sum_congr rfl;intro j _
      apply Finset.sum_congr rfl;intro k _
      apply Finset.sum_congr rfl;intro a _
      apply Finset.sum_congr rfl;intro c _
      apply Finset.sum_congr rfl;intro b _
      rw [hT12 a b c]
    _ = fourthContraction μ T := by
      simp [δ,mul_ite]
      exact (fourthContraction_expanded hμ T hT23).symm

private theorem reorderF6 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ k,∑ i,∑ j,∑ b,∑ c,∑ a,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ i,∑ k,∑ j,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ k,∑ i,∑ j,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_comm
    _ = ∑ k,∑ i,∑ j,∑ b,∑ a,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun k _=>Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_comm
    _ = ∑ k,∑ i,∑ j,∑ b,∑ c,∑ a,G i j k a b c := by
      exact Finset.sum_congr rfl fun k _=>Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun b _=>Finset.sum_comm

def F6 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualFourthCumulantArray μ i j b c*δ k a)
theorem F6_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : F6 μ T=fourthContraction μ T := by
  classical
  unfold F6
  rw [reorderF6]
  calc
    _ = ∑ k,∑ i,∑ j,∑ b,∑ c,∑ a,T k i j*T a b c*(actualFourthCumulantArray μ i j b c*δ k a) := by
      apply Finset.sum_congr rfl;intro k _
      apply Finset.sum_congr rfl;intro i _
      apply Finset.sum_congr rfl;intro j _
      apply Finset.sum_congr rfl;intro b _
      apply Finset.sum_congr rfl;intro c _
      apply Finset.sum_congr rfl;intro a _
      rw [hT23 i j k,hT12 i k j]
    _ = fourthContraction μ T := by
      simp [δ,mul_ite]
      exact (fourthContraction_expanded hμ T hT23).symm

private theorem reorderF7 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ j,∑ i,∑ k,∑ b,∑ c,∑ a,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ j,∑ i,∑ k,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_comm
    _ = ∑ j,∑ i,∑ k,∑ b,∑ a,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun k _=>Finset.sum_comm
    _ = ∑ j,∑ i,∑ k,∑ b,∑ c,∑ a,G i j k a b c := by
      exact Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun k _=>Finset.sum_congr rfl fun b _=>Finset.sum_comm

def F7 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualFourthCumulantArray μ i k b c*δ j a)
theorem F7_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : F7 μ T=fourthContraction μ T := by
  classical
  unfold F7
  rw [reorderF7]
  calc
    _ = ∑ j,∑ i,∑ k,∑ b,∑ c,∑ a,T j i k*T a b c*(actualFourthCumulantArray μ i k b c*δ j a) := by
      apply Finset.sum_congr rfl;intro j _
      apply Finset.sum_congr rfl;intro i _
      apply Finset.sum_congr rfl;intro k _
      apply Finset.sum_congr rfl;intro b _
      apply Finset.sum_congr rfl;intro c _
      apply Finset.sum_congr rfl;intro a _
      rw [hT12 i j k]
    _ = fourthContraction μ T := by
      simp [δ,mul_ite]
      exact (fourthContraction_expanded hμ T hT23).symm

private theorem reorderF8 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ i,∑ j,∑ k,∑ b,∑ c,∑ a,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ i,∑ j,∑ k,∑ b,∑ a,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun k _=>Finset.sum_comm
    _ = ∑ i,∑ j,∑ k,∑ b,∑ c,∑ a,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun k _=>Finset.sum_congr rfl fun b _=>Finset.sum_comm

def F8 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualFourthCumulantArray μ j k b c*δ i a)
theorem F8_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : F8 μ T=fourthContraction μ T := by
  classical
  unfold F8
  rw [reorderF8]
  calc
    _ = ∑ i,∑ j,∑ k,∑ b,∑ c,∑ a,T i j k*T a b c*(actualFourthCumulantArray μ j k b c*δ i a) := by
      apply Finset.sum_congr rfl;intro i _
      apply Finset.sum_congr rfl;intro j _
      apply Finset.sum_congr rfl;intro k _
      apply Finset.sum_congr rfl;intro b _
      apply Finset.sum_congr rfl;intro c _
      apply Finset.sum_congr rfl;intro a _
      rfl
    _ = fourthContraction μ T := by
      simp [δ,mul_ite]
      exact (fourthContraction_expanded hμ T hT23).symm

private theorem reorderS0 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ i,∑ c,∑ j,∑ k,∑ a,∑ b,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ i,∑ j,∑ k,∑ a,∑ c,∑ b,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun k _=>Finset.sum_congr rfl fun a _=>Finset.sum_comm
    _ = ∑ i,∑ j,∑ k,∑ c,∑ a,∑ b,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun k _=>Finset.sum_comm
    _ = ∑ i,∑ j,∑ c,∑ k,∑ a,∑ b,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_comm
    _ = ∑ i,∑ c,∑ j,∑ k,∑ a,∑ b,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_comm

def S0 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualThirdCubicArray μ i a b*actualThirdCubicArray μ j k c)
theorem S0_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : S0 μ T=signedTraceSquare μ T := by
  unfold S0
  rw [reorderS0]
  unfold signedTraceSquare KLSBelow25.CubicCreation.annihilation
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro c _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro k _
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro b _
  rw [hT23 a b c,hT12 a c b,third_rotate μ i a b]
  ring

private theorem reorderS1 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ j,∑ c,∑ i,∑ k,∑ a,∑ b,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ j,∑ i,∑ k,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_comm
    _ = ∑ j,∑ i,∑ k,∑ a,∑ c,∑ b,G i j k a b c := by
      exact Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun k _=>Finset.sum_congr rfl fun a _=>Finset.sum_comm
    _ = ∑ j,∑ i,∑ k,∑ c,∑ a,∑ b,G i j k a b c := by
      exact Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun k _=>Finset.sum_comm
    _ = ∑ j,∑ i,∑ c,∑ k,∑ a,∑ b,G i j k a b c := by
      exact Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ j,∑ c,∑ i,∑ k,∑ a,∑ b,G i j k a b c := by
      exact Finset.sum_congr rfl fun j _=>Finset.sum_comm

def S1 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualThirdCubicArray μ j a b*actualThirdCubicArray μ i k c)
theorem S1_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : S1 μ T=signedTraceSquare μ T := by
  unfold S1
  rw [reorderS1]
  unfold signedTraceSquare KLSBelow25.CubicCreation.annihilation
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro c _
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro k _
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro b _
  rw [hT12 i j k,hT23 a b c,hT12 a c b,third_rotate μ j a b]
  ring

private theorem reorderS2 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ k,∑ c,∑ i,∑ j,∑ a,∑ b,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ i,∑ k,∑ j,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ k,∑ i,∑ j,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_comm
    _ = ∑ k,∑ i,∑ j,∑ a,∑ c,∑ b,G i j k a b c := by
      exact Finset.sum_congr rfl fun k _=>Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun a _=>Finset.sum_comm
    _ = ∑ k,∑ i,∑ j,∑ c,∑ a,∑ b,G i j k a b c := by
      exact Finset.sum_congr rfl fun k _=>Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_comm
    _ = ∑ k,∑ i,∑ c,∑ j,∑ a,∑ b,G i j k a b c := by
      exact Finset.sum_congr rfl fun k _=>Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ k,∑ c,∑ i,∑ j,∑ a,∑ b,G i j k a b c := by
      exact Finset.sum_congr rfl fun k _=>Finset.sum_comm

def S2 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualThirdCubicArray μ k a b*actualThirdCubicArray μ i j c)
theorem S2_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : S2 μ T=signedTraceSquare μ T := by
  unfold S2
  rw [reorderS2]
  unfold signedTraceSquare KLSBelow25.CubicCreation.annihilation
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro k _
  apply Finset.sum_congr rfl;intro c _
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro b _
  rw [hT23 i j k,hT12 i k j,hT23 a b c,hT12 a c b,third_rotate μ k a b]
  ring

private theorem reorderS3 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ i,∑ b,∑ j,∑ k,∑ a,∑ c,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ i,∑ j,∑ k,∑ b,∑ a,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun k _=>Finset.sum_comm
    _ = ∑ i,∑ j,∑ b,∑ k,∑ a,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_comm
    _ = ∑ i,∑ b,∑ j,∑ k,∑ a,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_comm

def S3 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualThirdCubicArray μ i a c*actualThirdCubicArray μ j k b)
theorem S3_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : S3 μ T=signedTraceSquare μ T := by
  unfold S3
  rw [reorderS3]
  unfold signedTraceSquare KLSBelow25.CubicCreation.annihilation
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro b _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro k _
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro c _
  rw [hT12 a b c,third_rotate μ i a c]
  ring

private theorem reorderS4 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ j,∑ b,∑ i,∑ k,∑ a,∑ c,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ j,∑ i,∑ k,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_comm
    _ = ∑ j,∑ i,∑ k,∑ b,∑ a,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun k _=>Finset.sum_comm
    _ = ∑ j,∑ i,∑ b,∑ k,∑ a,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ j,∑ b,∑ i,∑ k,∑ a,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun j _=>Finset.sum_comm

def S4 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualThirdCubicArray μ j a c*actualThirdCubicArray μ i k b)
theorem S4_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : S4 μ T=signedTraceSquare μ T := by
  unfold S4
  rw [reorderS4]
  unfold signedTraceSquare KLSBelow25.CubicCreation.annihilation
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro b _
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro k _
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro c _
  rw [hT12 i j k,hT12 a b c,third_rotate μ j a c]
  ring

private theorem reorderS5 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ k,∑ b,∑ i,∑ j,∑ a,∑ c,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ i,∑ k,∑ j,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ k,∑ i,∑ j,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_comm
    _ = ∑ k,∑ i,∑ j,∑ b,∑ a,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun k _=>Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_comm
    _ = ∑ k,∑ i,∑ b,∑ j,∑ a,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun k _=>Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ k,∑ b,∑ i,∑ j,∑ a,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun k _=>Finset.sum_comm

def S5 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualThirdCubicArray μ k a c*actualThirdCubicArray μ i j b)
theorem S5_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : S5 μ T=signedTraceSquare μ T := by
  unfold S5
  rw [reorderS5]
  unfold signedTraceSquare KLSBelow25.CubicCreation.annihilation
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro k _
  apply Finset.sum_congr rfl;intro b _
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro c _
  rw [hT23 i j k,hT12 i k j,hT12 a b c,third_rotate μ k a c]
  ring

private theorem reorderS6 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ i,∑ a,∑ j,∑ k,∑ b,∑ c,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ i,∑ j,∑ a,∑ k,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_comm
    _ = ∑ i,∑ a,∑ j,∑ k,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_comm

def S6 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualThirdCubicArray μ i b c*actualThirdCubicArray μ j k a)
theorem S6_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : S6 μ T=signedTraceSquare μ T := by
  unfold S6
  rw [reorderS6]
  unfold signedTraceSquare KLSBelow25.CubicCreation.annihilation
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro k _
  apply Finset.sum_congr rfl;intro b _
  apply Finset.sum_congr rfl;intro c _
  rw [third_rotate μ i b c]
  ring

private theorem reorderS7 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ j,∑ a,∑ i,∑ k,∑ b,∑ c,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ j,∑ i,∑ k,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_comm
    _ = ∑ j,∑ i,∑ a,∑ k,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ j,∑ a,∑ i,∑ k,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun j _=>Finset.sum_comm

def S7 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualThirdCubicArray μ j b c*actualThirdCubicArray μ i k a)
theorem S7_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : S7 μ T=signedTraceSquare μ T := by
  unfold S7
  rw [reorderS7]
  unfold signedTraceSquare KLSBelow25.CubicCreation.annihilation
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro k _
  apply Finset.sum_congr rfl;intro b _
  apply Finset.sum_congr rfl;intro c _
  rw [hT12 i j k,third_rotate μ j b c]
  ring

private theorem reorderS8 {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ k,∑ a,∑ i,∑ j,∑ b,∑ c,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ i,∑ k,∑ j,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ k,∑ i,∑ j,∑ a,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_comm
    _ = ∑ k,∑ i,∑ a,∑ j,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun k _=>Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ k,∑ a,∑ i,∑ j,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun k _=>Finset.sum_comm

def S8 (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(actualThirdCubicArray μ k b c*actualThirdCubicArray μ i j a)
theorem S8_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : S8 μ T=signedTraceSquare μ T := by
  unfold S8
  rw [reorderS8]
  unfold signedTraceSquare KLSBelow25.CubicCreation.annihilation
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro k _
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro b _
  apply Finset.sum_congr rfl;intro c _
  rw [hT23 i j k,hT12 i k j,third_rotate μ k b c]
  ring

def D0 (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(δ i a*δ j b*δ k c)
theorem D0_eq (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : D0 T=tensorSquare T := by
  classical
  have he:D0 T=∑ i,∑ j,∑ k,T i j k*T i j k := by
    simp [D0,δ,mul_ite,ite_mul]
  rw [he]
  unfold tensorSquare square tripleSum
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro k _
  exact (pow_two _).symm

def D1 (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(δ i a*δ k b*δ j c)
theorem D1_eq (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : D1 T=tensorSquare T := by
  classical
  have he:D1 T=∑ i,∑ j,∑ k,T i j k*T i k j := by
    simp [D1,δ,mul_ite,ite_mul]
  rw [he]
  unfold tensorSquare square tripleSum
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro k _
  rw [hT23 i k j]
  exact (pow_two _).symm

def D2 (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(δ j a*δ i b*δ k c)
theorem D2_eq (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : D2 T=tensorSquare T := by
  classical
  have he:D2 T=∑ i,∑ j,∑ k,T i j k*T j i k := by
    simp [D2,δ,mul_ite,ite_mul]
  rw [he]
  unfold tensorSquare square tripleSum
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro k _
  rw [hT12 j i k]
  exact (pow_two _).symm

def D3 (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(δ j a*δ k b*δ i c)
theorem D3_eq (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : D3 T=tensorSquare T := by
  classical
  have he:D3 T=∑ i,∑ j,∑ k,T i j k*T j k i := by
    simp [D3,δ,mul_ite,ite_mul]
  rw [he]
  unfold tensorSquare square tripleSum
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro k _
  rw [hT23 j k i,hT12 j i k]
  exact (pow_two _).symm

def D4 (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(δ k a*δ i b*δ j c)
theorem D4_eq (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : D4 T=tensorSquare T := by
  classical
  have he:D4 T=∑ i,∑ j,∑ k,T i j k*T k i j := by
    simp [D4,δ,mul_ite,ite_mul]
  rw [he]
  unfold tensorSquare square tripleSum
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro k _
  rw [hT12 k i j,hT23 i k j]
  exact (pow_two _).symm

def D5 (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,T i j k*T a b c*(δ k a*δ j b*δ i c)
theorem D5_eq (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : D5 T=tensorSquare T := by
  classical
  have he:D5 T=∑ i,∑ j,∑ k,T i j k*T k j i := by
    simp [D5,δ,mul_ite,ite_mul]
  rw [he]
  unfold tensorSquare square tripleSum
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro k _
  rw [hT23 k j i,hT12 k i j,hT23 i k j]
  exact (pow_two _).symm

private theorem reorderSixth {ι : Type*} [Fintype ι] (G : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c)=∑ i,∑ a,∑ j,∑ k,∑ b,∑ c,G i j k a b c := by
  calc
    (∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,G i j k a b c) = ∑ i,∑ j,∑ a,∑ k,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_comm
    _ = ∑ i,∑ a,∑ j,∑ k,∑ b,∑ c,G i j k a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_comm

theorem sixth_contract_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) :
    contract T (fun i j k a b c=>cumulantJet μ [i,j,k,a,b,c] 0)=sixthContraction μ T := by
  unfold contract
  rw [reorderSixth]
  unfold sixthContraction
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro k _
  apply Finset.sum_congr rfl;intro b _
  apply Finset.sum_congr rfl;intro c _
  congr 1
  apply cumulantJet_perm_zero hμ
  apply List.perm_iff_count.mpr
  intro x
  simp only [List.count_cons,List.count_nil]
  omega

def momentKernel (μ : Measure (Space n)) (i j k a b c : Fin n) : ℝ :=
  cumulantJet μ [i,j,k,a,b,c] 0+(actualFourthCumulantArray μ i j a b*δ k c)+(actualFourthCumulantArray μ i k a b*δ j c)+(actualFourthCumulantArray μ j k a b*δ i c)+(actualFourthCumulantArray μ i j a c*δ k b)+(actualFourthCumulantArray μ i k a c*δ j b)+(actualFourthCumulantArray μ j k a c*δ i b)+(actualFourthCumulantArray μ i j b c*δ k a)+(actualFourthCumulantArray μ i k b c*δ j a)+(actualFourthCumulantArray μ j k b c*δ i a)+(actualThirdCubicArray μ i a b*actualThirdCubicArray μ j k c)+(actualThirdCubicArray μ j a b*actualThirdCubicArray μ i k c)+(actualThirdCubicArray μ k a b*actualThirdCubicArray μ i j c)+(actualThirdCubicArray μ i a c*actualThirdCubicArray μ j k b)+(actualThirdCubicArray μ j a c*actualThirdCubicArray μ i k b)+(actualThirdCubicArray μ k a c*actualThirdCubicArray μ i j b)+(actualThirdCubicArray μ i b c*actualThirdCubicArray μ j k a)+(actualThirdCubicArray μ j b c*actualThirdCubicArray μ i k a)+(actualThirdCubicArray μ k b c*actualThirdCubicArray μ i j a)+(δ i a*δ j b*δ k c)+(δ i a*δ k b*δ j c)+(δ j a*δ i b*δ k c)+(δ j a*δ k b*δ i c)+(δ k a*δ i b*δ j c)+(δ k a*δ j b*δ i c)

theorem momentKernel_contract_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) :
    contract T (momentKernel μ)=sixthContraction μ T+9*fourthContraction μ T+
      9*signedTraceSquare μ T+6*tensorSquare T := by
  have he:contract T (momentKernel μ)=contract T (fun i j k a b c=>cumulantJet μ [i,j,k,a,b,c] 0)+F0 μ T+F1 μ T+F2 μ T+F3 μ T+F4 μ T+F5 μ T+F6 μ T+F7 μ T+F8 μ T+S0 μ T+S1 μ T+S2 μ T+S3 μ T+S4 μ T+S5 μ T+S6 μ T+S7 μ T+S8 μ T+D0 T+D1 T+D2 T+D3 T+D4 T+D5 T := by
    unfold contract momentKernel F0 F1 F2 F3 F4 F5 F6 F7 F8 S0 S1 S2 S3 S4 S5 S6 S7 S8 D0 D1 D2 D3 D4 D5
    simp (config := { maxSteps := 2000000 }) only [mul_add,Finset.sum_add_distrib]
  rw [he,sixth_contract_eq hμ]
  rw [F0_eq hμ T hT12 hT23,F1_eq hμ T hT12 hT23,F2_eq hμ T hT12 hT23,F3_eq hμ T hT12 hT23,F4_eq hμ T hT12 hT23,F5_eq hμ T hT12 hT23,F6_eq hμ T hT12 hT23,F7_eq hμ T hT12 hT23,F8_eq hμ T hT12 hT23,S0_eq hμ T hT12 hT23,S1_eq hμ T hT12 hT23,S2_eq hμ T hT12 hT23,S3_eq hμ T hT12 hT23,S4_eq hμ T hT12 hT23,S5_eq hμ T hT12 hT23,S6_eq hμ T hT12 hT23,S7_eq hμ T hT12 hT23,S8_eq hμ T hT12 hT23,D0_eq T hT12 hT23,D1_eq T hT12 hT23,D2_eq T hT12 hT23,D3_eq T hT12 hT23,D4_eq T hT12 hT23,D5_eq T hT12 hT23]
  ring

end KLSConstantImprovement.CubicCumulantContraction
#print axioms KLSConstantImprovement.CubicCumulantContraction.cumulantJet_perm_zero
#print axioms KLSConstantImprovement.CubicCumulantContraction.sixth_contract_eq
#print axioms KLSConstantImprovement.CubicCumulantContraction.momentKernel_contract_eq
