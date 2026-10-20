import TemperedWeakDerivative
import FiniteNegativeSobolev
import MollifiedTensorPotential

/-! Integer Fourier Sobolev membership supplies an actual real L2 weak
derivative tower and its literal compact mollified smooth approximations. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter TemperedDistribution
open scoped ContDiff Topology SchwartzMap LineDeriv BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLSBelow25
variable {n q : ℕ}
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem coordinateTemperedWord_exists_Lp {u : 𝓢'(Space n,ℂ)}
    (hu : MemSobolev (q : ℝ) 2 u) (L : List (Fin n)) (hL : L.length ≤ q) :
    ∃ G : Lp ℂ 2 (volume : Measure (Space n)), coordinateTemperedWord L u=G := by
  apply memSobolev_zero_iff.mp
  exact (coordinateTemperedWord_memSobolev hu L).mono (by
    have hcast : (L.length : ℝ) ≤ q := by exact_mod_cast hL
    linarith)

def complexSobolevJet {u : 𝓢'(Space n,ℂ)} (hu : MemSobolev (q : ℝ) 2 u)
    (L : List (Fin n)) : Lp ℂ 2 (volume : Measure (Space n)) :=
  if hL : L.length ≤ q then Classical.choose (coordinateTemperedWord_exists_Lp hu L hL) else 0

theorem complexSobolevJet_tempered {u : 𝓢'(Space n,ℂ)}
    (hu : MemSobolev (q : ℝ) 2 u) (L : List (Fin n)) (hL : L.length ≤ q) :
    (complexSobolevJet hu L : 𝓢'(Space n,ℂ))=coordinateTemperedWord L u := by
  simp only [complexSobolevJet,dif_pos hL]
  exact (Classical.choose_spec (coordinateTemperedWord_exists_Lp hu L hL)).symm

def realSobolevJet {u : 𝓢'(Space n,ℂ)} (hu : MemSobolev (q : ℝ) 2 u)
    (L : List (Fin n)) : Lp ℝ 2 (volume : Measure (Space n)) :=
  Complex.reCLM.compLp (complexSobolevJet hu L)

theorem realSobolevJet_weak {u : 𝓢'(Space n,ℂ)}
    (hu : MemSobolev (q : ℝ) 2 u) (L : List (Fin n)) (hL : L.length < q) (i : Fin n) :
    HasWeakCoordinateDerivative (realSobolevJet hu L) i (realSobolevJet hu (i::L)) := by
  have hd : ∂_{EuclideanSpace.single i (1 : ℝ)}
      (complexSobolevJet hu L : 𝓢'(Space n,ℂ)) =
      (complexSobolevJet hu (i::L) : 𝓢'(Space n,ℂ)) := by
    rw [complexSobolevJet_tempered hu L (by omega),
      complexSobolevJet_tempered hu (i::L) (by simp only [List.length_cons]; omega)]
    rfl
  apply (hasLocalWeakCoordinateDerivative_realPart_of_tempered _ _ i hd).congr_ae
  · filter_upwards [Complex.reCLM.coeFn_compLp (complexSobolevJet hu L)] with x hx
    exact hx.symm
  · filter_upwards [Complex.reCLM.coeFn_compLp (complexSobolevJet hu (i::L))] with x hx
    exact hx.symm

theorem realSobolevJet_nil_ae {f : Space n → ℝ} (hf : MemLp f 2 volume)
    (hu : MemSobolev (q : ℝ) 2 (realMemLpToComplex hf : 𝓢'(Space n,ℂ))) :
    (realSobolevJet hu [] : Space n → ℝ)=ᵐ[volume] f := by
  have he : complexSobolevJet hu []=realMemLpToComplex hf := by
    apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ℂ) (μ := (volume : Measure (Space n))) (p := 2)))
    exact complexSobolevJet_tempered hu [] (by simp)
  filter_upwards [Complex.reCLM.coeFn_compLp (complexSobolevJet hu []),
    realMemLpToComplex_coe hf] with x hx hxf
  rw [he] at hx
  simpa [realSobolevJet,he,hxf] using hx

theorem coordinateWordDerivative_mollify_sobolev
    {f : Space n → ℝ} (hf : MemLp f 2 volume)
    (hu : MemSobolev (q : ℝ) 2 (realMemLpToComplex hf : 𝓢'(Space n,ℂ)))
    (L : List (Fin n)) (hL : L.length ≤ q) (k : ℕ) :
    coordinateWordDerivative (mollify k f) L=mollify k (realSobolevJet hu L) := by
  induction L with
  | nil =>
    change mollify k f=mollify k (realSobolevJet hu [])
    exact mollify_congr_ae (realSobolevJet_nil_ae hf hu).symm k
  | cons i L ih =>
    rw [coordinateWordDerivative_cons,ih (by simp only [List.length_cons] at hL; omega)]
    exact (realSobolevJet_weak hu L (by simp only [List.length_cons] at hL; omega) i).mollify_eq
      (Lp.memLp _) k

theorem eLpNorm_mollify_sobolev_jet_tendsto_zero
    {f : Space n → ℝ} (hf : MemLp f 2 volume)
    (hu : MemSobolev (q : ℝ) 2 (realMemLpToComplex hf : 𝓢'(Space n,ℂ)))
    (L : List (Fin n)) (hL : L.length ≤ q) :
    Tendsto (fun k => eLpNorm
      (coordinateWordDerivative (mollify k f) L-(realSobolevJet hu L : Space n → ℝ)) 2 volume)
      atTop (𝓝 0) := by
  simp_rw [coordinateWordDerivative_mollify_sobolev hf hu L hL]
  exact eLpNorm_mollify_sub_tendsto_zero (Lp.memLp _)

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.realSobolevJet_weak
#print axioms KLS.DeterministicBridgeIntegration.eLpNorm_mollify_sobolev_jet_tendsto_zero
