import TwoAxisHelicoid.IsothermalComplexAtlas
import TwoAxisHelicoid.ImmersionChartReparametrization

namespace TwoAxisHelicoid
open Complex Matrix Filter Set InnerProductSpace
open scoped Topology ContDiff Manifold ComplexConjugate
set_option maxHeartbeats 1300000

variable {M : Type*} [TopologicalSpace M]

theorem harmonic_surface_param_smooth {Y : ℂ → Fin 3 → ℝ} {y : ℂ} (hY : HarmonicAt Y y) :
    ContDiffAt ℝ ∞ Y y := by
  apply contDiffAt_pi.mpr
  intro j
  exact (_root_.HarmonicAt.analyticAt (hY.comp_CLM (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ))).contDiffAt

theorem surfaceTangentCross_nonzero_of_factor {Y : ℂ → Fin 3 → ℝ} {y : ℂ}
    {c : ℝ} (hc : 0 < c) (h : ∀ v, fderiv ℝ Y y v ⬝ᵥ fderiv ℝ Y y v = c*normSq v) :
    surfaceTangentCross Y y ≠ 0 := by
  let D := fderiv ℝ Y y
  have h₁ : D 1 ⬝ᵥ D 1 = c := by simpa [D] using h 1
  have hI : D I ⬝ᵥ D I = c := by simpa [D] using h I
  have h0 := (conformal_immersion_of_metric_factor D hc h).2.1
  intro hz
  have he : (D 1 ⨯₃ D I) ⬝ᵥ (D 1 ⨯₃ D I) = 0 := by
    change surfaceTangentCross Y y ⬝ᵥ surfaceTangentCross Y y = 0
    simp [hz]
  rw [cross_dot_cross,h₁,hI,h0,zero_mul,sub_zero] at he
  exact (mul_pos hc hc).ne' he

theorem continuousAt_surfaceTangentCross {Y : ℂ → Fin 3 → ℝ} {y : ℂ} (hY : ContDiffAt ℝ 2 Y y) :
    ContinuousAt (surfaceTangentCross Y) y := by
  have hd := (hY.fderiv_right (m := 1) (by norm_num)).continuousAt
  have hh (v : ℂ) (j : Fin 3) : ContinuousAt (fun z => fderiv ℝ Y z v j) y :=
    (continuous_apply j).continuousAt.comp (hd.clm_apply continuousAt_const)
  apply continuousAt_pi.mpr
  intro j
  fin_cases j <;> simp only [surfaceTangentCross,cross_apply] <;> exact ((hh _ _).mul (hh _ _)).sub ((hh _ _).mul (hh _ _))

theorem continuousAt_surfaceTransversal {F N : M → Fin 3 → ℝ} {e : OpenPartialHomeomorph M ℂ}
    {y : ℂ} (hy : y ∈ e.target) (hN : Continuous N) (hY : ContDiffAt ℝ 2 (F ∘ e.symm) y) :
    ContinuousAt (fun w => surfaceTangentCross (F ∘ e.symm) w ⬝ᵥ N (e.symm w)) y := by
  have ha := continuousAt_surfaceTangentCross hY
  have hb := hN.continuousAt.comp (e.symm.continuousAt hy)
  unfold dotProduct
  exact tendsto_finsetSum _ (fun j _ => ((continuous_apply j).continuousAt.comp ha).mul
    ((continuous_apply j).continuousAt.comp hb))

/-- Complex conjugation corrects the orientation on a negatively
oriented isothermal patch while preserving its actual induced metric. -/
theorem isothermal_chart_reverse {F N : M → Fin 3 → ℝ} {e : OpenPartialHomeomorph M ℂ}
    (hr : RegularImmersionChart F e)
    (hm : ∀ y ∈ e.target, ∃ c : ℝ, 0 < c ∧ ∀ v, fderiv ℝ (F ∘ e.symm) y v ⬝ᵥ
        fderiv ℝ (F ∘ e.symm) y v = c*normSq v)
    (ho : ∀ y ∈ e.target, surfaceTangentCross (F ∘ e.symm) y ⬝ᵥ N (e.symm y) < 0) :
    OrientedIsothermalChart F N (e.trans conjCLE.toHomeomorph.toOpenPartialHomeomorph) := by
  let k := e.trans conjCLE.toHomeomorph.toOpenPartialHomeomorph
  have hregular : RegularImmersionChart F k :=
    regularImmersionChart_reparametrize hr conjCLE
  refine ⟨hregular,?_⟩
  intro y hy
  have hy' : conj y ∈ e.target := hy.2
  obtain ⟨c,hc,hg⟩ := hm _ hy'
  have hd := (hr _ hy').1.differentiableAt (by simp)
  let Y := F ∘ e.symm
  have he (v : ℂ) : fderiv ℝ (F ∘ k.symm) y v = fderiv ℝ Y (conj y) (conj v) := by
    change fderiv ℝ (Y ∘ conjCLE) y v = _
    have hdY : DifferentiableAt ℝ Y (conjCLE y) := hd
    rw [fderiv_comp y hdY conjCLE.differentiableAt,conjCLE.fderiv]
    rfl
  refine ⟨⟨c,hc,fun v => ?_⟩,?_⟩
  · change _ ⬝ᵥ _ = _
    rw [he,show fderiv ℝ Y (conj y) (conj v) ⬝ᵥ fderiv ℝ Y (conj y) (conj v) = _ from hg (conj v)]
    simp
  · have hneg := ho (conj y) hy'
    change surfaceTangentCross (F ∘ k.symm) y ⬝ᵥ N (e.symm (conj y)) > 0
    unfold surfaceTangentCross
    rw [he,he]
    simp only [map_one,conj_I,map_neg,neg_dotProduct]
    exact neg_pos.mpr hneg

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.isothermal_chart_reverse
