import TwoAxisHelicoid.MinimalManifoldComplexStructure

namespace TwoAxisHelicoid
open Complex Matrix Filter Set
open scoped Topology ContDiff Manifold
set_option maxHeartbeats 1400000

theorem surfaceTangentCross_ne_zero_of_injective {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hi : Function.Injective (fderiv ℝ X z)) : surfaceTangentCross X z ≠ 0 := by
  let D := fderiv ℝ X z
  have h₁ : D 1 ≠ 0 := fun h => one_ne_zero (hi (h.trans D.map_zero.symm))
  apply crossProduct_ne_zero_iff_linearIndependent.mpr
  rw [LinearIndependent.pair_iff' h₁]
  intro t ht
  have hti : D (t • (1:ℂ)) = D I := (D.map_smul t 1).trans ht
  have him := congrArg Complex.im (hi hti)
  simp [Complex.real_smul] at him

noncomputable def normalizedTangentCross (X : ℂ → Fin 3 → ℝ) (z : ℂ) : Fin 3 → ℝ :=
  ‖surfaceTangentCross X z‖⁻¹ • surfaceTangentCross X z

theorem normalizedTangentCross_compatible {X Y : ℂ → Fin 3 → ℝ} {f : ℂ → ℂ} {z : ℂ}
    (he : X =ᶠ[𝓝 z] (Y ∘ f)) (hY : DifferentiableAt ℝ Y (f z)) (hf : DifferentiableAt ℝ f z)
    (ho : 0 < planeRealJacobian (fderiv ℝ f z)) :
    normalizedTangentCross X z = normalizedTangentCross Y (f z) := by
  unfold normalizedTangentCross
  rw [surfaceTangentCross_coordinate_change he hY hf,norm_smul,Real.norm_of_nonneg ho.le,smul_smul]
  congr 1
  field_simp

theorem normalizedTangentCross_continuousAt {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : ContDiffAt ℝ 2 X z) (hi : Function.Injective (fderiv ℝ X z)) :
    ContinuousAt (normalizedTangentCross X) z := by
  have hc := continuousAt_surfaceTangentCross hX
  exact (hc.norm.inv₀ (norm_ne_zero_iff.mpr (surfaceTangentCross_ne_zero_of_injective hi))).smul hc

theorem surfaceTangentCross_dot_normalized_pos {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hi : Function.Injective (fderiv ℝ X z)) : 0 < surfaceTangentCross X z ⬝ᵥ normalizedTangentCross X z := by
  let C := surfaceTangentCross X z
  have hn : C ≠ 0 := surfaceTangentCross_ne_zero_of_injective hi
  have hp : 0 < C ⬝ᵥ C := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (C i))
    (fun hh => hn (dotProduct_self_eq_zero.mp hh.symm))
  change 0 < C ⬝ᵥ (‖C‖⁻¹ • C)
  rw [dotProduct_smul,smul_eq_mul]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hn)) hp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- The real atlas is oriented precisely here by positive Jacobians
between its preferred charts at overlapping points. -/
def PositiveSurfaceAtlas (M : Type*) [TopologicalSpace M] [ChartedSpace ℂ M] : Prop :=
  ∀ x y : M, x ∈ (chartAt ℂ y).source →
    0 < planeRealJacobian (fderiv ℝ ((chartAt ℂ x).symm.trans (chartAt ℂ y)) ((chartAt ℂ x) x))

/-- The original real orientation and a regular immersion construct the
continuous transverse ambient normal used to orient the isothermal atlas. -/
theorem oriented_immersion_transverse_field {F : M → Fin 3 → ℝ}
    (hr : ∀ x : M, RegularImmersionChart F (chartAt ℂ x)) (ho : PositiveSurfaceAtlas M) :
    ∃ N : M → Fin 3 → ℝ, Continuous N ∧ ∀ x,
      0 < surfaceTangentCross (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ⬝ᵥ N x := by
  let N := fun x : M => normalizedTangentCross (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  refine ⟨N,continuous_iff_continuousAt.mpr ?_,?_⟩
  · intro y
    let d := chartAt ℂ y
    have hy : y ∈ d.source := mem_chart_source ℂ y
    have hcomp : ContinuousAt (fun x => normalizedTangentCross (F ∘ d.symm) (d x)) y :=
      (normalizedTangentCross_continuousAt ((hr y _ (d.map_source hy)).1.of_le (by norm_num))
        (hr y _ (d.map_source hy)).2).comp (d.continuousAt hy)
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [d.open_source.mem_nhds hy] with x hx
    let e := chartAt ℂ x
    let f := e.symm.trans d
    let z := e x
    have hz : x ∈ e.source := mem_chart_source ℂ x
    have hs : z ∈ f.source := ⟨e.map_source hz,by change e.symm (e x) ∈ d.source; rwa [e.left_inv hz]⟩
    have he : (F ∘ e.symm) =ᶠ[𝓝 z] ((F ∘ d.symm) ∘ f) := by
      filter_upwards [f.open_source.mem_nhds hs] with w hw
      exact congrArg F (d.left_inv hw.2).symm
    have hfy : f z = d x := congrArg d (e.left_inv hz)
    have hY := (hr y _ (d.map_source hx)).1.differentiableAt (by simp)
    have hf := (regularImmersionChart_transition (hr x) (hr y) hs).differentiableAt (by simp)
    have hh := normalizedTangentCross_compatible he (hfy.symm ▸ hY) hf (ho x y hx)
    rw [hfy] at hh
    exact hh
  · intro x
    exact surfaceTangentCross_dot_normalized_pos (hr x _ ((chartAt ℂ x).map_source (mem_chart_source ℂ x))).2

/-- An oriented real minimal manifold acquires its induced complex
analytic structure from the immersion and the original atlas alone. -/
theorem oriented_minimal_manifold_induced_complex_structure [IsManifold 𝓘(ℝ,ℂ) ∞ M]
    {F : M → Fin 3 → ℝ} (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F x)) (ho : PositiveSurfaceAtlas M)
    (hm : ∀ x : M, coordinateMeanCurvature (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0) :
    ∃ (N : M → Fin 3 → ℝ) (S : ChartedSpace ℂ M), let _ := S
      Continuous N ∧ IsManifold 𝓘(ℂ,ℂ) ω M ∧ ∀ e ∈ atlas ℂ M, OrientedIsothermalChart F N e := by
  obtain ⟨N,hn,ht⟩ := oriented_immersion_transverse_field (smooth_surface_regular_manifold_chart hF hi) ho
  obtain ⟨S,hs,hchart⟩ := smooth_minimal_manifold_induced_complex_structure hF hi hn hm (fun x => (ht x).ne')
  exact ⟨N,S,hn,hs,hchart⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.oriented_minimal_manifold_induced_complex_structure
