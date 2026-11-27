import TwoAxisHelicoid.PuncturedTorusRealOrientation
import TwoAxisHelicoid.SmoothMarkingOfAnalyticHandle
import TwoAxisHelicoid.SmoothMarkingFromPhysicalTorus
import TwoAxisHelicoid.UnmarkedHelicoidSpinCompactification

namespace TwoAxisHelicoid
open Complex Set Matrix Filter Topology
open scoped Topology ContDiff Manifold ComplexConjugate
universe u v

/-- A local conformal parametrization of the induced metric. The local patches
carry their own orientations and use the actual position of the surface. -/
def UnorientedLocalMetricChart {M : Type*} [TopologicalSpace M] (X : M → Fin 3 → ℝ)
    (e : OpenPartialHomeomorph M ℂ) : Prop :=
  RegularImmersionChart X e ∧ ∀ y∈e.target, ∃ c : ℝ, 0<c ∧ ∀ v : ℂ,
    let L := fderiv ℝ (X ∘ e.symm) y
    L v ⬝ᵥ L v = c*normSq v

theorem orient_local_metric_chart {M : Type*} [TopologicalSpace M] {X N : M → Fin 3 → ℝ}
    {e : OpenPartialHomeomorph M ℂ} {x : M} (normal : Continuous N)
    (regular : UnorientedLocalMetricChart X e) (hx : x∈e.source)
    (transverse : surfaceTangentCross (X ∘ e.symm) (e x) ⬝ᵥ N x ≠ 0) :
    ∃ d : OpenPartialHomeomorph M ℂ, OrientedIsothermalChart X N d ∧ x∈d.source := by
  let φ := fun w => surfaceTangentCross (X ∘ e.symm) w ⬝ᵥ N (e.symm w)
  have hz := e.map_source hx
  have hz0 : φ (e x) ≠ 0 := by simpa only [φ,e.left_inv hx] using transverse
  have cont : ContinuousAt φ (e x) := continuousAt_surfaceTransversal hz normal
    ((regular.1 _ hz).1.of_le (by norm_num))
  have sign : ∀ᶠ y in 𝓝 (e x), 0 < φ y*φ (e x) :=
    (cont.mul continuousAt_const).eventually (Ioi_mem_nhds (mul_self_pos.mpr hz0))
  obtain ⟨U,sub,op,atx⟩ := mem_nhds_iff.mp sign
  let d := e.trans (OpenPartialHomeomorph.ofSet U op)
  have src : x∈d.source := ⟨hx,atx⟩
  have reg : RegularImmersionChart X d := fun y hy => regular.1 _ hy.2
  have metric (y : ℂ) (hy : y∈d.target) : ∃ c : ℝ, 0<c ∧ ∀ v : ℂ,
      fderiv ℝ (X ∘ d.symm) y v ⬝ᵥ fderiv ℝ (X ∘ d.symm) y v = c*normSq v := regular.2 y hy.2
  by_cases hp : 0<φ (e x)
  · exact ⟨d,⟨reg,fun y hy => ⟨metric y hy,pos_of_mul_pos_left (sub hy.1) hp.le⟩⟩,src⟩
  · refine ⟨d.trans conjCLE.toHomeomorph.toOpenPartialHomeomorph,isothermal_chart_reverse reg metric ?_,src,mem_univ _⟩
    intro y hy
    have hh : 0<φ y*φ (e x) := sub hy.1
    rcases mul_pos_iff.mp hh with h | h
    · exact (hp h.2).elim
    · exact h.1

/-- Regularity in the physical charts tests both the manifold smoothness
and derivative rank of the same position in that atlas. -/
theorem immersion_of_preferred_physical_charts {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {X : M → Fin 3 → ℝ} (cont : Continuous X)
    (reg : ∀ x : M, RegularImmersionChart X (chartAt ℂ x)) :
    ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X ∧
    ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x) := by
  have deriv (x : M) : HasMFDerivAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x
      (fderiv ℝ (X ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)) := by
    have hx := (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    have hd := ((reg x _ hx).1.differentiableAt (by simp)).hasFDerivAt
    refine ⟨cont.continuousAt,?_⟩
    simpa only [writtenInExtChartAt,mfld_simps] using!
      hd.hasFDerivWithinAt (s := range 𝓘(ℝ,ℂ))
  constructor
  · intro x
    have hx := (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    apply contMDiffAt_iff.mpr
    refine ⟨cont.continuousAt,?_⟩
    simpa only [mfld_simps] using! (reg x _ hx).1.contDiffWithinAt (s:=range 𝓘(ℝ,ℂ))
  · intro x
    rw [(deriv x).mfderiv]
    exact (reg x _ ((chartAt ℂ x).map_source (mem_chart_source ℂ x))).2

private theorem compose_metric_marking {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    [ChartedSpace ℂ P] [ChartedSpace ℂ Q] {L : PeriodPair}
    (g : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) P Q ∞)
    (f : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) Q (PuncturedPeriodTorus L) ∞) :
    Nonempty (Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) P (PuncturedPeriodTorus L) ∞) := ⟨g.trans f⟩

/-- Purely local isothermal charts produce a global marking smooth in the
original real atlas. The topology supplies the compatible orientations. -/
theorem smooth_marking_of_unoriented_local_metric_charts {M : Type v}
    [TopologicalSpace M] [T2Space M] [initial : ChartedSpace ℂ M] {L₀ : PeriodPair}
    (top : M ≃ₜ PuncturedPeriodTorus L₀) {X : M → Fin 3 → ℝ}
    (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (imm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x))
    (localCharts : ∀ x : M, ∃ e : OpenPartialHomeomorph M ℂ, UnorientedLocalMetricChart X e ∧ x∈e.source) :
    ∃ L : PeriodPair, Nonempty (Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) M (PuncturedPeriodTorus L) ∞) := by
  choose e metric hx using localCharts
  obtain ⟨d,hd,hpos⟩ := topological_punctured_torus_positive_degree_atlas top
  obtain ⟨N,hN,transverse⟩ := surface_transverse_field_of_topological_atlas e d hx hd
    (fun x => (metric x).1) hpos
  let cover := fun x => orient_local_metric_chart hN (metric x) (hx x) (transverse x)
  have cont : Continuous X := sm.continuous
  let S := isothermalComplexAtlas X N cover
  have regular : let _ := S
      ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X ∧
      ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x) := by
    let _ := S
    exact immersion_of_preferred_physical_charts cont fun x => (cover x).choose_spec.1.1
  have marking : let _ := S
      ∃ L : PeriodPair, Nonempty (Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) M (PuncturedPeriodTorus L) ∞) := by
    let _ := S
    let _ : IsManifold 𝓘(ℂ,ℂ) ω M := isothermalComplexAtlas_isManifold X N cover
    exact smooth_marking_of_analytic_handle top
  obtain ⟨g,_⟩ := @smooth_marking_of_common_positions M M _ _ initial S (Homeomorph.refl M)
    X X sm imm regular.1 regular.2 (fun _ => rfl)
  obtain ⟨L,⟨f⟩⟩ := marking
  exact ⟨L,@compose_metric_marking M M _ _ initial S L g f⟩

/-- Proposition 4.4 for a real smoothly embedded surface with local
isothermal coordinates, with a cap and genuine even spin cover of its
original position. This includes nonminimal surfaces of finite end modulus. -/
theorem local_metric_handle_height_end_even_spin {M : Type v}
    [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] {L₀ : PeriodPair}
    (top : M ≃ₜ PuncturedPeriodTorus L₀) (X : M → Fin 3 → ℝ) (cl : IsClosedEmbedding X)
    (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (imm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x))
    (localCharts : ∀ x : M, ∃ e : OpenPartialHomeomorph M ℂ, UnorientedLocalMetricChart X e ∧ x∈e.source)
    (A : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates) (sa : ContDiff ℝ ∞ A)
    (si : ContDiff ℝ ∞ A.symm) (height : HasHelicoidHeightEnd (A ∘ X)) :
    ∃ (L : PeriodPair) (e : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) M (PuncturedPeriodTorus L) ∞),
      EvenSpinExtensionInMarking.{u} X e := by
  obtain ⟨L,⟨g⟩⟩ := smooth_marking_of_unoriented_local_metric_charts top sm imm localCharts
  exact ⟨L,g,abstract_helicoidal_surface_even_in_smooth_marking X cl sm imm A sa si height g⟩
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_marking_of_unoriented_local_metric_charts
#print axioms TwoAxisHelicoid.local_metric_handle_height_end_even_spin

