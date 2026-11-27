import TwoAxisHelicoid.PlaneChartOrientationCocycle
import Mathlib.Topology.IsLocalHomeomorph

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold

/-- A topological plane parametrizing a Riemann surface by a local
homeomorphism has one common orientation sign in all its complex
charts. The parametrization need only be continuous. -/
theorem complex_surface_plane_cover_orientation {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {p : ℂ → M} (cover : IsLocalHomeomorph p) :
    ∃ s : ℤ, (s=1 ∨ s= -1) ∧ ∀ (z : ℂ) (i : M), p z∈(chartAt ℂ i).source →
      HasPlaneOrientationAt ((chartAt ℂ i) ∘ p) z s := by
  have cp : Continuous p := cover.continuous
  choose l ls pr using cover
  have transfer (z : ℂ) (i j : M) (hi : p z∈(chartAt ℂ i).source)
      (hj : p z∈(chartAt ℂ j).source) {n : ℤ} (ori : HasPlaneOrientationAt ((chartAt ℂ i) ∘ p) z n) :
      HasPlaneOrientationAt ((chartAt ℂ j) ∘ p) z n := by
    let a := chartAt ℂ i
    let b := chartAt ℂ j
    let e := (l z).trans a
    let d := a.symm.trans b
    have form : (e : ℂ → ℂ)=a ∘ p := by rw [pr z]; rfl
    have src : z∈e.source := ⟨ls z,by change l z z∈a.source; rw [← pr z]; exact hi⟩
    have dz : e z∈d.source := by rw [form]; exact planeChart_transition_source hi hj
    have transdeg := (planeChartIndex_spec a b hi hj).2
    rw [planeChartIndex_holomorphic (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ i))
      (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ j)) hi hj] at transdeg
    have atd : HasPlaneOrientationAt d (e z) 1 := by rw [form]; exact transdeg
    have eo : HasPlaneOrientationAt e z n := form ▸ ori
    have result := openPartialHomeomorph_plane_orientation_comp e d src dz atd eo
    rw [one_mul] at result
    apply result.congr
    filter_upwards [(l z).open_source.mem_nhds (ls z),cp.continuousAt.eventually (a.open_source.mem_nhds hi)] with w _ hw
    change b (p w)=b (a.symm (e w))
    rw [form,Function.comp_apply,a.left_inv hw]
  have existsSign (z : ℂ) : ∃ s : ℤ, (s=1 ∨ s= -1) ∧ HasPlaneOrientationAt ((chartAt ℂ (p z)) ∘ p) z s := by
    let e := (l z).trans (chartAt ℂ (p z))
    have src : z∈e.source := ⟨ls z,by change l z z∈(chartAt ℂ (p z)).source; rw [← pr z]; exact mem_chart_source ℂ (p z)⟩
    have sign := openPartialHomeomorph_orientation_sign e src
    obtain ⟨s,unit,angle⟩ := sign
    exact ⟨s,unit,angle.congr (Eventually.of_forall fun w => congrArg (chartAt ℂ (p z)) (congrFun (pr z) w))⟩
  choose s unit ori using existsSign
  have lc : IsLocallyConstant s := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    let e := (l z).trans (chartAt ℂ (p z))
    have form : (e : ℂ → ℂ)=(chartAt ℂ (p z)) ∘ p := funext fun w => congrArg (chartAt ℂ (p z)) (congrFun (pr z).symm w)
    have src : z∈e.source := ⟨ls z,by change l z z∈(chartAt ℂ (p z)).source; rw [← pr z]; exact mem_chart_source ℂ (p z)⟩
    have ez : HasPlaneOrientationAt e z (s z) := form ▸ ori z
    filter_upwards [openPartialHomeomorph_orientation_locally_constant e src ez,
      cp.continuousAt.eventually ((chartAt ℂ (p z)).open_source.mem_nhds (mem_chart_source ℂ (p z)))] with w sign inside
    rw [form] at sign
    exact (ori w).unique (transfer w (p z) (p w) inside (mem_chart_source ℂ _) sign)
  refine ⟨s 0,unit 0,fun z i hz => ?_⟩
  have eq := lc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ z) (mem_univ 0)
  exact eq ▸ transfer z (p z) i (mem_chart_source ℂ _) hz (ori z)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.complex_surface_plane_cover_orientation
