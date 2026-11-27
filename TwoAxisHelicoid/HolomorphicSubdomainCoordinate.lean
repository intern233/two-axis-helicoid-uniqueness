import TwoAxisHelicoid.OpenSubsetCoordinate
import TwoAxisHelicoid.ExteriorComplexEnd
import TwoAxisHelicoid.TopologicalAnnulusUniformization

namespace TwoAxisHelicoid
open Complex Set Filter Metric TopologicalSpace
open scoped Topology ContDiff Manifold

/-- Extend a biholomorphism between open subdomains to a maximal atlas
chart on the whole manifold, with exactly the prescribed source and target. -/
theorem holomorphic_subdomain_coordinate {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (S : Opens M) (T : Opens ℂ) (ne : Nonempty S)
    (E : Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) S T ω) :
    ∃ e : OpenPartialHomeomorph M ℂ, e.source=S ∧ e.target=T ∧
      e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := by
  obtain ⟨e,src,tgt,forward⟩ := open_coordinate_of_subsets S.isOpen T.isOpen ne E.toHomeomorph
  have backward (y : T) : e.symm y.1=(E.symm y).1 := by
    have eq := forward (E.symm y)
    change e (E.symm y).1=(E (E.symm y)).1 at eq
    rw [E.apply_symm_apply] at eq
    rw [← eq,e.left_inv (by rw [src]; exact (E.symm y).2)]
  refine ⟨e,src,tgt,e.mem_maximalAtlas_of_contMDiffOn ?_ ?_⟩
  · intro x hx
    let z : S := ⟨x,show x∈(S : Set M) from src ▸ hx⟩
    have h : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun a : S => e a.1) z :=
      ((contMDiff_subtype_val (U := T)).comp E.contMDiff_toFun z).congr_of_eventuallyEq (Eventually.of_forall forward)
    exact (contMDiffAt_subtype_iff.mp h).contMDiffWithinAt
  · intro x hx
    let z : T := ⟨x,show x∈(T : Set ℂ) from tgt ▸ hx⟩
    have h : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun a : T => e.symm a.1) z :=
      ((contMDiff_subtype_val (U := S)).comp E.contMDiff_invFun z).congr_of_eventuallyEq (Eventually.of_forall backward)
    exact (contMDiffAt_subtype_iff.mp h).contMDiffWithinAt

universe u

/-- A topological puncture chart plus uniformization gives a genuine
holomorphic chart on the same end, with a round cylinder as target. -/
theorem puncture_topology_round_complex_chart {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (D : PuncturedComplexEnd M) (uni : TopologicalPlaneUniformization.{u}) :
    ∃ e : OpenPartialHomeomorph M ℂ, IsCompact e.sourceᶜ ∧
      e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M ∧ IsRoundCylinderTarget e.target := by
  let S : Opens M := ⟨D.coord.source,D.coord.open_source⟩
  have tgt : D.coord.target={z : ℂ | 0<‖z‖ ∧ ‖z‖<D.radius} := by
    rw [D.target_eq]
    ext z
    change (dist z 0<D.radius ∧ z≠0) ↔ 0<‖z‖ ∧ ‖z‖<D.radius
    rw [dist_zero_right,norm_pos_iff,and_comm]
  let mark : S ≃ₜ {z : ℂ // 0<‖z‖ ∧ ‖z‖<D.radius} :=
    D.coord.toHomeomorphSourceTarget.trans (Homeomorph.setCongr tgt)
  have half : 0<D.radius/2 := half_pos D.radius_pos
  have hnorm : ‖((D.radius/2:ℝ):ℂ)‖=D.radius/2 := by rw [Complex.norm_real,Real.norm_of_nonneg half.le]
  have n : Nonempty S := ⟨mark.symm ⟨((D.radius/2:ℝ):ℂ),by rw [hnorm]; exact ⟨half,half_lt_self D.radius_pos⟩⟩⟩
  obtain ⟨T,round,⟨U⟩⟩ := annular_uniformization_of_plane_dichotomy D.radius_pos mark uni
  obtain ⟨e,es,et,hol⟩ := holomorphic_subdomain_coordinate S T n U
  exact ⟨e,by rw [es]; exact D.compact_core,hol,by rw [et]; exact round⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.puncture_topology_round_complex_chart
