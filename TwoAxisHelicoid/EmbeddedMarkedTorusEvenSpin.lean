import TwoAxisHelicoid.SaddleHeightSurgery
import TwoAxisHelicoid.ImmersionChartReparametrization
import TwoAxisHelicoid.PinkallHelicoidSpinParity

namespace TwoAxisHelicoid
open Complex Set Filter Topology MeasureTheory Function
open scoped Topology ContDiff Manifold

/-- A compact embedded torus, smooth in the prescribed punctured
marking and regularly parametrized at the cap point, has even ambient
spin. A regular plane section is found inside the actual embedding. -/
theorem embedded_marked_torus_even_from_plane_sections (L : PeriodPair)
    (F : PeriodTorus L → Fin 3 → ℝ) (cont : Continuous F) (emb : Injective F)
    (sm : ∀ q≠0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q)
    (imm : ∀ q≠0, Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q))
    (d : OpenPartialHomeomorph (PeriodTorus L) ℂ) (src : (0:PeriodTorus L)∈d.source)
    (dsm : ContDiffAt ℝ ∞ (F ∘ d.symm) (d 0)) (dim : Injective (fderiv ℝ (F ∘ d.symm) (d 0))) :
    capAmbientSpinQuadratic L F (1,0)*capAmbientSpinQuadratic L F (0,1)=0 := by
  classical
  obtain ⟨H,marked⟩ := marked_torus_circle_product L
  by_contra odd
  obtain ⟨s,saddle,count⟩ := (odd_embedded_torus_has_single_saddle_section L F cont emb sm imm
    d src dsm dim H marked odd).exists
  let h := tiltedSpatialHeight s ∘ F
  let π := periodTorusProjection L
  let f := h ∘ π
  let B := f '' {z | z∉L.lattice ∧ fderiv ℝ f z=0}
  have smooth (z : ℂ) (away : h (π z)≠h 0) : ContDiffAt ℝ ∞ f z := by
    have off : z∉L.lattice := fun hit => away (congrArg h ((periodTorusProjection_eq_zero L z).mpr hit))
    exact (tiltedSpatialHeight s).contDiff.contDiffAt.comp z (spatial_torus_lift_regular_at L F off sm imm).1
  have traversal := marked_single_saddle_has_separated_return L H marked ((tiltedSpatialHeight s).continuous.comp cont) smooth saddle
  obtain ⟨u,good,x,obs⟩ := saddle_return_has_nonlifting_height_outside_countable H marked traversal
    (E:=insert (h 0) B) (count.insert _)
  have different : u≠h 0 := fun eq => good (Or.inl eq)
  apply odd
  apply embedded_torus_even_of_nonlifting_tilted_level L F cont emb sm imm H marked s different _ x obs
  intro z hit crit
  have off : z∉L.lattice := fun mem => different (hit.symm.trans (congrArg h ((periodTorusProjection_eq_zero L z).mpr mem)))
  exact good (Or.inr ⟨z,⟨off,crit⟩,hit⟩)

/-- The filled point of any smooth spatial cap carries the genuine
regular parametrization required by the argument with plane sections.
Its chart may be unrelated to the original marking at that point. -/
theorem embedded_cap_even_of_punctured_regularity (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ)
    (sm : ∀ q≠0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q)
    (imm : ∀ q≠0, Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q))
    (cs : ChartedSpace (ℝ×ℝ) (PeriodTorus L)) : let _ := cs
    IsManifold 𝓘(ℝ,ℝ×ℝ) ∞ (PeriodTorus L) → IsClosedEmbedding F →
    ContMDiff 𝓘(ℝ,ℝ×ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F →
    (∀ q, Injective (mfderiv 𝓘(ℝ,ℝ×ℝ) 𝓘(ℝ,Fin 3 → ℝ) F q)) →
    capAmbientSpinQuadratic L F (1,0)*capAmbientSpinQuadratic L F (0,1)=0 := by
  intro inst man closed smooth inject
  obtain ⟨H,_⟩ := marked_torus_circle_product L
  let : Nontrivial Circle := ⟨1,-1,by intro eq; have h := congrArg (fun c : Circle => (c : ℂ).re) eq; norm_num at h⟩
  let : Nontrivial (PeriodTorus L) := H.toEquiv.nontrivial
  obtain ⟨other,ne⟩ := exists_ne (0:PeriodTorus L)
  obtain ⟨e,he,_,src⟩ := punctured_immersion_regular_charts (p:=other) (fun q _ => smooth q)
    (fun q _ => inject q) 0 ne.symm
  let T := Complex.equivRealProdCLM.symm
  let d := e.trans T.toHomeomorph.toOpenPartialHomeomorph
  have regular : RegularImmersionChart F d := regularImmersionChart_reparametrize he T
  have dsrc : (0:PeriodTorus L)∈d.source := ⟨src,mem_univ _⟩
  obtain ⟨dsm,dim⟩ := regular (d 0) (d.map_source dsrc)
  exact embedded_marked_torus_even_from_plane_sections L F closed.continuous closed.injective sm imm d dsrc dsm dim

/-- Ambient parity for a closed torus in any smooth cap atlas compatible
with the original parametrization away from its marked point. -/
theorem embedded_torus_even_on_punctured_marking (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ)
    (cs : ChartedSpace (ℝ×ℝ) (PeriodTorus L)) : let _ := cs
    IsManifold 𝓘(ℝ,ℝ×ℝ) ∞ (PeriodTorus L) → IsClosedEmbedding F →
    ContMDiff 𝓘(ℝ,ℝ×ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F →
    (∀ q, Injective (mfderiv 𝓘(ℝ,ℝ×ℝ) 𝓘(ℝ,Fin 3 → ℝ) F q)) →
    (∀ q≠0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ×ℝ) ∞ (@id (PeriodTorus L)) q ∧
      ContMDiffAt 𝓘(ℝ,ℝ×ℝ) 𝓘(ℝ,ℂ) ∞ (@id (PeriodTorus L)) q) →
    capAmbientSpinQuadratic L F (1,0)*capAmbientSpinQuadratic L F (0,1)=0 := by
  intro inst hm he hF hi markings
  have reg (p : PeriodTorus L) (hp : p≠0) := cap_smooth_map_marked_regular L (cs:=cs) F
    (hF p) (hi p) (markings p hp).1 (markings p hp).2
  exact embedded_cap_even_of_punctured_regularity L F (fun p hp => (reg p hp).1)
    (fun p hp => (reg p hp).2) cs hm he hF hi

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.embedded_marked_torus_even_from_plane_sections
#print axioms TwoAxisHelicoid.embedded_torus_even_on_punctured_marking
