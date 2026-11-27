import TwoAxisHelicoid.HelicoidCanonicalSpinExtension
import TwoAxisHelicoid.ExactHelicoidMarkedEnd
import TwoAxisHelicoid.HelicoidalSolidTorusParity

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ContDiff Manifold
universe u

/-- Proposition 4.4 using the smooth solid side of an embedded torus:
the unique genuine compact spin extension is even for a normal graph
with height tending to zero. This proof of parity goes through a
compression disk on the chosen solid side. -/
theorem height_decay_helicoidal_torus_even_spin_of_solid_side
    (solid : EmbeddedTorusBoundsSmoothSolid) (L : PeriodPair) {X : PeriodTorus L → Fin 3 → ℝ}
    (A : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates) (hA : ContDiff ℝ ∞ A) (hAi : ContDiff ℝ ∞ A.symm)
    (hEnd : HasHelicoidHeightEnd (fun q : PuncturedPeriodTorus L => A (X q.1)))
    (hp : IsProperMap (fun q : PuncturedPeriodTorus L => X q.1))
    (inj : Function.Injective (fun q : PuncturedPeriodTorus L => X q.1))
    (sm : ∀ p ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X p)
    (di : ∀ p ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X p)) :
    HasUniqueGenuineCompactSpinExtension.{u} L X sm di (fun F => ∀ v w, torusIntersectionModTwo v w=1 →
      capAmbientSpinQuadratic L F v * capAmbientSpinQuadratic L F w=0) ∧
      ∀ v w, torusIntersectionModTwo v w=1 → capAmbientSpinQuadratic L X v * capAmbientSpinQuadratic L X w=0 := by
  obtain ⟨B,b,bi,graph⟩ := helicoidal_height_end_admits_C1_chart
    (X := fun q : PuncturedPeriodTorus L => X q.1) A hA hAi hEnd hp
  refine ⟨?_,helicoidal_torus_marked_arf_zero_of_solid_torus solid L B b bi graph hp inj sm di⟩
  obtain ⟨F,cs,hF,diF,K,ret,U,n,σ,β,kc,uo,ku,eq,man,emb,smooth,regular,unit,normal,point,cover,
    proj,base,core,rot,unique,_⟩ := helicoidal_surface_unique_genuine_spin_extension.{u} L B b bi graph hp inj sm di
  let _ := cs
  let _ := man
  have arf := compactified_solid_torus_forces_even_arf L emb.isEmbedding hF diF (solid L F cs man emb smooth regular)
  refine ⟨F,cs,hF,diF,K,ret,U,n,σ,β,kc,uo,ku,eq,man,emb,smooth,regular,unit,normal,point,cover,
    proj,base,core,rot,unique,?_⟩
  intro v w vw
  rw [cap_ambient_arf_basis L F v w vw]
  exact arf

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.height_decay_helicoidal_torus_even_spin_of_solid_side
