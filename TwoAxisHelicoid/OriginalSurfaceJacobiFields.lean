import TwoAxisHelicoid.SevenTorusJacobiFields
import TwoAxisHelicoid.OriginalHelicoidRepresentative
import TwoAxisHelicoid.HolomorphicCurveRealSmooth
import TwoAxisHelicoid.HarmonicChartJacobiOperator

namespace TwoAxisHelicoid
open Complex Matrix Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- The independent fields on the marked model pull back to actual smooth
normal components of the three translations, three rotations, and scaling
on the original immersed surface. The equation is checked in the covering
charts of a biholomorphic marking of the whole surface. -/
theorem marked_jacobi_fields_on_original {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (L : PeriodPair) (f : M ≃ₜ PuncturedPeriodTorus L) (hf : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f)
    (X : M → Fin 3 → ℝ) (Y : PeriodTorus L → Fin 3 → ℝ) (hXY : ∀ x, Y (f x).1 = X x)
    (hc : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => Y q.1))
    (hY : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun u => Y (periodTorusProjection L u) j) z) ∧
      ConformalCoordinateDerivatives (Y ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (Y ∘ periodTorusProjection L) z)) :
    ∃ (N : M → Fin 3 → ℝ) (J : (Fin 7 → ℝ) →ₗ[ℝ] (M → ℝ)),
      (∀ (z : ℂ) (hz : z ∉ L.lattice), N (f.symm (puncturedPlaneProjection L ⟨z,hz⟩)) =
        harmonicChartNormal (Y ∘ periodTorusProjection L) z) ∧
      Function.Injective J ∧ LinearIndependent ℝ (fun i : Fin 7 => J (Pi.basisFun ℝ (Fin 7) i)) ∧
      ∀ p, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ (J p) ∧ IsSmoothMarkedJacobiField L Y ((J p) ∘ f.symm) ∧
        ∀ x, J p x = similarityField ![p 0,p 1,p 2] ![p 3,p 4,p 5] (p 6) (X x) ⬝ᵥ N x := by
  let n := harmonicChartNormal (Y ∘ periodTorusProjection L)
  let N := fun x : M => periodTorusLift L n (marked_normal_periodic L Y) (f x).1
  let pull : (PuncturedPeriodTorus L → ℝ) →ₗ[ℝ] (M → ℝ) := {
    toFun g := g ∘ f
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  let J := pull.comp (sevenSimilarityNormalMap L Y)
  obtain ⟨hinj,_,heq⟩ := seven_geometric_jacobi_fields L Y hc hY
  have hi : Function.Injective J := by
    intro p q h
    apply hinj
    funext y
    obtain ⟨x,rfl⟩ := f.surjective y
    exact congrFun h x
  have hn (z : ℂ) (hz : z ∉ L.lattice) : N (f.symm (puncturedPlaneProjection L ⟨z,hz⟩)) = n z := by
    simp only [N,f.apply_symm_apply]
    rfl
  refine ⟨N,J,hn,hi,(Pi.basisFun ℝ (Fin 7)).linearIndependent.map' J (LinearMap.ker_eq_bot.mpr hi),?_⟩
  intro p
  have hg : J p ∘ f.symm = sevenSimilarityNormalMap L Y p := by
    funext y
    change (sevenSimilarityNormalMap L Y p) (f (f.symm y)) = _
    rw [f.apply_symm_apply]
  refine ⟨(heq p).1.comp (holomorphic_curve_map_real_smooth hf),hg ▸ heq p,?_⟩
  intro x
  rw [← hXY x]
  generalize hq : f x = q
  obtain ⟨z,rfl⟩ := puncturedPlaneProjection_surjective L q
  have hx : x = f.symm (puncturedPlaneProjection L z) := (f.symm_apply_apply x).symm.trans (congrArg f.symm hq)
  rw [hx,hn z.1 z.2]
  change (sevenSimilarityNormalMap L Y p) (f (f.symm _)) = _
  rw [f.apply_symm_apply]
  rfl

/-- An original representative has the seven independent geometric Jacobi
fields once the named exterior and genus-one uniformization inputs apply.
The numerical root and the intersection theorem are unnecessary here. -/
theorem original_representative_seven_jacobi_fields (surface : OriginalHelicoidRepresentative)
    (bbc : OriginalHelicoidExteriorPrinciple) (uniform : CompactGenusOneUniformization.{0} surface.modelTorus) :
    ∃ S : ChartedSpace ℂ surface.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω surface.carrier ∧ (∀ d ∈ atlas ℂ surface.carrier, InducedIsothermalChart surface.position d) ∧
      ∃ (L : PeriodPair) (f : surface.carrier ≃ₜ PuncturedPeriodTorus L) (Y : PeriodTorus L → Fin 3 → ℝ)
        (N : surface.carrier → Fin 3 → ℝ) (J : (Fin 7 → ℝ) →ₗ[ℝ] (surface.carrier → ℝ)),
        ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm ∧ (∀ x, Y (f x).1 = surface.position x) ∧
        (∀ (z : ℂ) (hz : z ∉ L.lattice), N (f.symm (puncturedPlaneProjection L ⟨z,hz⟩)) =
          harmonicChartNormal (Y ∘ periodTorusProjection L) z) ∧
        Function.Injective J ∧ LinearIndependent ℝ (fun i : Fin 7 => J (Pi.basisFun ℝ (Fin 7) i)) ∧
        ∀ p, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ (J p) ∧ IsSmoothMarkedJacobiField L Y ((J p) ∘ f.symm) ∧
          ∀ x, J p x = similarityField ![p 0,p 1,p 2] ![p 3,p 4,p 5] (p 6) (surface.position x) ⬝ᵥ N x := by
  have transfer {e : OpenPartialHomeomorph surface.carrier ℂ} (he : InducedIsothermalChart surface.position e) :
      HarmonicImmersionChart surface.position e :=
    real_minimal_isothermal_chart_harmonic surface.smooth surface.immersion surface.minimal he
  obtain ⟨S,hs,hchart,⟨A⟩⟩ := bbc surface
  refine ⟨S,hs,hchart,?_⟩
  let := S
  let := hs
  obtain ⟨L,f,Y,hf,hfi,hpos,hc,_,hY,_,_⟩ := original_surface_from_arbitrary_exterior_frame surface.topologicalType
    uniform surface.position surface.closedEmbedding (fun e he => transfer (hchart e he)) A surface.axes.pitch_ne surface.positional.1
  obtain ⟨N,J,hn,hi,hl,hj⟩ := marked_jacobi_fields_on_original L f hf surface.position Y hpos hc hY
  exact ⟨L,f,Y,N,J,hf,hfi,hpos,hn,hi,hl,hj⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_representative_seven_jacobi_fields
