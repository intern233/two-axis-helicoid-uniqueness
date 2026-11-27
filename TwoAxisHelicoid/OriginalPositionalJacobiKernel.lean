import TwoAxisHelicoid.HarmonicAtlasJacobiFields
import TwoAxisHelicoid.PositionalSimilarityVelocities
import TwoAxisHelicoid.PuncturedTorusRealOrientation

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- Proposition D.1 on the original real smooth surface with only the
manuscript's positional helicoidal asymptote. All seven fields are
smooth in its original atlas. The induced oriented isothermal atlas
identifies their Jacobi equation and its metric potential at every
point. No end theorem or uniformization is a premise. -/
theorem original_positional_seven_jacobi_fields (s : OriginalPositionallyAsymptoticHelicoid) :
    ∃ (N : s.carrier → Fin 3 → ℝ) (J : (Fin 7 → ℝ) →ₗ[ℝ] (s.carrier → ℝ)),
      Continuous N ∧ (∀ x, N x ⬝ᵥ N x=1) ∧ Function.Injective J ∧
      LinearIndependent ℝ (fun i : Fin 7 => J (Pi.basisFun ℝ (Fin 7) i)) ∧
      (∀ p, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ (J p)) ∧
      (∀ p x, J p x=similarityField ![p 0,p 1,p 2] ![p 3,p 4,p 5] (p 6) (s.position x) ⬝ᵥ N x) ∧
      ∃ S : ChartedSpace ℂ s.carrier, let _ := S
        IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧ ∀ e ∈ atlas ℂ s.carrier, HarmonicImmersionChart s.position e ∧
          ∀ z ∈ e.target, N (e.symm z)=harmonicChartNormal (s.position ∘ e.symm) z ∧
            ∀ p, conformalSurfaceJacobi (s.position ∘ e.symm) (J p ∘ e.symm) z=0 := by
  have old := smooth_surface_regular_manifold_chart s.smooth s.immersion
  obtain ⟨V,_,S,hs,hCharts⟩ := punctured_torus_minimal_induced_oriented_atlas s.topologicalType s.smooth s.immersion s.minimal
  obtain ⟨N,form,unit,cont⟩ := @oriented_harmonic_atlas_unit_normal _ _ S s.position V hCharts
  let J := geometricSimilarityNormalMap s.position N
  have eqKer (p : Fin 7 → ℝ) (hp : J p=0) : p=0 := by
    obtain ⟨ha,hb,hd⟩ := positional_similarity_velocity_kernel s S N (fun e he => (hCharts e he).2) form
      ![p 0,p 1,p 2] ![p 3,p 4,p 5] (p 6) (fun x => congrFun hp x)
    funext j
    fin_cases j
    · exact congrFun ha 0
    · exact congrFun ha 1
    · exact congrFun ha 2
    · exact congrFun hb 0
    · exact congrFun hb 1
    · exact congrFun hb 2
    · exact hd
  have inj : Function.Injective J := by
    intro p q eq
    exact sub_eq_zero.mp (eqKer (p-q) (by rw [map_sub,eq,sub_self]))
  have inChart (p : Fin 7 → ℝ) (e : OpenPartialHomeomorph s.carrier ℂ) (he : e ∈ S.atlas) (z : ℂ) (hz : z ∈ e.target) :
      AnalyticAt ℝ (J p ∘ e.symm) z ∧ conformalSurfaceJacobi (s.position ∘ e.symm) (J p ∘ e.symm) z=0 :=
    harmonic_atlas_similarity_jacobi _ _ _ e (hCharts e he).2 (form e he) hz
  refine ⟨N,J,cont,unit,inj,(Pi.basisFun ℝ (Fin 7)).linearIndependent.map' J (LinearMap.ker_eq_bot.mpr inj),?_,
    fun _ _ => rfl,S,hs,fun e he => ⟨(hCharts e he).2,fun z hz => ⟨form e he z hz,fun p => (inChart p e he z hz).2⟩⟩⟩
  intro p
  apply @smooth_of_regular_immersion_chart_germs s.carrier s.topology s.charts s.position old (J p)
  intro x
  let e := S.chartAt x
  have eh : e ∈ S.atlas := S.chart_mem_atlas x
  have ep : x ∈ e.source := S.mem_chart_source x
  exact ⟨e,ep,(hCharts e eh).1.1,(inChart p e eh (e x) (e.map_source ep)).1.contDiffAt⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_positional_seven_jacobi_fields
