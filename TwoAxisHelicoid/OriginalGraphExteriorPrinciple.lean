import TwoAxisHelicoid.OriginalGraphExteriorNormalization
import TwoAxisHelicoid.FiniteTopologyCurvatureClassification

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- From a single-layer end of the original surface, construct the full
normalized exterior input in the induced isothermal atlas. Its rigid
frame may be chosen to be the original frame of its two lines. -/
theorem c1_graph_exterior_principle_of_uniformization (uni : SimplyConnectedNoncompactUniformization.{0}) :
    OriginalHelicoidExteriorPrinciple := by
  intro s
  obtain ⟨N,_,S,man,charts⟩ := punctured_torus_minimal_induced_oriented_atlas s.topologicalType s.smooth s.immersion s.minimal
  let _ := S
  let _ := man
  obtain ⟨A,_⟩ := one_handle_original_frame_exterior s.topologicalType uni s.position s.closedEmbedding
    (fun e he => (charts e he).2) s.axes.pitch_ne s.graphEnd
  have eq : (fun x => (0:Fin 3 → ℝ)+(LinearEquiv.refl ℝ (Fin 3 → ℝ)) (s.position x))=s.position := by simp
  refine ⟨S,man,fun e he => ⟨(charts e he).1.1,fun z hz => ((charts e he).2 z hz).2.1⟩,⟨⟨LinearEquiv.refl ℝ _,fun _ _ => rfl,0,eq.symm ▸ A,s.axes.pitch,s.axes.pitch_ne,?_⟩⟩⟩
  rw [eq]
  exact s.positional.2

/-- For the weaker positional hypothesis the curvature bound of
Meeks–Pérez gives the same analytic exterior, including a Gauss
correction whose value at the compactification point is zero. -/
theorem positional_original_normalized_exterior (s : OriginalPositionallyAsymptoticHelicoid)
    (mp : FiniteTopologyGaussianCurvatureBound) (uni : SimplyConnectedNoncompactUniformization.{0}) :
    ∃ S : ChartedSpace ℂ s.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧ (∀ e∈atlas ℂ s.carrier, HarmonicImmersionChart s.position e) ∧
      ∃ A : GeometricExteriorCoordinate s.position, A.correction 0=0 := by
  obtain ⟨C,hC,bound⟩ := mp s.toOriginalSmoothHelicoid
  exact original_graph_normalized_exterior (s.graphRepresentative
    (original_physical_shape_bound_of_gaussian s.toOriginalSmoothHelicoid hC bound)) uni

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.c1_graph_exterior_principle_of_uniformization
#print axioms TwoAxisHelicoid.positional_original_normalized_exterior
