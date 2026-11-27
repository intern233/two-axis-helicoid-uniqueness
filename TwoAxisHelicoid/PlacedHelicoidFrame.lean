import TwoAxisHelicoid.OrthogonalMeanCurvature
import TwoAxisHelicoid.OriginalPositionalHelicoid
import TwoAxisHelicoid.CoordinateOrientationIsometry
import TwoAxisHelicoid.AffineHelicoidAsymptotics

namespace TwoAxisHelicoid
open Complex Matrix Set Topology
open scoped Topology ContDiff Manifold

/-- A Euclidean reference frame on spatial coordinates, allowing an
arbitrary origin and either orientation. -/
structure HelicoidSpatialFrame where
  linear : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ)
  orthogonal : ∀ u v, linear u ⬝ᵥ linear v = u ⬝ᵥ v
  offset : Fin 3 → ℝ

noncomputable def HelicoidSpatialFrame.homeo (F : HelicoidSpatialFrame) :
    (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ) := F.linear.toHomeomorph.trans (Homeomorph.addLeft F.offset)

noncomputable def HelicoidSpatialFrame.isometry (F : HelicoidSpatialFrame) :
    EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3) := by
  apply euclideanOrientationIsometry F.homeo
  intro v w
  have diff : F.homeo v-F.homeo w=F.linear (v-w) := by
    change (F.offset+F.linear v)-(F.offset+F.linear w)=_
    rw [map_sub]
    abel
  have sq (a b : Fin 3 → ℝ) : (∑ j, (a j-b j)^2) = (a-b) ⬝ᵥ (a-b) := by
    simp only [dotProduct,Pi.sub_apply,pow_two]
  rw [sq,sq,diff,F.orthogonal]

noncomputable def HelicoidSpatialFrame.standard : HelicoidSpatialFrame :=
  ⟨ContinuousLinearEquiv.refl ℝ _,fun _ _ => rfl,0⟩

@[simp] theorem HelicoidSpatialFrame.standard_apply (v : Fin 3 → ℝ) :
    standard.homeo v = v := zero_add _

@[simp] theorem HelicoidSpatialFrame.standard_symm_apply (v : Fin 3 → ℝ) :
    standard.homeo.symm v = v := standard.homeo.injective (by simp)

/-- A surface given in its physical coordinates. Minimality, proper
embeddedness and smoothness refer to the physical position. The
asymptotic helicoid and its axis may be placed anywhere in space. -/
structure PlacedPositionalHelicoid where
  carrier : Type
  [topology : TopologicalSpace carrier]
  [separation : T2Space carrier]
  [charts : ChartedSpace ℂ carrier]
  [manifold : IsManifold 𝓘(ℝ,ℂ) ∞ carrier]
  modelTorus : PeriodPair
  topologicalType : carrier ≃ₜ PuncturedPeriodTorus modelTorus
  position : carrier → Fin 3 → ℝ
  closedEmbedding : IsClosedEmbedding position
  smooth : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ position
  immersion : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) position x)
  minimal : ∀ x : carrier, coordinateMeanCurvature (position ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)=0
  frame : HelicoidSpatialFrame
  pitch : ℝ
  pitch_ne : pitch ≠ 0
  approaches : ApproachesSetAtInfinity (range position)
    (frame.homeo.symm '' range (axisRuledHelicoid I pitch 0))
  axialLine : ∀ t : ℝ, frame.homeo.symm ![0,0,t] ∈ range position
  horizontalPoint : Fin 3 → ℝ
  horizontalDirection : ℂ
  unit : ‖horizontalDirection‖=1
  horizontalLine : ∀ t : ℝ,
    frame.homeo.symm (horizontalPoint+t • ![horizontalDirection.re,horizontalDirection.im,0]) ∈ range position

attribute [instance] PlacedPositionalHelicoid.topology PlacedPositionalHelicoid.separation
  PlacedPositionalHelicoid.charts PlacedPositionalHelicoid.manifold

noncomputable def PlacedPositionalHelicoid.image (s : PlacedPositionalHelicoid) : Set (EuclideanSpace ℝ (Fin 3)) :=
  range (coordinateToEuclidean ∘ s.position)

noncomputable def PlacedPositionalHelicoid.normalized (s : PlacedPositionalHelicoid) :
    OriginalPositionallyAsymptoticHelicoid := by
  let F := s.frame
  let f := F.homeo
  let X := f ∘ s.position
  have sm : ContMDiff 𝓘(ℝ,Fin 3 → ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ f :=
    contMDiff_const.add F.linear.toContinuousLinearMap.contMDiff
  have fd (y : Fin 3 → ℝ) : fderiv ℝ f y = F.linear.toContinuousLinearMap := by
    change fderiv ℝ (fun v : Fin 3 → ℝ => F.offset+F.linear v) y=_
    rw [fderiv_const_add]
    exact F.linear.toContinuousLinearMap.hasFDerivAt.fderiv
  have hit {a : Fin 3 → ℝ} (h : f.symm a ∈ range s.position) : a ∈ range X := by
    obtain ⟨x,hx⟩ := h
    exact ⟨x,(congrArg f hx).trans (f.apply_symm_apply _)⟩
  refine {
    carrier := s.carrier
    modelTorus := s.modelTorus
    topologicalType := s.topologicalType
    position := X
    closedEmbedding := f.isClosedEmbedding.comp s.closedEmbedding
    smooth := sm.comp s.smooth
    immersion := ?_
    minimal := ?_
    axes := ⟨s.horizontalDirection,s.unit,s.horizontalPoint,
      fun t => hit (s.horizontalLine t),fun t => hit (s.axialLine t),s.pitch,s.pitch_ne⟩
    approaches := ?_ }
  · intro x
    change Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) (f ∘ s.position) x)
    rw [mfderiv_comp x (sm.mdifferentiable (by simp) _) (s.smooth.mdifferentiable (by simp) _),
      mfderiv_eq_fderiv,fd]
    exact F.linear.injective.comp (s.immersion x)
  · intro x
    exact coordinate_minimal_orthogonal_affine F.linear F.orthogonal F.offset (s.minimal x)
  · have transform := s.approaches.affine_image F.linear.toContinuousLinearMap F.offset
    change ApproachesSetAtInfinity (f '' range s.position) (f '' (f.symm '' _)) at transform
    rwa [← range_comp,image_image,show (fun x => f (f.symm x)) = id from funext f.apply_symm_apply,image_id] at transform

noncomputable def OriginalPositionallyAsymptoticHelicoid.placed (s : OriginalPositionallyAsymptoticHelicoid) :
    PlacedPositionalHelicoid where
  carrier := s.carrier
  modelTorus := s.modelTorus
  topologicalType := s.topologicalType
  position := s.position
  closedEmbedding := s.closedEmbedding
  smooth := s.smooth
  immersion := s.immersion
  minimal := s.minimal
  frame := HelicoidSpatialFrame.standard
  pitch := s.axes.pitch
  pitch_ne := s.axes.pitch_ne
  approaches := by
    have eq : (HelicoidSpatialFrame.standard.homeo.symm : _ → _) = id := funext HelicoidSpatialFrame.standard_symm_apply
    simpa only [eq,image_id] using s.approaches
  axialLine := by simpa only [HelicoidSpatialFrame.standard_symm_apply] using s.axes.vertical
  horizontalPoint := s.axes.horizontalPoint
  horizontalDirection := s.axes.horizontalDirection
  unit := s.axes.unit
  horizontalLine := by simpa only [HelicoidSpatialFrame.standard_symm_apply] using s.axes.horizontal

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.PlacedPositionalHelicoid.normalized
