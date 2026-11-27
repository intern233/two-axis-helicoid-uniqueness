import TwoAxisHelicoid.RegularGraphCoordinates
import Mathlib.Analysis.Calculus.Gradient.Basic

namespace TwoAxisHelicoid
open Complex Set Topology Filter InnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff

/-- At a critical point of a height with nonzero vertical coefficient,
the actual horizontal projection of the tangent plane is invertible. -/
theorem horizontal_projection_injective_at_height_contact {D : ℂ →L[ℝ] (Fin 3 → ℝ)}
    (immersed : Function.Injective D) (s : ℂ)
    (critical : ∀ v, D v 2=⟪s,spatialGraphProjection 0 1 (D v)⟫_ℝ) :
    Function.Injective ((spatialGraphProjection 0 1).comp D) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  apply immersed
  rw [map_zero]
  ext i
  fin_cases i
  · exact congrArg Complex.re hv
  · exact congrArg Complex.im hv
  · change D v 2=0
    rw [critical]
    change ⟪s,((spatialGraphProjection 0 1).comp D) v⟫_ℝ=0
    rw [hv,inner_zero_right]

/-- On every smooth patch where the horizontal projection is
nonsingular, the surface is a single graph in the actual horizontal
coordinates. Both the projected parameter and its inverse have the
indicated derivatives throughout smaller open neighborhoods. -/
theorem horizontal_graph_height_chart {F : ℂ → Fin 3 → ℝ} {z : ℂ}
    (smooth : ContDiffAt ℝ 3 F z)
    (inj : Function.Injective ((spatialGraphProjection 0 1).comp (fderiv ℝ F z))) :
    ∃ (e : OpenPartialHomeomorph ℂ ℂ) (f : ℂ → ℝ) (U : Set ℂ),
      IsOpen U ∧ z∈U ∧ U⊆e.source ∧ (∀ w, e w=spatialGraphProjection 0 1 (F w)) ∧
      (∀ w∈U, ContDiffAt ℝ 3 e w ∧
        ContDiffAt ℝ 3 e.symm (e w) ∧ ContDiffAt ℝ 3 f (e w)) ∧
      ∀ w∈U, F w 2=f (e w) := by
  let P := spatialGraphProjection 0 1
  let D := P.comp (fderiv ℝ F z)
  let p := P ∘ F
  have cp : ContDiffAt ℝ 3 p z := P.contDiff.contDiffAt.comp z smooth
  have deriv : HasFDerivAt p D z := P.hasFDerivAt.comp z (smooth.differentiableAt (by norm_num)).hasFDerivAt
  let L := (LinearEquiv.ofBijective D.toLinearMap ⟨inj,LinearMap.injective_iff_surjective.mp inj⟩).toContinuousLinearEquiv
  have deriv' : HasFDerivAt p (L : ℂ →L[ℝ] ℂ) z := deriv
  let e := cp.toOpenPartialHomeomorph p deriv' (by norm_num)
  have ze : z∈e.source := cp.mem_toOpenPartialHomeomorph_source deriv' (by norm_num)
  have back : ContDiffAt ℝ 3 e.symm (e z) := cp.to_localInverse deriv' (by norm_num)
  let f := fun w => F (e.symm w) 2
  have cf : ContDiffAt ℝ 3 f (e z) :=
    (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin 3 => ℝ) 2).contDiff.contDiffAt.comp _ (((e.left_inv ze).symm ▸ smooth).comp _ back)
  have good : ∀ᶠ w in 𝓝 z, w∈e.source ∧ ContDiffAt ℝ 3 e w ∧
      ContDiffAt ℝ 3 e.symm (e w) ∧ ContDiffAt ℝ 3 f (e w) := by
    filter_upwards [e.open_source.mem_nhds ze,cp.eventually (by norm_num),
      (e.continuousAt ze).eventually (back.eventually (by norm_num)),
      (e.continuousAt ze).eventually (cf.eventually (by norm_num))] with w ew cw bw fw
    exact ⟨ew,cw,bw,fw⟩
  obtain ⟨U,sub,op,hz⟩ := mem_nhds_iff.mp good
  exact ⟨e,f,U,op,hz,fun _ h => (sub h).1,fun _ => rfl,fun _ h => (sub h).2,fun w h =>
    congrArg (fun a => F a 2) (e.left_inv (sub h).1).symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.horizontal_projection_injective_at_height_contact
#print axioms TwoAxisHelicoid.horizontal_graph_height_chart
