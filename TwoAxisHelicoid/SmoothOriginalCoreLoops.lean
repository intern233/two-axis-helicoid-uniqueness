import TwoAxisHelicoid.SurfaceCoreFootRetraction
import TwoAxisHelicoid.SmoothLoopsInOpenSpace
import TwoAxisHelicoid.SmoothImmersionLeftInverse

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped Topology ContDiff Manifold

/-- Every based loop on an open core of the real original surface
has a representative with a globally C¹ Euclidean parametrization,
by smooth approximation inside an actual tube and projection back
to the same open core throughout a based homotopy. -/
theorem original_core_loop_smooth_representative (s : OriginalSmoothHelicoid)
    {V : Set s.carrier} (vo : IsOpen V) {b : V} (γ : Path b b) :
    ∃ (g : ℝ → V) (c : Path b b), Continuous g ∧
      ContDiff ℝ 1 (s.euclideanPosition ∘ Subtype.val ∘ g) ∧
      (∀ t : unitInterval, c t=g t) ∧ γ.Homotopic c := by
  let K := range (fun t : unitInterval => (γ t).1)
  have compact : IsCompact K := isCompact_range (continuous_subtype_val.comp γ.continuous)
  have kb : b.1∈K := ⟨0,congrArg Subtype.val γ.source⟩
  obtain ⟨O,P,op,img,toV,cp,fix,sm⟩ := original_open_core_foot_retraction s vo compact ⟨_,kb⟩
    (by rintro _ ⟨t,rfl⟩; exact (γ t).2)
  let a : O := ⟨s.euclideanPosition b.1,img (mem_image_of_mem _ kb)⟩
  let β : Path a a := {
    toFun := fun t => ⟨s.euclideanPosition (γ t).1,img (mem_image_of_mem _ (mem_range_self t))⟩
    continuous_toFun := (s.euclidean_proper.continuous.comp (continuous_subtype_val.comp γ.continuous)).subtype_mk _
    source' := Subtype.ext (congrArg (fun q : V => s.euclideanPosition q.1) γ.source)
    target' := Subtype.ext (congrArg (fun q : V => s.euclideanPosition q.1) γ.target) }
  let ρ := fun y : O => (⟨P y.1,toV y.2⟩ : V)
  have cρ : Continuous ρ := (continuousOn_iff_continuous_domRestrict.mp cp).subtype_mk _
  have same (t : unitInterval) : ρ (β t)=γ t := Subtype.ext (fix _ (mem_range_self t))
  obtain ⟨h,c,ch,smo,cval,⟨H⟩⟩ := smooth_based_loop_in_open_space op β
  let g := ρ ∘ h
  let d : Path b b := {
    toFun := fun t => ρ (c t)
    continuous_toFun := cρ.comp c.continuous
    source' := (congrArg ρ (c.source.trans β.source.symm)).trans ((same 0).trans γ.source)
    target' := (congrArg ρ (c.target.trans β.target.symm)).trans ((same 1).trans γ.target) }
  have sg : ContDiff ℝ 1 ((s.euclideanPosition ∘ P) ∘ Subtype.val ∘ h) :=
    contDiff_iff_contDiffAt.mpr (fun t => (sm _ (h t).2).comp t smo.contDiffAt)
  refine ⟨g,d,cρ.comp ch,sg,
    fun t => congrArg ρ (cval t),⟨{
      toFun := fun u => ρ (H u)
      continuous_toFun := cρ.comp H.continuous
      map_zero_left := fun t => (congrArg ρ (H.map_zero_left t)).trans (same t)
      map_one_left := fun t => congrArg ρ (H.map_one_left t)
      prop' := fun t u hu => (congrArg ρ (H.eq_fst t hu)).trans (same u) }⟩⟩

/-- A curve whose spatial position is C¹ has C¹ coordinates in every
smooth regular chart of the surface that contains its base point. -/
theorem regular_immersion_curve_coordinate_C1 {M : Type*} [TopologicalSpace M] {X : M → Fin 3 → ℝ}
    {p : ℝ → M} {t : ℝ} (cp : ContinuousAt p t)
    (sp : ContDiffAt ℝ 1 (coordinateToEuclidean ∘ X ∘ p) t)
    (a : OpenPartialHomeomorph M ℂ) (reg : RegularImmersionChart X a) (inside : p t∈a.source) :
    ContDiffAt ℝ 1 (a ∘ p) t := by
  let z := a (p t)
  let Y := X ∘ a.symm
  obtain ⟨sy,inj⟩ := reg z (a.map_source inside)
  obtain ⟨g,U,uo,zu,sg,left⟩ := smooth_local_left_inverse sy inj
  have cad : ContinuousAt (a ∘ p) t := (a.continuousAt inside).comp cp
  have germ : a ∘ p=ᶠ[𝓝 t] g ∘ X ∘ p := by
    filter_upwards [cad.eventually (uo.mem_nhds zu),cp.eventually (a.open_source.mem_nhds inside)] with w uw pw
    have h := left _ uw
    simpa only [Y,Function.comp_apply,a.left_inv pw] using h.symm
  have sx : ContDiffAt ℝ 1 (X ∘ p) t :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff.contDiffAt.comp t sp
  have atp : Y z=X (p t) := congrArg X (a.left_inv inside)
  have sg' : ContDiffAt ℝ 1 g (X (p t)) := atp ▸ sg.of_le (by simp)
  exact (sg'.comp t sx).congr_of_eventuallyEq germ

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_core_loop_smooth_representative
#print axioms TwoAxisHelicoid.regular_immersion_curve_coordinate_C1
