import TwoAxisHelicoid.PublishedOriginalSpinBranch
import TwoAxisHelicoid.RigidAmbientSpin
import TwoAxisHelicoid.HoffmanWhiteBasicBranch
import TwoAxisHelicoid.MarkedHelicoidIntersectionTheorem

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ContDiff Manifold

/-- On an actual TwoAxisHelicoid surface the spin parity of the chosen cap in
both ambient frames follows from the comparison theorem and the
computed spinor multipliers on the original marked loops. -/
theorem original_pointed_spin_cap_of_torus_uniformization (s : OriginalPositionallyAsymptoticHelicoid)
    (A : PublishedConformalPoleModel s.position) (uniform : CompactGenusOneUniformization.{0} s.modelTorus) :
    HasPointedOriginalSpinBranchCap s := by
  obtain ⟨S,hm,hchart,L,f,X,hfhol,hfihol,hf,hclose,him,hhi,hheight,hgauss⟩ :=
    original_smooth_surface_published_poles_to_torus s.toOriginalSmoothHelicoid
      uniform A s.approaches
  let _ := S
  let _ := hm
  let c := s.axes.horizontalDirection
  let C : Fin 3 → ℝ := ![0,0,s.axes.horizontalPoint 2]
  let R := lineAxisCoordinates c s.axes.unit C
  let Y := R ∘ X
  obtain ⟨hcross,hY,hhor,hver,hreg,h₁,h₂⟩ := horizontal_line_axes_placement L X hclose c s.axes.unit
    s.axes.horizontalPoint (him.symm ▸ s.axes.horizontal) (him.symm ▸ s.axes.vertical)
    s.axes.pitch_ne (him.symm ▸ s.approaches) hhi
  obtain ⟨b,t,hb,ht,hp,hZ⟩ := straight_axes_to_two_axis_harmonic_immersion L Y hY hhor hver hreg
  let M := rhombicPeriodPair t ht
  obtain ⟨_,e,_,_,_,hehol,heihol,_,he⟩ := scaled_harmonic_biholomorphic_correspondence L M b hb hp Y hZ
  have hi : Function.Injective (harmonicTorusImmersion hZ) := by
    intro q r h
    obtain ⟨u,rfl⟩ := e.surjective q
    obtain ⟨v,rfl⟩ := e.surjective r
    exact congrArg e (hY.injective ((he u).symm.trans (h.trans (he v))))
  obtain ⟨hh,hg⟩ := marked_torus_scaled_end_orders L M (Y ∘ periodTorusProjection L) b⁻¹ (inv_ne_zero hb)
    (fun z hz => ⟨(hreg z hz).1,(hreg z hz).2.1⟩) (h₁.trans hheight) (h₂.trans hgauss)
  obtain ⟨a,d,m,B,ha,hd,hT,ha',hB,hV,hhV,hgV⟩ := harmonic_meromorphic_oriented_integer_data ht hZ hh hg
  have hVmap := harmonicTorusImmersion_space_map hZ B hV
  have hVi : Function.Injective (harmonicTorusImmersion hV) := by
    rw [hVmap]
    exact B.injective.comp hi
  let J := R.trans B
  let E := f.trans e
  have hpt (x : s.carrier) : harmonicTorusImmersion hV (E x) = J (s.position x) := by
    rw [hVmap]
    change B (harmonicTorusImmersion hZ (e (f x))) = B (R (s.position x))
    exact congrArg B ((he (f x)).trans (congrArg R (hf x)))
  have hisom (v w : Fin 3 → ℝ) : (∑ j, (J v j-J w j)^2) = ∑ j, (v j-w j)^2 :=
    (hB (R v) (R w)).trans (lineAxisCoordinates_dist_sq c s.axes.unit C v w)
  obtain ⟨F,cs,U,hM,hemb,hsm,hFi,hU,h0,hcore,hfix,_hcompat,hparity⟩ :=
    actual_embedded_integer_branch_cap_arf ht ha hd m hV hVi hhV hgV
  have hmone : m=1 := integer_branch_one_of_intersection_principle marked_rhombic_helicoid_intersection
    ht ha hd m hV hVi hhV hgV
  have hodd : Odd m := hmone ▸ (by decide : Odd (1:ℤ))
  obtain ⟨hrE,hrS,hrI,hrQ⟩ := rigid_coordinates_cap_spin_transfer M F cs J hisom hM hemb hsm hFi
  have hRC : R C = 0 := by change verticalRotation _ (C-C) = 0; rw [sub_self,map_zero]
  have horigin := (he (e.symm (rhombicAxisPoint ht))).symm
  rw [e.apply_symm_apply,harmonicTorus_axis_point ht hZ] at horigin
  have hmarked : s.position (E.symm (rhombicAxisPoint ht)) = C := by
    change s.position (f.symm (e.symm _)) = C
    rw [← hf,f.apply_symm_apply]
    exact R.injective (horigin.trans hRC.symm)
  refine ⟨S,hm,fun l hl => (hchart l hl).1,t,ht,a,d,m,E,J,_,hV,hcross,hmarked,
    hehol.comp hfhol,hfihol.comp heihol,
    hisom,hpt,hVi,ha,hd,hT,ha',hhV,hgV,hodd,hmone,F,cs,U,hM,hemb,hsm,hFi,hU,h0,hcore,
    hrE,hrS,hrI,?_,?_⟩
  · intro x hx
    exact (congrArg J.symm ((hfix (E x) hx).trans (hpt x))).trans (J.symm_apply_apply _)
  · intro v w hvw
    have vpar := hparity v w hvw
    have zero : capAmbientSpinQuadratic M F v * capAmbientSpinQuadratic M F w=0 := by
      simpa only [hmone,show ¬Even (1:ℤ) by decide,ite_false] using vpar
    exact ⟨vpar,zero,hrQ.symm ▸ zero⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_pointed_spin_cap_of_torus_uniformization
