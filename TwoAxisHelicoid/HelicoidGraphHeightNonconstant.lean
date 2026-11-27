import TwoAxisHelicoid.CertifiedC1HelicoidEnd
import TwoAxisHelicoid.HarmonicTorusRigidityData
import TwoAxisHelicoid.PeriodicHeightRigidity

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

/-- Along the zero-radius ruling of a normal graph the vertical component
of the normal vector vanishes. Thus every sufficiently large positive
or negative height occurs on the actual end, even for a bounded graph
with no decay estimate. -/
theorem HasHelicoidC1End.contains_outer_heights {M : Type*} [TopologicalSpace M]
    {Y : M → HelicoidTubeCoordinates} (h : HasHelicoidC1End Y) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, R < |t| → ∃ q, (Y q).2 = t := by
  obtain ⟨C,_,R,hR,_,E,_,u,_,he,_⟩ := h
  refine ⟨R,hR,fun t ht => ?_⟩
  let b : exteriorPlaneBase R := ⟨(0,t),by
    change R < ‖((0:ℝ),t)‖
    simpa [Prod.norm_def,Real.norm_eq_abs] using ht⟩
  refine ⟨(E.symm b).1,?_⟩
  exact (congrArg Prod.snd (he b).2).trans (by simp [b,helicoidTubeMap,helicoidNormalMap,helicoidAngle])

/-- Distinct actual heights force a nonzero height differential at an
ordinary point of an arbitrary marked punctured torus. -/
theorem marked_height_form_nonzero_of_unequal_heights (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z)
    {q r : PuncturedPeriodTorus L} (hn : X q 2 ≠ X r 2) :
    ∃ z ∉ L.lattice, torusImmersionForms L X z 2 ≠ 0 := by
  by_contra! hh
  let P := fun w => torusFilledPosition L X (periodTorusProjection L w) 2
  obtain ⟨_,_,hD⟩ := torusImmersionForms_regular L X (fun z hz => (hX z hz).1) (fun z hz => (hX z hz).2)
  have hd (z : ℂ) (hz : z ∉ L.lattice) : HasFDerivAt P (0 : ℂ →L[ℝ] ℝ) z := by
    have h : HasFDerivAt P (realCoefficientDerivative (torusImmersionForms L X z 2)) z :=
      (ContinuousLinearMap.proj 2 : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z (hD z hz)
    rw [hh z hz] at h
    convert h using 1
    ext v
    simp
  obtain ⟨c,hc⟩ := L.isClosed_lattice.isOpen_compl.exists_eq_add_of_fderiv_eq
    (marked_torus_lattice_complement_connected L).isPreconnected
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (g := fun _ : ℂ => (0:ℝ)) (fun _ _ => (differentiableAt_const (0:ℝ)).differentiableWithinAt)
    (fun z hz => by rw [(hd z hz).fderiv,fderiv_const_apply])
  have hconst (s : PuncturedPeriodTorus L) : X s 2 = c := by
    obtain ⟨z,rfl⟩ := puncturedPlaneProjection_surjective L s
    exact (congrFun (torusFilledPosition_eq L X _) 2).symm.trans (by simpa only [zero_add] using! hc z.2)
  exact hn ((hconst q).trans (hconst r).symm)

/-- The actual normalized helicoidal end gives the height point needed
for analytic continuation, with no meromorphic end-order hypothesis. -/
theorem marked_helicoid_graph_height_form_nonzero (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z)
    {k : ℝ} {u : ℂ} {b : Fin 3 → ℝ}
    (hend : HasHelicoidC1End (fun q => coordinateToTube (k • verticalRotation u (X q)+b))) :
    ∃ z ∉ L.lattice, torusImmersionForms L X z 2 ≠ 0 := by
  obtain ⟨R,hR,h⟩ := hend.contains_outer_heights
  obtain ⟨p,hp⟩ := h (R+1) (by rw [abs_of_pos (by linarith)]; linarith)
  obtain ⟨q,hq⟩ := h (R+2) (by rw [abs_of_pos (by linarith)]; linarith)
  apply marked_height_form_nonzero_of_unequal_heights L X hX (q := p) (r := q)
  intro e
  change k*X p 2+b 2 = R+1 at hp
  change k*X q 2+b 2 = R+2 at hq
  rw [e] at hp
  linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_helicoid_graph_height_form_nonzero
