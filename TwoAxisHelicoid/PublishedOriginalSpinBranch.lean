import TwoAxisHelicoid.RawPublishedConformalPoleReduction
import TwoAxisHelicoid.ClassicalRiemannUniformizationSpecialization
import TwoAxisHelicoid.GeometricHelicoidIntersection
import TwoAxisHelicoid.OriginalPositionalHelicoid
import TwoAxisHelicoid.HorizontalLinePlacement
import TwoAxisHelicoid.SchwarzNormalizedImmersion
import TwoAxisHelicoid.ConformalTorusScaling
import TwoAxisHelicoid.TorusEndScalingOrders
import TwoAxisHelicoid.OriginalSpinCapRigidCoordinates
import TwoAxisHelicoid.ManuscriptSpinBasicBranch
import TwoAxisHelicoid.HarmonicAxisIntersectionPoint

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ContDiff Manifold

/-- The differential, embedding and spin conclusions on one fixed marking. -/
def OriginalMarkedSpinCapData (s : OriginalPositionallyAsymptoticHelicoid) [ChartedSpace ℂ s.carrier]
    {t : ℝ} {ht : 0 < t} (a c : ℝ) (m : ℤ)
    (e : s.carrier ≃ₜ PuncturedPeriodTorus (rhombicPeriodPair t ht))
    (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) (Z : ℂ → Fin 3 → ℝ)
    (hZ : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) Z) : Prop :=
  let L := rhombicPeriodPair t ht
  ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e.symm ∧
      (∀ v w : Fin 3 → ℝ, (∑ j, (R v j-R w j)^2) = ∑ j, (v j-w j)^2) ∧
      (∀ x, harmonicTorusImmersion hZ (e x) = R (s.position x)) ∧
      Function.Injective (harmonicTorusImmersion hZ) ∧
      a ∈ Ioo (0:ℝ) 1 ∧ c ≠ 0 ∧ t < ellipticVerticalUpper ∧ a = verticalA t ∧
      (∀ z ∉ L.lattice, puncturedImmersionCoefficient L Z z 2 = coordinateData t a c ht z 2) ∧
      (∀ z ∉ gaussLogPoleSet L a, nullGauss (puncturedImmersionCoefficient L Z z) = thetaGauss t a m z) ∧
      Odd m ∧ m = 1 ∧
      ∃ (F : PeriodTorus L → Fin 3 → ℝ) (cs : ChartedSpace (ℝ × ℝ) (PeriodTorus L))
        (U : Set (PeriodTorus L)), let _ := cs
        IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ (PeriodTorus L) ∧ IsClosedEmbedding F ∧
        ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F ∧
        (∀ q, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) F q)) ∧
        IsOpen U ∧ 0 ∉ U ∧ Subtype.val '' puncturedGeneratorCore L ⊆ U ∧
        IsClosedEmbedding (R.symm ∘ F) ∧
        ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ (R.symm ∘ F) ∧
        (∀ p, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) (R.symm ∘ F) p)) ∧
        (∀ x, (e x).1 ∈ U → R.symm (F (e x).1) = s.position x) ∧
        ∀ v w, torusIntersectionModTwo v w = 1 →
          capAmbientSpinQuadratic L F v * capAmbientSpinQuadratic L F w = (if Even m then 1 else 0) ∧
          capAmbientSpinQuadratic L F v * capAmbientSpinQuadratic L F w = 0 ∧
          capAmbientSpinQuadratic L (R.symm ∘ F) v * capAmbientSpinQuadratic L (R.symm ∘ F) w = 0

/-- The data and the cap retain their pointwise correspondence with the
original real surface. The cap in original spatial coordinates agrees
with that position on a full neighborhood of the two marked generators. -/
def HasOriginalSpinBranchCap (s : OriginalPositionallyAsymptoticHelicoid) : Prop :=
  ∃ S : ChartedSpace ℂ s.carrier, let _ := S
    IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧
    (∀ e ∈ atlas ℂ s.carrier, InducedIsothermalChart s.position e) ∧
    ∃ (t : ℝ) (ht : 0 < t) (a c : ℝ) (m : ℤ), let L := rhombicPeriodPair t ht
    ∃ (e : s.carrier ≃ₜ PuncturedPeriodTorus L) (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ))
      (Z : ℂ → Fin 3 → ℝ) (hZ : TwoAxisHarmonicConformalImmersion L Z),
      OriginalMarkedSpinCapData s a c m e R Z hZ

/-- The same spin cap with the location of the two-axis crossing in its conformal marking. -/
def HasPointedOriginalSpinBranchCap (s : OriginalPositionallyAsymptoticHelicoid) : Prop :=
  ∃ S : ChartedSpace ℂ s.carrier, let _ := S
    IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧
    (∀ e ∈ atlas ℂ s.carrier, InducedIsothermalChart s.position e) ∧
    ∃ (t : ℝ) (ht : 0 < t) (a c : ℝ) (m : ℤ), let L := rhombicPeriodPair t ht
    ∃ (e : s.carrier ≃ₜ PuncturedPeriodTorus L) (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ))
      (Z : ℂ → Fin 3 → ℝ) (hZ : TwoAxisHarmonicConformalImmersion L Z),
      (∃ r : ℝ, s.axes.horizontalPoint+r • ![s.axes.horizontalDirection.re,s.axes.horizontalDirection.im,0] =
        ![0,0,s.axes.horizontalPoint 2]) ∧
      s.position (e.symm (rhombicAxisPoint ht)) = ![0,0,s.axes.horizontalPoint 2] ∧
      OriginalMarkedSpinCapData s a c m e R Z hZ

/-- Corollary 4.5 via the spin of an actual cap of the original positional
candidate. All hypotheses of the four cited geometric results, up to
their separately displayed statements, are derived on that surface. -/
theorem published_original_pointed_spin_cap (s : OriginalPositionallyAsymptoticHelicoid)
    (A : PublishedConformalPoleModel s.position) (poincare : SimplyConnectedNoncompactUniformization.{0})
    (hw : GeometricTwoAxisIntersectionTheorem) (pinkall : PinkallEmbeddedTorusRegularHomotopy) :
    HasPointedOriginalSpinBranchCap s := by
  obtain ⟨S,hm,hchart,L,f,X,hfhol,hfihol,hf,hclose,him,hhi,hheight,hgauss⟩ :=
    original_smooth_surface_published_poles_to_torus s.toOriginalSmoothHelicoid
      (compact_genus_one_uniformization_of_classical poincare s.modelTorus) A s.approaches
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
  obtain ⟨F,cs,U,hM,hemb,hsm,hFi,hU,h0,hcore,hfix,hcompat,hparity⟩ :=
    actual_embedded_integer_branch_cap_arf ht ha hd m hV hVi hhV hgV
  have harf := pinkall_even_on_punctured_marking pinkall M F cs hM hemb hsm hFi hcompat
  have hodd : Odd m := by
    rw [← Int.not_even_iff_odd]
    intro h
    have hq := hparity (1,0) (0,1) (by decide)
    simp only [h,ite_true] at hq
    exact zero_ne_one (harf.symm.trans hq)
  have hmone : m = 1 := by
    rcases integer_branch_zero_or_one_of_intersection_principle (rhombic_intersection_of_geometric_theorem hw)
      ht ha hd m hV hVi hhV hgV with h | h
    · subst m
      simp at hodd
    · exact h
  obtain ⟨hrE,hrS,hrI,hrArf⟩ := rigid_coordinates_original_even_cap pinkall M F cs J hisom hM hemb hsm hFi hcompat
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
    exact ⟨hparity v w hvw,(cap_ambient_arf_basis M F v w hvw).trans harf,hrArf v w hvw⟩

/-- Forget the two added marking identities while retaining every cap conclusion. -/
theorem published_original_basic_branch_and_spin_cap (s : OriginalPositionallyAsymptoticHelicoid)
    (A : PublishedConformalPoleModel s.position) (poincare : SimplyConnectedNoncompactUniformization.{0})
    (hw : GeometricTwoAxisIntersectionTheorem) (pinkall : PinkallEmbeddedTorusRegularHomotopy) :
    HasOriginalSpinBranchCap s := by
  obtain ⟨S,hs,hc,t,ht,a,c,m,e,R,Z,hZ,_,_,h⟩ := published_original_pointed_spin_cap s A poincare hw pinkall
  exact ⟨S,hs,hc,t,ht,a,c,m,e,R,Z,hZ,h⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.published_original_pointed_spin_cap
#print axioms TwoAxisHelicoid.published_original_basic_branch_and_spin_cap
