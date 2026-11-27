import TwoAxisHelicoid.PublishedGeometricClassification
import TwoAxisHelicoid.PublishedOriginalSpinBranch

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ContDiff Manifold

/-- Apply the four published inputs to the given original real surface.
The two poles are in the actual BBC chart. Its compact marked surface is
identified at the missing point and at every original point with the torus
carrying the cap. In the original spatial coordinates an open subset of
the original surface containing both complete marked loops is fixed. -/
theorem original_geometric_surface_basic_spin_cap
    (s : OriginalPositionallyAsymptoticHelicoid)
    (bbc : PublishedOneHandleEndTheorem) (poincare : SimplyConnectedNoncompactUniformization.{0})
    (hw : GeometricTwoAxisIntersectionTheorem) (pinkall : PinkallEmbeddedTorusRegularHomotopy) :
    ∃ A : PublishedConformalPoleModel s.position,
      let X := (fun q => A.offset+A.frame (A.spatial q)) ∘ A.chart.symm
      meromorphicOrderAt (fun z => immersionComplexCoefficient X z 2) 0 = -2 ∧
      meromorphicOrderAt (immersionGaussLogDerivative X) 0 = -2 ∧
      HasOriginalSpinBranchCap s ∧
      ∃ (t : ℝ) (ht : 0 < t) (a c : ℝ) (m : ℤ), let L := rhombicPeriodPair t ht
      ∃ (e : s.carrier ≃ₜ PuncturedPeriodTorus L) (H : A.model ≃ₜ PeriodTorus L)
        (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) (Z : ℂ → Fin 3 → ℝ)
        (hZ : TwoAxisHarmonicConformalImmersion L Z)
        (G : PeriodTorus L → Fin 3 → ℝ) (cs : ChartedSpace (ℝ × ℝ) (PeriodTorus L))
        (V : Set s.carrier), let _ := cs
        H A.point = 0 ∧ (∀ x, H (A.marking x).1 = (e x).1) ∧
        (∀ v w : Fin 3 → ℝ, (∑ j, (R v j-R w j)^2) = ∑ j, (v j-w j)^2) ∧
        (∀ x, harmonicTorusImmersion hZ (e x) = R (s.position x)) ∧
        a ∈ Ioo (0:ℝ) 1 ∧ c ≠ 0 ∧ Odd m ∧ m = 1 ∧
        (∀ z ∉ L.lattice, puncturedImmersionCoefficient L Z z 2 = coordinateData t a c ht z 2) ∧
        (∀ z ∉ gaussLogPoleSet L a, nullGauss (puncturedImmersionCoefficient L Z z) = thetaGauss t a m z) ∧
        IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ (PeriodTorus L) ∧ IsClosedEmbedding G ∧
        ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ G ∧
        (∀ p, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) G p)) ∧
        IsOpen V ∧ (∀ (i : Fin 2) (r : unitInterval), e.symm (puncturedTorusGeneratorLoop L i r) ∈ V) ∧
        (∀ x ∈ V, G (e x).1 = s.position x) ∧
        ∀ v w, torusIntersectionModTwo v w = 1 →
          capAmbientSpinQuadratic L G v * capAmbientSpinQuadratic L G w = 0 := by
  obtain ⟨A⟩ := bbc s.toOriginalSmoothHelicoid s.intrinsic_complete s.one_topological_end s.image_ne_embedded_plane
  have h := published_original_basic_branch_and_spin_cap s A poincare hw pinkall
  refine ⟨A,A.heightOrder,A.gaussOrder,h,?_⟩
  obtain ⟨S,_,_,t,ht,a,c,m,e,R,Z,hZ,_,_,hR,hpt,_,ha,hc,_,_,hh,hg,ho,hm,F,cs,U,
    hM,_,_,_,hU,_,hcore,hE,hS,hI,hfix,hArf⟩ := h
  let L := rhombicPeriodPair t ht
  let H := compactPunctureExtension (A.marking.symm.trans e)
  let V := (fun x => (e x).1) ⁻¹' U
  have hH (x : s.carrier) : H (A.marking x).1 = (e x).1 := by
    have eq := compactPunctureExtension_apply (A.marking.symm.trans e) (A.marking x)
    exact eq.trans (congrArg (fun y => (e y).1) (A.marking.symm_apply_apply x))
  have hV : IsOpen V := hU.preimage (continuous_subtype_val.comp e.continuous)
  have hloop (i : Fin 2) (r : unitInterval) : e.symm (puncturedTorusGeneratorLoop L i r) ∈ V := by
    change (e (e.symm (puncturedTorusGeneratorLoop L i r))).1 ∈ U
    rw [e.apply_symm_apply]
    exact hcore ⟨_,puncturedTorusGeneratorLoop_mem_core L i r,rfl⟩
  exact ⟨t,ht,a,c,m,e,H,R,Z,hZ,R.symm ∘ F,cs,V,compactPunctureExtension_at_end _,hH,
    hR,hpt,ha,hc,ho,hm,hh,hg,hM,hE,hS,hI,hV,hloop,hfix,fun v w hvw => (hArf v w hvw).2.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_geometric_surface_basic_spin_cap
