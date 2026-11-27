import TwoAxisHelicoid.HelicoidHeightDecayStraightening

namespace TwoAxisHelicoid
open Set Filter Bornology
open scoped Topology ContDiff

/-- An exact exterior helicoid has the certified C¹ graph data, with
identically zero height and gradient on the actual projected end. -/
theorem HasExactHelicoidEnd.hasC1End {M : Type*} [TopologicalSpace M] {X : M → HelicoidTubeCoordinates}
    (hEnd : HasExactHelicoidEnd X) : HasHelicoidC1End X := by
  classical
  obtain ⟨S,hS,R,hR,E,hX⟩ := hEnd
  have hcoord (q : S) : helicoidBaseCoordinates (X q.1) = (E q).1 := by
    rw [hX]
    exact normal_graph_coordinates_exact (by norm_num) (E q).1
  let W := helicoidProjectedEnd X Sᶜ (exteriorPlaneBase R)
  have hW : W = S := by
    ext x
    constructor
    · intro h
      exact not_not.mp h.1
    · intro hx
      refine ⟨not_not.mpr hx,?_⟩
      rw [hcoord ⟨x,hx⟩]
      exact (E ⟨x,hx⟩).2
  let J := Homeomorph.setCongr hW
  let H : W ≃ₜ exteriorPlaneBase R := J.trans E
  have hproj (q : W) : H q = helicoidEndProjection X Sᶜ (exteriorPlaneBase R) q :=
    Subtype.ext (hcoord (J q)).symm
  let u : exteriorPlaneBase R → ℝ := fun _ => 0
  have hu : extendOpenScalar u = 0 := by
    funext x
    simp [extendOpenScalar,u]
  have hWc : IsCompact Wᶜ := by rw [hW]; exact hS
  refine ⟨Sᶜ,hS,R,hR,hWc,H,funext hproj,u,?_,?_,?_⟩
  · rw [hu]
    exact contDiffOn_const
  · intro b
    refine ⟨by norm_num [u],?_⟩
    have he := hX (J (H.symm b))
    have hb : E (J (H.symm b)) = b := H.apply_symm_apply b
    rw [hb] at he
    exact he
  · rw [hu]
    simpa [u,helicoidGraphGradientNorm] using
      (tendsto_const_nhds (x := (0:ℝ)) (f := comap (Subtype.val : exteriorPlaneBase R → ℝ × ℝ) (cobounded (ℝ × ℝ))))

/-- Smooth height decay alone admits ambient coordinates with a C¹
helicoidal end. The ambient isotopy can simultaneously fix any prescribed
compact set. Thus results formulated using C¹ coordinates apply to the
height-only hypothesis of Proposition 4.4. -/
theorem HasHelicoidHeightEnd.exists_ambient_C1_coordinates {M : Type*} [TopologicalSpace M] [T2Space M]
    {X : M → HelicoidTubeCoordinates} (hEnd : HasHelicoidHeightEnd X) (hX : IsProperMap X)
    {K : Set HelicoidTubeCoordinates} (hK : IsCompact K) :
    ∃ Ψ : Icc (0 : ℝ) 1 → HelicoidTubeCoordinates ≃ₜ HelicoidTubeCoordinates,
      IsSmoothAmbientIsotopy Ψ ∧ (∀ time y, y ∈ K → Ψ time y = y) ∧
      HasHelicoidC1End ((Ψ ⟨1,by norm_num⟩).symm ∘ X) := by
  obtain ⟨Ψ,hΨ,hfix,hE⟩ := hEnd.straightens hX hK
  exact ⟨Ψ,hΨ,hfix,hE.hasC1End⟩

/-- The allowed smooth ambient coordinate system for the general spin
cap is obtained from a height-only end in the originally supplied coordinates. -/
theorem helicoidal_height_end_admits_C1_chart {M : Type*} [TopologicalSpace M] [T2Space M]
    {X : M → Fin 3 → ℝ} (A : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates)
    (hA : ContDiff ℝ ∞ A) (hAi : ContDiff ℝ ∞ A.symm)
    (hEnd : HasHelicoidHeightEnd (A ∘ X)) (hX : IsProperMap X) :
    ∃ B : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates,
      ContDiff ℝ ∞ B ∧ ContDiff ℝ ∞ B.symm ∧ HasHelicoidC1End (B ∘ X) := by
  obtain ⟨Ψ,hΨ,_,hE⟩ := hEnd.exists_ambient_C1_coordinates (A.isProperMap.comp hX) isCompact_empty
  let e := (Ψ ⟨1,by norm_num⟩)
  exact ⟨A.trans e.symm,(hΨ.smooth _).2.comp hA,hAi.comp (hΨ.smooth _).1,hE⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasExactHelicoidEnd.hasC1End
#print axioms TwoAxisHelicoid.helicoidal_height_end_admits_C1_chart
