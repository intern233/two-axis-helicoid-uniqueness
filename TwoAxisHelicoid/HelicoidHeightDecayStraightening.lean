import TwoAxisHelicoid.HelicoidC1Straightening

namespace TwoAxisHelicoid
open Set Filter Bornology
open scoped Topology ContDiff

/-- The hypothesis of the cap construction in Proposition 4.4. On some
exterior with compact complement there is a single smooth normal graph
whose height tends to zero. No decay assumption on its derivative appears. -/
def HasHelicoidHeightEnd {M : Type*} [TopologicalSpace M] (X : M → HelicoidTubeCoordinates) : Prop :=
  ∃ (S : Set M), IsCompact Sᶜ ∧ ∃ R : ℝ, 0 < R ∧ ∃ E : S ≃ₜ exteriorPlaneBase R,
    ∃ u : exteriorPlaneBase R → ℝ,
      ContDiffOn ℝ ∞ (extendOpenScalar u) (exteriorPlaneBase R) ∧
      (∀ b, |u b| ≤ 1/2) ∧
      (∀ q : S, X q.1 = helicoidTubeMap ((u (E q),(E q).1.1),(E q).1.2)) ∧
      Tendsto (fun b : exteriorPlaneBase R => |u b|)
        (comap (Subtype.val : exteriorPlaneBase R → ℝ × ℝ) (cobounded (ℝ × ℝ))) (𝓝 0)

theorem HasHelicoidC1End.heightEnd {M : Type*} [TopologicalSpace M] {X : M → HelicoidTubeCoordinates}
    (hEnd : HasHelicoidC1End X) : HasHelicoidHeightEnd X := by
  obtain ⟨C,_,R,hR,hc,E,_,u,hus,hg,hd⟩ := hEnd
  refine ⟨_,hc,R,hR,E,u,hus,fun b => (hg b).1,fun q => ?_,?_⟩
  · simpa only [Homeomorph.symm_apply_apply] using (hg (E q)).2
  · exact squeeze_zero (fun b => abs_nonneg (u b))
      (fun b => le_add_of_nonneg_right (Real.sqrt_nonneg _)) hd

/-- In the interior of the normal tube, the actual base coordinates of
a parametrized normal graph recover its parameters. -/
theorem normal_graph_coordinates_exact {v : ℝ} (hv : |v| < 1) (p : ℝ × ℝ) :
    helicoidBaseCoordinates (helicoidTubeMap ((v,p.1),p.2)) = p := by
  have he : helicoidTubeEquiv.symm (helicoidTubeMap ((v,p.1),p.2)) = ((v,p.1),p.2) :=
    helicoidTubeEquiv.left_inv hv
  simp only [helicoidBaseCoordinates,he]

theorem HasHelicoidHeightEnd.straightens {M : Type*} [TopologicalSpace M] [T2Space M]
    {X : M → HelicoidTubeCoordinates} (hEnd : HasHelicoidHeightEnd X) (hX : IsProperMap X)
    {K : Set HelicoidTubeCoordinates} (hK : IsCompact K) :
    ∃ Ψ : Icc (0 : ℝ) 1 → HelicoidTubeCoordinates ≃ₜ HelicoidTubeCoordinates,
      IsSmoothAmbientIsotopy Ψ ∧ (∀ time y, y ∈ K → Ψ time y = y) ∧
      HasExactHelicoidEnd ((Ψ ⟨1,by norm_num⟩).symm ∘ X) := by
  obtain ⟨S,hS,R,_,E,u,hus,hbound,hgraph,hd⟩ := hEnd
  have hcoord (q : S) : (E q).1 = helicoidBaseCoordinates (X q.1) := by
    rw [hgraph]
    exact (normal_graph_coordinates_exact ((hbound (E q)).trans_lt (by norm_num)) (E q).1).symm
  obtain ⟨B,Ψ,hRB,hB0,hcont,hinv,hsmooth,hzero,hfix,hfar⟩ :=
    exterior_helicoid_graph_ambient_straightening hus hd hK
  refine ⟨Ψ,⟨hcont,hinv,hsmooth,hzero⟩,hfix,fartherExteriorSet (helicoidBaseCoordinates ∘ X) S B,
    farther_helicoid_graph_compact_complement hX hS E hcoord hbound hgraph,
    B,hB0,fartherExteriorHomeomorph E hcoord hRB,?_⟩
  intro q
  let qS : S := ⟨q.1,q.2.1⟩
  have hb : B ≤ ‖(E qS).1‖ := by rw [hcoord]; exact q.2.2.le
  change (Ψ ⟨1,by norm_num⟩).symm (X q.1) = helicoidTubeMap ((0,(E qS).1.1),(E qS).1.2)
  rw [hgraph qS]
  exact (hfar (E qS) hb).2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HasHelicoidC1End.heightEnd
#print axioms TwoAxisHelicoid.HasHelicoidHeightEnd.straightens
