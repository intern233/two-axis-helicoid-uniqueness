import TwoAxisHelicoid.HelicoidEndStraightening
import TwoAxisHelicoid.FartherHelicoidGraphCompact
import TwoAxisHelicoid.CertifiedC1HelicoidEnd

namespace TwoAxisHelicoid
open Set Filter Bornology
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

/-- A continuous ambient isotopy whose every slice is a smooth
diffeomorphism, with joint continuity also explicitly proved for inverses. -/
structure IsSmoothAmbientIsotopy
    (Ψ : Icc (0 : ℝ) 1 → HelicoidTubeCoordinates ≃ₜ HelicoidTubeCoordinates) : Prop where
  continuous : Continuous (fun q : Icc (0 : ℝ) 1 × HelicoidTubeCoordinates => Ψ q.1 q.2)
  inverse_continuous : Continuous (fun q : Icc (0 : ℝ) 1 × HelicoidTubeCoordinates => (Ψ q.1).symm q.2)
  smooth : ∀ time, ContDiff ℝ (∞ : WithTop ℕ∞) (Ψ time) ∧
    ContDiff ℝ (∞ : WithTop ℕ∞) (Ψ time).symm
  start : Ψ ⟨0,by norm_num⟩ = Homeomorph.refl HelicoidTubeCoordinates

/-- A genuinely compact parameter complement and an actual global
end homeomorphism identify the map exactly with the standard helicoid. -/
def HasExactHelicoidEnd {M : Type*} [TopologicalSpace M] (X : M → HelicoidTubeCoordinates) : Prop :=
  ∃ S : Set M, IsCompact Sᶜ ∧ ∃ B : ℝ, 0 < B ∧ ∃ E : S ≃ₜ exteriorPlaneBase B,
    ∀ q : S, X q.1 = helicoidTubeMap ((0,(E q).1.1),(E q).1.2)

/-- The full C¹ end already constructed can be pulled back to an exact
helicoid outside a genuine compact parameter set, while the ambient
isotopy fixes any chosen compact core pointwise. -/
theorem HasHelicoidC1End.exists_smooth_ambient_straightening
    {M : Type*} [TopologicalSpace M] [T2Space M] {X : M → HelicoidTubeCoordinates}
    (hEnd : HasHelicoidC1End X) (hX : IsProperMap X)
    {K : Set HelicoidTubeCoordinates} (hK : IsCompact K) :
    ∃ Ψ : Icc (0 : ℝ) 1 → HelicoidTubeCoordinates ≃ₜ HelicoidTubeCoordinates,
      IsSmoothAmbientIsotopy Ψ ∧ (∀ time y, y ∈ K → Ψ time y = y) ∧
      HasExactHelicoidEnd ((Ψ ⟨1,by norm_num⟩).symm ∘ X) := by
  obtain ⟨C,_hC,R,_hR,hcompact,E,hE,u,hus,hgraph,hdecay⟩ := hEnd
  let S := helicoidProjectedEnd X C (exteriorPlaneBase R)
  have hcoord (q : S) : (E q).1 = helicoidBaseCoordinates (X q.1) :=
    congrArg Subtype.val (congrFun hE q)
  have hEq (q : S) : X q.1 = helicoidTubeMap ((u (E q),(E q).1.1),(E q).1.2) := by
    simpa only [Homeomorph.symm_apply_apply] using (hgraph (E q)).2
  have hheight : Tendsto (fun p => |u p|)
      (comap (Subtype.val : exteriorPlaneBase R → ℝ × ℝ) (cobounded (ℝ × ℝ))) (𝓝 0) := by
    apply squeeze_zero (fun p => abs_nonneg (u p)) _ hdecay
    intro p
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  obtain ⟨B,Ψ,hRB,hB0,hcont,hinv,hsmooth,hzero,hfix,hfar⟩ :=
    exterior_helicoid_graph_ambient_straightening hus hheight hK
  refine ⟨Ψ,⟨hcont,hinv,hsmooth,hzero⟩,hfix,?_⟩
  refine ⟨fartherExteriorSet (helicoidBaseCoordinates ∘ X) S B,
    farther_helicoid_graph_compact_complement hX hcompact E hcoord (fun p => (hgraph p).1) hEq,
    B,hB0,fartherExteriorHomeomorph E hcoord hRB,?_⟩
  intro q
  let qS : S := ⟨q.1,q.2.1⟩
  have hb : B ≤ ‖(E qS).1‖ := by
    rw [hcoord]
    exact q.2.2.le
  change (Ψ ⟨1,by norm_num⟩).symm (X q.1) = helicoidTubeMap ((0,(E qS).1.1),(E qS).1.2)
  rw [hEq qS]
  exact (hfar (E qS) hb).2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HasHelicoidC1End.exists_smooth_ambient_straightening
