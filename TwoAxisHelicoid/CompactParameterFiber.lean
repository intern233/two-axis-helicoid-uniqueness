import TwoAxisHelicoid.RegularBoundaryConnectedTails
import Mathlib.Topology.Separation.Hausdorff

namespace TwoAxisHelicoid
open Set Topology Filter

/-- If arbitrarily small neighborhoods of a value have connected
interior preimages in a dense subspace, the entire fiber of a
continuous map from a compact parameter space is connected. This
also applies to a boundary value with no interior preimage of its own. -/
theorem connected_fiber_of_connected_approaches {K Y : Type*}
    [TopologicalSpace K] [CompactSpace K] [T2Space K] [TopologicalSpace Y] [T2Space Y]
    {f : K → Y} (cont : Continuous f) {D : Set K} (dense : Dense D) {q : Y}
    (approach : ∀ G : Set Y, IsOpen G → q∈G →
      ∃ O : Set Y, IsOpen O ∧ q∈O ∧ O⊆G ∧ IsPreconnected (D∩f ⁻¹' O)) :
    IsPreconnected (f ⁻¹' {q}) := by
  let S := f ⁻¹' {q}
  have cs : IsCompact S := (isClosed_singleton.preimage cont).isCompact
  apply isPreconnected_closed_iff.mpr
  intro A B ca cb cover meetA meetB
  by_contra miss
  have dj : Disjoint (S∩A) (S∩B) := disjoint_left.mpr fun z za zb => miss ⟨z,za.1,za.2,zb.2⟩
  obtain ⟨U,V,ou,ov,au,bv,apart⟩ := SeparatedNhds.of_isCompact_isCompact (cs.inter_right ca) (cs.inter_right cb) dj
  let G := (f '' (U∪V)ᶜ)ᶜ
  have og : IsOpen G := (((ou.union ov).isClosed_compl.isCompact.image cont).isClosed).isOpen_compl
  have qg : q∈G := by
    rintro ⟨x,outside,eq⟩
    have xs : x∈S := eq
    exact outside ((cover xs).imp (fun h => au ⟨xs,h⟩) (fun h => bv ⟨xs,h⟩))
  obtain ⟨O,oo,qo,sub,conn⟩ := approach G og qg
  have covered : D∩f ⁻¹' O ⊆ U∪V := by
    rintro x ⟨_,xo⟩
    by_contra h
    exact sub xo ⟨x,h,rfl⟩
  have touch {Z : Set K} (oz : IsOpen Z) {x : K} (xs : x∈S) (xz : x∈Z) : ((D∩f ⁻¹' O)∩Z).Nonempty := by
    obtain ⟨a,⟨az,ao⟩,ad⟩ := mem_closure_iff.mp (dense x) (Z∩f ⁻¹' O) (oz.inter (oo.preimage cont))
      ⟨xz,show f x∈O from (show f x=q from xs) ▸ qo⟩
    exact ⟨a,⟨ad,ao⟩,az⟩
  obtain ⟨x,xs,xa⟩ := meetA
  obtain ⟨y,ys,yb⟩ := meetB
  obtain ⟨z,_,zu,zv⟩ := conn U V ou ov covered (touch ou xs (au ⟨xs,xa⟩)) (touch ov ys (bv ⟨ys,yb⟩))
  exact disjoint_left.mp apart zu zv

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.connected_fiber_of_connected_approaches
