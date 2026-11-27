import TwoAxisHelicoid.LatticeSignDoubleCover
import TwoAxisHelicoid.SpinorFramePullback

namespace TwoAxisHelicoid
open Set Topology

/-- Multiplication by two kills the sign character, so two compact images
of fundamental domains cover the whole sign-cover total space. -/
theorem latticeSignCover_compactSpace (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    CompactSpace (LatticeSignCover L χ) := by
  let f : ZMod 2 → ℂ → LatticeSignCover L χ := fun g z => latticeSignCoverMk L χ (2*z,g)
  have hc (g : ZMod 2) : Continuous (f g) := by
    exact QuotientAddGroup.continuous_mk.comp
      ((continuous_const.mul continuous_id).prodMk continuous_const)
  have hp (g : ZMod 2) (z w : ℂ) (hw : w ∈ L.lattice) : f g (z+w) = f g z := by
    let ω : L.lattice := ⟨w,hw⟩
    apply (latticeSignCoverMk_eq L χ (2*(z+w),g) (2*z,g)).mpr
    refine ⟨ω+ω,?_,?_⟩
    · change 2*(z+w)-2*z = w+w
      ring
    · rw [sub_self,map_add,zmod_two_add_self]
  have h0 := IsZLattice.isCompact_range_of_periodic L.lattice (f 0) (hc 0) (hp 0)
  have h1 := IsZLattice.isCompact_range_of_periodic L.lattice (f 1) (hc 1) (hp 1)
  have he : range (f 0) ∪ range (f 1) = univ := by
    apply eq_univ_of_forall
    intro q
    obtain ⟨v,rfl⟩ := Quotient.exists_rep q
    have hv : f v.2 (v.1/2) = latticeSignCoverMk L χ v := by
      dsimp [f]
      congr 1
      apply Prod.ext
      · ring
      · rfl
    rcases zmod_two_cases v.2 with hg | hg
    · exact Or.inl ⟨v.1/2,by simpa only [hg] using! hv⟩
    · exact Or.inr ⟨v.1/2,by simpa only [hg] using! hv⟩
  exact isCompact_univ_iff.mp (he ▸ h0.union h1)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.latticeSignCover_compactSpace

