import TwoAxisHelicoid.HolomorphicDiskCover
import TwoAxisHelicoid.DiskBoundedDisplacement
import TwoAxisHelicoid.TopologicalTorusUniversalCover
import Mathlib.Analysis.Convex.Contractible

namespace TwoAxisHelicoid
open Complex Metric Set Function Filter Topology
open scoped Topology ContDiff Manifold ComplexConjugate

/-- An actual holomorphic universal covering of a compact topological
torus cannot be a disk. Each deck transformation has invariant
pseudohyperbolic displacement, which descends to the compact quotient
and attains a bound strictly below one. -/
theorem compact_topological_torus_no_disk_cover {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [CompactSpace M] {L : PeriodPair} (H : M ≃ₜ PeriodTorus L) {p : RiemannUnitDisk → M}
    (hp : IsCoveringMap p) (hs : Surjective p)
    (hhol : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω p) : False := by
  let o : RiemannUnitDisk := ⟨0,mem_ball_self one_pos⟩
  have hcDsc : ContractibleSpace RiemannUnitDisk :=
    (convex_ball (0:ℂ) 1).contractibleSpace ⟨o.1,o.2⟩
  have hlp : LocallyPathConnectedSpace RiemannUnitDisk := unitDiskOpen.isOpen.locallyPathConnectedSpace
  have ht := hp.homeomorph_comp H
  have hol {f : RiemannUnitDisk ≃ₜ RiemannUnitDisk} (he : ∀ z, p (f z) = p z) :
      ∀ a b, unitDiskDistance (f a) (f b) = unitDiskDistance a b := by
    apply unitDisk_biholomorphic_distance f (holomorphic_of_cover_deck hhol f.continuous he)
    apply holomorphic_of_cover_deck hhol f.symm.continuous
    intro z
    exact (he (f.symm z)).symm.trans (congrArg p (f.apply_symm_apply z))
  have hj : Injective p := by
    intro x y hxy
    obtain ⟨f,hfx,hf⟩ := simply_connected_cover_deck_transitive hp hxy
    let δ := fun a => unitDiskDistance a (f a)
    have hc : Continuous δ := by
      unfold δ unitDiskDistance diskMobius
      exact ((continuous_subtype_val.comp f.continuous).sub continuous_subtype_val).div
        (continuous_const.sub ((continuous_conj.comp continuous_subtype_val).mul (continuous_subtype_val.comp f.continuous)))
        (fun w => diskMobius_den_ne w.2 (f w).2) |>.norm
    have hdesc (a b : RiemannUnitDisk) (hh : p a = p b) : δ a = δ b := by
      obtain ⟨g,hga,hg⟩ := simply_connected_cover_deck_transitive hp hh
      have hcomm := topological_torus_cover_lifts_commute L ht o f.continuous g.continuous
        (fun z => congrArg H (hf z)) (fun z => congrArg H (hg z))
      change unitDiskDistance a (f a) = unitDiskDistance b (f b)
      rw [← hga,show f (g a) = g (f a) from congrFun hcomm a]
      exact (hol hg a (f a)).symm
    let D := fun q : M => δ (hs q).choose
    have hD (z : RiemannUnitDisk) : D (p z) = δ z := hdesc _ _ (hs (p z)).choose_spec
    have hcD : Continuous D := (hp.isQuotientMap hs).continuous_iff.mpr
      (by simpa only [Function.comp_def,hD] using hc)
    obtain ⟨m,_,hm⟩ := isCompact_univ.exists_isMaxOn
      (show (univ : Set M).Nonempty from ⟨p o,mem_univ _⟩) hcD.continuousOn
    let q := (hs m).choose
    have hlt : D m < 1 := by
      have h := diskMobius_mapsTo q.2 (f q).2
      change ‖diskMobius q.1 (f q).1‖ < 1
      simpa only [mem_ball,dist_zero_right] using h
    let g := unitDiskExtension f
    have hmap : MapsTo g complexUnitDisk complexUnitDisk := fun z hz => by
      change unitDiskExtension f z ∈ complexUnitDisk
      rw [show unitDiskExtension f z = (f ⟨z,hz⟩).1 from unitDiskExtension_apply f ⟨z,hz⟩]
      exact (f ⟨z,hz⟩).2
    have he := disk_identity_of_bounded_displacement
      (unitDiskExtension_analytic (holomorphic_of_cover_deck hhol f.continuous hf)) hmap
      (r := D m) (norm_nonneg _) hlt (fun z hz => by
        let w : RiemannUnitDisk := ⟨z,hz⟩
        change ‖diskMobius w.1 (unitDiskExtension f w.1)‖ ≤ D m
        rw [unitDiskExtension_apply]
        change δ w ≤ D m
        rw [← hD]
        exact hm (mem_univ (p w)))
    have hx : f x = x := Subtype.ext (by simpa only [unitDiskExtension_apply,id_eq] using he x.2)
    exact hx.symm.trans hfx
  let e := (Equiv.ofBijective p ⟨hj,hs⟩).toHomeomorphOfContinuousOpen hp.continuous hp.isOpenMap
  obtain ⟨τ,_⟩ := topological_torus_cover_equivalence L ht o
  exact noncompact_univ ℂ (by
    simpa only [image_univ,e.symm.surjective.range_eq,τ.surjective.range_eq] using
      ((isCompact_univ (X := M)).image e.symm.continuous).image τ.continuous)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_topological_torus_no_disk_cover
