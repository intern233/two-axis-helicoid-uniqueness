import TwoAxisHelicoid.OneEndedPlaneDiskCoordinate

namespace TwoAxisHelicoid
open Complex Set Metric Bornology Filter Function Topology
open scoped Topology

/-- A bounded connected plane domain with one topological end has a
normalized conformal disk coordinate. Simple connectivity follows
from the resulting bijection. -/
theorem bounded_one_ended_plane_disk_coordinate {U : Set ℂ} (op : IsOpen U) (connected : IsConnected U)
    (bounded : IsBounded U) (tails : HasConnectedCompactTails U) {p : ℂ} (hp : p∈U) :
    ∃ f, NormalizedDiskCoordinate U p f ∧ f '' U=complexUnitDisk := by
  obtain ⟨R,r⟩ := bounded.exists_norm_le
  let s := R+‖p‖+1
  have sp : 0<s := by dsimp [s]; linarith [r p hp,norm_nonneg p]
  have nz : (s:ℂ)≠0 := ofReal_ne_zero.mpr sp.ne'
  let f := fun z : ℂ => (z-p)/(s:ℂ)
  have der (z : ℂ) : HasDerivAt f (1/(s:ℂ)) z := ((hasDerivAt_id z).sub_const p).div_const _
  have norm : NormalizedDiskCoordinate U p f := by
    refine ⟨fun _ _ => (analyticAt_id.sub analyticAt_const).div_const,?_,?_,by simp [f],?_⟩
    · intro z hz
      apply mem_ball_zero_iff.mpr
      change ‖(z-p)/(s:ℂ)‖<1
      rw [norm_div,Complex.norm_real,Real.norm_of_nonneg sp.le,div_lt_one sp]
      exact (norm_sub_le z p).trans_lt (by dsimp [s]; linarith [r z hz])
    · intro x _ y _ eq
      exact sub_left_inj.mp ((div_left_inj' nz).mp eq)
    · intro z _
      rw [(der z).deriv]
      exact div_ne_zero one_ne_zero nz
  obtain ⟨g,hg,maximal⟩ := normalized_disk_coordinate_attains_maximum op connected.isPreconnected hp ⟨f,norm⟩
  refine ⟨g,hg,hg.maps.image_subset.antisymm ?_⟩
  intro a ha
  by_contra miss
  obtain ⟨k,hk,more⟩ := disk_coordinate_improves_on_one_ended_domain op connected tails hp ha hg miss
  exact more.not_ge (maximal k hk)

/-- Topological closed-ball cuts with a single collared end therefore
have open disk interiors wherever they admit a bounded planar model. -/
theorem bounded_one_ended_plane_open_disk {U : Set ℂ} (op : IsOpen U) (connected : IsConnected U)
    (bounded : IsBounded U) (tails : HasConnectedCompactTails U) : Nonempty (U ≃ₜ complexUnitDisk) := by
  obtain ⟨p,hp⟩ := connected.nonempty
  obtain ⟨f,hf,onto⟩ := bounded_one_ended_plane_disk_coordinate op connected bounded tails hp
  let g : U → complexUnitDisk := fun z => ⟨f z.1,hf.maps z.2⟩
  have bij : Bijective g := by
    refine ⟨fun x y eq => Subtype.ext (hf.injective x.2 y.2 (congrArg Subtype.val eq)),?_⟩
    intro y
    obtain ⟨x,hx,eq⟩ := (show y.1∈f '' U from onto.symm ▸ y.2)
    exact ⟨⟨x,hx⟩,Subtype.ext eq⟩
  have cont : Continuous g := (continuousOn_iff_continuous_domRestrict.mp hf.analytic.continuousOn).subtype_mk _
  have og : IsOpenMap g := by
    apply unitDiskOpen.isOpen.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr
    apply isOpenMap_iff_nhds_le.mpr
    intro x
    change 𝓝 (f x.1)≤map (f ∘ (Subtype.val : U → ℂ)) (𝓝 x)
    rw [← map_map,op.isOpenEmbedding_subtypeVal.map_nhds_eq x,(hf.analytic x.1 x.2).hasStrictDerivAt.map_nhds_eq (hf.regular x.1 x.2)]
  exact ⟨(Equiv.ofBijective g bij).toHomeomorphOfContinuousOpen cont og⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_one_ended_plane_disk_coordinate
#print axioms TwoAxisHelicoid.bounded_one_ended_plane_open_disk
