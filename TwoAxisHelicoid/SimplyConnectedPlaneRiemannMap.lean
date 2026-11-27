import TwoAxisHelicoid.ExtremalDiskAttainment
import TwoAxisHelicoid.RoundLogarithmicCover
import TwoAxisHelicoid.HolomorphicDiskCover
import TwoAxisHelicoid.InitialPlaneDiskCoordinate

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology TopologicalSpace
open scoped Topology ContDiff Manifold

/-- A first bounded univalent coordinate, fixing the chosen interior
point by a disk automorphism. -/
theorem initial_normalized_plane_coordinate {U : Set ℂ} (op : IsOpen U) (conn : IsSimplyConnected U)
    (proper : U≠univ) {p : ℂ} (hp : p∈U) : ∃ g, NormalizedDiskCoordinate U p g := by
  obtain ⟨f,an,mf,inj,reg⟩ := bounded_injective_coordinate_of_proper_plane_domain op conn proper hp
  let b := f p
  have hb : b∈complexUnitDisk := mf hp
  let g := diskMobius b ∘ f
  refine ⟨g,fun z hz => (diskMobius_analyticAt hb (mf hz)).comp (an z hz), (diskMobius_mapsTo hb).comp mf,
    (diskMobius_injOn hb).comp inj mf,by simp [g,b,diskMobius],?_⟩
  intro z hz
  rw [show deriv g z=deriv (diskMobius b) (f z)*deriv f z from
    deriv_comp z (diskMobius_analyticAt hb (mf hz)).differentiableAt (an z hz).differentiableAt]
  exact mul_ne_zero (diskMobius_regular hb (mf hz)) (reg z hz)

/-- The normalized Riemann map on every proper simply connected plane
domain is a regular analytic bijection onto the whole unit disk. -/
theorem simply_connected_plane_riemann_map {U : Set ℂ} (op : IsOpen U) (conn : IsSimplyConnected U)
    (proper : U≠univ) {p : ℂ} (hp : p∈U) :
    ∃ f, NormalizedDiskCoordinate U p f ∧ f '' U=complexUnitDisk := by
  obtain ⟨f,hf,maximal⟩ := normalized_disk_coordinate_attains_maximum op conn.isPathConnected.isConnected.isPreconnected hp
    (initial_normalized_plane_coordinate op conn proper hp)
  refine ⟨f,hf,hf.maps.image_subset.antisymm ?_⟩
  intro a ha
  by_contra skip
  obtain ⟨g,hg,larger⟩ := disk_coordinate_improves_at_omitted_value op conn hp ha hf skip
  exact larger.not_ge (maximal g hg)

/-- Realization in the actual standard complex manifold structures on
the open domain and disk, with the chosen point sent to the center. -/
theorem simply_connected_plane_disk_biholomorphism (S : Opens ℂ) (conn : IsSimplyConnected (S : Set ℂ))
    (proper : (S : Set ℂ)≠univ) (p : S) :
    ∃ H : Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) S RiemannUnitDisk ω, (H p).1=0 := by
  obtain ⟨f,hf,onto⟩ := simply_connected_plane_riemann_map S.isOpen conn proper p.2
  let g : S → RiemannUnitDisk := fun z => ⟨f z.1,hf.maps z.2⟩
  have bij : Bijective g := by
    refine ⟨fun x y eq => Subtype.ext (hf.injective x.2 y.2 (congrArg Subtype.val eq)),?_⟩
    intro y
    obtain ⟨z,hz,e⟩ := (show y.1∈f '' (S : Set ℂ) from onto.symm ▸ y.2)
    exact ⟨⟨z,hz⟩,Subtype.ext e⟩
  have cont : Continuous g := (continuousOn_iff_continuous_domRestrict.mp hf.analytic.continuousOn).subtype_mk _
  have og : IsOpenMap g := by
    apply unitDiskOpen.isOpen.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr
    apply isOpenMap_iff_nhds_le.mpr
    intro x
    change 𝓝 (f x.1)≤map (f ∘ (Subtype.val : S → ℂ)) (𝓝 x)
    have src : map (Subtype.val : S → ℂ) (𝓝 x)=𝓝 x.1 := S.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq x
    rw [← map_map,src,(hf.analytic x.1 x.2).hasStrictDerivAt.map_nhds_eq (hf.regular x.1 x.2)]
  let home := (Equiv.ofBijective g bij).toHomeomorphOfContinuousOpen cont og
  have ld := analytic_open_local_diffeomorphism f g (fun _ => rfl) (fun z hz => ⟨hf.analytic z hz,hf.regular z hz⟩) home.isLocalHomeomorph
  exact ⟨ld.diffeomorphOfBijective bij,hf.origin⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.simply_connected_plane_disk_biholomorphism
