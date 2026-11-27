import TwoAxisHelicoid.TorusHeightFluxLoop
import TwoAxisHelicoid.ParameterizedAnalyticImmersion

namespace TwoAxisHelicoid
open Complex Set Filter Topology

/-- A total version of the punctured-plane projection, with an arbitrary
value at a lattice point. Only its germs at regular points are used. -/
noncomputable def finiteTorusProjection (L : PeriodPair) (base : PuncturedPeriodTorus L) (z : ℂ) : PuncturedPeriodTorus L := by
  classical
  exact if h : z ∉ L.lattice then puncturedPlaneProjection L ⟨z,h⟩ else base

theorem finiteTorusProjection_map_nhds (L : PeriodPair) (base : PuncturedPeriodTorus L) {z : ℂ} (hz : z ∉ L.lattice) :
    map (finiteTorusProjection L base) (𝓝 z)=𝓝 (puncturedPlaneProjection L ⟨z,hz⟩) := by
  let a : PuncturedLatticePlane L := ⟨z,hz⟩
  have proj : finiteTorusProjection L base ∘ (Subtype.val : PuncturedLatticePlane L → ℂ)=puncturedPlaneProjection L :=
    funext fun q => by simp [finiteTorusProjection,q.2]
  have eo : IsOpenEmbedding (Subtype.val : PuncturedLatticePlane L → ℂ) := L.isClosed_lattice.isOpen_compl.isOpenEmbedding_subtypeVal
  rw [← eo.map_nhds_eq a,Filter.map_map,proj]
  exact (puncturedPlaneProjection_isLocalHomeomorph L).isOpenMap.map_nhds_eq (puncturedPlaneProjection_continuous L).continuousAt

theorem finiteTorusProjection_product_nhds (L : PeriodPair) (base : PuncturedPeriodTorus L) {z : ℂ} (hz : z ∉ L.lattice) (s : ℝ) :
    map (Prod.map (id : ℝ → ℝ) (finiteTorusProjection L base)) (𝓝 (s,z)) =
      𝓝 (s,puncturedPlaneProjection L ⟨z,hz⟩) := by
  rw [nhds_prod_eq,← Filter.prod_map_right,finiteTorusProjection_map_nhds L base hz,nhds_prod_eq]

theorem finiteTorusProjection_pullback_eq {E : Type*} [Zero E] (L : PeriodPair) (base : PuncturedPeriodTorus L)
    (Y : ℝ → PuncturedPeriodTorus L → E) (t : ℝ) {z : ℂ} (hz : z ∉ L.lattice) :
    (fun p : ℝ × ℂ => Y p.1 (finiteTorusProjection L base p.2)) =ᶠ[𝓝 (t,z)]
      fun p => puncturedTorusPullback L (Y p.1) p.2 := by
  filter_upwards [((continuous_snd : Continuous (Prod.snd : ℝ × ℂ → ℂ)).continuousAt (x := (t,z))).eventually
    (L.isClosed_lattice.isOpen_compl.mem_nhds hz)] with p hp
  change p.2 ∉ L.lattice at hp
  simp only [puncturedTorusPullback,finiteTorusProjection,dite_eq_left hp]

theorem marked_family_joint_continuous (L : PeriodPair) (Y : ℝ → PuncturedPeriodTorus L → Fin 3 → ℝ)
    (joint : ∀ t z, z ∉ L.lattice → ContinuousAt (fun p : ℝ × ℂ => puncturedTorusPullback L (Y p.1) p.2) (t,z)) :
    Continuous (fun p : ℝ × PuncturedPeriodTorus L => Y p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t,q⟩
  obtain ⟨a,rfl⟩ := puncturedPlaneProjection_surjective L q
  let b := puncturedPlaneProjection L a
  have c := (joint t a a.2).congr (finiteTorusProjection_pullback_eq L b Y t a.2).symm
  change Tendsto (fun p : ℝ × PuncturedPeriodTorus L => Y p.1 p.2) (𝓝 (t,b)) (𝓝 (Y t b))
  rw [← finiteTorusProjection_product_nhds L b a.2 t,tendsto_map'_iff]
  change Tendsto (fun p : ℝ × ℂ => Y p.1 (finiteTorusProjection L b p.2)) (𝓝 (t,a.1)) (𝓝 (Y t b))
  have h := c.tendsto
  change Tendsto (fun p : ℝ × ℂ => Y p.1 (finiteTorusProjection L b p.2)) (𝓝 (t,a.1)) (𝓝 (Y t (finiteTorusProjection L b a.1))) at h
  rwa [show finiteTorusProjection L b a.1=b by simp [finiteTorusProjection,b,a.2]] at h

/-- The local injectivity neighborhoods for a joint analytic immersion
family descend through the actual punctured covering projection. -/
theorem marked_family_uniform_local_injectivity (L : PeriodPair) (Y : ℝ → PuncturedPeriodTorus L → Fin 3 → ℝ)
    (joint : ∀ t z, z ∉ L.lattice → AnalyticAt ℝ (fun p : ℝ × ℂ => puncturedTorusPullback L (Y p.1) p.2) (t,z))
    (imm : ∀ t z, z ∉ L.lattice → Function.Injective (fderiv ℝ (puncturedTorusPullback L (Y t)) z)) :
    ∀ t q, ∃ V ∈ 𝓝 t, ∃ U ∈ 𝓝 q, ∀ s ∈ V, InjOn (Y s) U := by
  intro t q
  obtain ⟨a,rfl⟩ := puncturedPlaneProjection_surjective L q
  let b := puncturedPlaneProjection L a
  let π := finiteTorusProjection L b
  obtain ⟨V,hV,U,hU,inj⟩ := parameterized_immersion_locally_injective (joint t a a.2) (imm t a a.2)
  let D := U ∩ (L.lattice : Set ℂ)ᶜ
  have nh : D ∈ 𝓝 a.1 := inter_mem hU (L.isClosed_lattice.isOpen_compl.mem_nhds a.2)
  have hn : π '' D ∈ 𝓝 b := finiteTorusProjection_map_nhds L b a.2 ▸ image_mem_map nh
  refine ⟨V,hV,π '' D,hn,?_⟩
  rintro s hs _ ⟨z,hz,rfl⟩ _ ⟨w,hw,rfl⟩ same
  apply congrArg π
  apply inj s hs hz.1 hw.1
  have zreg : z ∉ L.lattice := hz.2
  have wreg : w ∉ L.lattice := hw.2
  simpa only [π,finiteTorusProjection,puncturedTorusPullback,dite_eq_left zreg,dite_eq_left wreg] using same

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_family_joint_continuous
#print axioms TwoAxisHelicoid.marked_family_uniform_local_injectivity
