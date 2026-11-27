import TwoAxisHelicoid.RoundCylinderParameter
import TwoAxisHelicoid.AnnularEndSeparation
import TwoAxisHelicoid.ExteriorComplexEnd

namespace TwoAxisHelicoid
open Complex Set Metric Filter
open scoped Topology ContDiff Manifold

theorem IsRoundCylinderTarget.excludes_zero {T : Set ℂ} (round : IsRoundCylinderTarget T) :
    ∀ z∈T, z≠0 := by
  rcases round with rfl|rfl|⟨R,hR,rfl⟩
  · exact fun z hz => norm_pos_iff.mp hz
  · exact fun z hz => norm_pos_iff.mp hz.1
  · exact fun z hz => norm_pos_iff.mp ((inv_pos.mpr (zero_lt_one.trans hR)).trans hz.1)

/-- Each round quotient has two genuine radial collars. The outer one
becomes a lower collar after holomorphic inversion. -/
theorem IsRoundCylinderTarget.collars {T : Set ℂ} (round : IsRoundCylinderTarget T) :
    ∃ m r s : ℝ, 0<m ∧ 0≤r ∧ r<m ∧ 0≤s ∧ s<m⁻¹ ∧
      (∀ z : ℂ, ‖z‖≤m → (z∈T ↔ r<‖z‖)) ∧
      (∀ z : ℂ, ‖z‖≤m⁻¹ → ((z≠0 ∧ z⁻¹∈T) ↔ s<‖z‖)) := by
  rcases round with rfl|rfl|⟨R,hr,rfl⟩
  · refine ⟨1,0,0,by norm_num,le_rfl,by norm_num,le_rfl,by norm_num,fun _ _ => Iff.rfl,?_⟩
    intro z _
    change (z≠0 ∧ 0<‖z⁻¹‖) ↔ 0<‖z‖
    simp [norm_pos_iff]
  · refine ⟨1/2,0,1,by norm_num,le_rfl,by norm_num,by norm_num,by norm_num,?_,?_⟩
    · intro z hz
      change (0<‖z‖ ∧ ‖z‖<1) ↔ 0<‖z‖
      exact ⟨And.left,fun h => ⟨h,hz.trans_lt (by norm_num)⟩⟩
    · intro z _
      change (z≠0 ∧ 0<‖z⁻¹‖ ∧ ‖z⁻¹‖<1) ↔ 1<‖z‖
      rw [norm_inv]
      constructor
      · rintro ⟨nz,_,h⟩
        exact (inv_lt_inv₀ (norm_pos_iff.mpr nz) zero_lt_one).mp (by simpa using h)
      · intro h
        have pos := zero_lt_one.trans h
        exact ⟨norm_pos_iff.mp pos,inv_pos.mpr pos,by simpa using (inv_lt_inv₀ pos zero_lt_one).mpr h⟩
  · have pos := zero_lt_one.trans hr
    have small : R⁻¹<1 := by simpa using (inv_lt_inv₀ pos zero_lt_one).mpr hr
    refine ⟨1,R⁻¹,R⁻¹,zero_lt_one,(inv_pos.mpr pos).le,small,(inv_pos.mpr pos).le,by simpa using small,?_,?_⟩
    · intro z hz
      change (R⁻¹<‖z‖ ∧ ‖z‖<R) ↔ R⁻¹<‖z‖
      exact ⟨And.left,fun h => ⟨h,hz.trans_lt hr⟩⟩
    · intro z hz
      have up : ‖z‖<R := (show ‖z‖≤1 by simpa using hz).trans_lt hr
      change (z≠0 ∧ R⁻¹<‖z⁻¹‖ ∧ ‖z⁻¹‖<R) ↔ R⁻¹<‖z‖
      rw [norm_inv]
      constructor
      · rintro ⟨nz,_,h⟩
        exact (inv_lt_inv₀ (norm_pos_iff.mpr nz) (inv_pos.mpr pos)).mp (by simpa using h)
      · intro h
        have zp := (inv_pos.mpr pos).trans h
        exact ⟨norm_pos_iff.mp zp,(inv_lt_inv₀ pos zp).mpr up,by simpa using (inv_lt_inv₀ zp (inv_pos.mpr pos)).mpr h⟩

/-- Holomorphic inversion on the punctured plane, viewed as a partial chart. -/
private noncomputable def punctured_plane_inversion : OpenPartialHomeomorph ℂ ℂ where
  toFun := fun z => z⁻¹
  invFun := fun z => z⁻¹
  source := {0}ᶜ
  target := {0}ᶜ
  map_source' := fun _ h => inv_ne_zero h
  map_target' := fun _ h => inv_ne_zero h
  left_inv' := fun z _ => inv_inv z
  right_inv' := fun z _ => inv_inv z
  open_source := isOpen_compl_singleton
  open_target := isOpen_compl_singleton
  continuousOn_toFun := fun _ h => (continuousAt_inv₀ h).continuousWithinAt
  continuousOn_invFun := fun _ h => (continuousAt_inv₀ h).continuousWithinAt

theorem puncture_reciprocal_chart {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    (e : OpenPartialHomeomorph M ℂ) (hol : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    (nz : ∀ z∈e.target, z≠0) :
    ∃ d : OpenPartialHomeomorph M ℂ, d.source=e.source ∧ (∀ x, d x=(e x)⁻¹) ∧
      (∀ w, w∈d.target ↔ w≠0 ∧ w⁻¹∈e.target) ∧ d∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := by
  let d := e.trans punctured_plane_inversion
  have es : d.source=e.source := by
    ext x
    change (x∈e.source ∧ e x≠0) ↔ x∈e.source
    exact ⟨And.left,fun h => ⟨h,nz _ (e.map_source h)⟩⟩
  have inv {w : ℂ} (hw : w≠0) : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun z : ℂ => z⁻¹) w :=
    contMDiffAt_iff_contDiffAt.mpr (analyticAt_id.inv hw).contDiffAt
  refine ⟨d,es,fun _ => rfl,fun _ => Iff.rfl,d.mem_maximalAtlas_of_contMDiffOn ?_ ?_⟩
  · intro x hx
    exact ((inv hx.2).comp x (contMDiffAt_of_mem_maximalAtlas hol hx.1)).contMDiffWithinAt
  · intro w hw
    exact ((contMDiffAt_symm_of_mem_maximalAtlas hol hw.2).comp w (inv hw.1)).contMDiffWithinAt

/-- Restrict a cofinal lower radial collar to its exact finite annulus.
Its compact complement is obtained from the cocompact filter. -/
theorem holomorphic_lower_end_collar {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] (e : OpenPartialHomeomorph M ℂ)
    (hol : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) (core : IsCompact e.sourceᶜ)
    {r m : ℝ} (lt : r<m) (round : ∀ z : ℂ, ‖z‖≤m → (z∈e.target ↔ r<‖z‖))
    (side : ∀ᶠ x in cocompact M, ‖e x‖<m) :
    ∃ d : OpenPartialHomeomorph M ℂ, d∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M ∧ IsCompact d.sourceᶜ ∧
      d.target={z : ℂ | r<‖z‖ ∧ ‖z‖<m} ∧ Tendsto (fun x => ‖d x‖) (cocompact M) (𝓝 r) := by
  let d := e.trans (OpenPartialHomeomorph.ofSet (ball (0:ℂ) m) isOpen_ball)
  have mem : e.source∈cocompact M := by simpa only [compl_compl] using core.compl_mem_cocompact
  have ev : d.source∈cocompact M := by
    filter_upwards [mem,side] with x hx h
    exact ⟨hx,by simpa using h⟩
  obtain ⟨K,k,sub⟩ := mem_cocompact'.mp ev
  refine ⟨d,d.mem_maximalAtlas_of_contMDiffOn ?_ ?_,k.of_isClosed_subset d.open_source.isClosed_compl sub,?_,
    end_chart_reaches_lower_radius e core lt round side⟩
  · exact fun _ h => (contMDiffAt_of_mem_maximalAtlas hol h.1).contMDiffWithinAt
  · exact fun _ h => (contMDiffAt_symm_of_mem_maximalAtlas hol h.2).contMDiffWithinAt
  · ext z
    change (dist z 0<m ∧ z∈e.target) ↔ (r<‖z‖ ∧ ‖z‖<m)
    rw [dist_zero_right]
    exact ⟨fun h => ⟨(round z h.1.le).mp h.2,h.1⟩,fun h => ⟨h.2,(round z h.2.le).mpr h.1⟩⟩

/-- A one-ended surface picks just one of the two annular quotient
boundaries. Either choice gives a holomorphic cofinal round collar. -/
theorem one_ended_round_chart_collar {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] (tails : HasConnectedCompactTails M)
    (e : OpenPartialHomeomorph M ℂ) (core : IsCompact e.sourceᶜ)
    (hol : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) (round : IsRoundCylinderTarget e.target) :
    ∃ (d : OpenPartialHomeomorph M ℂ) (r R : ℝ), 0≤r ∧ r<R ∧
      d∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M ∧ IsCompact d.sourceᶜ ∧
      d.target={z : ℂ | r<‖z‖ ∧ ‖z‖<R} ∧ Tendsto (fun x => ‖d x‖) (cocompact M) (𝓝 r) := by
  obtain ⟨m,r,s,hm,hr,rm,hs,sm,low,high⟩ := round.collars
  have circle : sphere (0:ℂ) m⊆e.target := fun z hz => by
    have norm : ‖z‖=m := by simpa only [mem_sphere,dist_zero_right] using hz
    exact (low z norm.le).mpr (norm.symm ▸ rm)
  rcases end_chart_eventually_one_side tails e core m circle with inward|outward
  · obtain ⟨d,c,k,t,l⟩ := holomorphic_lower_end_collar e hol core rm low inward
    exact ⟨d,r,m,hr,rm,c,k,t,l⟩
  · obtain ⟨a,src,val,tgt,ah⟩ := puncture_reciprocal_chart e hol round.excludes_zero
    have side : ∀ᶠ x in cocompact M, ‖a x‖<m⁻¹ := outward.mono fun x h => by
      rw [val,norm_inv]
      exact (inv_lt_inv₀ (hm.trans h) hm).mpr h
    obtain ⟨d,c,k,t,l⟩ := holomorphic_lower_end_collar a ah (by rw [src]; exact core) sm
      (fun z hz => (tgt z).trans (high z hz)) side
    exact ⟨d,s,m⁻¹,hs,sm,c,k,t,l⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.one_ended_round_chart_collar
