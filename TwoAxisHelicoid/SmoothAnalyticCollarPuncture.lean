import TwoAxisHelicoid.SmoothRoundAnnulus
import TwoAxisHelicoid.PuncturedEndInverseEscape

namespace TwoAxisHelicoid
open Set Filter Topology Metric
open scoped Topology ContDiff Manifold

/-- A finite or infinite modulus end collar yields a smooth punctured
disk coordinate. On the outer part it agrees with the original
holomorphic chart in both directions. -/
theorem real_smooth_puncture_of_round_collar {M : Type*} [TopologicalSpace M] [T2Space M]
    [WeaklyLocallyCompactSpace M] [NoncompactSpace M]
    (c : OpenPartialHomeomorph M ℂ) {r s R : ℝ} (hr : 0≤r) (rs : r<s) (sr : s<R)
    (core : IsCompact c.sourceᶜ) (target : c.target={z : ℂ | r<‖z‖ ∧ ‖z‖<R})
    (lim : Tendsto (fun x => ‖c x‖) (cocompact M) (𝓝 r)) :
    ∃ (E : PuncturedComplexEnd M) (d : OpenPartialHomeomorph ℂ ℂ), E.radius=R ∧
      E.coord=c.trans d ∧ E.coord.source=c.source ∧ d.source=c.target ∧
      (∀ z∈d.source, ContDiffAt ℝ ∞ d z) ∧ (∀ z∈d.target, ContDiffAt ℝ ∞ d.symm z) ∧
      (∀ z : ℂ, s≤‖z‖ → d z=z) ∧ (∀ z : ℂ, s≤‖z‖ → d.symm z=z) := by
  obtain ⟨f,d,fr,ds,dt,fw,bw,fixed,back⟩ := smooth_round_annulus_puncture hr rs sr
  have ds' : d.source=c.target := ds.trans target.symm
  let k := c.trans d
  have src : k.source=c.source := by
    ext x
    change (x∈c.source ∧ c x∈d.source) ↔ x∈c.source
    exact ⟨And.left,fun h => ⟨h,ds' ▸ c.map_source h⟩⟩
  have image : k.target=ball (0:ℂ) R \ {0} := by
    ext z
    change (z∈d.target ∧ d.symm z∈c.target) ↔ dist z 0<R ∧ z≠0
    rw [dist_zero_right]
    constructor
    · rintro ⟨h,_⟩
      rw [dt] at h
      exact ⟨h.2,norm_pos_iff.mp h.1⟩
    · rintro ⟨h,nz⟩
      have domain : z∈d.target := dt ▸ ⟨norm_pos_iff.mpr nz,h⟩
      exact ⟨domain,ds' ▸ d.map_target domain⟩
  have tail : c.source∈cocompact M := by simpa only [compl_compl] using core.compl_mem_cocompact
  have hlim : Tendsto k (cocompact M) (𝓝 (0:ℂ)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have cmp : Tendsto (fun x => f ‖c x‖) (cocompact M) (𝓝 0) := fr ▸ f.continuous.continuousAt.tendsto.comp lim
    apply cmp.congr'
    filter_upwards [tail] with x hx
    exact (fw (c x) (ds' ▸ c.map_source hx)).1.symm
  let E := puncturedComplexEndOfChart k (hr.trans_lt (rs.trans sr)) image (src ▸ core) hlim
  exact ⟨E,d,rfl,rfl,src,ds',fun z h => (fw z h).2,fun z h => (bw z h).2,fixed,back⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.real_smooth_puncture_of_round_collar

