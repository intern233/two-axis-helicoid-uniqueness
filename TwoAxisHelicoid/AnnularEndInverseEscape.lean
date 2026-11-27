import TwoAxisHelicoid.ComplexExteriorConnected
import TwoAxisHelicoid.PuncturedEndInverseEscape

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

theorem complex_open_annulus_isPreconnected {r R : ℝ} (hr : 0≤r) :
    IsPreconnected {z : ℂ | r<‖z‖ ∧ ‖z‖<R} := by
  have rank : 1<Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank,Complex.finrank_real_complex]
    norm_num
  have conn := (isPreconnected_sphere rank (0:ℂ) 1).prod
    (isPreconnected_Ioo : IsPreconnected (Ioo r R))
  have eq : (fun p : ℂ × ℝ => p.2 • p.1) '' (sphere (0:ℂ) 1 ×ˢ Ioo r R) =
      {z : ℂ | r<‖z‖ ∧ ‖z‖<R} := by
    ext z
    constructor
    · rintro ⟨⟨w,s⟩,⟨hw,hs⟩,rfl⟩
      have unit : ‖w‖=1 := by simpa only [mem_sphere,dist_zero_right] using hw
      change r<‖s • w‖ ∧ ‖s • w‖<R
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (hr.trans_lt hs.1),unit,mul_one] using (show r<s ∧ s<R from hs)
    · intro hz
      have nz := (hr.trans_lt hz.1).ne'
      refine ⟨((‖z‖⁻¹:ℝ) • z,‖z‖),⟨?_,hz⟩,?_⟩
      · change dist ((‖z‖⁻¹:ℝ) • z) 0=1
        rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)),inv_mul_cancel₀ nz]
      · change ‖z‖ • ((‖z‖⁻¹:ℝ) • z)=z
        rw [smul_smul,mul_inv_cancel₀ nz,one_smul]
  rw [← eq]
  exact conn.image _ (continuous_snd.smul continuous_fst).continuousOn

/-- For an annular collar of a one-ended surface, identifying which
boundary the coordinates approach already gives uniform escape from
compact sets in the reverse direction. -/
theorem annular_end_inverse_escapes {M : Type*} [TopologicalSpace M] [T2Space M]
    [WeaklyLocallyCompactSpace M] [NoncompactSpace M]
    (e : OpenPartialHomeomorph M ℂ) {r R : ℝ} (hr : 0≤r) (lt : r<R)
    (target : e.target={z : ℂ | r<‖z‖ ∧ ‖z‖<R}) (core : IsCompact e.sourceᶜ)
    (toRadius : Tendsto (fun x => ‖e x‖) (cocompact M) (𝓝 r))
    {K : Set M} (hK : IsCompact K) :
    ∃ s>r, ∀ z : ℂ, r<‖z‖ → ‖z‖<s → e.symm z∉K := by
  obtain ⟨D,hD,encl⟩ := exists_compact_superset (hK.union core)
  let B := D \ interior D
  have cb : IsCompact B := hD.inter_right isOpen_interior.isClosed_compl
  have src : B ⊆ e.source := fun x hx => by
    by_contra hn
    exact hx.2 (encl (Or.inr hn))
  let C := (fun x => ‖e x‖) '' B
  have cc : IsCompact C := cb.image_of_continuousOn (e.continuousOn.mono src).norm
  have avoid : r∉C := by
    rintro ⟨x,hx,eq⟩
    have dom := e.map_source (src hx)
    rw [target] at dom
    exact (dom.1.ne') eq
  obtain ⟨d,hd,ballSub⟩ := Metric.mem_nhds_iff.mp (cc.isClosed.isOpen_compl.mem_nhds avoid)
  let s := min R (r+d)
  have hs : r<s := lt_min lt (by linarith)
  let U := {z : ℂ | r<‖z‖ ∧ ‖z‖<s}
  have inc : U ⊆ e.target := by
    rw [target]
    exact fun z hz => ⟨hz.1,hz.2.trans_le (min_le_left _ _)⟩
  let A := e.symm '' U
  have conn : IsPreconnected A := (complex_open_annulus_isPreconnected (R := s) hr).image _
    (e.symm.continuousOn.mono inc)
  have sides : A ⊆ interior D ∪ Dᶜ := by
    rintro _ ⟨z,hz,rfl⟩
    by_contra both
    have b : e.symm z∈B := ⟨by by_contra hn; exact both (Or.inr hn),fun hi => both (Or.inl hi)⟩
    have inside : ‖z‖∈ball r d := by
      rw [mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr hz.1)]
      linarith [hz.2.trans_le (min_le_right R (r+d))]
    exact ballSub inside ⟨e.symm z,b,congrArg norm (e.right_inv (inc hz))⟩
  have tail : e.source∈cocompact M := by simpa only [compl_compl] using core.compl_mem_cocompact
  have ex : ∃ x, x∈A ∧ x∉D := by
    have ev : ∀ᶠ x in cocompact M, x∈e.source ∧ x∉D ∧ ‖e x‖<s := by
      filter_upwards [tail,hD.compl_mem_cocompact,toRadius.eventually (gt_mem_nhds hs)] with x hx hD' hlt
      exact ⟨hx,hD',hlt⟩
    obtain ⟨x,hx,nd,l⟩ := ev.exists
    have m := e.map_source hx
    rw [target] at m
    exact ⟨x,⟨e x,⟨m.1,l⟩,e.left_inv hx⟩,nd⟩
  have dis : Disjoint (interior D) Dᶜ := disjoint_compl_right.mono_left interior_subset
  rcases conn.subset_or_subset isOpen_interior hD.isClosed.isOpen_compl dis sides with inner|outer
  · obtain ⟨x,hx,hn⟩ := ex
    exact (hn (interior_subset (inner hx))).elim
  · exact ⟨s,hs,fun z hz hz' hk => outer (mem_image_of_mem _ (show z∈U from ⟨hz,hz'⟩))
      (interior_subset (encl (Or.inl hk)))⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.annular_end_inverse_escapes
