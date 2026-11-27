import TwoAxisHelicoid.PerronHarmonicReplacement
import TwoAxisHelicoid.HarmonicPerronEnvelope

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology Function InnerProductSpace
open scoped Topology ContDiff Manifold

theorem SurfaceHarmonicGerm.neg {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {x : M} {f : M → ℝ}
    (hf : SurfaceHarmonicGerm f x) : SurfaceHarmonicGerm (fun y => -f y) x := by
  obtain ⟨F,af,eq⟩ := hf
  refine ⟨fun y => -F y,af.neg,?_⟩
  filter_upwards [eq] with y hy using by simp only [hy,Complex.neg_re]

/-- A superharmonic majorant also bounds the actual Poisson
replacement, including its seam with the unaltered exterior. -/
theorem harmonic_replacement_le_superharmonic {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M] [NoncompactSpace M]
    {e : OpenPartialHomeomorph M ℂ} (chart : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    {c : ℂ} {r : ℝ} (domain : closedBall c r⊆e.target) {u v H : M → ℝ}
    (le : u≤H) (cv : Continuous v) (supH : ∀ x, SurfaceSubharmonicAt (fun y => -H y) x)
    (out : EqOn v u (e.symm '' ball c r)ᶜ) (inside : HarmonicOnNhd (v ∘ e.symm) (ball c r)) : v≤H := by
  let D := e.symm '' ball c r
  let K := e.symm '' closedBall c r
  have sub : D⊆K := image_mono ball_subset_closedBall
  have op : IsOpen D := e.symm.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans domain)
  have ck : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn (e.symm.continuousOn.mono domain)
  have bound (x : M) (d : x∉D) : v x≤H x := (out d).trans_le (le x)
  have cont : Continuous H := continuous_iff_continuousAt.mpr fun x => by
    have c : ContinuousAt (fun y => - -H y) x := (supH x).1.neg
    simpa only [neg_neg] using c
  intro x
  by_cases xd : x∈D
  · apply sub_nonpos.mp
    apply compact_boundary_maximum_principle ck (cv.sub cont).continuousOn _ _ x (sub xd)
    · intro y _ edge
      exact sub_nonpos.mpr (bound y fun yd => edge (mem_interior_iff_mem_nhds.mpr (mem_of_superset (op.mem_nhds yd) sub)))
    · intro y _ pos mx
      have yd : y∈D := by_contra fun hn => (sub_pos.mp pos).not_ge (bound y hn)
      obtain ⟨z,hz,rfl⟩ := yd
      have ht := domain (ball_subset_closedBall hz)
      have hv : SurfaceHarmonicGerm v (e.symm z) := (surface_harmonic_germ_in_chart chart (e.map_target ht)).mpr (by
        rw [e.right_inv ht]; exact inside z hz)
      have eq : (fun y => -H y- -v y)=(fun y => v y-H y) := by funext y; ring
      have res := (supH (e.symm z)).2 (fun y => -v y) hv.neg (eq.symm ▸ mx)
      filter_upwards [res] with w hw
      change v w-H w=v (e.symm z)-H (e.symm z)
      linarith
  · exact bound x xd

/-- Perron's method between continuous subharmonic and superharmonic
barriers on an open Riemann surface. The resulting function is harmonic
on the whole surface and lies between the prescribed functions. -/
theorem greatest_harmonic_minorant_of_superharmonic {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M] [NoncompactSpace M]
    {L H : M → ℝ} (lo : ∀ x, SurfaceSubharmonicAt L x) (hi : ∀ x, SurfaceSubharmonicAt (fun y => -H y) x)
    (order : L≤H) : ∃ h : M → ℝ, (∀ x, SurfaceHarmonicGerm h x) ∧ h≤H ∧
      ∀ f : M → ℝ, (∀ x, SurfaceSubharmonicAt f x) → f≤H → f≤h := by
  classical
  let A := {u : M → ℝ | (∀ x, SurfaceSubharmonicAt u x) ∧ L≤u ∧ u≤H}
  have hL : L∈A := ⟨lo,le_rfl,order⟩
  have non : A.Nonempty := ⟨L,hL⟩
  let _ : Nonempty A := non.to_subtype
  let h := fun x => ⨆ f : A, f.val x
  have bounded (x : M) : BddAbove (range (fun f : A => f.val x)) := ⟨H x,fun _ ⟨f,eq⟩ => eq ▸ f.2.2.2 x⟩
  refine ⟨h,?_,fun x => ciSup_le fun f => f.2.2.2 x,?_⟩
  swap
  · intro f sf fh x
    let g := fun y => max (f y) (L y)
    have sg : g∈A := ⟨fun y => surface_subharmonic_max (sf y) (lo y),fun _ => le_max_right _ _,
      fun y => max_le (fh y) (order y)⟩
    exact (le_max_left _ _).trans (le_ciSup (bounded x) (⟨g,sg⟩ : A))
  intro x
  let e := chartAt ℂ x
  have xs : x∈e.source := mem_chart_source ℂ x
  have chart := IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ℂ)) (n:=ω) x
  obtain ⟨r,rp,sub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (e.open_target.mem_nhds (e.map_source xs))
  have ch : Continuous H := continuous_iff_continuousAt.mpr fun z => by
    have c : ContinuousAt (fun y => - -H y) z := (hi z).1.neg
    simpa only [neg_neg] using c
  obtain ⟨a,_,mx⟩ := (isCompact_closedBall (e x) r).exists_isMaxOn ⟨e x,mem_closedBall_self rp.le⟩
    ((ch.comp_continuousOn e.symm.continuousOn).mono sub)
  apply (surface_harmonic_germ_in_chart chart xs).mpr
  apply directed_harmonic_perron_envelope non _ e.symm (c:=e x) (r:=r) (C:=H (e.symm a)) _ _ _ (mem_ball_self rp)
  · intro f hf g hg
    exact ⟨fun y => max (f y) (g y),⟨fun y => surface_subharmonic_max (hf.1 y) (hg.1 y),
      fun y => (hf.2.1 y).trans (le_max_left _ _),fun y => max_le (hf.2.2 y) (hg.2.2 y)⟩,
      fun _ => le_max_left _ _,fun _ => le_max_right _ _⟩
  · intro f hf z hz
    exact (hf.2.2 _).trans (mx (ball_subset_closedBall hz))
  · intro f hf
    obtain ⟨v,sv,dom,eq,harm⟩ := harmonic_replacement_on_chart_disk chart rp sub hf.1
    have cv := continuous_iff_continuousAt.mpr fun z => (sv z).1
    exact ⟨v,⟨sv,hf.2.1.trans dom,harmonic_replacement_le_superharmonic chart sub hf.2.2 cv hi eq harm⟩,dom,harm⟩

theorem surface_harmonic_function_between_barriers {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M] [NoncompactSpace M]
    {L H : M → ℝ} (lo : ∀ x, SurfaceSubharmonicAt L x) (hi : ∀ x, SurfaceSubharmonicAt (fun y => -H y) x)
    (order : L≤H) : ∃ h : M → ℝ, (∀ x, SurfaceHarmonicGerm h x) ∧ L≤h ∧ h≤H := by
  obtain ⟨h,hh,upper,greatest⟩ := greatest_harmonic_minorant_of_superharmonic lo hi order
  exact ⟨h,hh,greatest L lo order,upper⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.greatest_harmonic_minorant_of_superharmonic
