import TwoAxisHelicoid.PlaneOrientationProbe

namespace TwoAxisHelicoid
open Complex Set Function Filter Topology Metric
open scoped Topology

theorem HasPlaneOrientationAt.congr {f g : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hf : HasPlaneOrientationAt f p n) (he : g =ᶠ[𝓝 p] f) : HasPlaneOrientationAt g p n := by
  obtain ⟨R,hR,hf⟩ := hf
  obtain ⟨S,hS,hb⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨min R S,lt_min hR hS,fun r hr => ?_⟩
  have heq : planeOrientationProbe g p r = planeOrientationProbe f p r := by
    funext a
    unfold planeOrientationProbe
    rw [hb (orientation_probe_point_mem_ball ⟨hr.1,hr.2.trans_le (min_le_right _ _)⟩ a),he.self_of_nhds]
  rw [heq]
  exact hf _ ⟨hr.1,hr.2.trans_le (min_le_left _ _)⟩

theorem planeOrientation_identity (p : ℂ) : HasPlaneOrientationAt id p 1 := by
  refine ⟨1,one_pos,fun r hr => ?_⟩
  have he : planeOrientationProbe id p r = id := by
    funext a
    change planeOrientationDirection ((p+r • orientationRay a)-p) = a
    rw [add_sub_cancel_left,planeOrientationDirection_scaled_ray hr.1]
  rw [he]
  exact orientationCircle_degree_id

/-- Varying the radius of each input ray changes a composite link
continuously into the composition of the two normalized circle maps. -/
theorem circle_degree_of_radial_composition {g : ℂ → ℂ} {q : ℂ} {T s : ℝ}
    (hs : s ∈ Ioo 0 T) (hg : ContinuousOn g (ball q T)) (hj : InjOn g (ball q T))
    {v : OrientationCircle → ℂ} (hv : Continuous v) (hn : ∀ a, v a ≠ 0) (hb : ∀ a, ‖v a‖ < T)
    {m n : ℤ} (hm : HasOrientationCircleDegree (planeOrientationProbe g q s) m)
    (hd : HasOrientationCircleDegree (fun a => planeOrientationDirection (v a)) n) :
    HasOrientationCircleDegree (fun a => planeOrientationDirection (g (q+v a)-g q)) (m*n) := by
  let a' := fun a => planeOrientationDirection (v a)
  have ha : Continuous a' := continuous_iff_continuousAt.mpr fun a =>
    (planeOrientationDirection_continuousAt (hn a)).comp hv.continuousAt
  let ρ := fun x : ℝ × OrientationCircle => orientationInterpolate x.1 ‖v x.2‖ s
  have hρ : Continuous ρ :=
    (((continuous_const.sub (orientationBlend_continuous.comp continuous_fst)).mul (hv.comp continuous_snd).norm).add
      ((orientationBlend_continuous.comp continuous_fst).mul continuous_const))
  have hmem (x : ℝ × OrientationCircle) : ρ x ∈ Ioo 0 T :=
    orientationInterpolate_mem ⟨norm_pos_iff.mpr (hn x.2),hb x.2⟩ hs x.1
  let K := fun x : ℝ × OrientationCircle => planeOrientationProbe g q (ρ x) (a' x.2)
  have hc : Continuous K := continuous_planeOrientationProbe_family hg hj continuous_const hρ (ha.comp continuous_snd)
    (fun x => (hmem x).1) (fun _ => mem_ball_self (hs.1.trans hs.2)) (fun x => orientation_probe_point_mem_ball (hmem x) _)
  have h1 : HasOrientationCircleDegree (fun a => K (1,a)) (m*n) := by
    simpa only [K,ρ,a',orientationInterpolate_one,Function.comp_def] using hm.comp hd
  have h0 := h1.family (t := 0) hc
  have he : (fun a => K (0,a)) = fun a => planeOrientationDirection (g (q+v a)-g q) := by
    funext a
    simp only [K,ρ,a',orientationInterpolate_zero,planeOrientationProbe,planeOrientationDirection_reconstruct (hn a)]
  rwa [he] at h0

theorem openPartialHomeomorph_plane_orientation_exists (e : OpenPartialHomeomorph ℂ ℂ) {p : ℂ}
    (hp : p ∈ e.source) : ∃ n, HasPlaneOrientationAt e p n := by
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds hp)
  obtain ⟨n,hn⟩ := orientation_probe_radius_degree hR (e.continuousOn.mono hsub) (e.injOn.mono hsub)
  exact ⟨n,R,hR,hn⟩

theorem openPartialHomeomorph_plane_orientation_comp (e d : OpenPartialHomeomorph ℂ ℂ)
    {p : ℂ} (hp : p ∈ e.source) (hq : e p ∈ d.source) {m n : ℤ}
    (hm : HasPlaneOrientationAt d (e p) m) (hn : HasPlaneOrientationAt e p n) :
    HasPlaneOrientationAt (d ∘ e) p (m*n) := by
  obtain ⟨B,hB,hb⟩ := Metric.mem_nhds_iff.mp (d.open_source.mem_nhds hq)
  obtain ⟨S,hS,hs⟩ := hm
  obtain ⟨R,hR,hr⟩ := hn
  let s := min S B/2
  have hsp : 0 < s := half_pos (lt_min hS hB)
  have hs' : s < min S B := half_lt_self (lt_min hS hB)
  have he : e.source ∩ e ⁻¹' ball (e p) B ∈ 𝓝 p :=
    inter_mem (e.open_source.mem_nhds hp) ((e.continuousAt hp).eventually (ball_mem_nhds _ hB))
  obtain ⟨U,hU,hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨min R U,lt_min hR hU,fun r hru => ?_⟩
  let v := fun a => e (p+r • orientationRay a)-e p
  have heU (a : OrientationCircle) := hsub (orientation_probe_point_mem_ball
    ⟨hru.1,hru.2.trans_le (min_le_right _ _)⟩ a)
  have hT : Continuous (fun a => p+r • orientationRay a) :=
    (continuous_const (y := p)).add ((continuous_const (y := r)).smul orientationRay_continuous)
  have hv : Continuous v := (e.continuousOn.comp_continuous hT (fun a => (heU a).1)).sub (continuous_const (y := e p))
  have hne (a : OrientationCircle) : v a ≠ 0 := by
    intro hz
    have heq := e.injOn (heU a).1 hp (sub_eq_zero.mp hz)
    exact smul_ne_zero hru.1.ne' (orientationRay_ne_zero _) (add_eq_left.mp heq)
  have hh := circle_degree_of_radial_composition ⟨hsp,hs'.trans_le (min_le_right _ _)⟩
    (d.continuousOn.mono hb) (d.injOn.mono hb) hv hne
    (fun a => by simpa only [v,← dist_eq_norm] using (show dist (e (p+r • orientationRay a)) (e p) < B from (heU a).2))
    (hs _ ⟨hsp,hs'.trans_le (min_le_left _ _)⟩) (hr _ ⟨hru.1,hru.2.trans_le (min_le_left _ _)⟩)
  change HasOrientationCircleDegree (fun a => planeOrientationDirection (d (e (p+r • orientationRay a))-d (e p))) (m*n)
  simpa only [v,add_sub_cancel] using hh

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.openPartialHomeomorph_plane_orientation_comp
