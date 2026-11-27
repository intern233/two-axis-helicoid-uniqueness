import TwoAxisHelicoid.SurfaceHarmonicComparison
import TwoAxisHelicoid.PoissonDiskBoundary
import Mathlib.Topology.Piecewise

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology Function InnerProductSpace
open scoped Topology ContDiff Manifold

/-- At a contact point, increasing a subharmonic function without
changing its value preserves the strong harmonic comparison property
whenever the new function is continuous. -/
theorem surface_subharmonic_of_touch_below {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {x : M} {f g : M → ℝ} (sf : SurfaceSubharmonicAt f x) (cg : ContinuousAt g x) (le : f≤g) (eq : g x=f x) :
    SurfaceSubharmonicAt g x := by
  refine ⟨cg,?_⟩
  intro h hh mx
  have m : IsLocalMax (fun y => f y-h y) x := by
    filter_upwards [mx] with y hy
    change g y-h y≤g x-h x at hy
    exact (sub_le_sub_right (le y) _).trans (eq ▸ hy)
  filter_upwards [mx,sf.2 h hh m] with y hy same
  exact le_antisymm hy (by rw [eq,← same]; exact sub_le_sub_right (le y) _)

/-- Actual Poisson modification on a closed coordinate disk. The
modified global function majorizes the old one, preserves intrinsic
subharmonicity across the entire circle and is harmonic on its interior. -/
theorem harmonic_replacement_on_chart_disk {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M] [NoncompactSpace M]
    {e : OpenPartialHomeomorph M ℂ} (chart : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    {c : ℂ} {r : ℝ} (rp : 0<r) (domain : closedBall c r⊆e.target)
    {u : M → ℝ} (sub : ∀ x, SurfaceSubharmonicAt u x) :
    ∃ v : M → ℝ, (∀ x, SurfaceSubharmonicAt v x) ∧ u≤v ∧
      EqOn v u (e.symm '' ball c r)ᶜ ∧ HarmonicOnNhd (v ∘ e.symm) (ball c r) := by
  classical
  let B := ball c r
  let D := e.symm '' B
  let K := e.symm '' closedBall c r
  have uniq : D⊆K := image_mono ball_subset_closedBall
  have inside : K⊆e.source := by rintro _ ⟨z,hz,rfl⟩; exact e.map_target (domain hz)
  have disk : IsOpen D := e.symm.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans domain)
  have compact : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn (e.symm.continuousOn.mono domain)
  have clos : closure D⊆K := closure_minimal uniq compact.isClosed
  have cu : Continuous u := continuous_iff_continuousAt.mpr fun x => (sub x).1
  obtain ⟨H,hH,cH,bH⟩ := continuous_disk_dirichlet_solution rp
    ((cu.comp_continuousOn e.symm.continuousOn).mono (sphere_subset_closedBall.trans domain))
  let v := D.piecewise (H ∘ e) u
  have outside (x : M) (hx : x∉D) : v x=u x := piecewise_eq_of_notMem _ _ _ hx
  have atD (x : M) (hx : x∈D) : v =ᶠ[𝓝 x] H ∘ e := by
    filter_upwards [disk.mem_nhds hx] with y hy using piecewise_eq_of_mem _ _ _ hy
  have image (x : M) (hx : x∈K) : e x∈closedBall c r := by
    obtain ⟨z,hz,rfl⟩ := hx
    rwa [e.right_inv (domain hz)]
  have imageD (x : M) (hx : x∈D) : e x∈B := by
    obtain ⟨z,hz,rfl⟩ := hx
    rwa [e.right_inv (domain (ball_subset_closedBall hz))]
  have cv : Continuous v := by
    apply continuous_piecewise _ (cH.comp (e.continuousOn.mono (clos.trans inside)) (fun x hx => image x (clos hx))) cu.continuousOn
    intro x hx
    have kx := clos (frontier_subset_closure hx)
    have out : x∉D := by rw [disk.frontier_eq] at hx; exact hx.2
    have eb : e x∈sphere c r := by
      apply le_antisymm (mem_closedBall.mp (image x kx))
      by_contra! h
      exact out ⟨e x,h,e.left_inv (inside kx)⟩
    exact (bH eb).trans (congrArg u (e.left_inv (inside kx)))
  have inner (x : M) (hx : x∈D) : SurfaceHarmonicGerm v x := by
    have xs := inside (uniq hx)
    apply (surface_harmonic_germ_in_chart chart xs).mpr
    have back : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by simpa only [e.left_inv xs] using (e.symm.continuousAt (e.map_source xs)).tendsto
    apply (harmonicAt_congr_nhds (f₂:=H) ?_).mpr (hH _ (imageD x hx))
    filter_upwards [back.eventually (atD x hx),e.open_target.mem_nhds (e.map_source xs)] with z hz ht
    exact hz.trans (congrArg H (e.right_inv ht))
  have major : u≤v := by
    intro x
    by_cases hx : x∈D
    · apply sub_nonpos.mp
      apply compact_boundary_maximum_principle compact (cu.sub cv).continuousOn _ _ x (uniq hx)
      · intro y _ bd
        change u y-v y≤0
        rw [outside y (fun yd => bd (mem_interior_iff_mem_nhds.mpr (mem_of_superset (disk.mem_nhds yd) uniq))),sub_self]
      · intro y _ pos mx
        have yd : y∈D := by
          by_contra out
          exact (sub_pos.mp pos).ne (outside y out)
        exact (sub y).2 v (inner y yd) mx
    · rw [outside x hx]
  refine ⟨v,fun x => ?_,major,fun x hx => outside x hx,?_⟩
  · by_cases xd : x∈D
    · exact (inner x xd).subharmonicAt
    · exact surface_subharmonic_of_touch_below (sub x) cv.continuousAt major (outside x xd)
  · intro z hz
    have tx := domain (ball_subset_closedBall hz)
    have hg := (surface_harmonic_germ_in_chart chart (e.map_target tx)).mp (inner (e.symm z) (mem_image_of_mem _ hz))
    rwa [e.right_inv tx] at hg

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_replacement_on_chart_disk
