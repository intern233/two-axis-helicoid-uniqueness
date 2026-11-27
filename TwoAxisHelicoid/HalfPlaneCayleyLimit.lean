import TwoAxisHelicoid.HalfPlaneCrosscutOscillation
import TwoAxisHelicoid.BoundaryCutConvergence
import TwoAxisHelicoid.BoundaryCayleyCoordinate
import TwoAxisHelicoid.DiskMobiusDistance

namespace TwoAxisHelicoid
open Set Metric Filter Complex Bornology Topology
open scoped Topology

/-- Compactness selects a common cluster point for small square
crosscuts. The same point then controls every approach to the boundary
point of the half-plane. -/
theorem univalent_half_plane_boundary_limit {W : Set ℂ} (compact : IsCompact (closure W))
    (sides : ∀ x∈closure W, ∀ G : Set ℂ, IsOpen G → x∈G →
      ∃ O : Set ℂ, IsOpen O ∧ x∈O ∧ O⊆G ∧ IsPreconnected (O∩W))
    {f : ℂ → ℂ} (an : AnalyticOnNhd ℂ f rightPlaneDomain) (e : rightPlaneDomain ≃ₜ W)
    (rep : ∀ z, (e z).1=f z.1) :
    ∃ q∈closure W, ∀ L : Filter rightPlaneDomain, Tendsto (fun z : rightPlaneDomain => z.1) L (𝓝 0) →
      Tendsto (fun z : rightPlaneDomain => f z.1) L (𝓝 q) := by
  have mem {z : ℂ} (hz : z∈rightPlaneDomain) : f z∈W := rep ⟨z,hz⟩ ▸ (e ⟨z,hz⟩).2
  have bounded : IsBounded (f '' rightPlaneDomain) := compact.isBounded.subset
    (image_subset_iff.mpr fun _ hz => subset_closure (mem hz))
  have inject : InjOn f rightPlaneDomain := by
    intro x hx y hy eq
    have same : e ⟨x,hx⟩=e ⟨y,hy⟩ := Subtype.ext ((rep ⟨x,hx⟩).trans (eq.trans (rep ⟨y,hy⟩).symm))
    exact congrArg Subtype.val (e.injective same)
  let α := fun n : ℕ => 1/((n:ℝ)+1)
  have ap (n : ℕ) : 0<α n := by dsimp [α]; positivity
  choose r rp rd osc using fun n => half_plane_square_cut_small an inject bounded (ap n) (ap n)
  obtain ⟨q,hq,k,mono,lim⟩ := compact.tendsto_subseq (x:=fun n => f (r n:ℂ))
    (fun n => subset_closure (mem (z:=(r n:ℂ)) (rp n)))
  have scale : Tendsto (α ∘ k) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat.comp mono.tendsto_atTop
  let g := fun z : rightPlaneDomain => max z.1.re |z.1.im|
  have cuts (ε δ : ℝ) (ep : 0<ε) (dp : 0<δ) : ∃ s : ℝ, 0<s ∧ s<δ ∧ ∀ x, g x=s → (e x).1∈ball q ε := by
    obtain ⟨n,near,tiny⟩ := ((lim.eventually (ball_mem_nhds q (half_pos ep))).and
      (scale.eventually (Iio_mem_nhds (lt_min dp (half_pos ep))))).exists
    have small : α (k n)<min δ (ε/2) := tiny
    refine ⟨r (k n),rp _,(rd _).trans (small.trans_le (min_le_left _ _)),?_⟩
    intro z edge
    rw [rep,mem_ball]
    have left := osc (k n) z.1 z.2 edge
    have right : dist (f (r (k n):ℂ)) q<ε/2 := near
    linarith [dist_triangle (f z.1) (f (r (k n):ℂ)) q,small.trans_le (min_le_right _ _)]
  refine ⟨q,hq,?_⟩
  intro L atZero
  have cg : Continuous g := (continuous_re.comp continuous_subtype_val).max (continuous_im.comp continuous_subtype_val).abs
  have tend : Tendsto g L (𝓝 0) := by
    have h := ((continuous_re.continuousAt (x:=0)).tendsto.comp atZero).max
      (((continuous_im.continuousAt (x:=0)).tendsto.comp atZero).abs)
    simpa [g,Function.comp_def] using h
  exact (boundary_convergence_of_shrinking_cuts compact e g cg (fun x => x.2.trans_le (le_max_left _ _))
    sides (fun ε ep δ dp => cuts ε δ ep dp) tend).congr (fun x => rep x)

/-- The Cayley coordinate based at the opposite end of the diameter
sends the selected point of the unit circle to zero in the right half-plane. -/
noncomputable def boundaryDiskToRightPlane (u : ℂ) (hu : ‖u‖=1) : complexUnitDisk ≃ₜ rightPlaneDomain where
  toFun := fun z => ⟨boundaryCayley u z.1,boundaryCayley_right hu (mem_ball_zero_iff.mp z.2)⟩
  invFun := fun z => ⟨boundaryCayleyInv u z.1,mem_ball_zero_iff.mpr (boundaryCayleyInv_disk hu z.2)⟩
  left_inv := fun z => Subtype.ext (boundaryCayley_left_inv hu (mem_ball_zero_iff.mp z.2))
  right_inv := fun z => Subtype.ext (boundaryCayley_right_inv hu z.2)
  continuous_toFun := (continuous_iff_continuousAt.mpr fun x =>
    (boundaryCayley_analytic hu (mem_ball_zero_iff.mp x.2)).continuousAt.comp continuous_subtype_val.continuousAt).subtype_mk _
  continuous_invFun := (continuous_iff_continuousAt.mpr fun x =>
    (boundaryCayleyInv_analytic x.2).continuousAt.comp continuous_subtype_val.continuousAt).subtype_mk _

/-- A holomorphic disk parameter onto a relatively compact plane
domain with connected interior sides has a limit at every boundary
point of the parameter disk. -/
theorem disk_parameter_circle_limits {W : Set ℂ} (compact : IsCompact (closure W))
    (sides : ∀ x∈closure W, ∀ G : Set ℂ, IsOpen G → x∈G →
      ∃ O : Set ℂ, IsOpen O ∧ x∈O ∧ O⊆G ∧ IsPreconnected (O∩W))
    {f : ℂ → ℂ} (an : AnalyticOnNhd ℂ f complexUnitDisk) (e : complexUnitDisk ≃ₜ W)
    (rep : ∀ z, (e z).1=f z.1) {ζ : ℂ} (hz : ‖ζ‖=1) :
    ∃ q∈closure W, Tendsto f (𝓝[complexUnitDisk] ζ) (𝓝 q) := by
  let u := -ζ
  have hu : ‖u‖=1 := (norm_neg ζ).trans hz
  let c := boundaryDiskToRightPlane u hu
  let h := f ∘ boundaryCayleyInv u
  have ah : AnalyticOnNhd ℂ h rightPlaneDomain := fun z hz =>
    (an _ (mem_ball_zero_iff.mpr (boundaryCayleyInv_disk hu hz))).comp (boundaryCayleyInv_analytic hz)
  obtain ⟨q,hq,lim⟩ := univalent_half_plane_boundary_limit compact sides ah (c.symm.trans e)
    (fun z => rep (c.symm z))
  let L := comap (Subtype.val : complexUnitDisk → ℂ) (𝓝 ζ)
  have nz : u-ζ≠0 := by
    intro eq
    have zz : ζ=0 := by dsimp [u] at eq; linear_combination -eq/2
    simp [zz] at hz
  have atz : ContinuousAt (boundaryCayley u) ζ :=
    (continuousAt_const.add continuousAt_id).div (continuousAt_const.sub continuousAt_id) nz
  have van : boundaryCayley u ζ=0 := by simp [boundaryCayley,u]
  have zero : Tendsto (fun z : rightPlaneDomain => z.1) (map c L) (𝓝 0) := by
    rw [tendsto_map'_iff,← van]
    exact atz.tendsto.comp tendsto_comap
  refine ⟨q,hq,?_⟩
  have converges := (tendsto_map'_iff.mp (lim (map c L) zero)).congr (f₂:=fun z : complexUnitDisk => f z.1) (fun z =>
    congrArg f (boundaryCayley_left_inv hu (mem_ball_zero_iff.mp z.2)))
  have eq : map (Subtype.val : complexUnitDisk → ℂ) L=𝓝[complexUnitDisk] ζ := by
    dsimp only [L]
    rw [Filter.map_comap,Subtype.range_val,nhdsWithin]
  rw [← eq,tendsto_map'_iff]
  exact converges

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.univalent_half_plane_boundary_limit
#print axioms TwoAxisHelicoid.disk_parameter_circle_limits
