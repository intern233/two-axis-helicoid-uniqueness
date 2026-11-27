import TwoAxisHelicoid.BoundaryCayleyCoordinate
import TwoAxisHelicoid.DiskMobiusDistance
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace TwoAxisHelicoid
open Set Complex Metric Filter Topology
open scoped Topology

/-- A nontrivial compact-circle continuum contains a relatively open
arc. A Cayley projection, based outside the continuum, carries it to
a real interval and is injective on the rest of the circle. -/
theorem circle_continuum_contains_arc {S : Set ℂ} (part : S⊆sphere 0 1) (conn : IsPreconnected S)
    {x y : ℂ} (sx : x∈S) (sy : y∈S) (ne : x≠y) :
    ∃ O : Set ℂ, IsOpen O ∧ (O∩sphere 0 1).Nonempty ∧ O∩sphere 0 1⊆S := by
  by_cases whole : sphere (0:ℂ) 1⊆S
  · exact ⟨univ,isOpen_univ,⟨x,mem_univ _,part sx⟩,inter_subset_right.trans whole⟩
  obtain ⟨u,us,miss⟩ := not_subset.mp whole
  have hu : ‖u‖=1 := mem_sphere_zero_iff_norm.mp us
  let A := boundaryCayley u
  let g := fun z : ℂ => (A z).im
  let V : Set ℂ := {u}ᶜ
  have cv : ContinuousOn A V := by
    intro z hz
    exact ((continuousAt_const.add continuousAt_id).div (continuousAt_const.sub continuousAt_id)
      (sub_ne_zero.mpr (show u≠z from Ne.symm hz))).continuousWithinAt
  have cp : ContinuousOn g V := continuous_im.comp_continuousOn cv
  have sv : S⊆V := fun z hz eq => miss ((show z=u from eq) ▸ hz)
  have real (z : ℂ) (h : z∈sphere 0 1) : (A z).re=0 := by
    have nz : normSq z=1 := by rw [Complex.normSq_eq_norm_sq,mem_sphere_zero_iff_norm.mp h,one_pow]
    have nu : normSq u=1 := by rw [Complex.normSq_eq_norm_sq,hu,one_pow]
    change ((u+z)/(u-z)).re=0
    rw [Complex.div_re,← add_div]
    have n : (u+z).re*(u-z).re+(u+z).im*(u-z).im=0 := by
      simp only [add_re,sub_re,add_im,sub_im,normSq_apply] at *
      nlinarith
    rw [n,zero_div]
  have inject {a b : ℂ} (sa : a∈sphere 0 1) (sb : b∈sphere 0 1) (av : a∈V) (bv : b∈V) (h : g a=g b) : a=b := by
    have val : A a=A b := Complex.ext ((real a sa).trans (real b sb).symm) h
    change (u+a)/(u-a)=(u+b)/(u-b) at val
    have ea : u-a≠0 := sub_ne_zero.mpr (Ne.symm av)
    have eb : u-b≠0 := sub_ne_zero.mpr (Ne.symm bv)
    have cross := (div_eq_div_iff ea eb).mp val
    have nu : u≠0 := fun z => by simp [z] at hu
    have cancel : 2*u*(a-b)=0 := by linear_combination cross
    exact sub_eq_zero.mp ((mul_eq_zero.mp cancel).resolve_left (mul_ne_zero (by norm_num) nu))
  have distinct : g x≠g y := fun h => ne (inject (part sx) (part sy) (sv sx) (sv sy) h)
  have make {s t : ℂ} (hs : s∈S) (ht : t∈S) (lt : g s<g t) :
      ∃ O : Set ℂ, IsOpen O ∧ (O∩sphere 0 1).Nonempty ∧ O∩sphere 0 1⊆S := by
    let O := V ∩ g ⁻¹' Ioo (g s) (g t)
    have iv := conn.intermediate_value hs ht (cp.mono sv)
    obtain ⟨m,sm,eq⟩ := iv (show (g s+g t)/2∈Icc (g s) (g t) by constructor <;> linarith)
    refine ⟨O,cp.isOpen_inter_preimage isClosed_singleton.isOpen_compl isOpen_Ioo,
      ⟨m,⟨sv sm,show g m∈Ioo (g s) (g t) by rw [eq]; constructor <;> linarith⟩,part sm⟩,?_⟩
    rintro z ⟨⟨zv,zg⟩,zs⟩
    obtain ⟨w,ws,eq⟩ := iv (Ioo_subset_Icc_self zg)
    exact inject (part ws) zs (sv ws) zv eq ▸ ws
  rcases lt_or_gt_of_ne distinct with h|h
  · exact make sx sy h
  · exact make sy sx h

/-- A continuous disk function holomorphic in the interior cannot
vanish on an open boundary arc while remaining nonzero at its center.
Finitely many rotations of the arc cover the circle. The product of
the rotated functions then vanishes on the whole boundary. -/
theorem disk_arc_zero_at_center {f : ℂ → ℂ} (an : AnalyticOnNhd ℂ f complexUnitDisk)
    (cont : ContinuousOn f (closedBall 0 1)) {O : Set ℂ} (op : IsOpen O)
    (hit : (O∩sphere 0 1).Nonempty) (zero : ∀ z∈O∩sphere 0 1, f z=0) : f 0=0 := by
  classical
  obtain ⟨w,ow,hw⟩ := hit
  let A := sphere (0:ℂ) 1
  let cover := fun a : A => (fun z : ℂ => a.1*z) ⁻¹' O
  have rotate (z : ℂ) (a : A) : ‖a.1*z‖=‖z‖ := by rw [norm_mul,mem_sphere_zero_iff_norm.mp a.2,one_mul]
  have each : ∀ a, IsOpen (cover a) := fun a => op.preimage (continuous_const.mul continuous_id)
  have all : A⊆⋃ a, cover a := by
    intro x hx
    have n : ‖x‖=1 := mem_sphere_zero_iff_norm.mp hx
    have nz : x≠0 := fun eq => by simp [eq] at n
    let a : A := ⟨w/x,mem_sphere_zero_iff_norm.mpr (by rw [norm_div,mem_sphere_zero_iff_norm.mp hw,n,div_one])⟩
    refine mem_iUnion.mpr ⟨a,?_⟩
    change w/x*x∈O
    rwa [div_mul_cancel₀ _ nz]
  obtain ⟨T,tiles⟩ := (isCompact_sphere (0:ℂ) 1).elim_finite_subcover cover each all
  let F := fun z : ℂ => ∏ a ∈ T, f (a.1*z)
  have hol : AnalyticOnNhd ℂ F complexUnitDisk := fun z hz => T.analyticAt_fun_prod fun a _ =>
    (an _ (mem_ball_zero_iff.mpr ((rotate z a).symm ▸ mem_ball_zero_iff.mp hz))).comp (analyticAt_const.mul analyticAt_id)
  have cf : ContinuousOn F (closedBall 0 1) := continuousOn_finsetProd T fun a _ =>
    cont.comp (continuous_const.mul continuous_id).continuousOn (fun z hz =>
      mem_closedBall_zero_iff.mpr ((rotate z a).symm ▸ mem_closedBall_zero_iff.mp hz))
  have bd : ∀ z∈frontier complexUnitDisk, ‖F z‖≤0 := by
    intro z hz
    have zs : z∈A := by simpa only [complexUnitDisk,frontier_ball (0:ℂ) (one_ne_zero : (1:ℝ)≠0)] using hz
    obtain ⟨a,mem⟩ := mem_iUnion.mp (tiles zs)
    obtain ⟨at',az⟩ := mem_iUnion.mp mem
    have p : F z=0 := Finset.prod_eq_zero at' (zero _ ⟨az,mem_sphere_zero_iff_norm.mpr ((rotate z a).trans
      (mem_sphere_zero_iff_norm.mp zs))⟩)
    simp [p]
  have max := norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (show DiffContOnCl ℂ F complexUnitDisk from ⟨hol.differentiableOn,by simpa only [complexUnitDisk,closure_ball (0:ℂ) (one_ne_zero : (1:ℝ)≠0)] using cf⟩)
    bd (subset_closure (mem_ball_self (zero_lt_one : (0:ℝ)<1)))
  by_contra non
  exact (norm_pos_iff.mpr (show F 0≠0 from Finset.prod_ne_zero_iff.mpr fun a _ => by simpa using non)).not_ge max

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.circle_continuum_contains_arc
#print axioms TwoAxisHelicoid.disk_arc_zero_at_center
