import TwoAxisHelicoid.QuarterSpatialPathBounds
import TwoAxisHelicoid.RectangleRealPartBound
import TwoAxisHelicoid.ExplicitMarkedReflections

namespace TwoAxisHelicoid
open Complex Set

/-- Four bounds for the first horizontal spatial derivative propagate
across the early rectangle. Integration up to the marked axis fixes
the sign of the actual first spatial coordinate on this rectangle. -/
theorem low_slab_early_position_from_edges
    (left : ∀ y∈Icc (0:ℝ) (7/32), quarterSpatialRate true false ⟨1/2,y⟩≤ -(1/1024:ℝ))
    (right : ∀ y∈Icc (0:ℝ) (7/32), quarterSpatialRate true false ⟨1,y⟩≤ -(1/1024:ℝ))
    (bottom : ∀ x∈Icc (1/2:ℝ) 1, quarterSpatialRate true false ⟨x,0⟩≤ -(1/1024:ℝ))
    (top : ∀ x∈Icc (1/2:ℝ) 1, quarterSpatialRate true false ⟨x,7/32⟩≤ -(1/1024:ℝ)) :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    ∀ x∈Icc (1/2:ℝ) 1, ∀ y∈Icc (0:ℝ) (7/32), X 1 0≤X ⟨x,y⟩ 0 := by
  intro p X
  let F := fun z : ℂ => -(coordinateData p.t p.a 1 p.height_pos z 0)
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  have small := (by norm_num [rootTLower] : (7/32:ℝ)<rootTLower).trans certifiedClosedParameters_bounds.1.1
  have regular {z : ℂ} (hx : z.re∈Icc (1/2:ℝ) 1) (hy : z.im∈Icc (0:ℝ) (7/32)) : z∉certifiedPeriodPair.lattice := by
    rcases hy.1.eq_or_lt with zero|pos
    · rw [show z=(z.re:ℂ) from Complex.ext rfl (by simp [← zero])]
      exact real_not_mem_rhombic_lattice_of_pos p.height_pos (by linarith [hx.1]) (by linarith [hx.2])
    · exact rhombic_horizontal_strip_not_mem p.height_pos ⟨pos,hy.2.trans_lt small⟩
  have id (z : ℂ) : (F z).re= -quarterSpatialRate true false z := by simp [F,quarterSpatialRate,p]
  have bounds := rectangle_real_lower_bound (f:=F) (a:=1/2) (b:=1) (c:=0) (d:=7/32) (m:=1/1024)
    (by norm_num) (by norm_num) (fun z hx hy =>
      ((analyticAt_pi_iff.mp (coordinateData_analyticAt (a:=p.a) (c:=1) p.height_pos (regular hx hy))) 0).neg.differentiableAt)
    (by intro x hx y hy; rw [id]; rcases (show x=1/2 ∨ x=1 by simpa using hx) with rfl|rfl
        · linarith [left y hy]
        · linarith [right y hy])
    (by intro y hy x hx; rw [id]; rcases (show y=0 ∨ y=7/32 by simpa using hy) with rfl|rfl
        · linarith [bottom x hx]
        · linarith [top x hx])
  intro x hx y hy
  let g := fun x : ℝ => X ⟨x,y⟩ 0
  have df {u : ℝ} (hu : u∈Icc (1/2:ℝ) 1) : HasDerivAt g (quarterSpatialRate true false ⟨u,y⟩) u :=
    quarter_spatial_line_hasDerivAt true false y u d (regular (z:=(⟨u,y⟩:ℂ)) hu hy)
  have order : AntitoneOn g (Icc (1/2:ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (fun u hu => (df hu).continuousAt.continuousWithinAt)
      (fun _ hu => (df (interior_subset hu)).differentiableAt.differentiableWithinAt)
    intro u hu
    have uin := interior_subset hu
    have neg := bounds ⟨u,y⟩ uin hy
    rw [id] at neg
    rw [(df uin).deriv]
    linarith
  have axis := (actual_primitive_vertical_line p.height_pos d (show y∈Ioo (-p.t) p.t from
    ⟨by linarith [p.height_pos,hy.1],hy.2.trans_lt small⟩)).1
  have point : (1:ℂ)+I*y=⟨1,y⟩ := by apply Complex.ext <;> simp
  rw [point] at axis
  exact axis ▸ order hx (by norm_num) hx.2

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.low_slab_early_position_from_edges
