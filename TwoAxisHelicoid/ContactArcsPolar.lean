import TwoAxisHelicoid.CompactAngularZeroBranches
import TwoAxisHelicoid.HomogeneousHarmonicPlaneProfile

namespace TwoAxisHelicoid
open Complex Real Function Set Filter Topology Metric InnerProductSpace
open scoped Topology ContDiff InnerProductSpace Laplacian

/-- The local contact set in the conformal plane is represented by
embedded radial arcs. Each radius cuts each arm once and their initial
unit tangents are the consecutive angles of the leading polynomial. -/
structure EqualAngleContactArcs (f : ℂ → ℝ) (x : ℂ) where
  order : ℕ
  at_least_two : 2≤order
  coefficient : ℂ
  coefficient_ne : coefficient≠0
  radius : ℝ
  radius_pos : 0<radius
  arm : Fin (2*order) → ℝ → ℂ
  center : ∀ i, arm i 0=x
  regular : ∀ i, ContDiffOn ℝ 1 (arm i) (Ico 0 radius)
  tangent : ∀ i, HasDerivAt (arm i) (circleMap 0 1 (contactArmAngle order coefficient i.1)) 0
  distance : ∀ i r, dist (arm i r) x=|r|
  vanishes : ∀ i r, r∈Ioo 0 radius → f (arm i r)=0
  separated : ∀ i j r s, r∈Ioo 0 radius → s∈Ioo 0 radius → arm i r=arm j s → i=j ∧ r=s
  covers : ∀ z, 0<dist z x → dist z x<radius → f z=0 → ∃ i, z=arm i (dist z x)

private theorem scaled_contact_direction (r θ : ℝ) :
    circleMap 0 r θ=r • circleMap 0 1 θ := by simp [circleMap_zero,Complex.real_smul]

/-- A cut in any angular direction parametrizes every spatial point
at its actual radius from the center. -/
private theorem point_at_contact_radius (x z : ℂ) (b : ℝ) :
    ∃ θ∈Ioc b (b+2*Real.pi), z=x+dist z x • circleMap 0 1 θ := by
  let r := dist z x
  have h : z-x∈circleMap 0 r '' Ioc b (b+2*Real.pi) := by
    rw [(periodic_circleMap 0 r).image_Ioc Real.two_pi_pos b,range_circleMap]
    simp [r,dist_eq_norm]
  obtain ⟨θ,inside,eq⟩ := h
  refine ⟨θ,inside,?_⟩
  rw [← scaled_contact_direction,show circleMap 0 (dist z x) θ=z-x from eq]
  abel

theorem analytic_drift_equal_angle_contact {f A B : ℂ → ℝ} {x : ℂ}
    (an : AnalyticAt ℝ f x) (zero : f x=0) (flat : fderiv ℝ f x=0)
    (nonzero : ¬ f =ᶠ[𝓝 x] 0) (ca : ContinuousAt A x) (cb : ContinuousAt B x)
    (pde : ∀ᶠ z in 𝓝 x, (Δ f) z=A z*planePartial 1 f z+B z*planePartial I f z) :
    Nonempty (EqualAngleContactArcs f x) := by
  obtain ⟨n,C,H,R,n2,cn,rp,sh,profile,form⟩ := analytic_drift_germ_radial_normal_form an zero flat nonzero ca cb pde
  obtain ⟨φ,at0,allRoots⟩ := compact_angular_zero_branches sh cn (by omega : 0<n) profile
  let γ := fun i : Fin (2*n) => fun r : ℝ => x+r • circleMap 0 1 (φ i r)
  have near : ∀ᶠ r in 𝓝 (0:ℝ), ∀ i, ContDiffAt ℝ 1 (φ i) r :=
    eventually_all.mpr fun i => ((at0 i).1.of_le (by norm_num : (1:ℕ∞ω)≤∞)).eventually (by norm_num)
  obtain ⟨d,dp,inside⟩ := Metric.mem_nhds_iff.mp (near.and allRoots)
  let ε := min d R
  have eps : 0<ε := lt_min dp rp
  have valid {r : ℝ} (lo : 0≤r) (hi : r<ε) := inside (show r∈Metric.ball (0:ℝ) d by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg lo]
    exact hi.trans_le (min_le_left _ _))
  have scale (r θ : ℝ) : ‖r • circleMap 0 1 θ‖=|r| := by simp [Real.norm_eq_abs]
  have distγ (i : Fin (2*n)) (r : ℝ) : dist (γ i r) x=|r| := by
    simp [γ,dist_eq_norm]
  have fγ (i : Fin (2*n)) (r : ℝ) (insideR : r∈Ioo 0 ε) : f (γ i r)=0 := by
    have vr := valid insideR.1.le insideR.2
    have θ := vr.2.2.1 i
    have root := (vr.2.2.2 (φ i r) ⟨θ.1.le,θ.2.le⟩).mpr ⟨i,rfl⟩
    have bound : |r|<R := by rw [abs_of_pos insideR.1]; exact insideR.2.trans_le (min_le_right _ _)
    exact (form r _ ((scale r _).trans_lt bound)).trans (by rw [root,mul_zero])
  refine ⟨⟨n,n2,C,cn,ε,eps,γ,fun i => by simp [γ],?_,?_,distγ,fγ,?_,?_⟩⟩
  · intro i r hr
    exact (contDiffAt_const.add (contDiffAt_id.smul ((contDiff_circleMap 0 1).contDiffAt.comp r ((valid hr.1 hr.2).1 i)))).contDiffWithinAt
  · intro i
    have dφ := (((at0 i).1.differentiableAt (by norm_num)).hasDerivAt)
    have du := (hasDerivAt_circleMap 0 1 (φ i 0)).scomp 0 dφ
    simpa [γ,(at0 i).2] using (((hasDerivAt_id (0:ℝ)).smul du).const_add x)
  · intro i j r s hr hs eq
    have rs : r=s := by simpa only [distγ,abs_of_pos hr.1,abs_of_pos hs.1] using congrArg (fun z => dist z x) eq
    subst s
    have v := valid hr.1.le hr.2
    have unit : circleMap 0 1 (φ i r)=circleMap 0 1 (φ j r) :=
      (smul_right_injective ℂ hr.1.ne') (add_left_cancel eq)
    have inj := injOn_circleMap_of_abs_sub_le' (c:=(0:ℂ)) (R:=(1:ℝ)) one_ne_zero
      (a:=contactAngleBase n C) (b:=contactAngleBase n C+2*Real.pi) (by linarith)
    exact ⟨v.2.1.injective (inj ⟨(v.2.2.1 i).1.le,(v.2.2.1 i).2⟩
      ⟨(v.2.2.1 j).1.le,(v.2.2.1 j).2⟩ unit),rfl⟩
  · intro z zr small fz
    obtain ⟨θ,hθ,eq⟩ := point_at_contact_radius x z (contactAngleBase n C)
    let r := dist z x
    have vr := valid zr.le small
    have bound : ‖r • circleMap 0 1 θ‖<R := by
      rw [scale,abs_of_pos zr]; exact small.trans_le (min_le_right _ _)
    have root : H (r,circleMap 0 1 θ)=0 := (mul_eq_zero.mp ((form r _ bound).symm.trans ((congrArg f eq).symm.trans fz))).resolve_left (pow_ne_zero n zr.ne')
    obtain ⟨i,atθ⟩ := (vr.2.2.2 θ ⟨hθ.1.le,hθ.2⟩).mp root
    exact ⟨i,eq.trans (by rw [atθ])⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.analytic_drift_equal_angle_contact
