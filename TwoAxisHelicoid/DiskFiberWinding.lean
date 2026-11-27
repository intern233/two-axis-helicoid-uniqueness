import TwoAxisHelicoid.DegreeOnePlaneFibers
import TwoAxisHelicoid.PlaneOrientationJacobian

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology
open scoped Topology

/-- The winding along every sufficiently large circle is the sum
of the local signed multiplicities above the specified value. -/
theorem eventual_finite_fiber_winding {F : ℂ → ℂ} (cont : Continuous F) (c : ℂ)
    (finite : (F ⁻¹' {c}).Finite) (degree : ℂ → ℤ) (orient : ∀ z, HasPlaneOrientationAt F z (degree z)) :
    ∀ᶠ r : ℝ in atTop, HasOrientationCircleDegree
      (fun a => planeOrientationDirection (F (r • orientationRay a)-c)) (∑ z∈finite.toFinset,degree z) := by
  classical
  let S := finite.toFinset
  have mem (z : ℂ) : z∈S ↔ F z=c := finite.mem_toFinset
  obtain ⟨B,bd⟩ := finite.isBounded.exists_norm_le
  filter_upwards [eventually_gt_atTop B,eventually_gt_atTop (0:ℝ)] with r gap rp
  let A := fun z => planeOrientationDirection (F z-c)
  have reg : ContinuousOn A (S : Set ℂ)ᶜ := fun z hz =>
    ((planeOrientationDirection_continuousAt (sub_ne_zero.mpr (fun eq => hz ((mem z).mpr eq)))).comp
      (f:=fun w => F w-c) (cont.continuousAt.sub continuousAt_const)).continuousWithinAt
  have localDeg (z : ℂ) (hz : z∈S) : HasLocalWinding A z (degree z) := by
    obtain ⟨d,dp,count⟩ := orient z
    refine ⟨d,dp,fun s hs => ?_⟩
    have h := count s hs
    change HasOrientationCircleDegree (fun a => planeOrientationDirection (F (z+s • orientationRay a)-F z)) _ at h
    rwa [(mem _).mp hz] at h
  exact winding_sum_of_finite_plane_singularities S A degree reg localDeg rp (fun z hz => (bd z ((mem _).mp hz)).trans_lt gap)

/-- For a disk-valued map escaping to the boundary, a single simple
zero determines the multiplicity of every interior fiber. -/
theorem single_simple_zero_disk_bijection {F : ℂ → ℂ} (cont : Continuous F)
    (bounded : ∀ z, ‖F z‖<1) (boundary : Tendsto (fun z => ‖F z‖) (cocompact ℂ) (𝓝 1))
    (fibers : ∀ c : ℂ, ‖c‖<1 → (F ⁻¹' {c}).Finite) {s : ℤ} (sn : s≠0)
    (k : ℂ → ℕ) (ori : ∀ z, HasPlaneOrientationAt F z (((k z+1:ℕ):ℤ)*s))
    (p : ℂ) (zero : ∀ z, F z=0 ↔ z=p) (simple : k p=0) :
    Function.Injective F ∧ F '' univ=ball (0:ℂ) 1 := by
  classical
  let d := fun z => ((k z+1:ℕ):ℤ)*s
  have f0 := fibers 0 (by simp)
  have fs : f0.toFinset={p} := by ext z; simpa only [Set.Finite.mem_toFinset,mem_preimage,mem_singleton_iff,Finset.mem_singleton] using zero z
  have outer := eventual_finite_fiber_winding cont 0 f0 d ori
  simp only [fs,Finset.sum_singleton,d,simple,zero_add,Nat.cast_one,one_mul,sub_zero] at outer
  have one (c : ℂ) (hc : ‖c‖<1) : ∃! z, F z=c := by
    let fc := fibers c hc
    obtain ⟨K,compact,away⟩ := hasBasis_cocompact.mem_iff.mp (boundary.eventually (lt_mem_nhds hc))
    obtain ⟨B,bound⟩ := compact.isBounded.exists_norm_le
    obtain ⟨r,o,deg,above,rp⟩ := (outer.and ((eventual_finite_fiber_winding cont c fc d ori).and
      ((eventually_gt_atTop B).and (eventually_gt_atTop 0)))).exists
    let q := fun a : OrientationCircle => r • orientationRay a
    have cq : Continuous q := orientationRay_continuous.const_smul r
    have same := circle_degree_small_perturbation ((cont.comp cq).sub continuous_const) (cont.comp cq) o
      (fun a => by
        change ‖F (q a)-c-F (q a)‖<‖F (q a)‖
        rw [sub_right_comm,sub_self,zero_sub,norm_neg]
        apply away
        intro bad
        have v := bound (q a) bad
        simp only [q,norm_smul,Real.norm_of_nonneg rp.le,orientationRay_norm,mul_one] at v
        linarith)
    have hsum := deg.unique same
    change (∑ z∈fc.toFinset, ((k z+1:ℕ):ℤ)*s)=s at hsum
    rw [← Finset.sum_mul] at hsum
    have sum : (∑ z∈fc.toFinset, ((k z+1:ℕ):ℤ))=1 := mul_right_cancel₀ sn (hsum.trans (one_mul s).symm)
    have allOne (z : ℂ) (hz : z∈fc.toFinset) : k z=0 := by
      have h := Finset.single_le_sum (f:=fun z => ((k z+1:ℕ):ℤ)) (fun _ _ => by positivity) hz
      rw [sum] at h
      omega
    have card : fc.toFinset.card=1 := by
      have eq := Finset.sum_congr (s₂:=fc.toFinset) rfl (fun z hz =>
        (show ((k z+1:ℕ):ℤ)=1 by simp [allOne z hz]))
      rw [eq] at sum
      simpa using sum
    obtain ⟨z,single⟩ := Finset.card_eq_one.mp card
    have iff (w : ℂ) : F w=c ↔ w=z := by
      change w∈F ⁻¹' {c} ↔ _
      rw [← fc.mem_toFinset,single,Finset.mem_singleton]
    exact ⟨z,(iff z).mpr rfl,fun w hw => (iff w).mp hw⟩
  refine ⟨fun x y eq => (one (F x) (bounded x)).unique rfl eq.symm,?_⟩
  ext c
  constructor
  · rintro ⟨z,_,rfl⟩
    exact mem_ball_zero_iff.mpr (bounded z)
  · intro hc
    obtain ⟨z,hz,_⟩ := one c (mem_ball_zero_iff.mp hc)
    exact ⟨z,mem_univ _,hz⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.single_simple_zero_disk_bijection
