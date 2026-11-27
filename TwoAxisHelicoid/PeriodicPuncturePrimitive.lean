import TwoAxisHelicoid.PunctureBoundaryInverse
import TwoAxisHelicoid.PuncturePrimitiveResidue
import TwoAxisHelicoid.TorusEndScalingOrders

namespace TwoAxisHelicoid
open Complex Set Filter Metric MeasureTheory
open scoped Topology Interval

private theorem primitive_edge_increment {F f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0<R)
    (reg : ∀ z : ℂ, 0<‖z‖ → ‖z‖<R → DifferentiableAt ℂ f z)
    (prim : ∀ z : ℂ, 0<‖z‖ → ‖z‖<R → HasDerivAt F (f z-c/z) z)
    (a b : ℂ) (off : ∀ s∈Icc (0:ℝ) 1, a+(s:ℂ)*(b-a)≠0) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), dilatedEdgeIntegral f a b r=
      F ((r:ℂ)*b)-F ((r:ℂ)*a)+c*dilatedEdgeIntegral (fun z : ℂ => z⁻¹) a b r := by
  let K := ‖a‖+‖b-a‖+1
  have pos : 0<K := by dsimp [K]; positivity
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (div_pos hR pos))] with r hr small
  change 0<r at hr
  change r<R/K at small
  let v := (r:ℂ)*(b-a)
  let z := fun s : ℝ => (r:ℂ)*(a+(s:ℂ)*(b-a))
  have nz (s) (hs : s∈Icc (0:ℝ) 1) : 0<‖z s‖ := norm_pos_iff.mpr (mul_ne_zero (ofReal_ne_zero.mpr hr.ne') (off _ hs))
  have near (s) (hs : s∈Icc (0:ℝ) 1) : ‖z s‖<R := by
    have norm : ‖a+(s:ℂ)*(b-a)‖≤K := by
      apply (norm_add_le _ _).trans
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hs.1]
      dsimp [K]
      nlinarith [mul_le_mul_of_nonneg_right hs.2 (norm_nonneg (b-a))]
    rw [show z s=(r:ℂ)*(a+(s:ℂ)*(b-a)) from rfl,norm_mul,Complex.norm_real,Real.norm_of_nonneg hr.le]
    exact (mul_le_mul_of_nonneg_left norm hr.le).trans_lt ((lt_div_iff₀ pos).mp small)
  have cz : Continuous z := by dsimp [z]; fun_prop
  have cf : ContinuousOn (fun s => v*f (z s)) (Icc (0:ℝ) 1) :=
    continuousOn_const.mul (fun s hs => ((reg _ (nz s hs) (near s hs)).continuousAt.comp cz.continuousAt).continuousWithinAt)
  have ch : ContinuousOn (fun s => v*(z s)⁻¹) (Icc (0:ℝ) 1) :=
    continuousOn_const.mul (cz.continuousOn.inv₀ (fun s hs => norm_pos_iff.mp (nz _ hs)))
  have derivative (s : ℝ) (hs : s∈Icc (0:ℝ) 1) :
      HasDerivAt (fun u => F (z u)) (v*f (z s)-c*(v*(z s)⁻¹)) s := by
    have dz : HasDerivAt z v s := by
      simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul,z,v] using! (((ofRealCLM.hasDerivAt (x := s)).mul_const (b-a)).const_add a).const_mul (r:ℂ)
    convert (prim _ (nz s hs) (near s hs)).scomp s dz using 1
    all_goals first | rfl | (change _=v*(f (z s)-c/z s); ring)
  have ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (zero_le_one : (0:ℝ)≤1)
    (fun s hs => (derivative s hs).continuousAt.continuousWithinAt)
    (fun s hs => derivative s ⟨hs.1.le,hs.2.le⟩)
    ((cf.sub (continuousOn_const.mul ch)).intervalIntegrable_of_Icc zero_le_one)
  rw [intervalIntegral.integral_sub (cf.intervalIntegrable_of_Icc zero_le_one)
    ((ch.const_mul c).intervalIntegrable_of_Icc zero_le_one)] at ftc
  rw [intervalIntegral.integral_const_mul c] at ftc
  have left : z 0=(r:ℂ)*a := by simp [z]
  have right : z 1=(r:ℂ)*b := by simp [z]
  change _-_=F (z 1)-F (z 0) at ftc
  rw [right,left] at ftc
  exact (sub_eq_iff_eq_add.mp ftc)

/-- Every holomorphic periodic coefficient with just one lattice
puncture possesses a genuine local primitive at that puncture, even
when the singularity is essential. -/
theorem single_lattice_puncture_local_primitive (L : PeriodPair) (f : ℂ → ℂ)
    (reg : ∀ z∉L.lattice, DifferentiableAt ℂ f z) (per : ∀ z v, v∈L.lattice → f (z+v)=f z) :
    ∃ F : ℂ → ℂ, ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt F (f z) z := by
  obtain ⟨R,hR,sub⟩ := Metric.mem_nhdsWithin_iff.mp (punctured_lattice_regular_near_zero L)
  have diff (z : ℂ) (nz : 0<‖z‖) (small : ‖z‖<R) := reg z (sub (show z∈ball (0:ℂ) R ∩ {0}ᶜ from
    ⟨by rwa [mem_ball,dist_zero_right],norm_pos_iff.mp nz⟩))
  obtain ⟨c,F,prim⟩ := puncture_primitive_modulo_log hR diff
  have side (x y u v : ℝ) (sides : (x=u ∧ (x= -1/2 ∨ x=1/2)) ∨ (y=v ∧ (y= -1/2 ∨ y=1/2))) :=
    primitive_edge_increment hR diff prim (spinSquareLinear L x y) (spinSquareLinear L u v) (fun t _ bad => by
      have n := puncture_square_side_regular L x y u v t 1 zero_lt_one le_rfl sides
      simp only [ofReal_one,one_mul,bad] at n
      exact n L.lattice.zero_mem)
  have ev : ∀ᶠ r in 𝓝[>] (0:ℝ), c=0 := by
    filter_upwards [side (-1/2) (-1/2) (1/2) (-1/2) (Or.inr ⟨rfl,Or.inl rfl⟩),
      side (1/2) (-1/2) (1/2) (1/2) (Or.inl ⟨rfl,Or.inr rfl⟩),side (-1/2) (1/2) (1/2) (1/2) (Or.inr ⟨rfl,Or.inr rfl⟩),
      side (-1/2) (-1/2) (-1/2) (1/2) (Or.inl ⟨rfl,Or.inl rfl⟩),self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (zero_lt_one : (0:ℝ)<1))] with r b d t l pos small
    have h := single_puncture_boundary_integral_zero L reg per (r := r) pos (show r<1 from small).le
    apply (mul_eq_zero.mp (show c*punctureBoundaryIntegral L (fun w : ℂ => w⁻¹) r=0 by
      unfold punctureBoundaryIntegral at h ⊢
      linear_combination h-b-d+t+l)).resolve_right (puncture_boundary_integral_inv_ne_zero L pos)
  obtain ⟨_,rfl⟩ := ev.exists
  refine ⟨F,?_⟩
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) hR)] with z n h
  simpa only [zero_div,sub_zero] using prim z (norm_pos_iff.mpr n) (by simpa only [mem_ball,dist_zero_right] using h)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.single_lattice_puncture_local_primitive
