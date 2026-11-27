import TwoAxisHelicoid.PlaneOrientationJacobian
import Mathlib.Topology.TietzeExtension

namespace TwoAxisHelicoid
open Complex Filter Set Topology Metric
open scoped Topology

theorem HasOrientationCircleDegree.add {f g : OrientationCircle → OrientationCircle} {n m : ℤ}
    (hf : HasOrientationCircleDegree f n) (hg : HasOrientationCircleDegree g m) :
    HasOrientationCircleDegree (fun a => f a+g a) (n+m) := by
  obtain ⟨F,fc,hF,dF⟩ := hf
  obtain ⟨G,gc,hG,dG⟩ := hg
  refine ⟨fun x => F x+G x,fc.add gc,fun x => ?_,fun x => ?_⟩
  · rw [AddCircle.coe_add,hF,hG]
  · change F (x+1)+G (x+1)=F x+G x+((n+m:ℤ):ℝ)
    rw [dF,dG,Int.cast_add]
    abel

theorem HasOrientationCircleDegree.sub {f g : OrientationCircle → OrientationCircle} {n m : ℤ}
    (hf : HasOrientationCircleDegree f n) (hg : HasOrientationCircleDegree g m) :
    HasOrientationCircleDegree (fun a => f a-g a) (n-m) := by
  obtain ⟨F,fc,hF,dF⟩ := hf
  obtain ⟨G,gc,hG,dG⟩ := hg
  refine ⟨fun x => F x-G x,fc.sub gc,fun x => ?_,fun x => ?_⟩
  · rw [AddCircle.coe_sub,hF,hG]
  · change F (x+1)-G (x+1)=F x-G x+((n-m:ℤ):ℝ)
    rw [dF,dG,Int.cast_sub]
    abel

theorem orientationCircle_degree_const (c : OrientationCircle) :
    HasOrientationCircleDegree (fun _ => c) 0 := by
  obtain ⟨b,hb⟩ := (Quotient.mk_surjective : Function.Surjective ((↑) : ℝ → OrientationCircle)) c
  exact ⟨fun _ => b,continuous_const,fun _ => hb,fun _ => by simp⟩

theorem HasOrientationCircleDegree.zsmul {f : OrientationCircle → OrientationCircle} {n : ℤ}
    (h : HasOrientationCircleDegree f n) (k : ℤ) :
    HasOrientationCircleDegree (fun a => k • f a) (k*n) := by
  obtain ⟨F,fc,eq,step⟩ := h
  refine ⟨fun x => k • F x,fc.const_smul k,fun x => ?_,fun x => ?_⟩
  · rw [AddCircle.coe_zsmul,eq]
  · change k • F (x+1)=k • F x+((k*n:ℤ):ℝ)
    simp only [step,smul_add,zsmul_eq_mul,Int.cast_mul]

/-- A degree-zero circle map has a continuous real-valued argument on
the circle itself. -/
theorem HasOrientationCircleDegree.real_lift {f : OrientationCircle → OrientationCircle}
    (h : HasOrientationCircleDegree f 0) :
    ∃ g : C(OrientationCircle,ℝ), ∀ a, (g a : OrientationCircle)=f a := by
  obtain ⟨F,fc,eq,step⟩ := h
  have ends : F 0=F 1 := by simpa using (step 0).symm
  let g : C(OrientationCircle,ℝ) := ⟨AddCircle.liftIco 1 0 F,AddCircle.liftIco_zero_continuous ends fc.continuousOn⟩
  refine ⟨g,fun a => ?_⟩
  let x := AddCircle.equivIco (1:ℝ) 0 a
  have proj : ((x.1 : ℝ) : OrientationCircle)=a := AddCircle.coe_equivIco
  change ((F x.1 : ℝ) : OrientationCircle)=f a
  rw [eq,proj]

/-- A circle-valued map defined continuously on a closed disk has
degree zero on the oriented boundary. -/
theorem disk_boundary_winding_zero {F : ℂ → OrientationCircle} {p : ℂ} {r : ℝ}
    (hr : 0≤r) (cont : ContinuousOn F (closedBall p r)) :
    HasOrientationCircleDegree (fun a => F (p+r • orientationRay a)) 0 := by
  let Z := fun t : ℝ × OrientationCircle => p+(orientationBlend t.1*r) • orientationRay t.2
  have cz : Continuous Z := continuous_const.add (((orientationBlend_continuous.comp continuous_fst).mul continuous_const).smul
    (orientationRay_continuous.comp continuous_snd))
  have inc (t : ℝ × OrientationCircle) : Z t∈closedBall p r := by
    simp only [Z,mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,orientationRay_norm,mul_one,
      Real.norm_of_nonneg (mul_nonneg (orientationBlend_mem _).1 hr)]
    exact mul_le_of_le_one_left hr (orientationBlend_mem _).2
  have c := cont.comp_continuous cz inc
  have h : HasOrientationCircleDegree (fun a => (F ∘ Z) (0,a)) 0 := by
    simpa only [Function.comp_apply,Z,orientationBlend_zero,zero_mul,zero_smul,add_zero] using orientationCircle_degree_const (F p)
  simpa only [Function.comp_apply,Z,orientationBlend_one,one_mul] using h.family (t := 1) c

/-- The degree-zero criterion constructs a filling that agrees
pointwise with the prescribed circle map on the spatial boundary. -/
theorem fill_zero_winding_circle {F : ℂ → OrientationCircle} {p : ℂ} {r : ℝ} (hr : 0<r)
    (h : HasOrientationCircleDegree (fun a => F (p+r • orientationRay a)) 0) :
    ∃ G : C(ℂ,OrientationCircle), ∀ z∈sphere p r, G z=F z := by
  obtain ⟨g,eq⟩ := h.real_lift
  let a := fun z : sphere p r => planeOrientationDirection (z.1-p)
  have norm_eq (z : sphere p r) : ‖z.1-p‖=r := by simpa only [mem_sphere,dist_eq_norm] using z.2
  have nz (z : sphere p r) : z.1-p≠0 := norm_pos_iff.mp ((norm_eq z).trans_gt hr)
  have ca : Continuous a := continuous_iff_continuousAt.mpr fun z =>
    (planeOrientationDirection_continuousAt (nz z)).comp (f := fun u : sphere p r => u.1-p)
      (continuous_subtype_val.sub continuous_const).continuousAt
  obtain ⟨H,extension_eq⟩ := ContinuousMap.exists_restrict_eq isClosed_sphere (g.comp ⟨a,ca⟩)
  refine ⟨⟨fun z => (H z : OrientationCircle),QuotientAddGroup.continuous_mk.comp H.continuous⟩,?_⟩
  intro z hz
  let w : sphere p r := ⟨z,hz⟩
  have val : H z=g (a w) := congrArg (fun j : C(sphere p r,ℝ) => j w) extension_eq
  change (H z : OrientationCircle)=F z
  rw [val,eq]
  apply congrArg F
  rw [← norm_eq w,show ‖w.1-p‖ • orientationRay (a w)=w.1-p from planeOrientationDirection_reconstruct (nz w)]
  dsimp only [w]
  abel

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.fill_zero_winding_circle
