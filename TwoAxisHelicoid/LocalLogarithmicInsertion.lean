import TwoAxisHelicoid.SurfacePotentialArithmetic

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology InnerProductSpace
open scoped Topology ContDiff Manifold

theorem SurfaceHarmonicGerm.of_germ_eq {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {x : M}
    {u v : M → ℝ} (hu : SurfaceHarmonicGerm u x) (eq : v =ᶠ[𝓝 x] u) : SurfaceHarmonicGerm v x := by
  obtain ⟨F,hF,a⟩ := hu
  exact ⟨F,hF,eq.trans a⟩

/-- The difference of two translated quadratic potentials is the
real part of an affine holomorphic function. -/
theorem harmonic_difference_squared_norms {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {x : M}
    {f : M → ℂ} (hf : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f x) (c : ℂ) :
    SurfaceHarmonicGerm (fun y => ‖f y‖^2-‖f y-c‖^2) x := by
  let F := fun z : ℂ => 2*((starRingEnd ℂ c)*z)-((‖c‖^2:ℝ):ℂ)
  have lin : ContDiff ℂ ω F := by dsimp [F]; fun_prop
  refine ⟨F ∘ f,lin.contMDiff.contMDiffAt.comp x hf,.of_forall fun y => ?_⟩
  have ident : ((starRingEnd ℂ c)*f y).re=⟪c,f y⟫_ℝ := by rw [real_inner_eq_re_inner ℂ,RCLike.inner_apply']; rfl
  change ‖f y‖^2-‖f y-c‖^2=(2*((starRingEnd ℂ c)*f y)-((‖c‖^2:ℝ):ℂ)).re
  rw [norm_sub_sq_real,Complex.sub_re,Complex.ofReal_re,show (2*((starRingEnd ℂ c)*f y)).re=2*((starRingEnd ℂ c)*f y).re by
    rw [two_mul,Complex.add_re,two_mul],ident,real_inner_comm c (f y)]
  ring

/-- Insert a single logarithmic pole into a genuine strictly
subharmonic coordinate patch. The constructed lower and upper functions
have the same logarithmic coefficient, agree with bounded functions
outside the insertion disk, and are ordered everywhere. -/
theorem insert_pole_into_quadratic_patch {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ,ℂ) ω X] (d : X → ℝ) (cont : Continuous d) (dp : ∀ x, 0<d x)
    (B : X → ℝ) (sb : ∀ x, SurfaceSubharmonicAt B x) (bounds : ∀ x, -1≤B x ∧ B x≤0)
    (f : X → ℂ) (c : ℂ) {A r : ℝ} (ap : 0<A) (rp : 0<r)
    (hol : ∀ x, d x<2 → ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f x)
    (patch : ∀ x, d x<2 → ‖f x-c‖=r*d x ∧ B x=A*(‖f x‖^2-1)) :
    ∃ (L H : X → ℝ) (K : ℝ), (∀ x, SurfaceSubharmonicAt L x) ∧
      (∀ x, SurfaceSubharmonicAt (fun y => -H y) x) ∧ L≤H ∧
      (∀ x, L x≤ -1 ∧ H x≤0) ∧ (∀ x, 1≤d x → -K≤L x ∧ H x=0) ∧
      ∀ x, d x<1 → Real.log (d x)-K≤L x ∧ H x=Real.log (d x) := by
  classical
  let t := (r^2)⁻¹
  let k := t/A
  have tp : 0<t := inv_pos.mpr (sq_pos_of_pos rp)
  have kp : 0<k := div_pos tp ap
  let P := fun x => k*B x
  let Q := fun x => Real.log (d x)+P x-(d x)^2-1
  let O := fun x => P x-2
  let L := fun x => if d x<1 then Q x else O x
  let H := fun x => min 0 (Real.log (d x))
  have logG (x : X) (small : d x<2) : SurfaceHarmonicGerm (fun y => Real.log (d y)) x := by
    have nz : f x≠c := sub_ne_zero.mp (norm_pos_iff.mp ((patch x small).1.trans_gt (mul_pos rp (dp x))))
    apply ((surface_harmonic_log_distance (hol x small) nz).affine 1 (-Real.log r)).of_germ_eq
    filter_upwards [cont.continuousAt.eventually_lt continuousAt_const small] with y hy
    rw [(patch y hy).1,Real.log_mul rp.ne' (dp y).ne',one_mul]; ring
  have qharm (x : X) (small : d x<2) : SurfaceHarmonicGerm Q x := by
    apply ((logG x small).add ((harmonic_difference_squared_norms (hol x small) c).affine t (-t-1))).of_germ_eq
    filter_upwards [cont.continuousAt.eventually_lt continuousAt_const small] with y hy
    change Real.log (d y)+k*B y-(d y)^2-1=Real.log (d y)+(t*(‖f y‖^2-‖f y-c‖^2)+(-t-1))
    rw [(patch y hy).1,(patch y hy).2]
    dsimp [k,t]
    field_simp
    ring
  have so (x : X) : SurfaceSubharmonicAt O x := (sb x).affine_pos kp (-2)
  have nP (x : X) : P x≤0 := mul_nonpos_of_nonneg_of_nonpos kp.le (bounds x).2
  have lP (x : X) : -k≤P x := by dsimp [P]; nlinarith [mul_le_mul_of_nonneg_left (bounds x).1 kp.le]
  have val (x : X) : Q x-O x=1-(d x)^2+Real.log (d x) := by dsimp [Q,O]; ring
  have seam (x : X) (hx : 3/4<d x) : L x=max (Q x) (O x) := by
    have one : (3/4:ℝ)<1 := by norm_num
    by_cases low : d x<1
    · have h := log_quadratic_seam_order (show d x∈Ioi (3/4:ℝ) from hx) one low
      have eq := val x
      simp only [one_pow,sub_self,Real.log_one,add_zero] at h
      rw [show L x=Q x from ite_eq_left low,max_eq_left (by linarith)]
    · have h := log_quadratic_seam_order.antitoneOn one hx (le_of_not_gt low)
      have eq := val x
      simp only [one_pow,sub_self,Real.log_one,add_zero] at h
      rw [show L x=O x from ite_eq_right low,max_eq_right (by linarith)]
  have subL (x : X) : SurfaceSubharmonicAt L x := by
    rcases lt_trichotomy (d x) 1 with low|edge|high
    · apply (qharm x (by linarith)).subharmonicAt.congr_germ
      filter_upwards [cont.continuousAt.eventually_lt continuousAt_const low] with y hy using ite_eq_left hy
    · apply (surface_subharmonic_max (qharm x (by linarith)).subharmonicAt (so x)).congr_germ
      filter_upwards [continuousAt_const.eventually_lt cont.continuousAt (show 3/4<d x by linarith)] with y hy using seam y hy
    · apply (so x).congr_germ
      filter_upwards [continuousAt_const.eventually_lt cont.continuousAt high] with y hy using ite_eq_right hy.not_gt
  have outside (x : X) (hx : 1≤d x) : H x=0 := min_eq_left (Real.log_nonneg hx)
  have inH (x : X) (hx : d x<1) : H x=Real.log (d x) := min_eq_right (Real.log_neg (dp x) hx).le
  have subH (x : X) : SurfaceSubharmonicAt (fun y => -H y) x := by
    by_cases small : d x<2
    · apply (surface_subharmonic_max ((surface_harmonic_const 0 x).subharmonicAt) ((logG x small).affine (-1) 0).subharmonicAt).congr_germ
      exact .of_forall fun y => by
        by_cases le : Real.log (d y)≤0
        · simp [H,min_eq_right le,max_eq_right (neg_nonneg.mpr le)]
        · simp [H,min_eq_left (le_of_not_ge le),max_eq_left (neg_nonpos.mpr (le_of_not_ge le))]
    · apply ((surface_harmonic_const 0 x).subharmonicAt).congr_germ
      filter_upwards [continuousAt_const.eventually_lt cont.continuousAt (show 1<d x by linarith [le_of_not_gt small])] with y hy
      rw [outside y hy.le,neg_zero]
  have comp (x : X) (_low : d x<1) : Q x≤Real.log (d x)-1 := by dsimp only [Q]; linarith [nP x,sq_nonneg (d x)]
  refine ⟨L,H,k+2,subL,subH,fun x => ?_,fun x => ⟨?_,min_le_left _ _⟩,fun x hx => ⟨?_,outside x hx⟩,fun x hx => ⟨?_,inH x hx⟩⟩
  · by_cases low : d x<1
    · rw [show L x=Q x from ite_eq_left low,inH x low]
      linarith [comp x low]
    · rw [show L x=O x from ite_eq_right low,outside x (le_of_not_gt low)]
      dsimp only [O]; linarith [nP x]
  · by_cases low : d x<1
    · rw [show L x=Q x from ite_eq_left low]
      linarith [comp x low,Real.log_neg (dp x) low]
    · rw [show L x=O x from ite_eq_right low]
      dsimp only [O]; linarith [nP x]
  · rw [show L x=O x from ite_eq_right hx.not_gt]
    dsimp only [O]; linarith [lP x]
  · rw [show L x=Q x from ite_eq_left hx]
    dsimp only [Q]
    nlinarith [lP x,sq_lt_sq₀ (dp x).le zero_le_one |>.mpr hx]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.insert_pole_into_quadratic_patch
