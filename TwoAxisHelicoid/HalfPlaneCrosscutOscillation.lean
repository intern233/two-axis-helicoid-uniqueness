import TwoAxisHelicoid.HalfPlaneCrosscutEnergy

namespace TwoAxisHelicoid
open Set Metric Filter MeasureTheory Complex Bornology
open scoped Interval Topology

private theorem chord_bound_by_full_slice {f v : ℝ → ℂ} {j : ℝ → ℝ} (ji : Integrable j)
    (nn : ∀ x, 0≤j x) {a b : ℝ} (cv : ContinuousOn v (uIcc a b))
    (df : ∀ x∈uIcc a b, HasDerivAt f (v x) x) (eq : ∀ x∈uIcc a b, ‖v x‖^2=j x) :
    dist (f a) (f b)^2≤|a-b| * (∫ x, j x) := by
  have bound {s t : ℝ} (st : s≤t) (sub : Icc s t⊆uIcc a b) :
      dist (f t) (f s)^2≤(t-s)*(∫ x, j x) := by
    have est := interval_path_squared_displacement st (cv.mono sub) (fun x hx => df x (sub hx))
    have same : (∫ x in s..t, ‖v x‖^2)=∫ x in s..t, j x :=
      intervalIntegral.integral_congr (fun x hx => eq x (sub (uIcc_of_le st ▸ hx)))
    rw [same,intervalIntegral.integral_of_le st] at est
    exact est.trans (mul_le_mul_of_nonneg_left (setIntegral_le_integral ji (.of_forall nn)) (sub_nonneg.mpr st))
  rcases le_total a b with ab|ba
  · rw [abs_of_nonpos (sub_nonpos.mpr ab),neg_sub,dist_comm]
    exact bound ab (by rw [uIcc_of_le ab])
  · rw [abs_of_nonneg (sub_nonneg.mpr ba)]
    exact bound ba (by rw [uIcc_comm,uIcc_of_le ba])

private theorem horizontal_slice_chord {f : ℂ → ℂ} (an : AnalyticOnNhd ℂ f rightPlaneDomain)
    {a b y : ℝ} (ap : 0<a) (bp : 0<b) (ji : Integrable (fun x => halfPlaneJacobian f x y)) :
    dist (f ⟨a,y⟩) (f ⟨b,y⟩)^2≤|a-b| * (∫ x, halfPlaneJacobian f x y) := by
  let l := fun x : ℝ => (⟨x,y⟩:ℂ)
  have dl (x : ℝ) : HasDerivAt l 1 x := by
    have eq : l=fun t : ℝ => (t:ℂ)+I*y := by funext t; apply Complex.ext <;> simp [l]
    rw [eq]
    exact (hasDerivAt_id x).ofReal_comp.add_const _
  have active {x : ℝ} (hx : x∈uIcc a b) : l x∈rightPlaneDomain := (lt_min ap bp).trans_le hx.1
  have slope (x : ℝ) (hx : x∈uIcc a b) : HasDerivAt (f ∘ l) (deriv f (l x)) x := by
    simpa only [one_smul] using (an _ (active hx)).differentiableAt.hasDerivAt.scomp x (dl x)
  apply chord_bound_by_full_slice (v:=fun x => deriv f (l x)) ji (fun x => halfPlaneJacobian_nonneg f x y) _ slope
  · intro x hx
    rw [halfPlaneJacobian,indicator_of_mem (active hx)]
  · intro x hx
    exact ((an _ (active hx)).deriv.continuousAt.comp (dl x).continuousAt).continuousWithinAt

private theorem vertical_slice_chord {f : ℂ → ℂ} (an : AnalyticOnNhd ℂ f rightPlaneDomain)
    {r y v : ℝ} (rp : 0<r) (ji : Integrable (halfPlaneJacobian f r)) :
    dist (f ⟨r,y⟩) (f ⟨r,v⟩)^2≤|y-v| * (∫ x, halfPlaneJacobian f r x) := by
  let l := fun x : ℝ => (⟨r,x⟩:ℂ)
  have dl (x : ℝ) : HasDerivAt l I x := by
    have eq : l=fun t : ℝ => (r:ℂ)+I*t := by funext t; apply Complex.ext <;> simp [l]
    rw [eq]
    simpa using ((hasDerivAt_id x).ofReal_comp.const_mul I).const_add (r:ℂ)
  have active (x : ℝ) : l x∈rightPlaneDomain := rp
  have slope (x : ℝ) (_ : x∈uIcc y v) : HasDerivAt (f ∘ l) (deriv f (l x)*I) x := by
    simpa only [smul_eq_mul,mul_comm I] using (an _ (active x)).differentiableAt.hasDerivAt.scomp x (dl x)
  apply chord_bound_by_full_slice (v:=fun x => deriv f (l x)*I) ji (fun x => halfPlaneJacobian_nonneg f r x) _ slope
  · intro x _
    rw [halfPlaneJacobian,indicator_of_mem (active x),norm_mul,Complex.norm_I,mul_one]
  · intro x _
    exact (((an _ (active x)).deriv.continuousAt.comp (dl x).continuousAt).mul continuousAt_const).continuousWithinAt

/-- Arbitrarily close to zero, the three interior sides of a square
cutting off the boundary of the right half-plane have arbitrarily
small joint image diameter, relative to the midpoint of the right side. -/
theorem half_plane_square_cut_small {f : ℂ → ℂ} (an : AnalyticOnNhd ℂ f rightPlaneDomain)
    (inj : InjOn f rightPlaneDomain) (bounded : IsBounded (f '' rightPlaneDomain)) {δ ε : ℝ}
    (dp : 0<δ) (ep : 0<ε) :
    ∃ r : ℝ, 0<r ∧ r<δ ∧ ∀ z∈rightPlaneDomain, max z.re |z.im|=r → dist (f z) (f (r:ℂ))<ε := by
  let J := halfPlaneJacobian f
  obtain ⟨r,rp,rd,vI,pI,mI,total⟩ := univalent_half_plane_small_energy_slices an.differentiableOn inj bounded dp
    (show 0<(ε/2)^2 by positivity)
  let V := ∫ y, J r y
  let A := ∫ x, J x r
  let B := ∫ x, J x (-r)
  have vp : 0≤V := integral_nonneg (fun _ => halfPlaneJacobian_nonneg ..)
  have ap : 0≤A := integral_nonneg (fun _ => halfPlaneJacobian_nonneg ..)
  have bp : 0≤B := integral_nonneg (fun _ => halfPlaneJacobian_nonneg ..)
  change r*(V+A+B)<(ε/2)^2 at total
  have short {d k : ℝ} (k0 : 0≤k) (ke : k≤V+A+B) {s : ℝ} (sr : s≤r) (est : d^2≤s*k) : d<ε/2 := by
    have h := (est.trans (mul_le_mul_of_nonneg_right sr k0)).trans_lt ((mul_le_mul_of_nonneg_left ke rp.le).trans_lt total)
    nlinarith
  refine ⟨r,rp,rd,?_⟩
  intro z inside edge
  have all : z.re=r ∨ |z.im|=r := (le_total |z.im| z.re).elim
    (fun h => Or.inl ((max_eq_left h).symm.trans edge)) (fun h => Or.inr ((max_eq_right h).symm.trans edge))
  have xr : z.re≤r := (le_max_left _ _).trans_eq edge
  have yr : |z.im|≤r := (le_max_right _ _).trans_eq edge
  let corner : ℂ := ⟨r,z.im⟩
  have realPoint : (⟨r,0⟩:ℂ)=(r:ℂ) := by apply Complex.ext <;> simp
  have vert : dist (f corner) (f (r:ℂ))<ε/2 := short vp (by linarith) yr
    (by simpa only [sub_zero,realPoint,corner,V,J] using vertical_slice_chord (y:=z.im) (v:=0) an rp vI)
  have hori : dist (f z) (f corner)<ε/2 := by
    rcases all with eq|eq
    · have same : z=corner := Complex.ext eq rfl
      simpa only [same,dist_self] using half_pos ep
    · have dx : |z.re-r|≤r := by rw [abs_of_nonpos (sub_nonpos.mpr xr)]; linarith [show 0<z.re from inside]
      rcases (abs_eq (le_of_lt rp)).mp eq with plus|minus
      · have h := horizontal_slice_chord (a:=z.re) (b:=r) an inside rp pI
        apply short ap (by linarith) dx
        change dist (f ⟨z.re,z.im⟩) (f ⟨r,z.im⟩)^2≤_
        simpa only [plus] using h
      · have h := horizontal_slice_chord (a:=z.re) (b:=r) an inside rp mI
        apply short bp (by linarith) dx
        change dist (f ⟨z.re,z.im⟩) (f ⟨r,z.im⟩)^2≤_
        simpa only [minus] using h
  linarith [dist_triangle (f z) (f corner) (f (r:ℂ))]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.half_plane_square_cut_small
