import TwoAxisHelicoid.CyclicDiskGenerator

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology ComplexConjugate

noncomputable def boundaryCayley (u z : ℂ) : ℂ := (u+z)/(u-z)
noncomputable def boundaryCayleyInv (u w : ℂ) : ℂ := u*(w-1)/(w+1)

theorem boundaryCayley_right {u z : ℂ} (hu : ‖u‖=1) (hz : ‖z‖<1) : 0<(boundaryCayley u z).re := by
  have ne : u-z≠0 := sub_ne_zero.mpr fun eq => hz.ne (eq ▸ hu)
  have n : 0<normSq (u-z) := Complex.normSq_pos.mpr ne
  have hu' : normSq u=1 := by rw [Complex.normSq_eq_norm_sq,hu,one_pow]
  have hz' : normSq z<1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  unfold boundaryCayley
  rw [Complex.div_re]
  rw [← add_div]
  apply div_pos _ n
  simp only [Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
  simp only [Complex.normSq_apply] at hu' hz'
  nlinarith

theorem boundaryCayleyInv_disk {u w : ℂ} (hu : ‖u‖=1) (hw : 0<w.re) : ‖boundaryCayleyInv u w‖<1 := by
  have ne : w+1≠0 := by intro eq; have h := congrArg Complex.re eq; simp at h; linarith
  have e : ‖w-1‖<‖w+1‖ := by
    have h : normSq (w-1)<normSq (w+1) := by
      simp only [Complex.normSq_apply,Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,
        Complex.add_re,Complex.add_im,sub_zero,add_zero]
      nlinarith
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (w+1),norm_nonneg (w-1)]
  simpa only [boundaryCayleyInv,norm_div,norm_mul,hu,one_mul,div_lt_one (norm_pos_iff.mpr ne)] using e

theorem boundaryCayley_left_inv {u z : ℂ} (hu : ‖u‖=1) (hz : ‖z‖<1) :
    boundaryCayleyInv u (boundaryCayley u z)=z := by
  have ne : u-z≠0 := sub_ne_zero.mpr fun eq => hz.ne (eq ▸ hu)
  have pos := boundaryCayley_right hu hz
  have den : boundaryCayley u z+1≠0 := by intro eq; have h := congrArg Complex.re eq; simp at h; linarith
  unfold boundaryCayleyInv
  apply (div_eq_iff den).mpr
  unfold boundaryCayley
  field_simp
  ring

theorem boundaryCayley_right_inv {u w : ℂ} (hu : ‖u‖=1) (hw : 0<w.re) :
    boundaryCayley u (boundaryCayleyInv u w)=w := by
  have ne : w+1≠0 := by intro eq; have h := congrArg Complex.re eq; simp at h; linarith
  have small := boundaryCayleyInv_disk hu hw
  have den : u-boundaryCayleyInv u w≠0 := sub_ne_zero.mpr fun eq => small.ne (eq ▸ hu)
  unfold boundaryCayley
  apply (div_eq_iff den).mpr
  unfold boundaryCayleyInv
  field_simp
  ring

theorem boundaryCayley_analytic {u z : ℂ} (hu : ‖u‖=1) (hz : ‖z‖<1) : AnalyticAt ℂ (boundaryCayley u) z :=
  (analyticAt_const.add analyticAt_id).div (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr fun e => hz.ne (e ▸ hu))

theorem boundaryCayleyInv_analytic {u w : ℂ} (hw : 0<w.re) : AnalyticAt ℂ (boundaryCayleyInv u) w :=
  (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).div (analyticAt_id.add analyticAt_const)
    (by intro eq; have h := congrArg Complex.re eq; simp at h; linarith)

/-- Conjugating the disk fraction by a Cayley map based at a boundary
fixed point gives a complex affine transformation of the right half-plane. -/
theorem boundaryCayley_fraction_affine {u b k z : ℂ} (hu : ‖u‖=1) (hb : ‖b‖<1) (hz : ‖z‖<1)
    (fix : k*u+b=u*(1+conj b*k*u)) (den : 1+conj b*k*z≠0) (inside : ‖(k*z+b)/(1+conj b*k*z)‖<1) :
    boundaryCayley u ((k*z+b)/(1+conj b*k*z))=
      ((k*u+b)/(u-b))*boundaryCayley u z+(u-k*u)/(u-b) := by
  have a : u-z≠0 := sub_ne_zero.mpr fun e => hz.ne (e ▸ hu)
  have c : u-b≠0 := sub_ne_zero.mpr fun e => hb.ne (e ▸ hu)
  have d : u-(k*z+b)/(1+conj b*k*z)≠0 := sub_ne_zero.mpr fun e => inside.ne (e ▸ hu)
  let m := (k*z+b)/(1+conj b*k*z)
  have frac : m*(1+conj b*k*z)=k*z+b := div_mul_cancel₀ _ den
  change (u+m)/(u-m)=((k*u+b)/(u-b))*((u+z)/(u-z))+(u-k*u)/(u-b)
  apply (div_eq_iff d).mpr
  let t := ((k*u+b)/(u-b))*((u+z)/(u-z))+(u-k*u)/(u-b)
  have clear : t*((u-b)*(u-z))=(k*u+b)*(u+z)+(u-k*u)*(u-z) := by dsimp [t]; field_simp
  apply mul_right_cancel₀ (mul_ne_zero c a)
  calc
    (u+m)*((u-b)*(u-z)) = ((k*u+b)*(u+z)+(u-k*u)*(u-z))*(u-m) := by
      linear_combination 2*u^2*frac+2*m*z*fix
    _ = (t*(u-m))*((u-b)*(u-z)) := by rw [← clear]; ring

/-- An affine complex automorphism of the right half-plane scales
by a positive real number and translates in the imaginary direction. -/
theorem right_half_plane_affine_coefficients {p q : ℂ} (non : p≠0)
    (maps : ∀ w : ℂ, 0<w.re → 0<(p*w+q).re)
    (onto : ∀ y : ℂ, 0<y.re → ∃ w : ℂ, 0<w.re ∧ p*w+q=y) :
    p.im=0 ∧ 0<p.re ∧ q.re=0 := by
  have im : p.im=0 := by
    by_contra ne
    let t := (p.re+q.re)/p.im
    have bad := maps ⟨1,t⟩ (by norm_num)
    change 0<p.re*1-p.im*t+q.re at bad
    dsimp [t] at bad
    have eq : p.im*((p.re+q.re)/p.im)=p.re+q.re := by field_simp
    rw [eq] at bad
    linarith
  have equivReal (s : ℝ) : 0<s ↔ 0<p.re*s+q.re := by
    constructor
    · intro pos
      simpa [Complex.mul_re] using maps (s:ℂ) pos
    · intro pos
      have e : 0<(p*(s:ℂ)+q).re := by simpa [Complex.mul_re] using pos
      obtain ⟨w,hw,eq⟩ := onto _ e
      have ex := mul_left_cancel₀ non (add_right_cancel eq)
      simpa only [ex,Complex.ofReal_re] using hw
  have low : 0≤q.re := by
    have c : Continuous (fun s : ℝ => p.re*s+q.re) := by fun_prop
    have tend : Tendsto (fun s : ℝ => p.re*s+q.re) (𝓝[>] 0) (𝓝 q.re) := by
      simpa only [mul_zero,zero_add] using c.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
    apply ge_of_tendsto tend
    filter_upwards [self_mem_nhdsWithin] with s hs using ((equivReal s).mp hs).le
  have high : q.re≤0 := by
    by_contra! pos
    exact lt_irrefl (0:ℝ) ((equivReal 0).mpr (by simpa using pos))
  have eq := le_antisymm high low
  exact ⟨im,by simpa [eq] using (equivReal 1).mp zero_lt_one,eq⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.right_half_plane_affine_coefficients
