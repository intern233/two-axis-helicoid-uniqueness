import TwoAxisHelicoid.AlignedSpatialFrame

namespace TwoAxisHelicoid
open Complex Matrix Filter Set
open scoped Topology ContDiff
set_option maxHeartbeats 1300000

theorem aligned_horizontal_unit_ne_zero {a b : ℝ} (h : a^2+b^2=1) : (a:ℂ)-I*b ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp at hr hi
  simp [hr,hi] at h

theorem aligned_nullGauss_formula (a b t e : ℝ) {p q : Fin 3 → ℂ}
    (hq : q = ![(a:ℂ)*p 0-t*b*p 1,(b:ℂ)*p 0+t*a*p 1,(e:ℂ)*p 2])
    (hp : ComplexNull p) (h₂ : p 2 ≠ 0) (hab : a^2+b^2=1) :
    (t=1 → nullGauss q=((e:ℂ)/((a:ℂ)-I*b))*nullGauss p) ∧
    (t=-1 → nullGauss q=(-((e:ℂ)/((a:ℂ)-I*b)))/nullGauss p) := by
  let u : ℂ := (a:ℂ)-I*b
  have hu : u ≠ 0 := aligned_horizontal_unit_ne_zero hab
  obtain ⟨hm,hp'⟩ := null_horizontal_nonzero_of_height hp h₂
  have hh : nullHorizontalPlus p = -(p 2)^2/nullHorizontalMinus p := by
    apply (eq_div_iff hm).mpr
    rw [mul_comm,null_horizontal_product hp]
  have hq₂ : q 2 = (e:ℂ)*p 2 := by rw [hq]; rfl
  constructor
  · rintro rfl
    have he : nullHorizontalMinus q = u*nullHorizontalMinus p := by
      rw [hq]
      change (a:ℂ)*p 0-(1:ℝ)*b*p 1-I*((b:ℂ)*p 0+(1:ℝ)*a*p 1) = u*(p 0-I*p 1)
      dsimp only [u]
      push_cast
      linear_combination -(b:ℂ)*p 1*Complex.I_sq
    unfold nullGauss
    change q 2/nullHorizontalMinus q = (e:ℂ)/u*(p 2/nullHorizontalMinus p)
    rw [hq₂,he,div_mul_div_comm]
  · rintro rfl
    have he : nullHorizontalMinus q = u*nullHorizontalPlus p := by
      rw [hq]
      change (a:ℂ)*p 0-(-1:ℝ)*b*p 1-I*((b:ℂ)*p 0+(-1:ℝ)*a*p 1) = u*(p 0+I*p 1)
      dsimp only [u]
      push_cast
      linear_combination (b:ℂ)*p 1*Complex.I_sq
    unfold nullGauss
    change q 2/nullHorizontalMinus q = -((e:ℂ)/u)/(p 2/nullHorizontalMinus p)
    rw [hq₂,he,hh]
    field_simp

/-- A punctured germ identity gives equality on full neighborhoods of
all sufficiently nearby points distinct from the puncture. -/
theorem punctured_germ_eventually_local {A : Type*} {f g : ℂ → A} {z : ℂ} (he : f =ᶠ[𝓝[≠] z] g) :
    ∀ᶠ y in 𝓝[≠] z, f =ᶠ[𝓝 y] g := by
  filter_upwards [eventually_eventually_nhdsWithin.mpr he,self_mem_nhdsWithin] with y hy hyn
  change ∀ᶠ x in 𝓝 y, f x = g x
  simpa only [isOpen_compl_singleton.nhdsWithin_eq hyn] using hy

/-- A multiplicative or reciprocal Gauss gauge changes its logarithmic
derivative by the corresponding sign on the punctured germ. -/
theorem gauss_log_gauge_germ {f g : ℂ → ℂ} {a z : ℂ} (ha : a ≠ 0)
    (hd : ∀ᶠ y in 𝓝[≠] z, DifferentiableAt ℂ f y ∧ f y ≠ 0)
    (he : (g =ᶠ[𝓝[≠] z] fun w => a*f w) ∨ (g =ᶠ[𝓝[≠] z] fun w => a/f w)) :
    ∃ s : ℂ, s ≠ 0 ∧ (fun w => deriv g w/g w) =ᶠ[𝓝[≠] z] fun w => s*(deriv f w/f w) := by
  rcases he with he | he
  · refine ⟨1,one_ne_zero,?_⟩
    filter_upwards [punctured_germ_eventually_local he,hd] with y hy hf
    rw [hy.deriv_eq,hy.self_of_nhds,(hf.1.hasDerivAt.const_mul a).deriv]
    field_simp [hf.2]
  · refine ⟨-1,neg_ne_zero.mpr one_ne_zero,?_⟩
    filter_upwards [punctured_germ_eventually_local he,hd] with y hy hf
    have hv : HasDerivAt (fun w => a/f w) ((0*f y-a*deriv f y)/(f y)^2) y :=
      (hasDerivAt_const y a).div hf.1.hasDerivAt hf.2
    rw [hy.deriv_eq,hy.self_of_nhds,hv.deriv]
    field_simp [hf.2]
    ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.gauss_log_gauge_germ
