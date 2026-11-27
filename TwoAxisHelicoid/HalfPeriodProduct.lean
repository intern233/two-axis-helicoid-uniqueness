import TwoAxisHelicoid.EllipticPrincipalPart
import Mathlib.Analysis.Analytic.Order

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology

/-- The periods of a symmetric product with its half-period translate. -/
noncomputable def halfFirstPeriodPair (L : PeriodPair) : PeriodPair where
  ω₁ := L.ω₁ / 2
  ω₂ := L.ω₂
  indep := by
    apply LinearIndependent.pair_iff.mpr
    intro x y h
    have e := LinearIndependent.pair_iff.mp L.indep (x/2) y (by
      simpa [Complex.real_smul] using (show (x : ℂ)/2*L.ω₁ + y*L.ω₂ = 0 by
        change (x : ℂ)*(L.ω₁/2)+(y : ℂ)*L.ω₂ = 0 at h
        linear_combination h))
    exact ⟨by linarith [e.1], e.2⟩

theorem lattice_le_halfFirstPeriodPair (L : PeriodPair) :
    L.lattice ≤ (halfFirstPeriodPair L).lattice := by
  intro z hz
  obtain ⟨m,n,rfl⟩ := PeriodPair.mem_lattice.mp hz
  apply PeriodPair.mem_lattice.mpr
  refine ⟨2*m,n,?_⟩
  change ((2*m : ℤ) : ℂ)*(L.ω₁/2)+n*L.ω₂ = _
  push_cast
  ring

/-- Reflection cancels a possible simple pole. All nonzero points of order
two therefore have the same function value, the constant Laurent coefficient. -/
theorem elliptic_simple_pole_half_value (L : PeriodPair) {f g : ℂ → ℂ} {A : ℂ}
    (hf : AnalyticOnNhd ℂ f (L.lattice : Set ℂ)ᶜ)
    (hp : ∀ z ω, ω ∈ L.lattice → f (z+ω) = f z) (hg : AnalyticAt ℂ g 0)
    (hloc : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → f z = A/z+g z)
    {z : ℂ} (hz : z ∉ L.lattice) (h2 : z+z ∈ L.lattice) : f z = g 0 := by
  have he := elliptic_removable_puncture_constant L
    (f := fun w => f w+f (-w)) (g := fun w => g w+g (-w))
    (fun w hw => (hf w hw).differentiableAt.add
      ((hf (-w) (fun hn => hw (by simpa using L.lattice.neg_mem hn))).differentiableAt.comp
        w differentiableAt_id.neg))
    (fun w ω hω => by
      rw [neg_add,hp w ω hω,hp (-w) (-ω) (L.lattice.neg_mem hω)])
    (hg.add ((show AnalyticAt ℂ g (-(0 : ℂ)) by simpa using hg).comp analyticAt_id.neg)) (by
      have hl := (continuous_neg.continuousAt (x := (0 : ℂ))).eventually (by
        simpa using hloc : ∀ᶠ v in 𝓝 (-(0 : ℂ)), v ≠ 0 → f v = A/v+g v)
      filter_upwards [hloc,hl] with w hw hw' hn
      rw [hw hn,hw' (neg_ne_zero.mpr hn),div_neg]; ring) z hz
  have hper := hp (-z) (z+z) h2
  rw [show -z+(z+z)=z by ring] at hper
  simp only [neg_zero,← hper] at he
  linear_combination he/2

/-- Product with a half-period translate acquires a removable singularity
when the translate vanishes at zero. -/
theorem elliptic_half_product_constant (L : PeriodPair) {f g : ℂ → ℂ} {A : ℂ}
    (hf : AnalyticOnNhd ℂ f (L.lattice : Set ℂ)ᶜ)
    (hp : ∀ z ω, ω ∈ L.lattice → f (z+ω) = f z) (hg : AnalyticAt ℂ g 0)
    (hloc : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → f z = A/z+g z) (hh : f (L.ω₁/2) = 0) :
    ∃ k : ℂ, ∀ z ∉ (halfFirstPeriodPair L).lattice, f z*f (z+L.ω₁/2) = k := by
  let D := halfFirstPeriodPair L
  let h := L.ω₁/2
  let P := fun z => f z*f (z+h)
  have hD : h ∈ D.lattice := D.ω₁_mem_lattice
  have hP : Function.Periodic P h := by
    intro z
    change f (z+h)*f (z+h+h) = f z*f (z+h)
    rw [show z+h+h = z+L.ω₁ by dsimp [h]; ring,hp z _ L.ω₁_mem_lattice,mul_comm]
  have hQ : Function.Periodic P L.ω₂ := by
    intro z
    change f (z+L.ω₂)*f (z+L.ω₂+h) = f z*f (z+h)
    rw [show z+L.ω₂+h = (z+h)+L.ω₂ by ring,hp _ _ L.ω₂_mem_lattice,hp _ _ L.ω₂_mem_lattice]
  have hper (z ω : ℂ) (hω : ω ∈ D.lattice) : P (z+ω) = P z := by
    obtain ⟨m,n,rfl⟩ := PeriodPair.mem_lattice.mp hω
    simpa only [zsmul_eq_mul] using! ((hP.zsmul m).add_period (hQ.zsmul n)) z
  have ha : AnalyticAt ℂ (fun z => f (z+h)) 0 :=
    (show AnalyticAt ℂ f (0+h) by simpa [h] using hf _ L.ω₁_div_two_notMem_lattice).comp (f := fun z : ℂ => z+h)
      (analyticAt_id.add analyticAt_const)
  obtain ⟨r,hr,he⟩ := ha.exists_eventuallyEq_sum_add_pow_mul 1
  have he' : ∀ᶠ z in 𝓝 (0 : ℂ), f (z+h) = z*r z := by
    simpa [hh,h,smul_eq_mul] using he
  refine ⟨(A+0*g 0)*r 0, elliptic_removable_puncture_constant D
    (f := P) (g := fun z => (A+z*g z)*r z) ?_ hper
    ((analyticAt_const.add (analyticAt_id.mul hg)).mul hr) ?_⟩
  · intro z hz
    have hzh : z+h ∉ L.lattice := fun hm => hz (by
      simpa only [add_sub_cancel_right] using D.lattice.sub_mem (lattice_le_halfFirstPeriodPair L hm) hD)
    exact (hf z (fun hm => hz (lattice_le_halfFirstPeriodPair L hm))).differentiableAt.mul
      ((hf _ hzh).differentiableAt.comp z (differentiableAt_id.add_const h))
  · filter_upwards [hloc,he'] with z hz hez hn
    change f z*f (z+h) = _
    rw [hz hn,hez]
    field_simp
end TwoAxisHelicoid
