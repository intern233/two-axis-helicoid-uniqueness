import TwoAxisHelicoid.ActualComplexHeight
import TwoAxisHelicoid.HeightFlux
import TwoAxisHelicoid.WeierstrassVerticalDomain

namespace TwoAxisHelicoid
open Complex Set

/-- On any lift of the punctured fundamental domain the conjugate height
acquires a real additive period depending only on the real part of the
deck transformation. -/
theorem actual_height_im_add_lattice {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 1)
    (hG : thetaG t a = 0) {z ω : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hω : ω ∈ (rhombicPeriodPair t ht).lattice) :
    (actualComplexHeight t a c ht (z+ω)).im - (actualComplexHeight t a c ht z).im =
      -(Real.pi*c/t)*ω.re := by
  classical
  let L := rhombicPeriodPair t ht
  let H := actualComplexHeight t a c ht
  let F (v : ℂ) : ℝ := if v ∈ L.lattice then 0 else (H v).im+(Real.pi*c/t)*v.re
  change z ∉ L.lattice at hz
  change ω ∈ L.lattice at hω
  have hwp := (thetaG_zero_iff_wp_level ht ha).mp hG
  have him (v : ℂ) : (H v).im = -c*((thetaZeta t v).re+(L.weierstrassP a).re*v.re) := by
    simp [H,actualComplexHeight,L,Complex.mul_im,Complex.mul_re,rhombic_weierstrassP_real]
  have hgen (u : ℂ) (hu : u ∈ L.lattice)
      (hstep : ∀ v ∉ L.lattice, (thetaZeta t (v+u)).re = (thetaZeta t v).re+(thetaEtaExpression t).re*u.re) :
      Function.Periodic F u := by
    intro v
    by_cases hv : v ∈ L.lattice
    · simp [F,hv,L.lattice.add_mem hv hu]
    · have hv' : v+u ∉ L.lattice := fun hm => hv (by simpa using L.lattice.sub_mem hm hu)
      simp only [F,ite_eq_right hv',ite_eq_right hv,him,hstep v hv,Complex.add_re]
      dsimp [L]
      rw [hwp]
      ring
  have h₁ : Function.Periodic F L.ω₁ := by
    apply hgen _ L.ω₁_mem_lattice
    intro w _
    change (thetaZeta t (w+2)).re = _ + _ * (2:ℂ).re
    rw [thetaZeta_add_two]
    simp [Complex.mul_re,mul_comm]
  have h₂ : Function.Periodic F L.ω₂ := by
    apply hgen _ L.ω₂_mem_lattice
    intro w hw
    change (thetaZeta t (w+(1+I*t))).re = _ + _ * (1+I*t:ℂ).re
    rw [thetaZeta_add_half_of_pos ht ht hw]
    simp [Complex.mul_re,thetaEtaExpression_real]
  have hper : F (z+ω) = F z := by
    obtain ⟨m,n,rfl⟩ := PeriodPair.mem_lattice.mp hω
    simpa only [zsmul_eq_mul] using! ((h₁.zsmul m).add_period (h₂.zsmul n)) z
  have hn : z+ω ∉ L.lattice := fun h => hz (by simpa using L.lattice.sub_mem h hω)
  simp only [F,ite_eq_right hz,ite_eq_right hn,Complex.add_re,H] at hper
  linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_height_im_add_lattice
