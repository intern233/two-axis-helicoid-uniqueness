import TwoAxisHelicoid.EvenMeromorphicDoublePole
import TwoAxisHelicoid.HolomorphicImmersionCoordinateChange
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace TwoAxisHelicoid
open Complex Filter Topology
open scoped Topology

/-- The inverse of a holomorphic coordinate fixing the origin has an
explicit simple principal part and a holomorphic remainder. -/
theorem reciprocal_simple_coordinate_expansion {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (h0 : u 0=0) (hn : deriv u 0 ≠ 0) :
    ∃ v : ℂ → ℂ, AnalyticAt ℂ v 0 ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), u z ≠ 0 ∧ (u z)⁻¹ = (deriv u 0)⁻¹/z+v z := by
  let a := dslope u 0
  let b := fun z => (a z)⁻¹
  have ha : AnalyticAt ℂ a 0 := analyticAt_dslope_center hu
  have ea : a 0 = deriv u 0 := dslope_same _ _
  have hb : AnalyticAt ℂ b 0 := ha.inv (ea.trans_ne hn)
  have eu (z : ℂ) : z*a z = u z := by simpa [a,h0,smul_eq_mul] using sub_smul_dslope u 0 z
  have eb (z : ℂ) : z*dslope b 0 z = b z-b 0 := by simpa only [sub_zero,smul_eq_mul] using sub_smul_dslope b 0 z
  refine ⟨dslope b 0,analyticAt_dslope_center hb,?_⟩
  filter_upwards [(ha.continuousAt.eventually_ne (ea.trans_ne hn)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hza hz
  have hz0 : z ≠ 0 := hz
  rw [← eu z]
  refine ⟨mul_ne_zero hz0 hza,?_⟩
  apply mul_left_cancel₀ hz0
  rw [mul_add,mul_div_cancel₀ _ hz0,eb]
  simp [b,ea,mul_inv_rev,field]

/-- A residue-free meromorphic double pole of a one-form stays residue
free in a different local coordinate. The polar coefficient is divided
by the derivative of the coordinate change. -/
theorem residue_free_double_pole_change_coordinate {u f P r : ℂ → ℂ} {A : ℂ}
    (hu : AnalyticAt ℂ u 0) (h0 : u 0=0) (hn : deriv u 0 ≠ 0) (hr : AnalyticAt ℂ r 0)
    (hf : ∀ᶠ z in 𝓝[≠] (0:ℂ), f z=A/z^2+r z)
    (hP : ∀ᶠ z in 𝓝[≠] (0:ℂ), P z=deriv u z*f (u z)) :
    ∃ s : ℂ → ℂ, AnalyticAt ℂ s 0 ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), P z=(A/deriv u 0)/z^2+s z := by
  obtain ⟨v,hv,he⟩ := reciprocal_simple_coordinate_expansion hu h0 hn
  have ur : Tendsto u (𝓝[≠] (0:ℂ)) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,he.mono fun _ h => h.1⟩
    have t : Tendsto u (𝓝[≠] (0:ℂ)) (𝓝 (u 0)) := hu.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rwa [h0] at t
  have reciprocals : (fun z => (u z)⁻¹) =ᶠ[𝓝[≠] (0:ℂ)] fun z => (deriv u 0)⁻¹/z+v z := he.mono fun _ h => h.2
  have hd := (punctured_germ_eventually_local reciprocals).mono fun _ h => h.deriv_eq
  refine ⟨fun z => deriv u z*r (u z)-A*deriv v z,hu.deriv.mul ((show AnalyticAt ℂ r (u 0) by rwa [h0]).comp hu) |>.sub (analyticAt_const.mul hv.deriv),?_⟩
  filter_upwards [he,ur.eventually hf,hP,hd,hu.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    hv.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z he' hF hP' hD hau hav hz
  have hz0 : z ≠ 0 := hz
  have dL := (hau.differentiableAt.hasDerivAt.inv he'.1).deriv
  have dR := (((hasDerivAt_const z (deriv u 0)⁻¹).div (hasDerivAt_id z) hz0).add hav.differentiableAt.hasDerivAt).deriv
  have e : -deriv u z/(u z)^2 = (0*z-(deriv u 0)⁻¹*1)/z^2+deriv v z :=
    dL.symm.trans (hD.trans dR)
  rw [hP',hF]
  linear_combination -A*e

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.residue_free_double_pole_change_coordinate
