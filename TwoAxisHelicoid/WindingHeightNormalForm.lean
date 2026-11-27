import TwoAxisHelicoid.MeromorphicHeightPowerCoordinate
import TwoAxisHelicoid.EvenMeromorphicDoublePole
import Mathlib.Analysis.Calculus.Deriv.ZPow

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology

/-- Two simple poles on the same punctured disk have a unique
proportional leading part. In the reciprocal height coordinate, a
nonvanishing Gauss factor therefore has an integer power, a linear
exponential and a unit holomorphic at infinity. -/
theorem winding_height_normal_form {H F g : ℂ → ℂ} {n : ℤ}
    (hm : MeromorphicAt H 0) (fm : MeromorphicAt F 0)
    (ho : meromorphicOrderAt H 0=((-1:ℤ):WithTop ℤ)) (fo : meromorphicOrderAt F 0=((-1:ℤ):WithTop ℤ))
    (data : ∀ᶠ z in 𝓝[≠] (0:ℂ), g z=z^n*exp (F z)) :
    ∃ (k B : ℂ → ℂ) (c : ℂ), AnalyticAt ℂ k 0 ∧ k 0=0 ∧ Tendsto k (𝓝[≠] 0) (𝓝[≠] 0) ∧
      AnalyticAt ℂ B 0 ∧ B 0≠0 ∧ c≠0 ∧ (∀ᶠ z in 𝓝[≠] (0:ℂ), k ((H z)⁻¹)=z) ∧ ∀ᶠ w in 𝓝[≠] (0:ℂ),
        H (k w)=w⁻¹ ∧ g (k w)=w^n*exp (c/w)*B w := by
  obtain ⟨u,ua,un,hu⟩ := (meromorphicOrderAt_eq_int_iff hm).mp ho
  obtain ⟨v,va,vn,hv⟩ := (meromorphicOrderAt_eq_int_iff fm).mp fo
  let c := v 0/u 0
  let d := fun z => v z-c*u z
  let J := dslope d 0
  have dz : d 0=0 := by dsimp [d,c]; field_simp [un]; ring
  have ja : AnalyticAt ℂ J 0 := analyticAt_dslope_center (va.sub (analyticAt_const.mul ua))
  obtain ⟨p,k,_,ka,p0,k0,right,left,height⟩ := meromorphic_pole_power_coordinate hm (n := 1) (by decide) (by simpa using ho)
  have lim : Tendsto k (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa only [k0] using ka.continuousAt.continuousWithinAt.tendsto,?_⟩
    filter_upwards [right.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w r nw
    intro bad
    change k w=0 at bad
    apply nw
    change w=0
    rw [← r,bad,p0]
  let B := fun w => (u (k w))^n*exp (J (k w))
  have ba : AnalyticAt ℂ B 0 := (((ua.comp_of_eq ka k0).zpow (n := n) (by simpa only [Function.comp_apply,k0] using un)).mul
    (analyticAt_cexp.comp (ja.comp_of_eq ka k0)))
  have inverse : ∀ᶠ z in 𝓝[≠] (0:ℂ), k ((H z)⁻¹)=z := by
    filter_upwards [height,left.filter_mono nhdsWithin_le_nhds] with z h l
    rw [h,pow_one,inv_inv]
    exact l
  refine ⟨k,B,c,ka,k0,lim,ba,by dsimp [B]; rw [k0]; exact mul_ne_zero (zpow_ne_zero _ un) (exp_ne_zero _),
    div_ne_zero vn un,inverse,?_⟩
  filter_upwards [lim.eventually (hu.and (hv.and (height.and data))),lim.eventually self_mem_nhdsWithin,
      right.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w facts nz inv nw
  obtain ⟨h,f,hh,gg⟩ := facts
  have h' : H (k w)=u (k w)/(k w) := by simpa [div_eq_inv_mul,smul_eq_mul] using h
  have f' : F (k w)=v (k w)/(k w) := by simpa [div_eq_inv_mul,smul_eq_mul] using f
  have value : H (k w)=w⁻¹ := by simpa only [inv,pow_one] using hh
  have nk : k w≠0 := nz
  have nw' : w≠0 := nw
  have ratio : u (k w)/(k w)=1/w := h'.symm.trans (value.trans (one_div w).symm)
  have ku : k w=w*u (k w) := by simpa only [one_mul,mul_one,mul_comm] using ((div_eq_div_iff nk nw').mp ratio).symm
  have jj : J (k w)=(v (k w)-c*u (k w))/(k w) := by
    rw [show J (k w)=slope d 0 (k w) from dslope_of_ne _ nz,slope_def_field,dz,sub_zero,sub_zero]
  have split : F (k w)=c/w+J (k w) := by
    rw [f',jj]
    calc
      _ = c*(u (k w)/k w)+(v (k w)-c*u (k w))/k w := by ring
      _ = _ := by rw [ratio]; ring
  refine ⟨value,?_⟩
  rw [gg,split,exp_add,show (k w)^n=w^n*(u (k w))^n from (congrArg (fun z : ℂ => z^n) ku).trans (mul_zpow _ _ _)]
  dsimp [B]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.winding_height_normal_form
