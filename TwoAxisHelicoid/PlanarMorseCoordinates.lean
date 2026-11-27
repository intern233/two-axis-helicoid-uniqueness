import TwoAxisHelicoid.PlanarMorseSquareCompletion
import TwoAxisHelicoid.PlanarTaylorBilinearForm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff

private theorem signed_pivots (a b c : ℝ) (regular : a*c-b^2≠0) :
    ∃ m s t : ℝ, s*s=1 ∧ t*t=1 ∧ 0<s*(a+2*m*b+m^2*c) ∧
      0<t*(c-(b+m*c)^2/(a+2*m*b+m^2*c)) := by
  have choice : ∃ m : ℝ, a+2*m*b+m^2*c≠0 := by
    by_contra! none
    have left := none (-1)
    have right := none 1
    have az : a=0 := by simpa using none 0
    norm_num at left right
    have bz : b=0 := by linarith
    exact regular (by simp [az,bz])
  obtain ⟨m,nonzero⟩ := choice
  have schur : c-(b+m*c)^2/(a+2*m*b+m^2*c)≠0 := by
    intro zero
    have eq := (div_eq_iff nonzero).mp (sub_eq_zero.mp zero).symm
    apply regular
    nlinarith [eq]
  have sign {r : ℝ} (nz : r≠0) : ∃ s : ℝ, s*s=1 ∧ 0<s*r := by
    rcases lt_or_gt_of_ne nz with h|h
    · exact ⟨-1,by norm_num,by simpa using neg_pos.mpr h⟩
    · exact ⟨1,by norm_num,by simpa using h⟩
  obtain ⟨s,ss,sp⟩ := sign nonzero
  obtain ⟨t,tt,tp⟩ := sign schur
  exact ⟨m,s,t,ss,tt,sp,tp⟩

/-- A planar C³ function at a nondegenerate critical point has a genuine
local C¹ Morse chart. A linear shear supplies a nonzero diagonal pivot
even when both diagonal entries of the original Hessian vanish. -/
theorem planar_nondegenerate_morse_coordinates {f : ℝ × ℝ → ℝ}
    (sm : ContDiffAt ℝ 3 f 0) (critical : fderiv ℝ f 0=0)
    (det : let H := fderiv ℝ (fderiv ℝ f) 0
      H (1,0) (1,0)*H (0,1) (0,1)-(H (1,0) (0,1))^2≠0) :
    ∃ (s t : ℝ) (J : (ℝ×ℝ) ≃L[ℝ] (ℝ×ℝ)) (e : OpenPartialHomeomorph (ℝ×ℝ) (ℝ×ℝ)),
      s*s=1 ∧ t*t=1 ∧ (0:ℝ×ℝ)∈e.source ∧ e 0=0 ∧
      ContDiffAt ℝ 1 e 0 ∧ ContDiffAt ℝ 1 e.symm 0 ∧
      ∀ᶠ z : ℝ×ℝ in 𝓝 0, f (J z)=f 0+s*(e z).1^2+t*(e z).2^2 := by
  obtain ⟨Q,sq,zero,agree⟩ := planar_critical_taylor_bilinear sm critical
  let ex : ℝ×ℝ := (1,0)
  let ey : ℝ×ℝ := (0,1)
  let a := fun z => Q z ex ex
  let b := fun z => (Q z ex ey+Q z ey ex)/2
  let c := fun z => Q z ey ey
  have entry (v w : ℝ×ℝ) : ContDiff ℝ 1 (fun z => Q z v w) :=
    (sq.clm_apply contDiff_const).clm_apply contDiff_const
  have sb : ContDiff ℝ 1 b := ((entry ex ey).add (entry ey ex)).div_const 2
  have expand (z : ℝ×ℝ) : Q z z z=a z*z.1^2+2*b z*z.1*z.2+c z*z.2^2 := by
    have coord : z=z.1 • ex+z.2 • ey := by ext <;> simp [ex,ey]
    calc Q z z z=Q z (z.1 • ex+z.2 • ey) (z.1 • ex+z.2 • ey) :=
            congrArg₂ (fun v w => Q z v w) coord coord
         _ = _ := by simp [a,b,c,map_add,map_smul,smul_eq_mul]; ring
  have regular : a 0*c 0-(b 0)^2≠0 := by
    have sym := sm.isSymmSndFDerivAt (by norm_num) ey ex
    dsimp only [a,b,c]
    rw [zero]
    simp only [smul_apply,smul_eq_mul,sym]
    change fderiv ℝ (fderiv ℝ f) 0 ex ex*fderiv ℝ (fderiv ℝ f) 0 ey ey-
      (fderiv ℝ (fderiv ℝ f) 0 ex ey)^2≠0 at det
    intro h
    apply det
    nlinarith [h]
  obtain ⟨m,s,t,ss,tt,first,second⟩ := signed_pivots _ _ _ regular
  let J := ((LinearEquiv.refl ℝ ℝ).skewProd (LinearEquiv.refl ℝ ℝ) (m • LinearMap.id)).toContinuousLinearEquiv
  let A := fun z => a (J z)+2*m*b (J z)+m^2*c (J z)
  let B := fun z => b (J z)+m*c (J z)
  let C := fun z => c (J z)
  have sa' := (entry ex ex).comp (J.contDiff (n:=1))
  have sb' := sb.comp (J.contDiff (n:=1))
  have sc' := (entry ey ey).comp (J.contDiff (n:=1))
  have A' : ContDiffAt ℝ 1 A 0 := ((sa'.add (contDiff_const.mul sb')).add (contDiff_const.mul sc')).contDiffAt
  have B' : ContDiffAt ℝ 1 B 0 := (sb'.add (contDiff_const.mul sc')).contDiffAt
  obtain ⟨e,src,at0,se,back,quadratic⟩ := planar_quadratic_coefficient_chart
    A' B' (show ContDiffAt ℝ 1 C 0 from sc'.contDiffAt) s t ss tt
    (by simpa only [A,map_zero] using first) (by simpa only [A,B,C,map_zero] using second)
  refine ⟨s,t,J,e,ss,tt,src,at0,se,back,?_⟩
  have nearby : ∀ᶠ z in 𝓝 0, f (J z)=f 0+Q (J z) (J z) (J z) := by
    have limit : Tendsto J (𝓝 0) (𝓝 0) := by simpa only [map_zero] using (J.continuous.continuousAt (x:=(0:ℝ×ℝ))).tendsto
    exact limit.eventually agree
  filter_upwards [nearby,quadratic] with z hz hq
  rw [hz,expand,add_assoc (f 0) (s*(e z).1^2) (t*(e z).2^2),← hq]
  apply congrArg (f 0+·)
  change a (J z)*z.1^2+2*b (J z)*z.1*(z.2+m*z.1)+c (J z)*(z.2+m*z.1)^2=_
  dsimp only [A,B,C]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.planar_nondegenerate_morse_coordinates
