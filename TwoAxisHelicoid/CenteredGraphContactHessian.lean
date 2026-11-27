import TwoAxisHelicoid.CountableGraphSlopeInverses
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace TwoAxisHelicoid
open Complex Filter Set Topology InnerProductSpace
open scoped Topology ContDiff RealInnerProductSpace

private theorem plane_discriminant_ne_zero_of_injective
    (B : (ℝ×ℝ) →L[ℝ] (ℝ×ℝ) →L[ℝ] ℝ) (inj : Function.Injective B)
    (sym : B (1,0) (0,1)=B (0,1) (1,0)) :
    B (1,0) (1,0)*B (0,1) (0,1)-(B (1,0) (0,1))^2≠0 := by
  let ex : ℝ×ℝ := (1,0)
  let ey : ℝ×ℝ := (0,1)
  let a := B ex ex
  let b := B ex ey
  let c := B ey ey
  have vanishes {v : ℝ×ℝ} (hx : B v ex=0) (hy : B v ey=0) : v=0 := by
    apply inj
    apply ContinuousLinearMap.ext
    intro w
    have split : w=w.1 • ex+w.2 • ey := by ext <;> simp [ex,ey]
    calc
      B v w=B v (w.1 • ex+w.2 • ey) := congrArg (B v) split
      _=B 0 w := by simp [hx,hy]
  change a*c-b^2≠0
  intro singular
  by_cases az : a=0
  · have bz : b=0 := by rw [az,zero_mul,zero_sub] at singular; nlinarith
    have impossible := vanishes (v:=ex) az bz
    exact one_ne_zero (congrArg Prod.fst impossible)
  · have kernel := vanishes (v:=b • ex-a • ey) (by
      simp only [map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul]
      change b*a-a*(B ey ex)=0
      rw [← sym]
      dsimp only [b]
      ring) (by
      simp only [map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul]
      change b*b-a*c=0
      nlinarith)
    apply az
    have coord := congrArg Prod.snd kernel
    simpa [ex,ey] using neg_eq_zero.mp (show -a=0 from by simpa [ex,ey] using coord)

theorem centered_graph_contact_hessian {u : ℂ → ℝ} {x s : ℂ} (sm : ContDiffAt ℝ 3 u x)
    (critical : gradient u x=s) (det : (fderiv ℝ (gradient u) x).det≠0) :
    let E := Complex.equivRealProdCLM.symm
    let F := fun z : ℝ×ℝ => u (x+E z)-⟪s,x+E z⟫_ℝ
    ContDiffAt ℝ 3 F 0 ∧ fderiv ℝ F 0=0 ∧
      let B := fderiv ℝ (fderiv ℝ F) 0
      B (1,0) (1,0)*B (0,1) (0,1)-(B (1,0) (0,1))^2≠0 := by
  let E := Complex.equivRealProdCLM.symm
  let A := fun z : ℝ×ℝ => x+E z
  let F := fun z => u (A z)-⟪s,A z⟫_ℝ
  let L : ℂ ≃L[ℝ] ((ℝ×ℝ) →L[ℝ] ℝ) := (toDual ℝ ℂ).toContinuousLinearEquiv.trans
    (E.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
  have at0 : A 0=x := by simp [A]
  have atA (z : ℝ×ℝ) : HasFDerivAt A E.toContinuousLinearMap z := E.hasFDerivAt.const_add x
  have sA : ContDiff ℝ 3 A := contDiff_const.add E.contDiff
  have sm0 : ContDiffAt ℝ 3 u (A 0) := at0.symm ▸ sm
  have sF : ContDiffAt ℝ 3 F 0 := (sm0.comp 0 sA.contDiffAt).sub ((innerSL ℝ s).contDiff.contDiffAt.comp 0 sA.contDiffAt)
  have first : fderiv ℝ F =ᶠ[𝓝 0] fun w => L (gradient u (A w)-s) := by
    filter_upwards [(atA 0).continuousAt.eventually (sm0.eventually (by norm_num))] with z uz
    have du := uz.differentiableAt (by norm_num)
    have d := (du.hasFDerivAt.comp z (atA z)).sub ((innerSL ℝ s).hasFDerivAt.comp z (atA z))
    apply ContinuousLinearMap.ext
    intro v
    rw [show fderiv ℝ F z=_ from d.fderiv]
    change fderiv ℝ u (A z) (E v)-⟪s,E v⟫_ℝ=⟪gradient u (A z)-s,E v⟫_ℝ
    rw [inner_sub_left,inner_gradient_left]
  have crit : fderiv ℝ F 0=0 := by
    rw [first.self_of_nhds]
    change L (gradient u (A 0)-s)=0
    rw [at0,critical,sub_self,map_zero]
  let D := fderiv ℝ (gradient u) x
  have sg : ContDiffAt ℝ 1 (gradient u) x :=
    (toDual ℝ ℂ).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x
      (sm.fderiv_right (m:=1) (by norm_num))
  have g : HasFDerivAt (gradient u) D (A 0) := at0.symm ▸ (sg.differentiableAt one_ne_zero).hasFDerivAt
  have dh := L.hasFDerivAt.comp 0 ((g.comp 0 (atA 0)).sub_const s)
  have hess : fderiv ℝ (fderiv ℝ F) 0=L.toContinuousLinearMap.comp (D.comp E.toContinuousLinearMap) :=
    (first.fderiv_eq (𝕜:=ℝ)).trans dh.fderiv
  have injective : Function.Injective (fderiv ℝ (fderiv ℝ F) 0) := by
    rw [hess]
    exact L.injective.comp ((D.toLinearMap.equivOfDetNeZero det).injective.comp E.injective)
  exact ⟨sF,crit,plane_discriminant_ne_zero_of_injective _ injective (sF.isSymmSndFDerivAt (by norm_num) _ _)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.centered_graph_contact_hessian
