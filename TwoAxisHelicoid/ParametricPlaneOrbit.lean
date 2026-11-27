import TwoAxisHelicoid.PlaneOrbitTemperedDerivative
import TwoAxisHelicoid.PlaneBesselEvaluation
import TwoAxisHelicoid.PlaneTemperedLaplacianTranslations

namespace TwoAxisHelicoid
open MeasureTheory Complex Set TemperedDistribution Real
open scoped SchwartzMap LineDeriv Laplacian ContDiff BoundedContinuousFunction

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

private theorem joint_orbit_direction (u : P → Lp ℂ 2 (volume : Measure ℂ))
    (s : ContDiff ℝ ∞ (fun x : P × ℂ => planeFieldTranslate x.2 (u x.1))) (d : ℂ) :
    ContDiff ℝ ∞ (fun x : P × ℂ => planeFieldTranslate x.2 (planeOrbitDirection (u x.1) d)) := by
  let F := fun x : P × ℂ => planeFieldTranslate x.2 (u x.1)
  have slice (p : P) : ContDiff ℝ ∞ (fun t : ℂ => planeFieldTranslate t (u p)) :=
    s.comp (contDiff_const.prodMk contDiff_id)
  have point (x : P × ℂ) : planeFieldTranslate x.2 (planeOrbitDirection (u x.1) d) =
      fderiv ℝ F x (0,d) := by
    rw [plane_orbit_direction_translate _ (slice x.1)]
    have e := (((s.differentiable (by simp)) x).hasFDerivAt.comp x.2
      (hasFDerivAt_prodMk_right (𝕜:=ℝ) x.1 x.2)).fderiv
    exact congrArg (fun L : ℂ →L[ℝ] Lp ℂ 2 (volume : Measure ℂ) => L d) e
  rw [funext point]
  exact (s.fderiv_right (by simp)).clm_apply contDiff_const

/-- A jointly smooth translation orbit in the energy norm has a single
pointwise representative smooth in both the parameter and the position. -/
theorem parametric_smooth_plane_representative (u : P → Lp ℂ 2 (volume : Measure ℂ))
    (s : ContDiff ℝ ∞ (fun x : P × ℂ => planeFieldTranslate x.2 (u x.1))) :
    ∃ f : P × ℂ → ℂ, ContDiff ℝ ∞ f ∧ ∀ p, ⇑(u p) =ᵐ[volume] (fun z => f (p,z)) := by
  let b := stdOrthonormalBasis ℝ ℂ
  let first := fun (i : Fin (Module.finrank ℝ ℂ)) (p : P) => planeOrbitDirection (u p) (b i)
  let second := fun (i : Fin (Module.finrank ℝ ℂ)) (p : P) => planeOrbitDirection (first i p) (b i)
  let v := fun p => ∑ i, second i p
  have s1 (i) : ContDiff ℝ ∞ (fun x : P × ℂ => planeFieldTranslate x.2 (first i x.1)) :=
    joint_orbit_direction _ s _
  have s2 (i) : ContDiff ℝ ∞ (fun x : P × ℂ => planeFieldTranslate x.2 (second i x.1)) :=
    joint_orbit_direction _ (s1 i) _
  have sv : ContDiff ℝ ∞ (fun x : P × ℂ => planeFieldTranslate x.2 (v x.1)) := by
    simp only [v,map_sum]
    exact ContDiff.sum (fun i _ => s2 i)
  have lap (p : P) : Δ (u p : 𝓢'(ℂ, ℂ)) = (v p : 𝓢'(ℂ, ℂ)) := by
    rw [TemperedDistribution.laplacian_eq_sum b]
    change _=Lp.toTemperedDistributionCLM ℂ volume 2 (∑ i, second i p)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have si : ContDiff ℝ ∞ (fun t : ℂ => planeFieldTranslate t (u p)) :=
      s.comp (contDiff_const.prodMk contDiff_id)
    have sj : ContDiff ℝ ∞ (fun t : ℂ => planeFieldTranslate t (first i p)) :=
      (s1 i).comp (contDiff_const.prodMk contDiff_id)
    rw [plane_explicit_orbit_tempered_derivative _ si (b i)]
    exact plane_explicit_orbit_tempered_derivative _ sj _
  obtain ⟨J,recover⟩ := exists_plane_bessel_evaluation
  let c : ℝ := (-(2*π)^2)⁻¹
  let w := fun p => u p+c • v p
  have sw : ContDiff ℝ ∞ (fun x : P × ℂ => planeFieldTranslate x.2 (w x.1)) := by
    simp only [w,map_add,map_smul]
    exact s.add (sv.const_smul c)
  let f := fun x : P × ℂ => J (planeFieldTranslate x.2 (w x.1)) 0
  let evalZero : (ℂ →ᵇ ℂ) →L[ℝ] ℂ := BoundedContinuousFunction.evalCLM ℝ (0:ℂ)
  have sf : ContDiff ℝ ∞ f := by
    change ContDiff ℝ ∞ (evalZero ∘ (J.restrictScalars ℝ) ∘ (fun x : P × ℂ => planeFieldTranslate x.2 (w x.1)))
    exact evalZero.contDiff.comp ((J.restrictScalars ℝ).contDiff.comp sw)
  refine ⟨f,sf,?_⟩
  intro p
  have input : besselPotential ℂ ℂ 2 (u p : 𝓢'(ℂ,ℂ)) = (w p : 𝓢'(ℂ,ℂ)) := by
    change _=Lp.toTemperedDistributionCLM ℂ volume 2 (u p+c • v p)
    rw [plane_order_two_bessel,lap,map_add,ContinuousLinearMap.map_smul_of_tower]
    rfl
  have rep := recover _ _ input
  have point (t : ℂ) : J (w p) t=f (p,t) := by
    have shifted : besselPotential ℂ ℂ 2 ((planeFieldTranslate t (u p)) : 𝓢'(ℂ,ℂ)) =
        ((planeFieldTranslate t (w p)) : 𝓢'(ℂ,ℂ)) := by
      change _=Lp.toTemperedDistributionCLM ℂ volume 2 (planeFieldTranslate t (u p+c • v p))
      rw [plane_order_two_bessel,plane_laplacian_translate _ _ (lap p),map_add,map_smul,map_add,ContinuousLinearMap.map_smul_of_tower]
      rfl
    have left := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp rep
    have right := recover _ _ shifted
    have ae : (fun z : ℂ => J (w p) (z+t)) =ᵐ[volume] ⇑(J (planeFieldTranslate t (w p))) := by
      filter_upwards [left,right,planeFieldTranslate_ae t (u p)] with z a b e
      exact a.symm.trans (e.symm.trans b)
    have eq := MeasureTheory.Measure.eq_of_ae_eq ae ((J (w p)).continuous.comp (continuous_id.add continuous_const))
      (J (planeFieldTranslate t (w p))).continuous
    simpa only [f,zero_add] using congrFun eq 0
  exact rep.trans (ae_of_all _ point)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.parametric_smooth_plane_representative
