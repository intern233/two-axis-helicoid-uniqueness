import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.UnitInterval

namespace TwoAxisHelicoid
open Set Topology

/-- A smooth homotopy on a genuine closed time interval has jointly
continuous spatial derivatives up to both time endpoints. Only the
spatial parameter is unrestricted locally. -/
theorem interval_homotopy_spatial_derivative_continuous {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {U : Set E} (hU : IsOpen U) {H : ℝ × E → V} (hH : ContDiffOn ℝ 1 H (Icc (0:ℝ) 1 ×ˢ U)) :
    Continuous (fun w : unitInterval × U => fderiv ℝ (fun z => H (w.1.1,z)) w.2.1) := by
  let K := Icc (0:ℝ) 1 ×ˢ U
  let J : E →L[ℝ] (ℝ × E) := (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)
  have hK : UniqueDiffOn ℝ K := (uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1)).prod hU.uniqueDiffOn
  let a (w : unitInterval × U) := (w.1.1,w.2.1)
  have ha : Continuous a := (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  have haK (w : unitInterval × U) : a w ∈ K := ⟨w.1.2,w.2.2⟩
  have hc := (hH.continuousOn_fderivWithin hK le_rfl).comp_continuous ha haK
  have hid (w : unitInterval × U) : fderiv ℝ (fun z => H (w.1.1,z)) w.2.1 =
      (fderivWithin ℝ H K (a w)).comp J := by
    have h := (hH.differentiableOn (by simp) (a w) (haK w)).hasFDerivWithinAt
    have hs : HasFDerivAt (fun z : E => (w.1.1,z)) J w.2.1 :=
      (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
    have hd := h.comp (t := K) (s := U) w.2.1 hs.hasFDerivWithinAt (fun z hz => ⟨w.1.2,hz⟩)
    exact (hd.hasFDerivAt (hU.mem_nhds w.2.2)).fderiv
  simp_rw [hid]
  exact hc.clm_comp continuous_const

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.interval_homotopy_spatial_derivative_continuous
