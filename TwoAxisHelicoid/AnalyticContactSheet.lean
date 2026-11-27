import TwoAxisHelicoid.ParameterizedAnalyticImmersion
import TwoAxisHelicoid.RegularGraphCoordinates

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology

/-- Inverse spatial coordinates of a moving graph sheet. Both identities
hold on actual neighborhoods in the product of time and position. -/
structure AnalyticContactSheet (F : ℝ × ℂ → Fin 3 → ℝ) (t : ℝ) (z : ℂ) where
  inv : ℝ × ℂ → ℂ
  center : inv (t,spatialGraphProjection 0 1 (F (t,z)))=z
  analytic : AnalyticAt ℝ inv (t,spatialGraphProjection 0 1 (F (t,z)))
  right_inv : ∀ᶠ q in 𝓝 (t,spatialGraphProjection 0 1 (F (t,z))), spatialGraphProjection 0 1 (F (q.1,inv q))=q.2
  left_inv : ∀ᶠ q in 𝓝 (t,z), inv (q.1,spatialGraphProjection 0 1 (F q))=q.2

theorem exists_analytic_contact_sheet {F : ℝ × ℂ → Fin 3 → ℝ} {t : ℝ} {z : ℂ}
    (hf : AnalyticAt ℝ F (t,z))
    (hi : Function.Injective ((spatialGraphProjection 0 1).comp (fderiv ℝ (fun w => F (t,w)) z))) :
    Nonempty (AnalyticContactSheet F t z) := by
  let P := spatialGraphProjection 0 1
  let H := P ∘ F
  have ah : AnalyticAt ℝ H (t,z) := (P.analyticAt _).comp hf
  have hz : AnalyticAt ℝ (fun w => F (t,w)) z := hf.comp (analyticAt_const.prod analyticAt_id)
  have dh := P.hasFDerivAt.comp z hz.differentiableAt.hasFDerivAt
  obtain ⟨e,he,hs,hinv⟩ := parameterized_analytic_projection_chart ah (show Function.Injective (fderiv ℝ (fun w => H (t,w)) z) from dh.fderiv.symm ▸ hi)
  have chartEq (q : ℝ × ℂ) : e q=(q.1,H q) := congrFun he q
  have ht : (t,H (t,z)) ∈ e.target := chartEq (t,z) ▸ e.map_source hs
  have center : e.symm (t,H (t,z))=(t,z) := by rw [← chartEq (t,z),e.left_inv hs]
  refine ⟨⟨fun q => (e.symm q).2,congrArg Prod.snd center,
    ((ContinuousLinearMap.snd ℝ ℝ ℂ).analyticAt _).comp hinv,?_,?_⟩⟩
  · filter_upwards [e.open_target.mem_nhds ht] with q hq
    have eq : ((e.symm q).1,H (e.symm q))=q := (chartEq (e.symm q)).symm.trans (e.right_inv hq)
    have e₀ := congrArg Prod.fst eq
    change H (q.1,(e.symm q).2)=q.2
    rw [← e₀]
    exact congrArg Prod.snd eq
  · filter_upwards [e.open_source.mem_nhds hs] with q hq
    change (e.symm (q.1,H q)).2=q.2
    rw [← chartEq q,e.left_inv hq]

noncomputable def AnalyticContactSheet.height {F : ℝ × ℂ → Fin 3 → ℝ} {t : ℝ} {z : ℂ}
    (s : AnalyticContactSheet F t z) (q : ℝ × ℂ) : ℝ := F (q.1,s.inv q) 2

theorem AnalyticContactSheet.analytic_height {F : ℝ × ℂ → Fin 3 → ℝ} {t : ℝ} {z : ℂ}
    (s : AnalyticContactSheet F t z) (hf : AnalyticAt ℝ F (t,z)) :
    AnalyticAt ℝ s.height (t,spatialGraphProjection 0 1 (F (t,z))) := by
  let q := (t,spatialGraphProjection 0 1 (F (t,z)))
  have hin : AnalyticAt ℝ (fun w : ℝ × ℂ => (w.1,s.inv w)) q :=
    ((ContinuousLinearMap.fst ℝ ℝ ℂ).analyticAt _).prod s.analytic
  have ah : AnalyticAt ℝ F (q.1,s.inv q) := by simpa only [q,s.center] using hf
  exact (analyticAt_pi_iff.mp (ah.comp (f := fun w : ℝ × ℂ => (w.1,s.inv w)) hin)) 2

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exists_analytic_contact_sheet
#print axioms TwoAxisHelicoid.AnalyticContactSheet.analytic_height
