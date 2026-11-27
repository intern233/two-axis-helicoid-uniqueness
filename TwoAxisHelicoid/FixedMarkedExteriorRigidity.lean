import TwoAxisHelicoid.RemovableCurveMarking
import TwoAxisHelicoid.OriginalExteriorGaussRigidity

namespace TwoAxisHelicoid
open Complex Set Filter Topology Matrix InnerProductSpace
open scoped Topology OnePoint ContDiff Manifold

/-- The exponential exterior on an already marked punctured torus has
the stated Laurent data in that same marking. -/
theorem fixed_marked_exterior_has_end_forms (L : PeriodPair)
    (X : PuncturedPeriodTorus L → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (hc : ∀ d∈atlas ℂ (PuncturedPeriodTorus L), HarmonicImmersionChart X d) (A : GeometricExteriorCoordinate X) :
    MarkedHelicoidalEndForms L X := by
  let M := PuncturedPeriodTorus L
  let f : M ≃ₜ PuncturedPeriodTorus L := Homeomorph.refl _
  have tails := homeomorphic_punctured_surface_connected_tails (0:PeriodTorus L) f
  have cx := (continuous_apply (2:Fin 3)).comp closed.continuous
  have hnc : NoncompactSpace M := noncompact_of_exterior_height A.chart A.target _ cx A.heightOffset A.height
  have hlc : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  have esc := true_exterior_height_coordinate_escapes tails A.chart A.target A.core _ cx A.heightOffset A.height
  let E := exteriorCoordinateComplexEnd A.chart A.positive A.target A.core esc
  let _ := compactifiedEndAtlas E
  have he : E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := reciprocalExteriorChart_mem_maximalAtlas A.chart A.positive A.target A.holomorphic
  let H := f.onePointCongr.trans (punctureCompactification (0:PeriodTorus L))
  have iso := existing_marking_fills_actual_puncture E he f contMDiff_id contMDiff_id
  have h := exterior_forms_in_pointed_filling X hc A esc H rfl iso.1 iso.2
  have eq (q : PuncturedPeriodTorus L) : H.symm q.1=(q:OnePoint M) := H.symm_apply_eq.mpr rfl
  simpa only [eq,OnePoint.elim_some] using h

/-- On the given complex torus the genuine nonvertical conormal
flux, both fixed-data rigidity assertions and the first-order
López–Ros phase condition all use its original marking. -/
theorem fixed_marked_exterior_flux_and_rigidity (L : PeriodPair)
    (X : PuncturedPeriodTorus L → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (hc : ∀ d∈atlas ℂ (PuncturedPeriodTorus L), HarmonicImmersionChart X d) (A : GeometricExteriorCoordinate X) :
    (∃ (q : PuncturedPeriodTorus L) (γ : Path q q) (j : Fin 3) (v : ℝ),
      j≠2 ∧ v≠0 ∧ TorusSpatialConormalIntegral L X j γ v) ∧
    (∀ {k : ℝ → ℂ} {d : ℂ}, HasDerivAt k d 0 → k 0=1 → (LopezRosClosedToFirstOrder L X k ↔ d.re=0)) ∧
    ∀ Y : PuncturedPeriodTorus L → Fin 3 → ℝ,
    (∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧ ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z) →
    (((∀ z ∉ L.lattice, torusImmersionForms L Y z 2=torusImmersionForms L X z 2) ∧
      (∀ z ∉ L.lattice, torusImmersionForms L X z 2≠0 →
        immersionGaussLog (torusImmersionForms L Y) z=immersionGaussLog (torusImmersionForms L X) z)) ∨
     (CommonLaurentPartAt (fun z => torusImmersionForms L X z 2) (fun z => torusImmersionForms L Y z 2) 0 ∧
       ∀ z, CommonLaurentPartAt (immersionGaussLog (torusImmersionForms L X)) (immersionGaussLog (torusImmersionForms L Y)) z)) →
    ∃ (θ : ℝ) (b : Fin 3 → ℝ), (∀ q, Y q=verticalRotation (exp ((θ:ℂ)*I)) (X q)+b) ∧
      ∀ q, torusSphericalGauss L Y q=OnePoint.map (exp ((θ:ℂ)*I)*·) (torusSphericalGauss L X q) := by
  have e := fixed_marked_exterior_has_end_forms L X closed hc A
  have regular z (hz : z ∉ L.lattice) := And.intro (e.regular z hz).1 (e.regular z hz).2.1
  obtain ⟨_,_,_,ar,lg⟩ := e.gauss_expansion
  have reg := torusImmersionForms_regular L X (fun z hz => (e.regular z hz).1) (fun z hz => (e.regular z hz).2.1)
  have nz (z : ℂ) (hz : z ∉ L.lattice) : torusImmersionForms L X z≠0 :=
    immersionComplexCoefficient_regular (analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt ((e.regular z hz).1 j))).differentiableAt (e.regular z hz).2.2
  obtain ⟨a,_,D⟩ := one_end_torus_has_simple_gauss_divisor L _ reg.1 (torusImmersionForms_periodic L X)
    reg.2.1 nz e.height_order ar lg
  have flux := nonvertical_flux_from_exterior_and_simple_point X closed hc A L (Homeomorph.refl _) contMDiff_id X (fun _ => rfl)
    e.regular D.zero_regular D.minus_nonzero D.height_zero D.simple_height_zero
  obtain ⟨q,γ,j,v,hj,hγ,hv⟩ := (torus_spatial_nonvertical_flux_iff L X regular).mpr flux
  refine ⟨⟨q,γ,j,v,hj,hv,hγ⟩,fun hd hk => lopez_ros_first_order_closure_iff_rotation L X regular flux hd hk,?_⟩
  intro Y hY h
  have motion : ∃ (θ : ℝ) (b : Fin 3 → ℝ), ∀ q, Y q=verticalRotation (exp ((θ:ℂ)*I)) (X q)+b := by
    rcases h with ⟨hh,hg⟩ | ⟨hh,hg⟩
    · exact intrinsic_punctured_torus_fixed_log_rigidity L X Y regular hY e.height_order hh hg flux
    · exact intrinsic_punctured_torus_fixed_parts_rigidity L X Y regular hY e.height_order hh hg flux
  obtain ⟨θ,b,hθ⟩ := motion
  exact ⟨θ,b,hθ,torusSphericalGauss_rotate L X Y regular hY (by simp [Complex.norm_exp]) hθ⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.fixed_marked_exterior_has_end_forms
#print axioms TwoAxisHelicoid.fixed_marked_exterior_flux_and_rigidity
