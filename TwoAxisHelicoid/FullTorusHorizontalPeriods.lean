import TwoAxisHelicoid.TorusPathIntegrals
import TwoAxisHelicoid.AllHorizontalPathPeriods
import TwoAxisHelicoid.FullPeriodBranch

namespace TwoAxisHelicoid
open Complex Set

/-- A coordinate period on the punctured torus, with arbitrary piecewise
smooth loops and arbitrary choices of lifts on their constituent arcs. -/
def TorusHorizontalPeriodsVanish (t a c : ℝ) (ht : 0 < t) : Prop :=
  ∀ q : PuncturedPeriodTorus (rhombicPeriodPair t ht), ∀ γ : Path q q,
    ∀ (j : Fin 3), j ≠ 2 → ∀ v : ℂ,
      TorusPathIntegral (rhombicPeriodPair t ht) (fun z => coordinateData t a c ht z j) γ v →
        v.re = 0

/-- The original period criterion intrinsically on the quotient torus.
Every manifold C¹ path has such an integral, and finite concatenations
are included even when the lifts at successive vertices differ. -/
theorem torus_horizontal_periods_iff {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 1)
    (hc : c ≠ 0) (hG : thetaG t a = 0) :
    TorusHorizontalPeriodsVanish t a c ht ↔ thetaHorizontalPeriod t a = 0 := by
  let L := rhombicPeriodPair t ht
  constructor
  · intro h
    apply (all_horizontal_path_periods_iff ht ha hc hG).mp
    intro x y p hxy j hj
    obtain ⟨hx,hy,γ,hγ⟩ := p.projected_hasIntegral (fun z => coordinateData t a c ht z j)
    exact h _ _ j hj _ (hγ.cast rfl (Subtype.ext hxy))
  · intro hH q γ j _ v hp
    obtain ⟨X,hX,hper⟩ := (actual_global_primitive_exists_iff ht ha hc).mpr ⟨hG,hH⟩
    have hf (z : ℂ) (hz : z ∉ L.lattice) : AnalyticAt ℂ (fun w => coordinateData t a c ht w j) z :=
      ((ContinuousLinearMap.proj j : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt _).comp (coordinateData_analyticAt ht hz)
    have he := hp.real_primitive (fun z hz => (hf z hz).continuousAt.continuousWithinAt)
      (fun z hz => actual_coordinate_primitive_component ht hX hz j)
      (fun z ω hω => congrFun (hper z ω hω) j)
    simpa only [sub_self] using he

theorem original_one_period_on_punctured_torus {t c : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper)
    (hc : c ≠ 0) : TorusHorizontalPeriodsVanish t (verticalA t) c ht.1 ↔ actualPeriodAlong t = 0 :=
  torus_horizontal_periods_iff ht.1 (verticalA_spec ht).1 hc (verticalA_spec ht).2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.original_one_period_on_punctured_torus
