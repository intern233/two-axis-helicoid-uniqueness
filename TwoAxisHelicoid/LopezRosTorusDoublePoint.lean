import TwoAxisHelicoid.LopezRosImmersionDoublePoint
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology InnerProductSpace
open scoped Topology

/-- A double point near a simple vertical point in the covering plane
is a double point of the actual punctured-torus immersion for all large
positive multipliers. Both preimages can be located in any prescribed
neighborhood of the vertical point. -/
theorem lopez_ros_torus_position_eventually_not_injective
    (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z)
    {a : ℂ} (ha : a ∉ L.lattice) (hm : nullHorizontalMinus (torusImmersionForms L X a) ≠ 0)
    (hh : torusImmersionForms L X a 2 = 0)
    (hs : deriv (fun w => torusImmersionForms L X w 2) a ≠ 0)
    (Y : ℝ → PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hY : ∀ k > 0, ∀ z ∉ L.lattice, HasFDerivAt (puncturedTorusPullback L (Y k))
      (nullRealDerivative (lopezRosCoefficients (k:ℂ) (torusImmersionForms L X z))) z)
    {V : Set (PuncturedPeriodTorus L)} (hV : V ∈ 𝓝 (puncturedPlaneProjection L ⟨a,ha⟩)) :
    ∀ᶠ k : ℝ in atTop, ∃ u ∈ V, ∃ v ∈ V, u ≠ v ∧ Y k u = Y k v := by
  let p := torusImmersionForms L X
  have data := torusImmersionForms_regular L X (fun z hz => (hX z hz).1) (fun z hz => (hX z hz).2)
  let T := fun w : ℂ => w+a
  have hT : Continuous T := continuous_id.add continuous_const
  have e0 : T 0 = a := zero_add _
  obtain ⟨e,hae,he⟩ := periodTorusProjection_isLocalHomeomorph L a
  let U : Set ℂ := T ⁻¹' ((L.lattice:Set ℂ)ᶜ ∩ e.source)
  have hU : IsOpen U := (L.isClosed_lattice.isOpen_compl.inter e.open_source).preimage hT
  have h0U : (0:ℂ) ∈ U := by change T 0 ∈ (L.lattice:Set ℂ)ᶜ ∩ e.source; rw [e0]; exact ⟨ha,hae⟩
  let F : U → PuncturedPeriodTorus L := fun w => puncturedPlaneProjection L ⟨T w.1,w.2.1⟩
  have hF : Continuous F := (puncturedPlaneProjection_isLocalHomeomorph L).continuous.comp
    ((hT.comp continuous_subtype_val).subtype_mk fun w : U => w.2.1)
  let base : U := ⟨0,h0U⟩
  have eb : F base = puncturedPlaneProjection L ⟨a,ha⟩ := by
    apply congrArg (puncturedPlaneProjection L)
    exact Subtype.ext e0
  have hv : F ⁻¹' V ∈ 𝓝 base := hF.continuousAt (eb.symm ▸ hV)
  have hnear : (Subtype.val '' (F ⁻¹' V)) ∈ 𝓝 (0:ℂ) :=
    (hU.isOpenEmbedding_subtypeVal.map_nhds_eq base ▸ Filter.image_mem_map hv)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  have dT (w : ℂ) : HasFDerivAt T (ContinuousLinearMap.id ℝ ℂ) w := (hasFDerivAt_id w).add_const a
  have dz (k : ℝ) (hk : 0 < k) (w : ℂ) (hw : w ∈ ball 0 r) :
      HasFDerivAt (puncturedTorusPullback L (Y k) ∘ T) (nullRealDerivative (lopezRosCoefficients (k:ℂ) (p (T w)))) w := by
    simpa only [ContinuousLinearMap.comp_id] using (hY k hk _ (hball hw).1).comp w (dT w)
  have crosses := lopez_ros_immersions_cross_near_simple_vertical_point (p ∘ T) hr
    (fun w hw => (analyticAt_pi_iff.mpr (data.1 _ (hball hw).1)).comp (analyticAt_id.add analyticAt_const))
    (fun w hw => data.2.1 _ (hball hw).1) (by change nullHorizontalMinus (p (T 0)) ≠ 0; rwa [e0]) (by change p (T 0) 2 = 0; rwa [e0])
    (by
      have d := deriv_comp_add_const (fun w => p w 2) a 0
      change deriv (fun w => p (w+a) 2) 0 ≠ 0
      rw [d,zero_add]
      exact hs)
    (fun k => puncturedTorusPullback L (Y k) ∘ T) dz hnear
  filter_upwards [crosses] with k hk
  obtain ⟨_,⟨u,hu,rfl⟩,_,⟨v,hv,rfl⟩,hne,eq⟩ := hk
  refine ⟨F u,hu,F v,hv,?_,?_⟩
  · intro same
    have projected : periodTorusProjection L (T u.1) = periodTorusProjection L (T v.1) := congrArg Subtype.val same
    rw [he] at projected
    exact hne (add_right_cancel (e.injOn u.2.2 v.2.2 projected))
  · change puncturedTorusPullback L (Y k) (T u.1) = puncturedTorusPullback L (Y k) (T v.1) at eq
    have hou : T u.1 ∉ L.lattice := u.2.1
    have hov : T v.1 ∉ L.lattice := v.2.1
    simpa [puncturedTorusPullback,hou,hov,F] using eq

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lopez_ros_torus_position_eventually_not_injective
