import TwoAxisHelicoid.ExtremalDiskCoordinates
import TwoAxisHelicoid.HolomorphicDiskNormalFamily
import TwoAxisHelicoid.UnivalentHolomorphicLimits
import Mathlib.Topology.Order.IsLUB

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology

/-- The supremal derivative among normalized disk coordinates is
attained in the same class. Compactness gives a holomorphic limit;
the maximum principle excludes boundary values, and Hurwitz controls
both injectivity and all derivatives. -/
theorem normalized_disk_coordinate_attains_maximum {U : Set ℂ} (op : IsOpen U) (conn : IsPreconnected U)
    {p : ℂ} (hp : p∈U) (initial : ∃ f, NormalizedDiskCoordinate U p f) :
    ∃ f, NormalizedDiskCoordinate U p f ∧ ∀ g, NormalizedDiskCoordinate U p g → ‖deriv g p‖≤‖deriv f p‖ := by
  classical
  let A := {a : ℝ | ∃ f, NormalizedDiskCoordinate U p f ∧ ‖deriv f p‖=a}
  obtain ⟨f₀,h₀⟩ := initial
  have nonempty : A.Nonempty := ⟨_,f₀,h₀,rfl⟩
  obtain ⟨r,rp,ballU⟩ := Metric.isOpen_iff.mp op p hp
  have bdd : BddAbove A := by
    refine ⟨1/r,?_⟩
    rintro _ ⟨f,hf,rfl⟩
    apply norm_deriv_le_div_of_mapsTo_ball (hf.analytic.differentiableOn.mono ballU) _ rp
    rw [hf.origin]
    exact fun _ h => ball_subset_closedBall (hf.maps (ballU h))
  have supremum : 0<sSup A := (norm_pos_iff.mpr (h₀.regular p hp)).trans_le
    (le_csSup bdd (show ‖deriv f₀ p‖∈A from ⟨f₀,h₀,rfl⟩))
  obtain ⟨u,_,ul,mem⟩ := exists_seq_tendsto_sSup nonempty bdd
  choose F good vals using mem
  let l := Ultrafilter.of (atTop : Filter ℕ)
  have ll : (l : Filter ℕ)≤atTop := Ultrafilter.of_le atTop
  obtain ⟨f,conv,hol,closed⟩ := bounded_holomorphic_disk_normal_limit l F (U:=U) (by
    intro x hx
    obtain ⟨s,sp,ballS⟩ := Metric.isOpen_iff.mp op x hx
    exact ⟨s,sp,ballS,.of_forall fun i => ⟨(good i).analytic.differentiableOn.mono ballS,
      fun _ h => ball_subset_closedBall ((good i).maps (ballS h))⟩⟩)
  have derivs := conv.deriv (.of_forall fun i => (good i).analytic.differentiableOn) op
  have limitNorm : ‖deriv f p‖=sSup A := by
    apply tendsto_nhds_unique (derivs.tendsto_at hp).norm
    exact (ul.mono_left ll).congr (fun i => (vals i).symm)
  have regP : deriv f p≠0 := norm_pos_iff.mp (limitNorm.trans_gt supremum)
  have base : f p=0 := tendsto_nhds_unique (conv.tendsto_at hp)
    (tendsto_const_nhds.congr fun i => (good i).origin.symm)
  have varying (b : ℂ) (eq : EqOn f (fun _ => b) U) : False := by
    have near : f =ᶠ[𝓝 p] fun _ => b := by filter_upwards [op.mem_nhds hp] with _ h using eq h
    exact regP (near.deriv_eq.trans (deriv_const p b))
  have inside : MapsTo f U complexUnitDisk := by
    intro x hx
    apply mem_ball_zero_iff.mpr
    apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp (closed hx))
    intro eq
    apply varying (f x)
    exact eqOn_of_isPreconnected_of_isMaxOn_norm conn op hol.differentiableOn hx
      (fun y hy => (mem_closedBall_zero_iff.mp (closed hy)).trans_eq eq.symm)
  have inject := nonconstant_univalent_limit_injective op conn conv
    (.of_forall fun i => ⟨(good i).analytic.differentiableOn,(good i).injective⟩) varying
  have derAnalytic : AnalyticOnNhd ℂ (deriv f) U := fun z hz => (hol z hz).deriv
  have regular (z : ℂ) (hz : z∈U) (van : deriv f z=0) : False := by
    have germ := zero_free_holomorphic_limit_local op derivs (.of_forall fun i =>
      ⟨(show AnalyticOnNhd ℂ (deriv (F i)) U from fun w hw => ((good i).analytic w hw).deriv).differentiableOn,
        (good i).regular⟩) hz van
    exact regP (derAnalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero conn hz germ hp)
  refine ⟨f,⟨hol,inside,inject,base,regular⟩,?_⟩
  intro g hg
  rw [limitNorm]
  exact le_csSup bdd ⟨g,hg,rfl⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.normalized_disk_coordinate_attains_maximum
