import TwoAxisHelicoid.SmoothParameterCoefficient
import TwoAxisHelicoid.BoundedCoefficientMultiplier
import TwoAxisHelicoid.PlaneWeakConductivity
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import TwoAxisHelicoid.FrozenPlaneConductivity

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Metric Filter Topology
open scoped ContDiff BoundedContinuousFunction

/-- Taking translated spatial slices of a compact smooth family also depends
smoothly on both variables in the actual energy norm. -/
theorem exists_smooth_compact_parameter_field {f : ℝ × ℂ → ℝ} (s : ContDiff ℝ ∞ f)
    (h : HasCompactSupport f) (c : ℂ) :
    ∃ b : ℝ × ℂ → Lp ℂ 2 (volume:Measure ℂ), ContDiff ℝ ∞ b ∧
      ∀ t, ⇑(b t) =ᵐ[volume] (fun z => f (t.1,z+t.2) • c) := by
  let F := compactParameterTrace f s.continuous h
  let J := Classical.choose exists_bounded_coefficient_multiplier
  have hJ : ∀ f w, ⇑(J f w) =ᵐ[volume] (fun z => f z • w z) :=
    Classical.choose_spec exists_bounded_coefficient_multiplier
  obtain ⟨R,_,cover⟩ := h.isBounded.subset_ball_lt 0 (0:ℝ × ℂ)
  let disk (r : ℝ) : Lp ℂ 2 (volume:Measure ℂ) :=
    indicatorConstLp 2 (isOpen_ball (x:=(0:ℂ)) (ε:=r)).measurableSet measure_ball_lt_top.ne c
  have disk_ae (r : ℝ) : ⇑(disk r) =ᵐ[volume] (ball (0:ℂ) r).indicator (fun _ => c) :=
    indicatorConstLp_coeFn
  let v := fun (r : ℝ) (t : ℝ × ℂ) => J (F t) (disk r)
  have smooth (r : ℝ) : ContDiff ℝ ∞ (v r) :=
    (J.contDiff.comp (smooth_compactParameterTrace s h)).clm_apply contDiff_const
  have rep (r : ℝ) (t : ℝ × ℂ) (inside : R+‖t.2‖≤r) :
      ⇑(v r t) =ᵐ[volume] (fun z => f (t.1,z+t.2) • c) := by
    filter_upwards [hJ (F t) (disk r),disk_ae r] with z hv hd
    change J (F t) (disk r) z=_
    rw [hv,hd]
    change f (t.1,z+t.2) • (ball (0:ℂ) r).indicator (fun _ => c) z=_
    by_cases hz : z∈ball (0:ℂ) r
    · rw [indicator_of_mem hz]
    · have out : (t.1,z+t.2)∉tsupport f := by
        intro m
        have small := mem_ball.mp (cover m)
        rw [dist_zero_right] at small
        have sz := lt_of_le_of_lt (norm_snd_le (t.1,z+t.2)) small
        have far : r≤‖z‖ := by simpa [mem_ball,dist_eq_norm] using hz
        have tri : ‖z‖≤‖z+t.2‖+‖t.2‖ := by simpa using norm_sub_le (z+t.2) t.2
        change ‖z+t.2‖<R at sz
        linarith
      simp [image_eq_zero_of_notMem_tsupport out]
  let b := fun t : ℝ × ℂ => v (R+‖t.2‖) t
  have actual (t : ℝ × ℂ) : ⇑(b t) =ᵐ[volume] (fun z => f (t.1,z+t.2) • c) :=
    rep _ t le_rfl
  refine ⟨b,contDiff_iff_contDiffAt.mpr (fun t => ?_),actual⟩
  let r := R+‖t.2‖+1
  apply (smooth r).contDiffAt.congr_of_eventuallyEq
  have openNear : ∀ᶠ y : ℝ × ℂ in 𝓝 t, ‖y.2‖<‖t.2‖+1 :=
    (continuous_snd.norm.continuousAt).eventually_lt continuousAt_const (by linarith)
  filter_upwards [openNear] with y hy
  exact Lp.ext ((actual y).trans (rep r y (by dsimp [r]; linarith)).symm)

/-- The affine load is the difference between the constant reference flux
at the prescribed point and the rescaled conductivity acting on 1. -/
theorem exists_frozen_plane_load (A : ℂ → ℝ) {B C : ℂ → ℝ}
    (sb : ContDiff ℝ ∞ B) (sc : ContDiff ℝ ∞ C) (p : ℂ) :
    ∃ b : ℝ × ℂ → Lp ℂ 2 (volume:Measure ℂ), ContDiff ℝ ∞ b ∧
      ∀ t, ⇑(b t) =ᵐ[volume] (fun z => planeMetricFlux A B C p 1 -
        planeMetricFlux (planeFrozenCoefficient A p t.1) (planeFrozenCoefficient B p t.1)
          (planeFrozenCoefficient C p t.1) (z+t.2) 1) := by
  obtain ⟨u,su,hu⟩ := exists_smooth_compact_parameter_field (planeFreezePerturbation_smooth sc p)
    (planeFreezePerturbation_compact C p) (-1)
  obtain ⟨v,sv,hv⟩ := exists_smooth_compact_parameter_field (planeFreezePerturbation_smooth sb p)
    (planeFreezePerturbation_compact B p) I
  refine ⟨fun t => u t+v t,su.add sv,?_⟩
  intro t
  filter_upwards [Lp.coeFn_add (u t) (v t),hu t,hv t] with z h x y
  rw [h,Pi.add_apply,x,y]
  apply Complex.ext <;> simp [planeMetricFlux,planeFrozenCoefficient]
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exists_frozen_plane_load
