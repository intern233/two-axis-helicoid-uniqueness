import TwoAxisHelicoid.OneEndedPlaneCompactAvoidance
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Homotopy.Lifting

namespace TwoAxisHelicoid
open Complex Set Topology Metric

/-- Transport the principal logarithm from a point far to the left to
an omitted point along a path avoiding the given compact set. The
homotopy lifts simultaneously on the whole compact set. -/
theorem compact_logarithm_at_omitted_point {V K : Set ℂ} (op : IsOpen V) (tails : HasConnectedCompactTails V)
    (compact : IsCompact K) (inside : K⊆V) (non : K.Nonempty) {a : ℂ} (outsidePoint : a∉V) :
    ∃ l : C(K,ℂ), ∀ z : K, exp (l z)=z.1-a := by
  obtain ⟨R,paths⟩ := one_ended_plane_compact_avoidance op tails compact inside non
  obtain ⟨S,bound⟩ := compact.isBounded.exists_norm_le
  let B := max (max 0 R) S+1
  have pos : 0<B := by dsimp [B]; linarith [(le_max_left (0:ℝ) R).trans (le_max_left (max 0 R) S)]
  have far : R<B := by dsimp [B]; linarith [(le_max_right (0:ℝ) R).trans (le_max_left (max 0 R) S)]
  let b : ℂ := -(B:ℂ)
  have size : ‖b‖=B := by rw [show b= -(B:ℂ) from rfl,norm_neg,Complex.norm_real,Real.norm_of_nonneg pos.le]
  obtain ⟨γ,away⟩ := (paths a outsidePoint b (size ▸ far)).symm
  let E := {z : ℂ // z≠0}
  let π := fun u : ℂ => (⟨exp u,exp_ne_zero u⟩:E)
  have cov : IsCoveringMap π := Complex.isCoveringMap_exp
  have positive (z : K) : 0<(z.1-b).re := by
    have est := (Complex.abs_re_le_norm z.1).trans (bound z.1 z.2)
    change 0<(z.1- -(B:ℂ)).re
    simp only [sub_neg_eq_add,add_re,ofReal_re]
    dsimp only [B]
    linarith [(abs_le.mp est).1,le_max_right (max 0 R) S]
  let f : C(K,ℂ) := ⟨fun z => log (z.1-b),continuous_iff_continuousAt.mpr fun z =>
    (continuousAt_clog (Or.inl (positive z))).comp (f:=fun w : K => w.1-b) (continuous_subtype_val.continuousAt.sub continuousAt_const)⟩
  let H : C(unitInterval×K,E) := ⟨fun v => ⟨v.2.1-γ v.1,sub_ne_zero.mpr fun eq => away v.1 (eq ▸ v.2.2)⟩,
    ((continuous_subtype_val.comp continuous_snd).sub (γ.continuous.comp continuous_fst)).subtype_mk _⟩
  have lift0 (z : K) : H (0,z)=π (f z) := by
    apply Subtype.ext
    change z.1-γ 0=exp (log (z.1-b))
    rw [γ.source,exp_log (fun eq => (positive z).ne' (congrArg re eq))]
  let G := cov.liftHomotopy H f lift0
  refine ⟨⟨fun z => G (1,z),G.continuous.comp (continuous_const.prodMk continuous_id)⟩,fun z => ?_⟩
  have h := congrArg Subtype.val (congrFun (cov.liftHomotopy_lifts H f lift0) (1,z))
  change exp (G (1,z))=z.1-γ 1 at h
  rwa [γ.target] at h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_logarithm_at_omitted_point
