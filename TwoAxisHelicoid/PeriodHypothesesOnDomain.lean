import TwoAxisHelicoid.PeriodConclusion

namespace TwoAxisHelicoid
open Set Filter Topology

/-- The bounds use only values on the open vertical solvability interval.
At the two ends of the closed derivative interval the ambient derivatives agree
because these endpoints too are interior to the vertical solvability interval. -/
theorem PeriodHypotheses.transfer_on_domain {F H : ℝ → ℝ} {T : ℝ}
    (h : PeriodHypotheses H T) (eqn : EqOn F H (Ioo (0 : ℝ) T)) :
    PeriodHypotheses F T := by
  have domain {t : ℝ} (pos : 0 < t) (bound : t ≤ 7/5) : t ∈ Ioo (0 : ℝ) T :=
    ⟨pos, bound.trans_lt h.endpoint⟩
  have middle {t : ℝ} (ht : t ∈ Icc (17/20 : ℝ) (9/10)) : t ∈ Ioo (0 : ℝ) T :=
    domain (by linarith [ht.1]) (by linarith [ht.2])
  refine ⟨h.endpoint, h.continuous.congr (fun t ht => eqn (middle ht)), ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [eqn (domain ht.1 (by linarith [ht.2]))]
    exact h.left t ht
  · intro t ht
    rw [eqn (domain (by linarith [ht.1]) (by linarith [ht.2]))]
    exact h.positive t ht
  · intro t ht
    rw [eqn (domain (by linarith [ht.1]) ht.2)]
    exact h.negative t ht
  · intro t ht
    rw [eqn (show t ∈ Ioo (0 : ℝ) T from ⟨by linarith [ht.1], ht.2⟩)]
    exact h.right t ht
  · intro t ht
    have localEq : F =ᶠ[𝓝 t] H := by
      filter_upwards [isOpen_Ioo.mem_nhds (middle ht)] with u hu
      exact eqn hu
    rw [localEq.deriv_eq]
    exact h.derivative t ht

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.PeriodHypotheses.transfer_on_domain
