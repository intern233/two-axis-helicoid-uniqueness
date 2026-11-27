import TwoAxisHelicoid.SmoothCoreLoopBounds
import TwoAxisHelicoid.TorusLoopBasisDisplacements
import TwoAxisHelicoid.CompactCoreParameterGap

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology Manifold ENNReal
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace

/-- Two actual marked generating curves, represented by smooth plane arcs
on the unit interval. Generation is formulated in the fundamental group
of the compactification, which is canonically its first homology group. -/
structure SmoothGeneratingTorusCurves (L : PeriodPair) where
  base : ℂ
  loop : Fin 2 → Path (periodTorusProjection L base) (periodTorusProjection L base)
  arc : Fin 2 → ComplexPeriodArc (L.lattice : Set ℂ)ᶜ
  left : ∀ i, (arc i).left = 0
  right : ∀ i, (arc i).right = 1
  start : ∀ i, (arc i).curve 0 = base
  projects : ∀ i (s : unitInterval), periodTorusProjection L ((arc i).curve s) = loop i s
  generate : ∀ g : FundamentalGroup (PeriodTorus L) (periodTorusProjection L base),
    ∃ m n : ℤ, g = (FundamentalGroup.fromPath (.mk (loop 0)))^m * (FundamentalGroup.fromPath (.mk (loop 1)))^n

noncomputable def SmoothGeneratingTorusCurves.toBoundedCore {L : PeriodPair} (C : SmoothGeneratingTorusCurves L)
    (X : ℂ → Fin 3 → ℝ) (B : ℝ) (hl : ∀ i, Manifold.pathELength 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      (coordinateToEuclidean ∘ X ∘ (C.arc i).curve) 0 1 ≤ ENNReal.ofReal B) : BoundedGeneratingCore L X B := by
  have hω i : (C.arc i).curve 1-C.base ∈ L.lattice := by
    apply (periodTorusProjection_eq_iff L C.base _).mp
    exact ((C.projects i 1).trans (C.loop i).target).symm
  let ω := fun i => (⟨(C.arc i).curve 1-C.base,hω i⟩ : L.lattice)
  let f (i : Fin 2) : C(unitInterval,ℂ) := ⟨fun s => (C.arc i).curve s,
    continuousOn_iff_continuous_domRestrict.mp (by simpa only [C.left,C.right] using (C.arc i).continuous_curve)⟩
  have hspan := torus_generating_loops_span_deck L C.base C.loop f ω (fun i => funext (C.projects i)) C.start
    (fun i => by change (C.arc i).curve 1 = C.base+((C.arc i).curve 1-C.base); ring) C.generate
  exact { arc := C.arc
          closed := fun i => by simpa only [C.left,C.right,C.start] using hω i
          generate := by simpa only [C.left,C.right,C.start,ω] using hspan
          length_bound := fun i => by simpa only [C.left,C.right] using hl i }

/-- Uniform C¹ transport on two actual loops supplies the common length
bound and integral deck-generation requirement in the flux argument. -/
theorem smooth_generator_transport_gives_bounded_cores {L : ℕ → PeriodPair}
    (X : ℕ → ℂ → Fin 3 → ℝ) (C : ∀ n, SmoothGeneratingTorusCurves (L n))
    (v : Fin 2 → ℝ → EuclideanSpace ℝ (Fin 3)) (hv : ∀ i, ContinuousOn (v i) (Icc 0 1))
    (hC : ∀ i, TendstoUniformlyOn (fun n => deriv (coordinateToEuclidean ∘ X n ∘ ((C n).arc i).curve))
      (v i) atTop (Icc 0 1)) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, Nonempty (BoundedGeneratingCore (L n) (X n) B) := by
  obtain ⟨B,hB,h₀⟩ := bounded_lengths_of_uniformly_convergent_core_velocities (hv 0) (hC 0)
  obtain ⟨D,_,h₁⟩ := bounded_lengths_of_uniformly_convergent_core_velocities (hv 1) (hC 1)
  refine ⟨max B D,hB.trans (le_max_left ..),?_⟩
  filter_upwards [h₀,h₁] with n hn hm
  refine ⟨(C n).toBoundedCore (X n) _ (fun i => ?_)⟩
  fin_cases i
  · exact hn.trans (ENNReal.ofReal_le_ofReal (le_max_left ..))
  · exact hm.trans (ENNReal.ofReal_le_ofReal (le_max_right ..))

/-- The actual input from the smooth compact-core limit is a transported
pair of generating loops with convergent velocities on each compact
parameter interval. -/
def HasSubsequentialSmoothGeneratingCurves (S : Set PitchNormalizedBasicImmersion) : Prop :=
  ∀ x : ℕ → S, ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ C : ∀ n, SmoothGeneratingTorusCurves (rhombicPeriodPair (x (φ n)).1.t (x (φ n)).1.ht),
      ∃ v : Fin 2 → ℝ → EuclideanSpace ℝ (Fin 3), (∀ i, ContinuousOn (v i) (Icc 0 1)) ∧
        ∀ i, TendstoUniformlyOn (fun n => deriv (coordinateToEuclidean ∘ (x (φ n)).1.position ∘ ((C n).arc i).curve))
          (v i) atTop (Icc 0 1)

theorem smooth_generating_curves_give_subsequential_bounded_cores {S : Set PitchNormalizedBasicImmersion}
    (hs : HasSubsequentialSmoothGeneratingCurves S) : HasSubsequentialBoundedGeneratingCores S := by
  intro x
  obtain ⟨φ,hφ,C,v,hv,hC⟩ := hs x
  obtain ⟨B,hB,h⟩ := smooth_generator_transport_gives_bounded_cores (fun n => (x (φ n)).1.position) C v hv hC
  obtain ⟨N,hN⟩ := eventually_atTop.1 h
  exact ⟨fun n => φ (n+N),B,hφ.comp (strictMono_id.add_const N),hB,fun n => hN (n+N) (Nat.le_add_left ..)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_generating_curves_give_subsequential_bounded_cores
