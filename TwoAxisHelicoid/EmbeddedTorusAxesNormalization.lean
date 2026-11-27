import TwoAxisHelicoid.TorusTwoReflections
import TwoAxisHelicoid.EmbeddedAxisFixedLocus
import TwoAxisHelicoid.EmbeddedSymmetryAlgebra
import TwoAxisHelicoid.SimilaritySymmetry

namespace TwoAxisHelicoid
open Complex Set Topology

theorem periodTorus_t2Space (L : PeriodPair) : T2Space (PeriodTorus L) := by
  let : T1Space (PeriodTorus L) := QuotientAddGroup.t1Space_iff.mpr L.isClosed_lattice
  infer_instance

theorem halfTurnX_involutive : Function.Involutive halfTurnX := by
  intro v
  ext j
  fin_cases j <;> simp [halfTurnX]

theorem halfTurnZ_involutive : Function.Involutive halfTurnZ := by
  intro v
  ext j
  fin_cases j <;> simp [halfTurnZ]

theorem halfTurnX_halfTurnZ_commute : Function.Commute halfTurnX halfTurnZ := by
  intro v
  ext j
  fin_cases j <;> simp [halfTurnX,halfTurnZ]

theorem halfTurnX_fixed_iff (v : Fin 3 → ℝ) :
    halfTurnX v = v ↔ v ∈ range (fun r : ℝ => ![r,0,0]) := by
  constructor
  · intro h
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    change -v 1 = v 1 at h1
    change -v 2 = v 2 at h2
    have hv1 : v 1 = 0 := by linarith
    have hv2 : v 2 = 0 := by linarith
    refine ⟨v 0,?_⟩
    ext j
    fin_cases j <;> simp [hv1,hv2]
  · rintro ⟨r,rfl⟩
    simp [halfTurnX]

/-- The actual ambient half-turns of an embedded punctured complex torus,
with its complete horizontal axis, force all hypotheses of the simultaneous
rhombic normalization. The conformal compactification and Schwarz reflection
action are deliberately visible inputs. -/
theorem embedded_torus_axes_rhombic_normalization (L : PeriodPair)
    {X : PeriodTorus L → Fin 3 → ℝ}
    (hX : ∀ q ≠ 0, ContinuousAt X q)
    (hEmb : IsEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (haxis : ∀ r : ℝ, ∃ q : PuncturedPeriodTorus L, X q.1 = ![r,0,0])
    (f g : PeriodTorus L ≃ₜ PeriodTorus L)
    (hf : TorusAntiholomorphic L L f) (hg : TorusAntiholomorphic L L g)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (heqf : ∀ q ≠ 0, X (f q) = halfTurnX (X q))
    (heqg : ∀ q ≠ 0, X (g q) = halfTurnZ (X q)) :
    ∃ (s : ℂ) (t : ℝ) (hs : s ≠ 0) (ht : 0 < t)
      (hp : ∀ z : ℂ, z ∈ L.lattice ↔ s*z ∈ (rhombicPeriodPair t ht).lattice),
      let e := periodTorusScalingHomeomorph L (rhombicPeriodPair t ht) s hs hp
      (∀ q, e (f q) = rhombicHorizontalReflection ht (e q)) ∧
      (∀ q, e (g q) = rhombicVerticalReflection ht (e q)) := by
  let := periodTorus_compactSpace L
  let := periodTorus_t2Space L
  have hfi := embedded_equivariant_involution hEmb f hf0 halfTurnX_involutive heqf
  have hgi := embedded_equivariant_involution hEmb g hg0 halfTurnZ_involutive heqg
  have hcomm := embedded_equivariant_commute hEmb f g hf0 hg0 halfTurnX_halfTurnZ_commute heqf heqg
  have hne : (f : PeriodTorus L → PeriodTorus L) ≠ g := by
    intro he
    obtain ⟨q,hq⟩ := haxis 1
    have h := congrArg X (congrFun he q.1)
    rw [heqf q.1 q.2,heqg q.1 q.2,hq] at h
    have h0 := congrFun h 0
    norm_num [halfTurnX,halfTurnZ] at h0
  have hconn : IsConnected {q : PeriodTorus L | f q = q} :=
    embedded_axis_reflection_fixed_locus_connected hX hEmb
      (show Continuous (fun r : ℝ => ![r,0,0]) by fun_prop)
      (show Continuous (fun v : Fin 3 → ℝ => v 0) from continuous_apply 0)
      (fun _ => rfl) haxis halfTurnX_fixed_iff f.continuous hf0 hfi heqf
  exact torus_two_reflections_rhombic_normalization L hf hg hf0 hg0 hfi hgi hcomm hne hconn.2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.embedded_torus_axes_rhombic_normalization
