module

public import TwoAxisHelicoid.CompactMovingPreimage
public import Mathlib.Topology.Homeomorph.Lemmas

public section

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology

/-- An ambient homeomorphism preserving each nearby image as a set yields
continuous tracks in the source. Only the central slice needs to be proper. -/
theorem unmarked_compact_core_homeomorphism_lifts {M E : Type*} [TopologicalSpace M] [T2Space M]
    [MetricSpace E] [ProperSpace E] (o : E)
    (cores : ∀ p : M, ∃ K : Set M, IsCompact K ∧ IsConnected K ∧ p ∈ K ∧
      ∀ d : M ≃ₜ M, ∃ a ∈ K, d a ∈ K)
    {X : ℝ → M → E} (joint : ∀ z, ContinuousAt (fun q : ℝ × M => X q.1 q.2) (0,z))
    (proper : IsProperMap (X 0)) (emb : ∀ᶠ s in 𝓝 (0:ℝ), IsEmbedding (X s))
    (R : E ≃ₜ E) (invariant : ∀ᶠ s in 𝓝 (0:ℝ), ∀ y, y ∈ range (X s) ↔ R y ∈ range (X s)) :
    ∃ d : ℝ → M ≃ₜ M, (∀ p, ContinuousAt (fun s => d s p) 0) ∧
      ∀ᶠ s in 𝓝 (0:ℝ), ∀ p, X s (d s p) = R (X s p) := by
  classical
  let P (s : ℝ) := ∃ d : M ≃ₜ M, ∀ p, X s (d p) = R (X s p)
  have existsAction : ∀ᶠ s in 𝓝 (0:ℝ), P s := by
    filter_upwards [emb,invariant] with s es inv
    let e := es.toHomeomorph
    let r : range (X s) ≃ₜ range (X s) := R.subtype inv
    refine ⟨e.trans (r.trans e.symm),?_⟩
    intro p
    exact congrArg Subtype.val (e.apply_symm_apply (r (e p)))
  let d (s : ℝ) := if h : P s then h.choose else Homeomorph.refl M
  have acts : ∀ᶠ s in 𝓝 (0:ℝ), ∀ p, X s (d s p) = R (X s p) := by
    filter_upwards [existsAction] with s hs
    simpa only [d,dite_eq_left hs] using hs.choose_spec
  refine ⟨d,?_,acts⟩
  intro p
  obtain ⟨K,kc,conn,pin,meet⟩ := cores p
  obtain ⟨H,hc,confined⟩ := compact_core_confines_reflected_parameter o joint proper R.continuous
    kc conn pin meet d acts
  have cp : ContinuousAt (fun s => R (X s p)) 0 :=
    R.continuous.continuousAt.comp ((joint p).comp (f := fun s : ℝ => (s,p)) (x := (0:ℝ))
      (continuousAt_id.prodMk continuousAt_const))
  exact continuousAt_of_compact_moving_preimage joint cp emb.self_of_nhds.injective
    (acts.mono fun _ hs => hs p) hc confined

/-- For an involution, the one-sided inclusion given by Schwarz reflection
already implies setwise invariance and hence continuous parameter tracks. -/
theorem unmarked_compact_core_involution_lifts {M E : Type*} [TopologicalSpace M] [T2Space M]
    [MetricSpace E] [ProperSpace E] (o : E)
    (cores : ∀ p : M, ∃ K : Set M, IsCompact K ∧ IsConnected K ∧ p ∈ K ∧
      ∀ d : M ≃ₜ M, ∃ a ∈ K, d a ∈ K)
    {X : ℝ → M → E} (joint : ∀ z, ContinuousAt (fun q : ℝ × M => X q.1 q.2) (0,z))
    (proper : IsProperMap (X 0)) (emb : ∀ᶠ s in 𝓝 (0:ℝ), IsEmbedding (X s))
    {R : E → E} (ct : Continuous R) (inv : Function.Involutive R)
    (sym : ∀ᶠ s in 𝓝 (0:ℝ), ∀ p, R (X s p) ∈ range (X s)) :
    ∃ d : ℝ → M ≃ₜ M, (∀ p, ContinuousAt (fun s => d s p) 0) ∧
      ∀ᶠ s in 𝓝 (0:ℝ), ∀ p, X s (d s p) = R (X s p) := by
  let h : E ≃ₜ E := ⟨⟨R,R,inv,inv⟩,ct,ct⟩
  apply unmarked_compact_core_homeomorphism_lifts o cores joint proper emb h
  filter_upwards [sym] with s hs
  intro y
  constructor
  · rintro ⟨p,rfl⟩
    exact hs p
  · rintro ⟨p,hp⟩
    have eq : R (X s p) = y := (congrArg R hp).trans (inv y)
    exact eq ▸ hs p

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.unmarked_compact_core_homeomorphism_lifts
#print axioms TwoAxisHelicoid.unmarked_compact_core_involution_lifts
