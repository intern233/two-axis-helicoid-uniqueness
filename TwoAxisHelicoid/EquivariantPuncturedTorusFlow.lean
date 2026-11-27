import TwoAxisHelicoid.PeriodTorusTopology
import Mathlib.Topology.Homeomorph.Lemmas

namespace TwoAxisHelicoid
open Complex Set Topology

/-- Descent of a lattice-equivariant plane homeomorphism preserves the
actual quotient and its marked puncture, with the same projection on
both sides. -/
theorem equivariant_punctured_torus_homeomorph (L : PeriodPair) (F : ℂ ≃ₜ ℂ)
    (per : ∀ z w, w∈L.lattice → F (z+w)=F z+w) (fixed : F 0=0) :
    ∃ E : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus L,
      (∀ (q : PuncturedPeriodTorus L) (z : ℂ), periodTorusProjection L z=q.1 →
        (E q).1=periodTorusProjection L (F z)) ∧
      ∀ (q : PuncturedPeriodTorus L) (z : ℂ), periodTorusProjection L z=q.1 →
        (E.symm q).1=periodTorusProjection L (F.symm z) := by
  have back (z w : ℂ) (hw : w∈L.lattice) : F.symm (z+w)=F.symm z+w := by
    apply F.injective
    rw [F.apply_symm_apply,per _ w hw,F.apply_symm_apply]
  have invariant (f : ℂ → ℂ) (p : ∀ z w, w∈L.lattice → f (z+w)=f z+w) (z w : ℂ) (hw : w∈L.lattice) :
      periodTorusProjection L (f (z+w))=periodTorusProjection L (f z) := by
    rw [p _ _ hw,periodTorusProjection_add_lattice _ _ _ hw]
  let T := fun (f : ℂ → ℂ) (p : ∀ z w,w∈L.lattice → f (z+w)=f z+w) =>
    periodTorusLift L (periodTorusProjection L ∘ f) (invariant f p)
  have ct (f : ℂ → ℂ) (p : ∀ z w, w∈L.lattice → f (z+w)=f z+w) (cf : Continuous f) :
      Continuous (T f p) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    obtain ⟨z,rfl⟩ := Quotient.exists_rep q
    exact periodTorusLift_continuousAt L _ _ (QuotientAddGroup.continuous_mk.comp cf).continuousAt
  let H : PeriodTorus L ≃ₜ PeriodTorus L :=
    { toFun := T F per
      invFun := T F.symm back
      left_inv := fun q => by
        obtain ⟨z,rfl⟩ := Quotient.exists_rep q
        exact congrArg (periodTorusProjection L) (F.symm_apply_apply z)
      right_inv := fun q => by
        obtain ⟨z,rfl⟩ := Quotient.exists_rep q
        exact congrArg (periodTorusProjection L) (F.apply_symm_apply z)
      continuous_toFun := ct F per F.continuous
      continuous_invFun := ct F.symm back F.symm.continuous }
  have z0 : H 0=0 := congrArg (periodTorusProjection L) fixed
  let E := H.subtype (p := fun q => q≠0) (q := fun q => q≠0) (fun q =>
    ⟨fun hn he => hn (H.injective (he.trans z0.symm)),fun hn he => hn ((congrArg H he).trans z0)⟩)
  refine ⟨E,?_,?_⟩
  · intro q z hz
    change H q.1=periodTorusProjection L (F z)
    rw [← hz]
    rfl
  · intro q z hz
    change H.symm q.1=periodTorusProjection L (F.symm z)
    rw [← hz]
    rfl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.equivariant_punctured_torus_homeomorph
