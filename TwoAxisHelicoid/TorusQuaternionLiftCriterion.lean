import TwoAxisHelicoid.PuncturedCoverExtension
import TwoAxisHelicoid.TangentPhaseMonodromy
import TwoAxisHelicoid.TorusGeneratorIntersections

namespace TwoAxisHelicoid
open Complex Set

def SpatialFrameCurveCloses (P : unitInterval → OrthonormalTangentPair) : Prop :=
  ∃ q : C(unitInterval,UnitQuaternion), q 1 = q 0 ∧ ∀ r, unitQuaternionFrame (q r) = P r

/-- The two marked curves detect the existence of a global ambient quaternion
lift of any periodic continuous frame field on a torus. -/
theorem torus_frame_global_lift_iff (L : PeriodPair) (P : C(ℂ,OrthonormalTangentPair))
    (hP : ∀ z ω, ω ∈ L.lattice → P (z+ω) = P z) :
    (∃ q : C(ℂ,UnitQuaternion), (∀ z, unitQuaternionFrame (q z) = P z) ∧
        ∀ z ω, ω ∈ L.lattice → q (z+ω) = q z) ↔
      ∀ i, SpatialFrameCurveCloses (fun r => P (periodBasisLine L i r)) := by
  have hγ (i : Fin 2) : Continuous (fun r : unitInterval => periodBasisLine L i r) :=
    (show Continuous (periodBasisLine L i) from continuous_iff_continuousAt.mpr fun s =>
      (periodBasisLine_hasDerivAt L i s).continuousAt).comp continuous_subtype_val
  have hends (i : Fin 2) : periodBasisLine L i 1 = periodBasisLine L i 0 + L.basis i := by
    simpa only [zero_add] using periodBasisLine_add_one L i 0
  have hb (i : Fin 2) : L.basis i ∈ L.lattice :=
    (periodGeneratorPeriod_val L i) ▸ (periodGeneratorPeriod L i).2
  constructor
  · rintro ⟨q,hq,hper⟩ i
    refine ⟨⟨fun r => q (periodBasisLine L i r),(q.continuous.comp (hγ i))⟩,
      ?_,fun r => hq _⟩
    change q (periodBasisLine L i 1) = q (periodBasisLine L i 0)
    rw [hends,hper _ _ (hb i)]
  · intro h
    obtain ⟨u,hu⟩ := unitQuaternionFrame_surjective (P 0)
    obtain ⟨g,⟨_,hl⟩,_⟩ := unitQuaternionFrame_isCoveringMap.existsUnique_continuousMap_lifts P 0 u hu
    have hg (z : ℂ) : unitQuaternionFrame (g z) = P z := congrFun hl z
    have gen (i : Fin 2) : Function.Periodic g (L.basis i) := by
      obtain ⟨q,hc,hq⟩ := h i
      have hclose : g (periodBasisLine L i 1) = g (periodBasisLine L i 0) :=
        (quaternion_frame_lifts_closed_iff q.continuous (g.continuous.comp (hγ i))
          (funext fun r => (hq r).trans (hg _).symm) 0 1).mp hc
      rw [hends] at hclose
      have heq : (fun z => g (z+L.basis i)) = g := by
        apply unitQuaternionFrame_isCoveringMap.eq_of_comp_eq (g.continuous.comp (continuous_id.add_const _))
          g.continuous _ (periodBasisLine L i 0) hclose
        exact funext fun z => (hg _).trans ((hP z _ (hb i)).trans (hg z).symm)
      exact congrFun heq
    refine ⟨g,hg,?_⟩
    intro z ω hω
    obtain ⟨m,n,rfl⟩ := PeriodPair.mem_lattice.mp hω
    have e₁ := (gen 0).zsmul m z
    have e₂ := (gen 1).zsmul n (z+(m:ℂ)*L.ω₁)
    simp only [zsmul_eq_mul] at e₁ e₂
    rw [show L.basis 0 = L.ω₁ by simp] at e₁
    rw [show L.basis 1 = L.ω₂ by simp] at e₂
    simpa only [add_assoc] using e₂.trans e₁

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.torus_frame_global_lift_iff
