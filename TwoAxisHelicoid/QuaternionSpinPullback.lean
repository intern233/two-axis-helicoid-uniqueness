import TwoAxisHelicoid.SignCoverFrameHomeomorph
import TwoAxisHelicoid.QuaternionFrameCover

namespace TwoAxisHelicoid
open Set Topology

/-- The pullback of the standard unit-quaternion covering along an actual
oriented orthonormal tangent frame map. -/
abbrev QuaternionFramePullback {B : Type*} (f : B → OrthonormalTangentPair) :=
  CoverPullback f unitQuaternionFrame

noncomputable def spinorQuaternionPullbackHomeomorph {B : Type*} [TopologicalSpace B]
    (f : B → OrthonormalTangentPair) :
    CoverPullback f unitSpinorTangentFrame ≃ₜ QuaternionFramePullback f :=
  ((Homeomorph.refl B).prodCongr unitSpinorQuaternionHomeomorph).subtype (fun v => by
    change f v.1 = unitSpinorTangentFrame v.2 ↔
      f v.1 = unitQuaternionFrame (unitSpinorQuaternionHomeomorph v.2)
    rw [unitQuaternionFrame_spinor])

theorem spinorQuaternionPullbackHomeomorph_base {B : Type*} [TopologicalSpace B]
    (f : B → OrthonormalTangentPair) (q : CoverPullback f unitSpinorTangentFrame) :
    (spinorQuaternionPullbackHomeomorph f q).1.1 = q.1.1 := rfl

/-- The flat character model and the standard quaternion pullback are
homeomorphic over the punctured torus. No parity conclusion is assumed. -/
noncomputable def signCoverQuaternionHomeomorph (L : PeriodPair)
    (χ : L.lattice →+ ZMod 2) (s : PuncturedLatticePlane L → UnitSpinor)
    (hs : UnitSpinorEquivariant L χ s) (hc : Continuous s) :
    PuncturedSignCover L χ ≃ₜ QuaternionFramePullback (equivariantTorusFrame L s) :=
  (signCoverFramePullbackHomeomorph L χ s hs hc).trans
    (spinorQuaternionPullbackHomeomorph (equivariantTorusFrame L s))

theorem signCoverQuaternionHomeomorph_base (L : PeriodPair)
    (χ : L.lattice →+ ZMod 2) (s : PuncturedLatticePlane L → UnitSpinor)
    (hs : UnitSpinorEquivariant L χ s) (hc : Continuous s) (q : PuncturedSignCover L χ) :
    (signCoverQuaternionHomeomorph L χ s hs hc q).1.1 =
      puncturedSignCoverProjection L χ q :=
  signCoverFramePullbackHomeomorph_over_base L χ s hs hc q

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.signCoverQuaternionHomeomorph
#print axioms TwoAxisHelicoid.signCoverQuaternionHomeomorph_base

