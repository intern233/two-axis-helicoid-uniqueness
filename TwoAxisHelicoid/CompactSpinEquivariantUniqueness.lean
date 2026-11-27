import TwoAxisHelicoid.NormalFrameSpinExtensionUniqueness
import TwoAxisHelicoid.SpatialSpinEquivariance

namespace TwoAxisHelicoid
open Set Matrix Topology
open scoped Matrix

noncomputable def normalFrameRotation {B : Type*} (n : B → Fin 3 → ℝ) (u : Circle)
    (x : NormalFieldFrames n) : NormalFieldFrames n :=
  ⟨(x.1.1,rotateTangentPair u x.1.2),x.2.trans (rotateTangentPair_same_normal _ _).symm⟩

theorem normalSpinRotation_projection {B : Type*} [TopologicalSpace B] (n : B → Fin 3 → ℝ) (u : Circle)
    (x : NormalFieldSpin n) : normalFieldSpinProjection n (normalSpinRotation n u x) =
      normalFrameRotation n (u^2) (normalFieldSpinProjection n x) :=
  Subtype.ext (Prod.ext rfl (unitQuaternionFrame_spinCircleAction u x.1.2))

/-- The unique compact identification is an isomorphism of spin
structures: every rotation is intertwined once this holds on the
specified punctured restriction. No topology assumptions on the total
space of the competing cover beyond being a covering are imposed. -/
theorem actual_compact_spin_equivariant_unique {M E : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [TopologicalSpace E] (p : M) (n : C(M,Fin 3 → ℝ)) (hn : ∀ b, n b ⬝ᵥ n b = 1)
    (a : E → NormalFieldFrames n) (ha : IsCoveringMap a) (r : Circle → E → E) (hr : ∀ u, Continuous (r u))
    (hrπ : ∀ u x, a (r u x) = normalFrameRotation n (u^2) (a x))
    (i : {x : E // (a x).1.1 ≠ p} ≃ₜ {y : NormalFieldSpin n // y.1.1 ≠ p})
    (hi : ∀ x, normalFieldSpinProjection n (i x).1 = a x.1)
    (hir : ∀ u (x : {e : E // (a e).1.1 ≠ p}) (h : (a (r u x.1)).1.1 ≠ p),
      (i ⟨r u x.1,h⟩).1 = normalSpinRotation n u (i x).1) :
    ∃! H : E ≃ₜ NormalFieldSpin n, (∀ e, normalFieldSpinProjection n (H e) = a e) ∧
      (∀ x : {e : E // (a e).1.1 ≠ p}, H x.1 = (i x).1) ∧ ∀ u x, H (r u x) = normalSpinRotation n u (H x) := by
  let b := normalFieldSpinProjection n
  have hb := normalFieldSpinProjection_isCoveringMap n
  obtain ⟨H,⟨hH,hHi⟩,huniq⟩ := actual_surface_spin_cover_extension_unique p n hn a b ha hb i hi
  have hD := ((normal_field_frames_puncture_removable p n hn).preimage ha.isLocalHomeomorph).dense
  refine ⟨H,⟨hH,hHi,fun u => ?_⟩,fun T hT => huniq T ⟨hT.1,hT.2.1⟩⟩
  apply congrFun
  apply cover_maps_eq_of_dense hb (H.continuous.comp (hr u)) ((normalSpinRotation_continuous n u).comp H.continuous)
    (fun x => ((hH (r u x)).trans (hrπ u x)).trans
      ((congrArg (normalFrameRotation n (u^2)) (hH x).symm).trans (normalSpinRotation_projection n u (H x)).symm)) hD
  intro x hx
  let xx : {e : E // (a e).1.1 ≠ p} := ⟨x,hx⟩
  have hux : (a (r u x)).1.1 ≠ p := by rw [hrπ]; exact hx
  exact ((hHi ⟨r u x,hux⟩).trans (hir u xx hux)).trans (congrArg (normalSpinRotation n u) (hHi xx).symm)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_compact_spin_equivariant_unique
