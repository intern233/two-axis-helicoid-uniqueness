import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Separation.Connected
import Mathlib.Analysis.Normed.Group.Real
import TwoAxisHelicoid.ActualTorusManifoldImmersion

namespace TwoAxisHelicoid
open Set Metric Topology

abbrev MeridianDiskParameter := closedBall (0:ℂ) 1

/-- In an injectively parametrized solid torus, one meridian disk avoids
any specified finite set of ambient points and a given list of longitudes.
This applies even when the bounded solid torus contains the point at infinity. -/
theorem solid_torus_has_meridian_avoiding_finite {N : Type*}
    (B : Circle × MeridianDiskParameter → N) (hB : Function.Injective B)
    (P : Set N) (hP : P.Finite) (A : Set Circle) (hA : A.Finite) :
    ∃ a : Circle, a ∉ A ∧ ∀ z, B (a,z) ∉ P := by
  classical
  let _ : ConnectedSpace Circle := Circle.exp_surjective.connectedSpace Circle.exp.continuous
  let _ : Nontrivial Circle := ⟨⟨1,-1,fun hh => by
    have he := congrArg (fun x : Circle => (x:ℂ).re) hh
    norm_num at he⟩⟩
  let _ : Infinite Circle := PreconnectedSpace.infinite
  let U := Prod.fst '' (B ⁻¹' P)
  have hU : U.Finite := (hP.preimage hB.injOn).image _
  obtain ⟨a,ha⟩ := (hA.union hU).exists_notMem
  exact ⟨a,fun h => ha (Or.inl h),fun z h => ha (Or.inr ⟨(a,z),h,rfl⟩)⟩

theorem same_range_parameter_homeomorph {A B N : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace N] {f : A → N} {g : B → N}
    (hf : IsEmbedding f) (hg : IsEmbedding g) (hr : range f = range g) :
    ∃ H : A ≃ₜ B, ∀ a, g (H a) = f a := by
  let e := Homeomorph.setCongr hr
  let H := (hf.toHomeomorph.trans e).trans hg.toHomeomorph.symm
  refine ⟨H,fun a => ?_⟩
  exact congrArg Subtype.val (hg.toHomeomorph.apply_symm_apply (e (hf.toHomeomorph a)))

/-- The marking of the complete boundary is obtained from the actual
boundary image of the solid torus and the embedded compact surface. -/
theorem solid_torus_compactified_boundary_marking (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ)
    (hF : IsEmbedding F) (S : Circle × ℂ → OnePoint (Fin 3 → ℝ))
    (hs : ContinuousOn S (univ ×ˢ closedBall 0 1))
    (hi : InjOn S (univ ×ˢ closedBall 0 1))
    (hbd : range (fun v : Circle × Circle => S (v.1,(v.2 : ℂ))) =
      range (fun p => (F p : OnePoint (Fin 3 → ℝ)))) :
    ∃ H : Circle × Circle ≃ₜ PeriodTorus L, ∀ u v,
      (F (H (u,v)) : OnePoint (Fin 3 → ℝ)) = S (u,(v:ℂ)) := by
  let b (v : Circle × Circle) := (v.1,(v.2 : ℂ))
  have hc : Continuous b := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hb (v : Circle × Circle) : b v ∈ univ ×ˢ closedBall (0:ℂ) 1 := ⟨trivial,by simp [b,mem_closedBall]⟩
  have hi' : Function.Injective (S ∘ b) := by
    intro x y h
    have he := hi (hb x) (hb y) h
    exact Prod.ext (congrArg (Prod.fst : Circle × ℂ → Circle) he) (Subtype.ext (congrArg (Prod.snd : Circle × ℂ → ℂ) he))
  have hs' : Continuous (S ∘ b) := hs.comp_continuous hc hb
  obtain ⟨H,hH⟩ := same_range_parameter_homeomorph (hs'.isClosedEmbedding hi').isEmbedding
    (OnePoint.isOpenEmbedding_coe.isEmbedding.comp hF) hbd
  exact ⟨H,fun u v => hH (u,v)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.solid_torus_has_meridian_avoiding_finite
#print axioms TwoAxisHelicoid.solid_torus_compactified_boundary_marking
