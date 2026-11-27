import TwoAxisHelicoid.OriginalHandleTopology
import TwoAxisHelicoid.MinimalManifoldComplexStructure
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold

/-- A closed embedded smooth surface contained in an affine plane
fills that plane. In particular its parameter surface is a plane.
The proof applies to a nonorthogonal parametrization of the plane. -/
theorem closed_immersed_surface_in_affine_plane {M : Type*} [TopologicalSpace M] [Nonempty M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] {X : M → Fin 3 → ℝ}
    (closed : IsClosedEmbedding X) (sx : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (imm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x))
    (T : ℂ →L[ℝ] (Fin 3 → ℝ)) (ti : Function.Injective T) (o : Fin 3 → ℝ)
    (contained : range X ⊆ range (fun z => o+T z)) :
    ∃ E : M ≃ₜ ℂ, ∀ x, o+T (E x)=X x := by
  obtain ⟨Q₀,left⟩ := T.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr ti)
  let Q := Q₀.toContinuousLinearMap
  let Y := fun x => Q (X x-o)
  let P := fun z => o+T z
  have inverse (w : ℂ) : Q (T w)=w := DFunLike.congr_fun left w
  have read (w : ℂ) : Q (P w-o)=w := by simp only [P,add_sub_cancel_left,inverse]
  have recover (x : M) : P (Y x)=X x := by
    obtain ⟨w,hw⟩ := contained (mem_range_self x)
    change P w=X x at hw
    simp only [Y,← hw,read]
  have project : Continuous Y := Q.continuous.comp (closed.continuous.sub continuous_const)
  have place : Continuous P := continuous_const.add T.continuous
  have emb : IsEmbedding Y := IsEmbedding.of_comp project place ((funext recover : P ∘ Y=X) ▸ closed.isEmbedding)
  have rangeEq : range Y=P ⁻¹' range X := by
    ext w
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x,(recover x).symm⟩
    · rintro ⟨x,hx⟩
      exact ⟨x,by change Q (X x-o)=w; rw [hx,read]⟩
  have op : IsOpen (range Y) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨x,rfl⟩
    let c := chartAt ℂ x
    let z := c x
    let Z := X ∘ c.symm
    let f := Y ∘ c.symm
    have inc : x∈c.source := mem_chart_source ℂ x
    obtain ⟨zs,zi⟩ := smooth_surface_regular_manifold_chart sx imm x z (c.map_source inc)
    have fs : ContDiffAt ℝ 1 f z :=
      Q.contDiff.contDiffAt.comp z ((zs.of_le (by simp)).sub contDiffAt_const)
    have eq : Z = fun w => o+T (f w) := funext fun w => (recover (c.symm w)).symm
    have dz : fderiv ℝ Z z=T.comp (fderiv ℝ f z) := by
      rw [eq,fderiv_const_add]
      exact (T.hasFDerivAt.comp z (fs.differentiableAt one_ne_zero).hasFDerivAt).fderiv
    have di : Function.Injective (fderiv ℝ f z) := by
      intro a b h
      apply zi
      change fderiv ℝ Z z a=fderiv ℝ Z z b
      rw [dz]
      exact congrArg T h
    have bij : Function.Bijective (fderiv ℝ f z) :=
      ⟨di,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl (f := (fderiv ℝ f z).toLinearMap)).mp di⟩
    let A := (LinearEquiv.ofBijective (fderiv ℝ f z).toLinearMap bij).toContinuousLinearEquiv
    have df : HasFDerivAt f A.toContinuousLinearMap z := (fs.differentiableAt one_ne_zero).hasFDerivAt
    let e := fs.toOpenPartialHomeomorph f df (by simp)
    have inS : z∈e.source := fs.mem_toOpenPartialHomeomorph_source df (by simp)
    have ev : f z=Y x := congrArg Y (c.left_inv inc)
    rw [← ev]
    apply mem_of_superset (e.open_target.mem_nhds (e.map_source inS))
    intro w hw
    exact ⟨c.symm (e.symm w),e.right_inv hw⟩
  have cl : IsClosed (range Y) := rangeEq ▸ closed.isClosed_range.preimage place
  have all : range Y=univ := IsClopen.eq_univ ⟨cl,op⟩ (range_nonempty Y)
  exact ⟨emb.toHomeomorphOfSurjective (range_eq_univ.mp all),recover⟩

/-- Finite genus here excludes a planar immersion by topology alone,
before using any conformal or asymptotic description of the end. -/
theorem OriginalSmoothHelicoid.not_contained_in_parametric_plane (s : OriginalSmoothHelicoid)
    (T : ℂ →L[ℝ] (Fin 3 → ℝ)) (ti : Function.Injective T) (o : Fin 3 → ℝ) :
    ¬range s.position ⊆ range (fun z => o+T z) := by
  intro sub
  let _ : Nonempty s.carrier := (s.axes.vertical 0).elim fun x _ => ⟨x⟩
  obtain ⟨E,_⟩ := closed_immersed_surface_in_affine_plane s.closedEmbedding s.smooth s.immersion T ti o sub
  exact s.not_simply_connected (E.toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.OriginalSmoothHelicoid.not_contained_in_parametric_plane
