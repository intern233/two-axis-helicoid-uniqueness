import TwoAxisHelicoid.ContactProjectionMinor

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology Function
open scoped Topology ContDiff

/-- A single spatial projection identifies genuine open patches of both
tangent sheets with open subsets of the same plane. -/
theorem tangent_sheet_projection_charts {X Y : ℂ → Fin 3 → ℝ} {a b : ℂ}
    (sx : ContDiffAt ℝ 2 X a) (sy : ContDiffAt ℝ 2 Y b)
    (ix : Injective (fderiv ℝ X a)) (iy : Injective (fderiv ℝ Y b))
    (same : (fderiv ℝ X a).range=(fderiv ℝ Y b).range) :
    ∃ (P : (Fin 3 → ℝ) →L[ℝ] ℂ) (e d : OpenPartialHomeomorph ℂ ℂ),
      a∈e.source ∧ b∈d.source ∧ (∀ z, e z=P (X z)) ∧ (∀ w, d w=P (Y w)) := by
  obtain ⟨σ,mx,my⟩ := common_coordinate_minor_of_tangent_eq _ _ ix iy same
  let P := spatialGraphProjection (σ 0) (σ 1)
  have chart (Z : ℂ → Fin 3 → ℝ) (z : ℂ) (s : ContDiffAt ℝ 2 Z z)
      (inj : Injective (P.comp (fderiv ℝ Z z))) :
      ∃ e : OpenPartialHomeomorph ℂ ℂ, z∈e.source ∧ ∀ w, e w=P (Z w) := by
    let f := P ∘ Z
    let A := P.comp (fderiv ℝ Z z)
    let D := (LinearEquiv.ofBijective A.toLinearMap
      ⟨inj,LinearMap.injective_iff_surjective.mp inj⟩).toContinuousLinearEquiv
    have sf : ContDiffAt ℝ 2 f z := P.contDiff.contDiffAt.comp z s
    have df : HasFDerivAt f (D : ℂ →L[ℝ] ℂ) z := P.hasFDerivAt.comp z (s.differentiableAt two_ne_zero).hasFDerivAt
    exact ⟨sf.toOpenPartialHomeomorph f df two_ne_zero,sf.mem_toOpenPartialHomeomorph_source df two_ne_zero,fun _ => rfl⟩
  obtain ⟨e,ea,ex⟩ := chart X a sx (spatialGraphProjection_injective _ _ _ mx)
  obtain ⟨d,db,dy⟩ := chart Y b sy (spatialGraphProjection_injective _ _ _ my)
  exact ⟨P,e,d,ea,db,ex,dy⟩

/-- A one-sided inclusion of regular graph germs gives actual equality
of two open sheet patches inside any prescribed neighborhoods. -/
theorem equal_open_sheet_patches {X Y : ℂ → Fin 3 → ℝ} {a b : ℂ}
    {P : (Fin 3 → ℝ) →L[ℝ] ℂ} {e d : OpenPartialHomeomorph ℂ ℂ}
    (ea : a∈e.source) (db : b∈d.source) (ex : ∀ z, e z=P (X z)) (dy : ∀ w, d w=P (Y w))
    (meet : X a=Y b) {U₀ V₀ : Set ℂ} (un : U₀∈𝓝 a) (vs : V₀⊆d.source)
    (inside : ∀ᶠ z in 𝓝 a, X z∈Y '' V₀) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ a∈U ∧ b∈V ∧ U⊆U₀ ∧ V⊆V₀ ∧
      InjOn X U ∧ InjOn Y V ∧ X '' U=Y '' V := by
  obtain ⟨r,rp,h⟩ := Metric.mem_nhds_iff.mp (inter_mem (inter_mem un (e.open_source.mem_nhds ea)) inside)
  let U := Metric.ball a r
  have Ux : U⊆e.source := fun z hz => (h hz).1.2
  let V := d.source∩d ⁻¹' (e '' U)
  have center : a∈U := Metric.mem_ball_self rp
  have lift {y : ℂ} (hy : y∈V) : ∃ z∈U, X z=Y y ∧ y∈V₀ := by
    obtain ⟨z,hz,eq⟩ := hy.2
    obtain ⟨w,hw,zw⟩ := (h hz).2
    have wy : w=y := d.injOn (vs hw) hy.1 (((dy w).trans (congrArg P zw)).trans ((ex z).symm.trans eq))
    exact ⟨z,hz,zw.symm.trans (congrArg Y wy),wy ▸ hw⟩
  refine ⟨U,V,Metric.isOpen_ball,d.isOpen_inter_preimage (e.isOpen_image_of_subset_source Metric.isOpen_ball Ux),
    center,⟨db,a,center,(ex a).trans ((congrArg P meet).trans (dy b).symm)⟩,
    fun z hz => (h hz).1.1,fun y hy => (lift hy).choose_spec.2.2,?_,?_,?_⟩
  · intro z hz w hw eq
    exact e.injOn (Ux hz) (Ux hw) ((ex z).trans ((congrArg P eq).trans (ex w).symm))
  · intro z hz w hw eq
    exact d.injOn hz.1 hw.1 ((dy z).trans ((congrArg P eq).trans (dy w).symm))
  · ext p
    constructor
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨y,hy,eq⟩ := (h hz).2
      exact ⟨y,⟨vs hy,z,hz,(ex z).trans ((congrArg P eq.symm).trans (dy y).symm)⟩,eq⟩
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨z,hz,zy,_⟩ := lift hy
      exact ⟨z,hz,zy⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.equal_open_sheet_patches
