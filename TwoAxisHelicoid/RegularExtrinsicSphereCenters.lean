import TwoAxisHelicoid.RegularChartNormalStability
import Mathlib.Topology.MetricSpace.HausdorffDimension

namespace TwoAxisHelicoid
open Set Filter Metric Topology TopologicalSpace
open scoped Topology ContDiff RealInnerProductSpace ENNReal

/-- At a critical point of distance on a regular immersed plane the
center of the cutting sphere is one of the two signed normal offsets. -/
theorem center_eq_signed_normal_offset {T : ℂ →L[ℝ] SurfaceEuclideanSpace} (inj : Function.Injective T)
    {y c n : SurfaceEuclideanSpace} {r : ℝ} (rp : 0<r) (sphere : dist y c=r) (unit : ‖n‖=1)
    (normal : ∀ u, ⟪T u,n⟫=0) (critical : ∀ u, ⟪T u,c-y⟫=0) :
    c=y+r • n ∨ c=y+(-r) • n := by
  let b := r⁻¹ • (c-y)
  have offset : r • b=c-y := by simp only [b,smul_smul,mul_inv_cancel₀ rp.ne',one_smul]
  have norm : ‖c-y‖=r := (dist_eq_norm c y).symm.trans ((dist_comm c y).trans sphere)
  have un : ‖b‖=1 := by rw [show b=r⁻¹ • (c-y) from rfl,norm_smul,Real.norm_of_nonneg (inv_pos.mpr rp).le,norm,inv_mul_cancel₀ rp.ne']
  have perp (v : ℂ) : ⟪T v,b⟫=0 := by rw [show b=r⁻¹ • (c-y) from rfl,real_inner_smul_right,critical,mul_zero]
  rcases regular_plane_unit_normal_choices inj unit un normal perp with h|h
  · left
    rw [← h,offset]
    abel
  · right
    have eq : (-r) • n=c-y := by simpa only [h,smul_neg,neg_smul] using offset
    rw [eq]
    abel

/-- For each fixed positive radius the centers of spheres transverse to
a regularly immersed surface are dense in three-space. The exceptional
centers are covered by countably many two-dimensional normal offsets. -/
theorem dense_regular_extrinsic_sphere_centers {M : Type*} [TopologicalSpace M] [SecondCountableTopology M]
    (Y : M → Fin 3 → ℝ) (a : M → OpenPartialHomeomorph M ℂ) (inside : ∀ p, p∈(a p).source)
    (reg : ∀ p, RegularImmersionChart Y (a p)) {r : ℝ} (rp : 0<r) :
    Dense {c : SurfaceEuclideanSpace | ∀ q : M, dist (coordinateToEuclidean (Y q)) c=r →
      ∃ p : M, q∈(a p).source ∧ ∃ v : ℂ,
        ⟪coordinateToEuclidean (fderiv ℝ (Y ∘ (a p).symm) (a p q) v),c-coordinateToEuclidean (Y q)⟫≠0} := by
  obtain ⟨P,count,cover⟩ := TopologicalSpace.countable_cover_nhds (fun q => (a q).open_source.mem_nhds (inside q))
  let F := fun p => Y ∘ (a p).symm
  let X := fun p => coordinateToEuclidean ∘ F p
  let offset := fun (p : M) (t : ℝ) (z : ℂ) => X p z+t • euclideanUnitChartNormal (F p) z
  let bad := fun p => (offset p r '' (a p).target) ∪ (offset p (-r) '' (a p).target)
  have dim (p : M) (t : ℝ) : dimH (offset p t '' (a p).target)≤2 := by
    have df : DifferentiableOn ℝ (offset p t) (a p).target := by
      intro z hz
      obtain ⟨sm,inj⟩ := reg p z hz
      have sx : ContDiffAt ℝ 1 (X p) z := coordinateToEuclidean.contDiff.contDiffAt.comp _ (sm.of_le (by simp))
      have sn := euclideanUnitChartNormal_contDiffAt (sm.of_le (by norm_num)) inj
      exact ((sx.add (sn.const_smul t)).differentiableAt one_ne_zero).differentiableWithinAt
    apply df.dimH_image_le.trans
    apply (dimH_mono (subset_univ _)).trans
    rw [Real.dimH_univ_eq_finrank,Complex.finrank_real_complex]
    norm_num
  have bound : dimH (⋃ p∈P, bad p)≤2 := by
    rw [dimH_bUnion count]
    refine iSup₂_le fun p _ => ?_
    change dimH (_ ∪ _)≤2
    rw [dimH_union]
    exact max_le (dim p r) (dim p (-r))
  have dense : Dense (⋃ p∈P, bad p)ᶜ := dense_compl_of_dimH_lt_finrank (bound.trans_lt (by rw [finrank_euclideanSpace_fin]; norm_num))
  apply dense.mono
  intro c avoid q sphere
  obtain ⟨p,hp,qp⟩ := mem_iUnion₂.mp (show q∈⋃ p∈P, (a p).source from cover.symm ▸ mem_univ q)
  refine ⟨p,qp,?_⟩
  let z := a p q
  let T := coordinateToEuclidean.comp (fderiv ℝ (F p) z)
  let y := coordinateToEuclidean (Y q)
  let n := euclideanUnitChartNormal (F p) z
  have target := (a p).map_source qp
  have inj := (reg p z target).2
  have orth (v : ℂ) : ⟪T v,n⟫=0 :=
    (chartEuclideanTangent_iff_unitNormal (F := Y) (e := a p) inj _).mp ⟨v,rfl⟩
  by_contra! critical
  have base : X p z=y := congrArg (coordinateToEuclidean ∘ Y) ((a p).left_inv qp)
  have cases := center_eq_signed_normal_offset (surfaceCartesianEquiv.symm.injective.comp inj) rp sphere (euclideanUnitChartNormal_unit inj) orth critical
  apply avoid
  apply mem_iUnion₂.mpr
  refine ⟨p,hp,?_⟩
  rcases cases with h|h
  · exact Or.inl ⟨z,target,(congrArg (fun u => u+r • n) base).trans h.symm⟩
  · exact Or.inr ⟨z,target,(congrArg (fun u => u+(-r) • n) base).trans h.symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.dense_regular_extrinsic_sphere_centers
