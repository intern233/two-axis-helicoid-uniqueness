import TwoAxisHelicoid.CompactCoreNormalTube
import TwoAxisHelicoid.EuclideanUnitChartNormal
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace TwoAxisHelicoid
open Complex Filter Set Metric Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- The signed normal map in an arbitrary smooth regular surface chart is
a local homeomorphism at height zero. Orthonormal surface parameters are
unnecessary. -/
theorem normal_coordinate_smooth_local_inverse {X N : ℂ → SurfaceEuclideanSpace} {z : ℂ}
    (sx : ContDiffAt ℝ 1 X z) (sn : ContDiffAt ℝ 1 N z)
    (inj : Function.Injective (fderiv ℝ X z)) (unit : ‖N z‖=1)
    (ortho : ∀ v, ⟪fderiv ℝ X z v,N z⟫=0) :
    ∃ e : OpenPartialHomeomorph (ℂ × ℝ) SurfaceEuclideanSpace, (z,0)∈e.source ∧
      ((e : ℂ × ℝ → SurfaceEuclideanSpace)=fun a => X a.1+a.2 • N a.1) ∧
      ContDiffAt ℝ 1 e.symm (X z) := by
  let p : ℂ × ℝ := (z,0)
  let P := ContinuousLinearMap.fst ℝ ℂ ℝ
  let S := ContinuousLinearMap.snd ℝ ℂ ℝ
  let D := (fderiv ℝ X z).comp P+S.smulRight (N z)
  let F := fun a : ℂ × ℝ => X a.1+a.2 • N a.1
  have dx := sx.hasStrictFDerivAt (by simp)
  have dn := sn.hasStrictFDerivAt (by simp)
  have d : HasStrictFDerivAt F D p := by
    have h := (dx.comp p P.hasStrictFDerivAt).add (S.hasStrictFDerivAt.smul (dn.comp p P.hasStrictFDerivAt))
    simpa only [show S p=0 from rfl,zero_smul,zero_add] using! h
  have one : ⟪N z,N z⟫=1 := by rw [real_inner_self_eq_norm_sq,unit,one_pow]
  have di : Function.Injective D := by
    apply (injective_iff_map_eq_zero _).mpr
    rintro ⟨v,s⟩ eq
    change fderiv ℝ X z v+s • N z=0 at eq
    have h := congrArg (fun u => ⟪u,N z⟫) eq
    simp only [inner_add_left,real_inner_smul_left,ortho,one,inner_zero_left,zero_add,mul_one] at h
    subst s
    rw [zero_smul,add_zero] at eq
    exact Prod.ext (inj (eq.trans (map_zero _).symm)) rfl
  have dims : Module.finrank ℝ (ℂ × ℝ)=Module.finrank ℝ SurfaceEuclideanSpace := by
    rw [Module.finrank_prod,Complex.finrank_real_complex,Module.finrank_self,finrank_euclideanSpace_fin]
  have db : Function.Bijective D := ⟨di,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank dims (f := D.toLinearMap)).mp di⟩
  let E := (LinearEquiv.ofBijective D.toLinearMap db).toContinuousLinearEquiv
  have de : HasStrictFDerivAt F E.toContinuousLinearMap p := d
  have sf : ContDiffAt ℝ 1 F p := (sx.comp p contDiffAt_fst).add (contDiffAt_snd.smul (sn.comp p contDiffAt_fst))
  have nz : (1 : WithTop ℕ∞)≠0 := by simp
  have fp : F p=X z := by simp [F,p]
  refine ⟨sf.toOpenPartialHomeomorph F de.hasFDerivAt nz,sf.mem_toOpenPartialHomeomorph_source de.hasFDerivAt nz,rfl,?_⟩
  rw [← fp]
  exact sf.to_localInverse de.hasFDerivAt nz

theorem normal_coordinate_local_inverse {X N : ℂ → SurfaceEuclideanSpace} {z : ℂ}
    (sx : ContDiffAt ℝ 1 X z) (sn : ContDiffAt ℝ 1 N z)
    (inj : Function.Injective (fderiv ℝ X z)) (unit : ‖N z‖=1)
    (ortho : ∀ v, ⟪fderiv ℝ X z v,N z⟫=0) :
    ∃ e : OpenPartialHomeomorph (ℂ × ℝ) SurfaceEuclideanSpace, (z,0)∈e.source ∧
      (e : ℂ × ℝ → SurfaceEuclideanSpace)=fun a => X a.1+a.2 • N a.1 := by
  obtain ⟨e,he,eq,_⟩ := normal_coordinate_smooth_local_inverse sx sn inj unit ortho
  exact ⟨e,he,eq⟩

/-- The compact core of a regular embedded surface admits a single
Euclidean tube with actual inverse coordinates on an open image. -/
theorem compact_immersed_core_normal_tube {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {X N : M → SurfaceEuclideanSpace} {K : Set M} (kc : IsCompact K) (embed : InjOn X K)
    (charts : ∀ p∈K, let e := chartAt ℂ p
      let z := e p
      ContDiffAt ℝ 1 (X ∘ e.symm) z ∧ ContDiffAt ℝ 1 (N ∘ e.symm) z ∧
        Function.Injective (fderiv ℝ (X ∘ e.symm) z) ∧ ‖N p‖=1 ∧ ∀ v, ⟪fderiv ℝ (X ∘ e.symm) z v,N p⟫=0) :
    ∃ (U : Set M) (r : ℝ), IsOpen U ∧ K⊆U ∧ 0<r ∧
      IsOpenEmbedding ((U ×ˢ ball (0:ℝ) r).domRestrict (fun a => X a.1+a.2 • N a.1)) := by
  let F := fun a : M × ℝ => X a.1+a.2 • N a.1
  apply compact_core_uniform_open_tube kc (show InjOn (fun x => F (x,0)) K by simpa only [F,zero_smul,add_zero] using embed)
  apply IsLocalHomeomorphOn.mk
  rintro ⟨x,s⟩ ⟨hx,hs⟩
  change s=0 at hs
  subst s
  let e := chartAt ℂ x
  have ex : x∈e.source := mem_chart_source ℂ x
  obtain ⟨sx,sn,inj,one,ort⟩ := charts x hx
  obtain ⟨d,dx,eq⟩ := normal_coordinate_local_inverse (X := X ∘ e.symm) (N := N ∘ e.symm) (z := e x) sx sn inj
    (by simpa only [Function.comp_apply,e.left_inv ex] using one)
    (fun v => by simpa only [Function.comp_apply,e.left_inv ex] using ort v)
  let h := (e.prod (OpenPartialHomeomorph.refl ℝ)).trans d
  refine ⟨h,⟨⟨ex,trivial⟩,dx⟩,?_⟩
  intro a ha
  change X a.1+a.2 • N a.1=d (e a.1,a.2)
  rw [eq]
  simp only [Function.comp_apply,e.left_inv ha.1.1]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.normal_coordinate_local_inverse
#print axioms TwoAxisHelicoid.compact_immersed_core_normal_tube
