import TwoAxisHelicoid.BoundaryCayleyCoordinate

namespace TwoAxisHelicoid
open Complex Set Metric Filter
open scoped Topology ComplexConjugate ContDiff Manifold

/-- A fixed-point-free biholomorphic generator on the disk is conjugate
by an explicit Cayley coordinate to w ↦ a*w+i*b, with a>0. -/
theorem disk_deck_half_plane_form (f : RiemannUnitDisk ≃ₜ RiemannUnitDisk)
    (hol : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f) (inv : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm)
    (free : ∀ z, f z≠z) :
    ∃ (u : ℂ) (a b : ℝ), ‖u‖=1 ∧ 0<a ∧ (a≠1 ∨ b≠0) ∧
      ∀ z : RiemannUnitDisk, boundaryCayley u (f z).1=(a:ℂ)*boundaryCayley u z.1+(b:ℂ)*I := by
  obtain ⟨c,k,hc,hk,frac⟩ := disk_automorphism_fraction f hol inv
  have forbid (z : ℂ) (hz : ‖z‖<1) : (k*z+c)/(1+conj c*k*z)≠z := by
    let q : RiemannUnitDisk := ⟨z,by change z∈ball 0 1; simpa using hz⟩
    exact fun eq => free q (Subtype.ext ((frac q).trans eq))
  obtain ⟨u,hu,fix⟩ := fixed_point_free_disk_boundary_root hc hk forbid
  let p := (k*u+c)/(u-c)
  let q := (u-k*u)/(u-c)
  have small (z : RiemannUnitDisk) : ‖z.1‖<1 := by simpa using (show z.1∈ball 0 1 from z.2)
  have linear (z : RiemannUnitDisk) : boundaryCayley u (f z).1=p*boundaryCayley u z.1+q := by
    rw [frac]
    apply boundaryCayley_fraction_affine hu hc (small z) fix
    · have h : ‖conj c*k*z.1‖<1 := by
        rw [norm_mul,norm_mul,Complex.norm_conj,hk,mul_one]
        exact (mul_le_mul_of_nonneg_right hc.le (norm_nonneg _)).trans_lt (by simpa using small z)
      intro zero
      have eq : conj c*k*z.1= -1 := by linear_combination zero
      simp [eq] at h
    · rw [← frac]; exact small _
  have onto (w : ℂ) (hw : 0<w.re) : ∃ z : RiemannUnitDisk, boundaryCayley u z.1=w :=
    ⟨⟨boundaryCayleyInv u w,by change _∈ball 0 1; simpa using boundaryCayleyInv_disk hu hw⟩,boundaryCayley_right_inv hu hw⟩
  have sur (w : ℂ) (hw : 0<w.re) : ∃ v : ℂ, 0<v.re ∧ p*v+q=w := by
    obtain ⟨z,eq⟩ := onto w hw
    refine ⟨boundaryCayley u (f.symm z).1,boundaryCayley_right hu (small _),?_⟩
    rw [← linear,f.apply_symm_apply,eq]
  have pn : p≠0 := by
    intro zero
    obtain ⟨v,_,x⟩ := sur 1 (by norm_num)
    obtain ⟨w,_,y⟩ := sur 2 (by norm_num)
    rw [zero,zero_mul,zero_add] at x y
    exact (by norm_num : (1:ℂ)≠2) (x.symm.trans y)
  obtain ⟨im,pos,re⟩ := right_half_plane_affine_coefficients pn (fun w hw => by
    obtain ⟨z,rfl⟩ := onto w hw
    rw [← linear]
    exact boundaryCayley_right hu (small _)) sur
  have ep : (p.re:ℂ)=p := by apply Complex.ext <;> simp [im]
  have eq : (q.im:ℂ)*I=q := by apply Complex.ext <;> simp [re]
  refine ⟨u,p.re,q.im,hu,pos,?_,fun z => by rw [ep,eq]; exact linear z⟩
  by_contra! same
  have p1 := ep.symm.trans (congrArg Complex.ofReal same.1)
  have q0 : q=0 := eq.symm.trans (by rw [same.2]; simp)
  let z : RiemannUnitDisk := ⟨0,by simp [unitDiskOpen,complexUnitDisk]⟩
  have id := linear z
  rw [p1,Complex.ofReal_one,one_mul,q0,add_zero] at id
  apply free z
  apply Subtype.ext
  exact (boundaryCayley_left_inv hu (small (f z))).symm.trans ((congrArg (boundaryCayleyInv u) id).trans (boundaryCayley_left_inv hu (small z)))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.disk_deck_half_plane_form
