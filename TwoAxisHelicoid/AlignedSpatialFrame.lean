import TwoAxisHelicoid.AlignedSpatialHeight

namespace TwoAxisHelicoid
open Complex Matrix Filter Set
open scoped Topology
set_option maxHeartbeats 1400000

/-- The horizontal orthogonal block of an ambient axis-preserving map
is a rotation composed, when the horizontal orientation changes, with
one coordinate reflection. -/
theorem aligned_orthogonal_frame (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    (hL : ∀ u v, L u ⬝ᵥ L v = u ⬝ᵥ v)
    (haxis : L ![0,0,1] 0 = 0 ∧ L ![0,0,1] 1 = 0) :
    ∃ a b t e : ℝ, a^2+b^2 = 1 ∧ (t = 1 ∨ t = -1) ∧ (e = 1 ∨ e = -1) ∧
      ∀ p, L p = ![a*p 0-t*b*p 1,b*p 0+t*a*p 1,e*p 2] := by
  let i : Fin 3 → ℝ := ![1,0,0]
  let j : Fin 3 → ℝ := ![0,1,0]
  let k : Fin 3 → ℝ := ![0,0,1]
  obtain ⟨e,he,hz⟩ := aligned_orthogonal_height L hL haxis
  have hi₂ : L i 2 = 0 := by rw [hz]; simp [i]
  have hj₂ : L j 2 = 0 := by rw [hz]; simp [j]
  let a := L i 0
  let b := L i 1
  let c := L j 0
  let d := L j 1
  let t := a*d-b*c
  have haa : a*a+b*b = 1 := by
    have hh := hL i i
    simpa [dotProduct,Fin.sum_univ_succ,hi₂,a,b,show i 0 = 1 from rfl,show i 1 = 0 from rfl,
      show i 2 = 0 from rfl] using hh
  have hcc : c*c+d*d = 1 := by
    have hh := hL j j
    simpa [dotProduct,Fin.sum_univ_succ,hj₂,c,d,show j 0 = 0 from rfl,show j 1 = 1 from rfl,
      show j 2 = 0 from rfl] using hh
  have hac : a*c+b*d = 0 := by
    have hh := hL i j
    simpa [dotProduct,Fin.sum_univ_succ,hi₂,hj₂,a,b,c,d,show i 0 = 1 from rfl,show i 1 = 0 from rfl,
      show i 2 = 0 from rfl,show j 0 = 0 from rfl] using hh
  have ht : t^2 = 1 := by
    calc
      t^2 = (a*a+b*b)*(c*c+d*d)-(a*c+b*d)^2 := by dsimp only [t]; ring
      _ = _ := by rw [haa,hcc,hac]; norm_num
  have htc : c = -t*b := by
    dsimp only [t]
    linear_combination a*hac-c*haa
  have htd : d = t*a := by
    dsimp only [t]
    linear_combination b*hac-d*haa
  refine ⟨a,b,t,e,by simpa only [pow_two] using haa,?_,he,?_⟩
  · have h0 : (t-1)*(t+1) = 0 := by nlinarith only [ht]
    exact (mul_eq_zero.mp h0).imp sub_eq_zero.mp eq_neg_of_add_eq_zero_left
  · intro p
    have hdec : p = p 0 • i+p 1 • j+p 2 • k := by
      ext m
      fin_cases m <;> simp [i,j,k]
    have hh : L p = p 0 • L i+p 1 • L j+p 2 • L k := by
      nth_rw 1 [hdec]
      rw [map_add,map_add,map_smul,map_smul,map_smul]
    ext m
    fin_cases m
    · change L p 0 = _
      rw [hh]
      change p 0*a+p 1*c+p 2*L k 0 = a*p 0-t*b*p 1
      rw [show L k 0 = 0 from haxis.1,htc]
      ring
    · change L p 1 = _
      rw [hh]
      change p 0*b+p 1*d+p 2*L k 1 = b*p 0+t*a*p 1
      rw [show L k 1 = 0 from haxis.2,htd]
      ring
    · exact hz p

theorem scalarComplexCoefficient_horizontal {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : DifferentiableAt ℝ X z) (c a b : ℝ) :
    scalarComplexCoefficient (fun w => c+(a*X w 0+b*X w 1)) z =
      (a : ℂ)*immersionComplexCoefficient X z 0+(b : ℂ)*immersionComplexCoefficient X z 1 := by
  let f := fun w => X w 0
  let g := fun w => X w 1
  have hf : DifferentiableAt ℝ f z :=
    (ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ).differentiableAt.comp z hX
  have hg : DifferentiableAt ℝ g z :=
    (ContinuousLinearMap.proj (1 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ).differentiableAt.comp z hX
  have hd : HasFDerivAt (fun w => c+(a*f w+b*g w)) (a • fderiv ℝ f z+b • fderiv ℝ g z) z :=
    ((hf.hasFDerivAt.const_smul a).add (hg.hasFDerivAt.const_smul b)).const_add c
  change scalarComplexCoefficient (fun w => c+(a*f w+b*g w)) z =
    (a : ℂ)*scalarComplexCoefficient f z+(b : ℂ)*scalarComplexCoefficient g z
  unfold scalarComplexCoefficient
  rw [hd.fderiv]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul,Complex.ofReal_add,Complex.ofReal_mul]
  ring

/-- The real orthogonal transformation gives these three actual
complex Weierstrass coefficients by differentiation of the map. -/
theorem aligned_orthogonal_immersion_coefficients
    (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (P : Fin 3 → ℝ)
    (hL : ∀ u v, L u ⬝ᵥ L v = u ⬝ᵥ v) (haxis : L ![0,0,1] 0 = 0 ∧ L ![0,0,1] 1 = 0) :
    ∃ a b t e : ℝ, a^2+b^2 = 1 ∧ (t = 1 ∨ t = -1) ∧ (e = 1 ∨ e = -1) ∧
      ∀ (X : ℂ → Fin 3 → ℝ) (z : ℂ), DifferentiableAt ℝ X z →
        let q := immersionComplexCoefficient X z
        immersionComplexCoefficient (fun w => P+L (X w)) z =
          ![(a:ℂ)*q 0-t*b*q 1,(b:ℂ)*q 0+t*a*q 1,(e:ℂ)*q 2] := by
  obtain ⟨a,b,t,e,hab,ht,he,hframe⟩ := aligned_orthogonal_frame L hL haxis
  refine ⟨a,b,t,e,hab,ht,he,?_⟩
  intro X z hX
  dsimp only
  ext j
  fin_cases j
  · change scalarComplexCoefficient (fun w => P 0+L (X w) 0) z = _
    simp only [hframe,Matrix.cons_val_zero,sub_eq_add_neg,← neg_mul]
    rw [scalarComplexCoefficient_horizontal hX]
    push_cast
    ring
  · change scalarComplexCoefficient (fun w => P 1+L (X w) 1) z = _
    simp only [hframe,Matrix.cons_val_one,Matrix.cons_val_zero]
    rw [scalarComplexCoefficient_horizontal hX]
    push_cast
    ring
  · change scalarComplexCoefficient (fun w => P 2+L (X w) 2) z = _
    simp only [hframe,Matrix.cons_val_two]
    exact scalarComplexCoefficient_affine
      ((ContinuousLinearMap.proj (2 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ).differentiableAt.comp z hX) _ _

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.aligned_orthogonal_immersion_coefficients
