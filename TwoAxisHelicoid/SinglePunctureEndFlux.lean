import TwoAxisHelicoid.RadialEdgeStokes
import TwoAxisHelicoid.SpinSquareFundamentalDomain
import TwoAxisHelicoid.HarmonicTorusRigidityData

namespace TwoAxisHelicoid
open Complex Set MeasureTheory InnerProductSpace

/-- The oriented integral around a shrinking fundamental parallelogram
centered at the missing point. The top and left edges have reversed signs. -/
noncomputable def punctureBoundaryIntegral (L : PeriodPair) (f : ℂ → ℂ) (r : ℝ) : ℂ :=
  let A := spinSquareLinear L (-1/2) (-1/2)
  let B := spinSquareLinear L (1/2) (-1/2)
  let C := spinSquareLinear L (-1/2) (1/2)
  let D := spinSquareLinear L (1/2) (1/2)
  dilatedEdgeIntegral f A B r+dilatedEdgeIntegral f B D r-
    dilatedEdgeIntegral f C D r-dilatedEdgeIntegral f A C r

private theorem translated_dilated_edge {f : ℂ → ℂ} {v : ℂ} (hp : ∀ z, f (z+v) = f z)
    (a b : ℂ) : dilatedEdgeIntegral f (a+v) (b+v) 1 = dilatedEdgeIntegral f a b 1 := by
  simp only [dilatedEdgeIntegral,Complex.ofReal_one,one_mul,add_sub_add_right_eq_sub]
  apply intervalIntegral.integral_congr
  intro s _
  change (b-a)*f (a+v+(s:ℂ)*(b-a)) = (b-a)*f (a+(s:ℂ)*(b-a))
  rw [show a+v+(s:ℂ)*(b-a) = a+(s:ℂ)*(b-a)+v by ring,hp]

private theorem swept_period_coordinates (L : PeriodPair) (x y u v s t : ℝ) :
    (t:ℂ)*(spinSquareLinear L x y+(s:ℂ)*(spinSquareLinear L u v-spinSquareLinear L x y)) =
      spinSquareLinear L (t*(x+s*(u-x))) (t*(y+s*(v-y))) := by
  simp [spinSquareLinear,Complex.real_smul]
  ring

private theorem nonintegral_scaled_half {r k : ℝ} (hr : 0 < r) (hr' : r ≤ 1)
    (hk : k = -1/2 ∨ k = 1/2) : ¬ ∃ n : ℤ, r*k = n := by
  intro h
  rcases hk with rfl | rfl <;>
    have h0 := real_integer_between_neg_one_one (x := r*_) (by linarith) (by linarith) h <;> linarith

/-- Each point of a scaled boundary side has a nonintegral lattice coordinate.
This holds even at a vertex and for arbitrary choices of the free coordinate. -/
theorem puncture_square_side_regular (L : PeriodPair) (x y u v s t : ℝ) (ht : 0 < t) (ht' : t ≤ 1)
    (h : (x = u ∧ (x = -1/2 ∨ x = 1/2)) ∨ (y = v ∧ (y = -1/2 ∨ y = 1/2))) :
    (t:ℂ)*(spinSquareLinear L x y+(s:ℂ)*(spinSquareLinear L u v-spinSquareLinear L x y)) ∉ L.lattice := by
  rw [swept_period_coordinates]
  intro hm
  obtain ⟨m,n,hm,hn⟩ := (integral_period_coordinates_iff L _).mp hm
  rw [(spinSquareLinear_coords L _ _).1] at hm
  rw [(spinSquareLinear_coords L _ _).2] at hn
  rcases h with ⟨rfl,hx⟩ | ⟨rfl,hy⟩
  · exact nonintegral_scaled_half ht ht' hx ⟨m,by simpa using hm⟩
  · exact nonintegral_scaled_half ht ht' hy ⟨n,by simpa using hn⟩

/-- Every periodic holomorphic differential on the once-punctured torus
has zero complex period around its end. No regularity at the puncture is
needed. Opposite outer edges cancel, and Green's formula transports this
to every smaller parallelogram. -/
theorem single_puncture_boundary_integral_zero (L : PeriodPair) {f : ℂ → ℂ}
    (hf : ∀ z ∉ L.lattice, DifferentiableAt ℂ f z)
    (hp : ∀ z v, v ∈ L.lattice → f (z+v) = f z) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) :
    punctureBoundaryIntegral L f r = 0 := by
  let A := spinSquareLinear L (-1/2) (-1/2)
  let B := spinSquareLinear L (1/2) (-1/2)
  let C := spinSquareLinear L (-1/2) (1/2)
  let D := spinSquareLinear L (1/2) (1/2)
  have sides (x y u v : ℝ)
      (h : (x = u ∧ (x = -1/2 ∨ x = 1/2)) ∨ (y = v ∧ (y = -1/2 ∨ y = 1/2))) :
      dilatedEdgeIntegral f (spinSquareLinear L x y) (spinSquareLinear L u v) 1-
      dilatedEdgeIntegral f (spinSquareLinear L x y) (spinSquareLinear L u v) r =
      radialConnectorIntegral f (spinSquareLinear L u v) r 1-radialConnectorIntegral f (spinSquareLinear L x y) r 1 := by
    apply dilated_edge_stokes _ _ hr'
    intro t ht s _
    exact hf _ (puncture_square_side_regular L x y u v s t (hr.trans_le ht.1) ht.2 h)
  have bottom := sides (-1/2) (-1/2) (1/2) (-1/2) (Or.inr ⟨rfl,Or.inl rfl⟩)
  have top := sides (-1/2) (1/2) (1/2) (1/2) (Or.inr ⟨rfl,Or.inr rfl⟩)
  have left := sides (-1/2) (-1/2) (-1/2) (1/2) (Or.inl ⟨rfl,Or.inl rfl⟩)
  have right := sides (1/2) (-1/2) (1/2) (1/2) (Or.inl ⟨rfl,Or.inr rfl⟩)
  have Bx : B = A+L.ω₁ := by simp [B,A,spinSquareLinear,Complex.real_smul]; ring
  have Cx : C = A+L.ω₂ := by simp [C,A,spinSquareLinear,Complex.real_smul]; ring
  have Dx : D = C+L.ω₁ := by simp [D,C,spinSquareLinear,Complex.real_smul]; ring
  have Dy : D = B+L.ω₂ := by simp [D,B,spinSquareLinear,Complex.real_smul]; ring
  have htop : dilatedEdgeIntegral f C D 1 = dilatedEdgeIntegral f A B 1 := by
    rw [Cx,Dy]; exact translated_dilated_edge (fun z => hp z _ L.ω₂_mem_lattice) _ _
  have hright : dilatedEdgeIntegral f B D 1 = dilatedEdgeIntegral f A C 1 := by
    rw [Bx,Dx]; exact translated_dilated_edge (fun z => hp z _ L.ω₁_mem_lattice) _ _
  change dilatedEdgeIntegral f A B r+dilatedEdgeIntegral f B D r-dilatedEdgeIntegral f C D r-
    dilatedEdgeIntegral f A C r = 0
  linear_combination top+left-bottom-right-htop+hright

/-- All three coordinate fluxes of an actual harmonic immersion vanish on
the peripheral cycle, even when a handle cycle has nonzero flux. -/
theorem actual_immersion_end_flux_zero (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hh : ∀ z ∉ L.lattice, ∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z)
    {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) (j : Fin 3) :
    punctureBoundaryIntegral L (fun z => torusImmersionForms L X z j) r = 0 :=
  single_puncture_boundary_integral_zero L (fun z hz => (scalarComplexCoefficient_analyticAt (hh z hz j)).differentiableAt)
    (fun z v hv => congrFun (torusImmersionForms_periodic L X z v hv) j) hr hr'

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_immersion_end_flux_zero
