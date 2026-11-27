import TwoAxisHelicoid.HoffmanWhiteCompactClass
import TwoAxisHelicoid.UnmarkedChartPlaneLimit

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology RealInnerProductSpace

/-- In the topology of smooth local sheets, ordinary point convergence
and exhausting first derivative control verify the cutoff hypothesis
for a fixed-axis class. Its sheets have no prescribed numbering or
marking and the index has no prescribed multiplicity. -/
theorem FixedAxisHelicoidNormalClass.compactCutoffs_of_local_charts {I : Type*}
    [TopologicalSpace I] [FirstCountableTopology I] (F : FixedAxisHelicoidNormalClass I)
    {B : I → Type*} (X N : ∀ m, B m → SurfaceEuclideanSpace)
    (normal : ∀ m, F.normal m=unorientedSurfaceNormals (X m) (N m))
    (unit : ∀ m b, ‖N m b‖=1)
    (compact : ∀ η : ℝ, Real.pi/2<η → IsCompact {m : I | HasNoScrewBelow η (physicalNormalPositions (F.normal m))})
    (positions : ∀ (a : ℕ → I) m, Tendsto a atTop (𝓝 m) →
      LocalSpatialImageLimit (fun n => range (X (a n))) (range (X m)))
    (charts : ∀ (a : ℕ → I) m, Tendsto a atTop (𝓝 m) → ∀ b : B m,
      ∃ T : ℂ →L[ℝ] SurfaceEuclideanSpace, Function.Injective T ∧ (∀ v, ⟪T v,N m b⟫=0) ∧
        ∀ V∈𝓝 T, ∃ W∈𝓝 (X m b), ∀ᶠ n in atTop, ∀ y : B (a n), X (a n) y∈W →
          ∃ (Y : ℂ → SurfaceEuclideanSpace) (w : ℂ), Y w=X (a n) y ∧ fderiv ℝ Y w∈V ∧
            ∀ v, ⟪fderiv ℝ Y w v,N (a n) y⟫=0) : F.compactCutoffs := by
  apply F.compactCutoffs_of_topological compact
  intro a m conv
  change LocalSpatialImageLimit (fun n => F.normal (a n)) (F.normal m)
  simp only [normal]
  apply unmarked_chart_derivatives_give_normal_limit
  · rintro n y t ⟨b,atb,sign⟩
    refine ⟨b,atb,?_⟩
    rcases sign with h|h
    · exact Or.inr (congrArg Neg.neg h)
    · change t= -N (a n) b at h
      exact Or.inl ((congrArg Neg.neg h).trans (neg_neg _))
  · rintro n q ⟨b,_,h|h⟩
    · rw [h,unit]
    · rw [h,norm_neg,unit]
  · have eq (n : ℕ) : Prod.fst '' unorientedSurfaceNormals (X (a n)) (N (a n))=range (X (a n)) := by
      ext y
      constructor
      · rintro ⟨q,⟨b,h,_⟩,rfl⟩
        exact ⟨b,h⟩
      · rintro ⟨b,rfl⟩
        exact ⟨(X (a n) b,N (a n) b),⟨b,rfl,Or.inl rfl⟩,rfl⟩
    simpa only [eq] using positions a m conv
  · intro b
    obtain ⟨T,inj,perp,region⟩ := charts a m conv b
    refine ⟨T,inj,unit m b,perp,?_⟩
    intro V nv
    obtain ⟨W,nw,event⟩ := region V nv
    refine ⟨W,nw,?_⟩
    filter_upwards [event] with n good
    rintro q ⟨y,pos,sig⟩ hq
    obtain ⟨Y,w,point,dy,ortho⟩ := good y (pos.symm ▸ hq)
    refine ⟨Y,w,point.trans pos,dy,?_⟩
    intro v
    rcases sig with h|h
    · rw [h,ortho]
    · rw [h,inner_neg_right,ortho,neg_zero]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.FixedAxisHelicoidNormalClass.compactCutoffs_of_local_charts
