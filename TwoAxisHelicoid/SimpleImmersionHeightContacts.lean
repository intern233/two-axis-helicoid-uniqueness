import TwoAxisHelicoid.ImmersionHorizontalGraphCover
import TwoAxisHelicoid.GenericSimpleGraphContacts

namespace TwoAxisHelicoid
open Complex Filter Set Topology MeasureTheory InnerProductSpace
open scoped ContDiff Topology RealInnerProductSpace

private theorem spatial_graph_point_eq {p q : Fin 3 → ℝ}
    (eq : (spatialGraphProjection 0 1 p,p 2)=(spatialGraphProjection 0 1 q,q 2)) : p=q := by
  ext i
  fin_cases i
  · exact congrArg (fun u : ℂ × ℝ => u.1.re) eq
  · exact congrArg (fun u : ℂ × ℝ => u.1.im) eq
  · exact congrArg Prod.snd eq

/-- Generic tilted heights on an actual immersed patch have a nonsingular
graph Hessian at every critical point. Distinct physical contact points
have distinct heights and avoid the height of a prescribed physical
point. The domain can be a lattice complement, and the parameter may
cover the same physical point more than once. -/
theorem ae_simple_immersion_height_contacts {D : Set ℂ} {F : ℂ → Fin 3 → ℝ}
    (smooth : ∀ z∈D, ContDiffAt ℝ 3 F z)
    (imm : ∀ z∈D, Function.Injective (fderiv ℝ F z)) (mark : Fin 3 → ℝ) :
    ∀ᵐ s : ℂ, ∀ z∈D, fderiv ℝ (tiltedSpatialHeight s ∘ F) z=0 →
      (∃ (e : OpenPartialHomeomorph ℂ ℂ) (u : ℂ → ℝ), z∈e.source ∧
        (∀ y, e y=spatialGraphProjection 0 1 (F y)) ∧
        ContDiffAt ℝ 3 e z ∧ ContDiffAt ℝ 3 e.symm (e z) ∧ ContDiffAt ℝ 3 u (e z) ∧
        (∀ᶠ y in 𝓝 z, F y 2=u (e y)) ∧ gradient u (e z)=s ∧
        (fderiv ℝ (gradient u) (e z)).det≠0) ∧
      (∀ w∈D, fderiv ℝ (tiltedSpatialHeight s ∘ F) w=0 →
        tiltedSpatialHeight s (F w)=tiltedSpatialHeight s (F z) → F w=F z) ∧
      (tiltedSpatialHeight s (F z)=tiltedSpatialHeight s mark → F z=mark) := by
  classical
  let P := spatialGraphProjection 0 1
  obtain ⟨C,ct,W,f,sw,cover⟩ := countable_horizontal_graph_contact_cover smooth imm
  let _ : Countable C := ct.to_subtype
  have good := ae_simple_graph_plane_contacts W f sw (P mark,mark 2)
  filter_upwards [good] with s simple
  intro z hz critical
  obtain ⟨i,inside,hz'c,grad,e,es,proj,de,back,near⟩ := cover s z hz critical
  obtain ⟨det,separate,fixed⟩ := simple i _ inside grad
  refine ⟨⟨e,f i,es,proj,de,back,?_,near,?_,?_⟩,?_,?_⟩
  · rw [proj]; exact sw i _ inside
  · rwa [proj]
  · rwa [proj]
  · intro w hw crit eq
    obtain ⟨j,hj,wc,gw,_⟩ := cover s w hw crit
    have ht : f i (P (F z))-⟪s,P (F z)⟫_ℝ=f j (P (F w))-⟪s,P (F w)⟫_ℝ := by
      rw [hz'c,wc]; exact eq.symm
    have same := separate j _ hj gw ht
    rw [hz'c,wc] at same
    exact spatial_graph_point_eq same.symm
  · intro eq
    have ht : f i (P (F z))-⟪s,P (F z)⟫_ℝ=mark 2-⟪s,P mark⟫_ℝ := by
      rw [hz'c]; exact eq
    have same := fixed ht
    rw [hz'c] at same
    exact spatial_graph_point_eq same

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ae_simple_immersion_height_contacts
