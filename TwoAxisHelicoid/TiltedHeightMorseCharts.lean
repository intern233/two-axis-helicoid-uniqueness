import TwoAxisHelicoid.CenteredGraphContactHessian
import TwoAxisHelicoid.PlanarMorseCoordinates
import TwoAxisHelicoid.SimpleImmersionHeightContacts

namespace TwoAxisHelicoid
open Complex Filter Set Topology MeasureTheory InnerProductSpace
open scoped Topology ContDiff RealInnerProductSpace

/-- At a nondegenerate contact of an actual embedded surface with a
tilted plane the physical height is exactly a signed sum of squares
in a local chart centered at the contact. -/
theorem tilted_height_morse_chart_with_differentials {F : ℂ → Fin 3 → ℝ} {z s : ℂ}
    (e : OpenPartialHomeomorph ℂ ℂ) (u : ℂ → ℝ) (src : z∈e.source)
    (proj : ∀ y, e y=spatialGraphProjection 0 1 (F y)) (sm : ContDiffAt ℝ 3 u (e z))
    (near : ∀ᶠ y in 𝓝 z, F y 2=u (e y))
    (crit : gradient u (e z)=s) (det : (fderiv ℝ (gradient u) (e z)).det≠0) :
    ∃ (a b : ℝ) (q : OpenPartialHomeomorph ℂ (ℝ×ℝ)),
      a*a=1 ∧ b*b=1 ∧ z∈q.source ∧ q z=0 ∧
      (ContDiffAt ℝ 1 e z → ContDiffAt ℝ 1 e.symm (e z) →
        ContDiffAt ℝ 1 q z ∧ ContDiffAt ℝ 1 q.symm 0) ∧
      ∀ᶠ w in 𝓝 z, tiltedSpatialHeight s (F w)=tiltedSpatialHeight s (F z)+a*(q w).1^2+b*(q w).2^2 := by
  let x := e z
  let E := Complex.equivRealProdCLM.symm
  let G := fun p : ℝ×ℝ => u (x+E p)-⟪s,x+E p⟫_ℝ
  obtain ⟨smooth,zero,regular⟩ := centered_graph_contact_hessian sm crit det
  obtain ⟨a,b,J,m,aa,bb,at0,m0,dm,dmback,model⟩ := planar_nondegenerate_morse_coordinates (f:=G) smooth zero regular
  let T := (J.toHomeomorph.trans E.toHomeomorph).trans (Homeomorph.addRight x)
  let k := e.trans T.symm.toOpenPartialHomeomorph
  let q := k.trans m
  have T0 : T 0=x := by simp [T]
  have kz : k z=0 := T.injective (by change T (T.symm x)=T 0; rw [T.apply_symm_apply,T0])
  have ks : z∈k.source := ⟨src,mem_univ _⟩
  have qs : z∈q.source := ⟨ks,show k z∈m.source by rw [kz]; exact at0⟩
  have qz : q z=0 := by change m (k z)=0; rw [kz,m0]
  have coord (w : ℂ) : x+E (J (k w))=e w := by
    rw [add_comm]
    exact T.apply_symm_apply (e w)
  have lift : Tendsto k (𝓝 z) (𝓝 0) := kz ▸ k.continuousAt ks
  have G0 : G 0=tiltedSpatialHeight s (F z) := by
    change u (x+E 0)-⟪s,x+E 0⟫_ℝ=F z 2-⟪s,spatialGraphProjection 0 1 (F z)⟫_ℝ
    rw [map_zero,add_zero,near.self_of_nhds,← proj]
  have dT : ContDiff ℝ 1 T := (E.contDiff.comp J.contDiff).add contDiff_const
  have dTinv : ContDiff ℝ 1 T.symm := J.symm.contDiff.comp (E.symm.contDiff.comp (contDiff_id.add contDiff_const))
  have inv0 : m.symm 0=0 := (congrArg m.symm m0.symm).trans (m.left_inv at0)
  refine ⟨a,b,q,aa,bb,qs,qz,?_,?_⟩
  · intro de deback
    have dk : ContDiffAt ℝ 1 k z := dTinv.contDiffAt.comp z de
    have dm' : ContDiffAt ℝ 1 m (k z) := kz.symm ▸ dm
    have dd : ContDiffAt ℝ 1 e.symm (T (m.symm 0)) := by rw [inv0,T0]; exact deback
    refine ⟨dm'.comp z dk,?_⟩
    change ContDiffAt ℝ 1 (e.symm ∘ (T ∘ m.symm)) 0
    exact dd.comp 0 (dT.contDiffAt.comp 0 dmback)
  filter_upwards [near,lift.eventually model] with w h eq
  change G (J (k w))=G 0+a*(q w).1^2+b*(q w).2^2 at eq
  rw [← G0,← eq]
  change F w 2-⟪s,spatialGraphProjection 0 1 (F w)⟫_ℝ=
    u (x+E (J (k w)))-⟪s,x+E (J (k w))⟫_ℝ
  rw [coord,h,proj]

/- The underlying oriented height germ does not require differentiability of its projection chart. -/
theorem tilted_height_morse_chart {F : ℂ → Fin 3 → ℝ} {z s : ℂ}
    (e : OpenPartialHomeomorph ℂ ℂ) (u : ℂ → ℝ) (src : z∈e.source)
    (proj : ∀ y, e y=spatialGraphProjection 0 1 (F y)) (sm : ContDiffAt ℝ 3 u (e z))
    (near : ∀ᶠ y in 𝓝 z, F y 2=u (e y))
    (crit : gradient u (e z)=s) (det : (fderiv ℝ (gradient u) (e z)).det≠0) :
    ∃ (a b : ℝ) (q : OpenPartialHomeomorph ℂ (ℝ×ℝ)),
      a*a=1 ∧ b*b=1 ∧ z∈q.source ∧ q z=0 ∧
      ∀ᶠ w in 𝓝 z, tiltedSpatialHeight s (F w)=tiltedSpatialHeight s (F z)+a*(q w).1^2+b*(q w).2^2 := by
  obtain ⟨a,b,q,aa,bb,qs,qz,_,model⟩ := tilted_height_morse_chart_with_differentials e u src proj sm near crit det
  exact ⟨a,b,q,aa,bb,qs,qz,model⟩

/-- Almost every tilt gives local extrema or an ordinary four-branch
saddle at each immersion contact, with distinct critical values for
distinct spatial points. -/
theorem ae_tilted_height_differentiable_morse_charts {D : Set ℂ} {F : ℂ → Fin 3 → ℝ}
    (sm : ∀ z∈D, ContDiffAt ℝ 3 F z) (imm : ∀ z∈D, Function.Injective (fderiv ℝ F z))
    (mark : Fin 3 → ℝ) :
    ∀ᵐ s : ℂ, ∀ z∈D, fderiv ℝ (tiltedSpatialHeight s ∘ F) z=0 →
      (∃ (a b : ℝ) (q : OpenPartialHomeomorph ℂ (ℝ×ℝ)), a*a=1 ∧ b*b=1 ∧ z∈q.source ∧ q z=0 ∧
        ContDiffAt ℝ 1 q z ∧ ContDiffAt ℝ 1 q.symm 0 ∧
        ∀ᶠ w in 𝓝 z, tiltedSpatialHeight s (F w)=tiltedSpatialHeight s (F z)+a*(q w).1^2+b*(q w).2^2) ∧
      (∀ w∈D, fderiv ℝ (tiltedSpatialHeight s ∘ F) w=0 →
        tiltedSpatialHeight s (F w)=tiltedSpatialHeight s (F z) → F w=F z) ∧
      (tiltedSpatialHeight s (F z)=tiltedSpatialHeight s mark → F z=mark) := by
  filter_upwards [ae_simple_immersion_height_contacts sm imm mark] with s hs
  intro z hz critical
  obtain ⟨⟨e,u,src,proj,de,db,du,near,grad,det⟩,simple,fixed⟩ := hs z hz critical
  obtain ⟨a,b,q,aa,bb,qs,qz,diff,model⟩ := tilted_height_morse_chart_with_differentials e u src proj du near grad det
  obtain ⟨dq,dback⟩ := diff (de.of_le (by norm_num)) (db.of_le (by norm_num))
  exact ⟨⟨a,b,q,aa,bb,qs,qz,dq,dback,model⟩,simple,fixed⟩

theorem ae_tilted_height_morse_charts {D : Set ℂ} {F : ℂ → Fin 3 → ℝ}
    (sm : ∀ z∈D, ContDiffAt ℝ 3 F z) (imm : ∀ z∈D, Function.Injective (fderiv ℝ F z))
    (mark : Fin 3 → ℝ) :
    ∀ᵐ s : ℂ, ∀ z∈D, fderiv ℝ (tiltedSpatialHeight s ∘ F) z=0 →
      (∃ (a b : ℝ) (q : OpenPartialHomeomorph ℂ (ℝ×ℝ)), a*a=1 ∧ b*b=1 ∧ z∈q.source ∧ q z=0 ∧
        ∀ᶠ w in 𝓝 z, tiltedSpatialHeight s (F w)=tiltedSpatialHeight s (F z)+a*(q w).1^2+b*(q w).2^2) ∧
      (∀ w∈D, fderiv ℝ (tiltedSpatialHeight s ∘ F) w=0 →
        tiltedSpatialHeight s (F w)=tiltedSpatialHeight s (F z) → F w=F z) ∧
      (tiltedSpatialHeight s (F z)=tiltedSpatialHeight s mark → F z=mark) := by
  filter_upwards [ae_tilted_height_differentiable_morse_charts sm imm mark] with s good
  intro z hz critical
  obtain ⟨⟨a,b,q,aa,bb,src,center,_,_,model⟩,simple,fixed⟩ := good z hz critical
  exact ⟨⟨a,b,q,aa,bb,src,center,model⟩,simple,fixed⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ae_tilted_height_morse_charts

#print axioms TwoAxisHelicoid.ae_tilted_height_differentiable_morse_charts
