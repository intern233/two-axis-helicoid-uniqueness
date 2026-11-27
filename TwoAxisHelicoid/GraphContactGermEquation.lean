import TwoAxisHelicoid.MinimalContactSheet
import TwoAxisHelicoid.ContactProjectionMinor

namespace TwoAxisHelicoid
open Complex Set Filter Function Topology InnerProductSpace
open scoped Topology ContDiff InnerProductSpace Laplacian

/-- The height difference from the second minimal sheet has zero
value and differential at a genuine tangency. Its nearby zero set is
exactly the local sheet intersection, with an arbitrarily small patch
of the second sheet. -/
private theorem regular_graph_contact_germ {X Y : ℂ → Fin 3 → ℝ} {a b : ℂ}
    (hx : ∀ᶠ z in 𝓝 a, (∀ j, HarmonicAt (fun u => X u j) z) ∧ ConformalCoordinateDerivatives X z)
    (hy : ∀ᶠ z in 𝓝 b, (∀ j, HarmonicAt (fun u => Y u j) z) ∧ ConformalCoordinateDerivatives Y z)
    (ix : Injective (fderiv ℝ X a)) (meet : X a=Y b)
    (tangent : ∀ v, ∃ w, fderiv ℝ X a v=fderiv ℝ Y b w)
    (minor : fderiv ℝ Y b 1 0*fderiv ℝ Y b I 1-fderiv ℝ Y b 1 1*fderiv ℝ Y b I 0≠0)
    {V₀ : Set ℂ} (nbd : V₀∈𝓝 b) :
    ∃ (V : Set ℂ) (f A B : ℂ → ℝ), V∈𝓝 b ∧ V⊆V₀ ∧ AnalyticAt ℝ f a ∧ f a=0 ∧ fderiv ℝ f a=0 ∧
      ContinuousAt A a ∧ ContinuousAt B a ∧
      (∀ᶠ z in 𝓝 a, (Δ f) z=A z*planePartial 1 f z+B z*planePartial I f z) ∧
      ∀ᶠ z in 𝓝 a, f z=0 ↔ X z∈Y '' V := by
  let P := spatialGraphProjection 0 1
  let F := fun p : ℝ × ℂ => Y p.2
  let point := P (Y b)
  have ax : AnalyticAt ℝ X a := analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (hx.self_of_nhds.1 j))
  have ay : AnalyticAt ℝ Y b := analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (hy.self_of_nhds.1 j))
  have af : AnalyticAt ℝ F (0,b) := ay.comp ((ContinuousLinearMap.snd ℝ ℝ ℂ).analyticAt _)
  obtain ⟨G⟩ := exists_analytic_contact_sheet af (spatialGraphProjection_injective _ 0 1 minor)
  let g := fun w : ℂ => G.height (0,w)
  let h := fun w : ℂ => G.inv (0,w)
  have an : AnalyticAt ℝ g point := (G.analytic_height af).comp (analyticAt_const.prod analyticAt_id)
  have pin : P (X a)=point := congrArg P meet
  have ag : AnalyticAt ℝ g (P (X a)) := pin ▸ an
  have mY : horizontalMinor (planePartial 1 Y b) (planePartial I Y b)≠0 := by
    simpa only [horizontalMinor,planePartial,mul_comm (fderiv ℝ Y b I 0) _] using minor
  have pde : ∀ᶠ w in 𝓝 (P (X a)), cartesianMinimalGraphOperator g w=0 := pin ▸ G.minimal_graph af hy mY
  let f := immersionGraphDifference X g
  obtain ⟨A,B,ca,cb,eq⟩ := harmonic_immersion_graph_difference_local_drift hx ix ag pde
  have fixed (w : ℂ) : ContinuousAt (fun w : ℂ => ((0:ℝ),w)) w := continuousAt_const.prodMk continuousAt_id
  have center : h point=b := G.center
  have g0 : g point=Y b 2 := congrArg (fun v => Y v 2) center
  have left : ∀ᶠ y in 𝓝 b, h (P (Y y))=y := (fixed b).eventually G.left_inv
  let V := V₀∩{y | h (P (Y y))=y}
  have vnb : V∈𝓝 b := inter_mem nbd left
  have right : ∀ᶠ w in 𝓝 point, P (Y (h w))=w := (fixed point).eventually G.right_inv
  have invt : Tendsto h (𝓝 point) (𝓝 b) := center ▸ (G.analytic.comp (analyticAt_const.prod analyticAt_id)).continuousAt.tendsto
  have project : Tendsto (P ∘ X) (𝓝 a) (𝓝 point) := pin ▸ (P.continuous.continuousAt.comp ax.continuousAt).tendsto
  let L : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 2-(fderiv ℝ g point).comp P
  have dF (Z : ℂ → Fin 3 → ℝ) (z : ℂ) (az : AnalyticAt ℝ Z z) (pz : P (Z z)=point) :
      HasFDerivAt (immersionGraphDifference Z g) (L.comp (fderiv ℝ Z z)) z := by
    have p := P.hasFDerivAt.comp z az.differentiableAt.hasFDerivAt
    have grad : HasFDerivAt g (fderiv ℝ g point) (P (Z z)) := pz ▸ an.differentiableAt.hasFDerivAt
    exact ((ContinuousLinearMap.proj 2 : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z az.differentiableAt.hasFDerivAt).sub (grad.comp z p)
  have zy : immersionGraphDifference Y g =ᶠ[𝓝 b] 0 := by
    filter_upwards [left] with y hy
    exact sub_eq_zero.mpr (congrArg (fun v => Y v 2) hy.symm)
  have nullY : L.comp (fderiv ℝ Y b)=0 := (dF Y b ay rfl).fderiv.symm.trans (zy.fderiv_eq.trans (by simp))
  have flat : fderiv ℝ f a=0 := by
    rw [show fderiv ℝ f a=_ from (dF X a ax pin).fderiv]
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w,e⟩ := tangent v
    change L (fderiv ℝ X a v)=0
    rw [e]
    exact congrArg (fun D : ℂ →L[ℝ] ℝ => D w) nullY
  have touch : f a=0 := sub_eq_zero.mpr ((congrFun meet 2).trans ((congrArg g pin).trans g0).symm)
  refine ⟨V,f,A,B,vnb,inter_subset_left,immersionGraphDifference_analytic ax ag,touch,flat,ca,cb,eq,?_⟩
  filter_upwards [project.eventually right,project.eventually (invt.eventually vnb)] with z proj vin
  constructor
  · intro hz
    exact ⟨h (P (X z)),vin,eq_of_cartesian_graph_data proj (sub_eq_zero.mp hz).symm⟩
  · rintro ⟨y,hy,eq⟩
    change X z 2-g (P (X z))=0
    rw [← eq]
    exact sub_eq_zero.mpr (congrArg (fun v => Y v 2) hy.2.symm)

/-- In arbitrary Cartesian coordinates, the two original regular
minimal sheets yield a scalar analytic drift germ in the *first*
sheet's conformal parameter and the intersection with a genuine
neighborhood of the second sheet. -/
theorem tangent_minimal_sheet_germ_equation {X Y : ℂ → Fin 3 → ℝ} {a b : ℂ}
    (hx : ∀ᶠ z in 𝓝 a, (∀ j, HarmonicAt (fun u => X u j) z) ∧ ConformalCoordinateDerivatives X z)
    (hy : ∀ᶠ z in 𝓝 b, (∀ j, HarmonicAt (fun u => Y u j) z) ∧ ConformalCoordinateDerivatives Y z)
    (ix : Injective (fderiv ℝ X a)) (iy : Injective (fderiv ℝ Y b)) (meet : X a=Y b)
    (same : (fderiv ℝ X a).range=(fderiv ℝ Y b).range) {V₀ : Set ℂ} (nbd : V₀∈𝓝 b) :
    ∃ (V : Set ℂ) (f A B : ℂ → ℝ), V∈𝓝 b ∧ V⊆V₀ ∧ AnalyticAt ℝ f a ∧ f a=0 ∧ fderiv ℝ f a=0 ∧
      ContinuousAt A a ∧ ContinuousAt B a ∧
      (∀ᶠ z in 𝓝 a, (Δ f) z=A z*planePartial 1 f z+B z*planePartial I f z) ∧
      ∀ᶠ z in 𝓝 a, f z=0 ↔ X z∈Y '' V := by
  obtain ⟨σ,_,minor⟩ := common_coordinate_minor_of_tangent_eq _ _ ix iy same
  let T : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (σ j))
  have inj : Injective T := by
    intro v w eq
    funext k
    obtain ⟨i,rfl⟩ := σ.surjective k
    exact congrFun eq i
  have reg (Z : ℂ → Fin 3 → ℝ) {z : ℂ}
      (hz : (∀ j, HarmonicAt (fun u => Z u j) z) ∧ ConformalCoordinateDerivatives Z z) :
      (∀ j, HarmonicAt (fun u => (T ∘ Z) u j) z) ∧ ConformalCoordinateDerivatives (T ∘ Z) z :=
    ⟨fun j => hz.1 (σ j),conformal_reindex_coordinates σ hz.2⟩
  have d (Z : ℂ → Fin 3 → ℝ) {z : ℂ} (hz : ∀ j, HarmonicAt (fun u => Z u j) z) :
      fderiv ℝ (T ∘ Z) z=T.comp (fderiv ℝ Z z) :=
    (T.hasFDerivAt.comp z (analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (hz j))).differentiableAt.hasFDerivAt).fderiv
  have dx := d X hx.self_of_nhds.1
  have dy := d Y hy.self_of_nhds.1
  have transfer (v : ℂ) : ∃ w, fderiv ℝ (T ∘ X) a v=fderiv ℝ (T ∘ Y) b w := by
    have inside : fderiv ℝ X a v∈(fderiv ℝ Y b).range := by rw [← same]; exact ⟨v,rfl⟩
    obtain ⟨w,hw⟩ := inside
    exact ⟨w,by rw [dx,dy]; exact congrArg T hw.symm⟩
  obtain ⟨V,f,A,B,vn,vs,an,z,flat,ca,cb,eq,localEq⟩ := regular_graph_contact_germ
    (hx.mono fun _ h => reg X h) (hy.mono fun _ h => reg Y h)
    (dx ▸ inj.comp ix) (congrArg T meet) transfer (by rw [dy]; exact minor) nbd
  refine ⟨V,f,A,B,vn,vs,an,z,flat,ca,cb,eq,?_⟩
  filter_upwards [localEq] with u h
  exact h.trans ⟨fun ⟨v,hv,e⟩ => ⟨v,hv,inj e⟩,fun ⟨v,hv,e⟩ => ⟨v,hv,congrArg T e⟩⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.tangent_minimal_sheet_germ_equation
