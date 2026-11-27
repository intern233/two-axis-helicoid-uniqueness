import TwoAxisHelicoid.SpatialPairedIntegral
import TwoAxisHelicoid.QuarterSpatialPathBounds

namespace TwoAxisHelicoid
open Complex Set Metric

noncomputable def spatialMeanObservable (first reflected : Bool) : ℂ →L[ℝ] ℝ :=
  if first then (-1/2:ℝ) • Complex.reCLM else (if reflected then (1/2:ℝ) else -1/2) • Complex.imCLM

/-- Exact endpoint displacement on a horizontal parameter segment
of the actual certified immersion, using the two complex theta
integrals on reflected segments. -/
theorem actual_horizontal_displacement_by_means (first : Bool) (e l r : ℝ) (lr : l≤r) :
    let p := certifiedClosedParameters
    let f := thetaA p.t p.a
    let x := (l+r)/2
    let h := (r-l)/2
    let c : ℂ := ⟨x,e⟩
    ∀ {X : ℂ → Fin 3 → ℝ}, HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos →
      (∀ t∈Icc l r, centralBandEdgePoint false e t∉certifiedPeriodPair.lattice) →
      ContinuousOn (fun t : ℝ => f (c+(h:ℂ)*t)) (Icc (-1:ℝ) 1) →
      ContinuousOn (fun t : ℝ => f (-c+(h:ℂ)*t)) (Icc (-1:ℝ) 1) →
      X ⟨r,e⟩ (if first then 0 else 1)-X ⟨l,e⟩ (if first then 0 else 1)=
        (r-l)*(spatialMeanObservable first false (normalizedIntegral f c h)+
          spatialMeanObservable first true (normalizedIntegral f (-c) h)) := by
  intro p f x h c X d off plus minus
  let j : Fin 3 := if first then 0 else 1
  let u := fun t : ℝ => X (centralBandEdgePoint false e (x+h*t)) j
  have hp : 0≤h := by dsimp [h]; linarith
  have z (t : ℝ) : centralBandEdgePoint false e (x+h*t)=c+(h:ℂ)*t := by
    apply Complex.ext <;> simp [centralBandEdgePoint,c]
  have rate (t : ℝ) (tI : t∈Icc (-1:ℝ) 1) : HasDerivAt u
      (h*(spatialMeanObservable first false (f (c+(h:ℂ)*t))+
        spatialMeanObservable first true (f (-(c+(h:ℂ)*t))))) t := by
    have bnd : x+h*t∈Icc l r := by
      have low := mul_le_mul_of_nonneg_left tI.1 hp
      have high := mul_le_mul_of_nonneg_left tI.2 hp
      dsimp [x,h] at *
      constructor <;> linarith
    have linear : HasDerivAt (fun v : ℝ => x+h*v) h t := by
      simpa only [id_eq,mul_one] using (((hasDerivAt_id t).const_mul h).const_add x)
    have g := (quarter_spatial_line_hasDerivAt first false e (x+h*t) d (off _ bnd)).comp t linear
    have val : quarterSpatialRate first false (centralBandEdgePoint false e (x+h*t))=
        spatialMeanObservable first false (f (c+(h:ℂ)*t))+spatialMeanObservable first true (f (-(c+(h:ℂ)*t))) := by
      rw [z]; cases first <;> simp [quarterSpatialRate,coordinateData,spatialMeanObservable,f,p,mul_re] <;> ring
    change HasDerivAt u (quarterSpatialRate first false (centralBandEdgePoint false e (x+h*t))*h) t at g
    rw [← val,mul_comm h]
    exact g
  have endR : centralBandEdgePoint false e (x+h*1)=⟨r,e⟩ := by
    apply Complex.ext <;> simp [centralBandEdgePoint,x,h]
    ring
  have endL : centralBandEdgePoint false e (x+h*(-1))=⟨l,e⟩ := by
    apply Complex.ext <;> simp [centralBandEdgePoint,x,h]
    ring
  have eq := spatial_paired_horizontal_means (spatialMeanObservable first false) (spatialMeanObservable first true)
    c h plus minus rate
  change X (centralBandEdgePoint false e (x+h*1)) j-X (centralBandEdgePoint false e (x+h*(-1))) j=_ at eq
  rw [endR,endL,show 2*h=r-l by dsimp [h]; ring] at eq
  exact eq

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_horizontal_displacement_by_means
