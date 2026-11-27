import TwoAxisHelicoid.SlopingScalarEnvelope
import TwoAxisHelicoid.TraceDataSlopingSpatialCover
import TwoAxisHelicoid.CentralHalfPeriodSpatialSeparation

namespace TwoAxisHelicoid
open Complex Set

/-- The entire positive half of the manuscript's sloping cycle maps
injectively into its horizontal projection. Every interior point lies
strictly on one side of the plane through the vertical and transverse
axes. These conclusions use both coordinates on overlapping intervals. -/
theorem sloping_half_generator_simple {t a : ℝ} (ht : t∈Icc (rootTLower:ℝ) rootTUpper)
    (ha : a∈Icc (rootALower:ℝ) rootAUpper) (hp : 0<t) {X : ℂ → Fin 3 → ℝ}
    (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 hp)
    (per : ∀ z p, p∈(rhombicPeriodPair t hp).lattice → X (z+p)=X z) :
    let F := fun s => X (originalPeriodPath t s)
    InjOn (fun s => (F s 0,F s 1)) (Icc (0:ℝ) 1) ∧
      F 0 0=X 1 0 ∧ F 1 0=X 1 0 ∧ ∀ s∈Ioo (0:ℝ) 1, F s 0<X 1 0 := by
  intro F
  let f := fun s => F s 0
  let g := fun s => F s 1
  have df (s : ℝ) (hs : s∈Icc (0:ℝ) 1) : HasDerivAt f (slopingLongitudinalRate t a s) s :=
    sloping_longitudinal_spatial_derivative hp d hs
  have dg (s : ℝ) (hs : s∈Icc (0:ℝ) 1) : HasDerivAt g (slopingTransverseRate t a s) s :=
    sloping_transverse_spatial_derivative hp d hs
  have X02 := TraceData.slopingFirstSpan02.sound ht ha df
  have X23 := TraceData.slopingFirstSpan23.sound ht ha df
  have X34 := TraceData.slopingFirstSpan34.sound ht ha df
  have X46 := TraceData.slopingFirstSpan46.sound ht ha df
  have Y01 := TraceData.slopingSecondSpan01.sound ht ha dg
  have Y12 := TraceData.slopingSecondSpan12.sound ht ha dg
  have Y15 := TraceData.slopingSecondSpan15.sound ht ha dg
  have Y45 := TraceData.slopingSecondSpan45.sound ht ha dg
  have Y26 := TraceData.slopingSecondSpan26.sound ht ha dg
  have Y56 := TraceData.slopingSecondSpan56.sound ht ha dg
  norm_num at X02 X23 X34 X46 Y01 Y12 Y15 Y45 Y26 Y56
  have dec : StrictAntiOn f (Icc 0 (51/128:ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun s hs => (df s ⟨hs.1,by linarith [hs.2]⟩).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Icc] at hs
    have b := (X02.rates s (Ioo_subset_Icc_self hs)).2
    rw [(df s ⟨hs.1.le,by linarith [hs.2]⟩).deriv]
    norm_num at b
    linarith
  have inc : StrictMonoOn f (Icc (183/256:ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun s hs => (df s ⟨by linarith [hs.1],hs.2⟩).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Icc] at hs
    have b := (X46.rates s (Ioo_subset_Icc_self hs)).1
    rw [(df s ⟨by linarith [hs.1],hs.2.le⟩).deriv]
    norm_num at b
    linarith
  have mid : StrictMonoOn g (Icc (3/16:ℝ) (225/256)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun s hs => (dg s ⟨by linarith [hs.1],by linarith [hs.2]⟩).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Icc] at hs
    have b := (Y15.rates s (Ioo_subset_Icc_self hs)).1
    rw [(dg s ⟨by linarith [hs.1],by linarith [hs.2]⟩).deriv]
    norm_num at b
    linarith
  have sep {u v : ℝ} (hu : u∈Icc (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1) (uv : u<v) : f u≠f v ∨ g u≠g v := by
    by_cases early : v≤51/128
    · exact Or.inl (dec ⟨hu.1,uv.le.trans early⟩ ⟨hv.1,early⟩ uv).ne'
    by_cases late : 183/256≤u
    · exact Or.inl (inc ⟨late,hu.2⟩ ⟨late.trans uv.le,hv.2⟩ uv).ne
    by_cases low : u≤3/16
    · have one := (Y01.part u (3/16) hu.1 low le_rfl).1
      have two := Y12.total.1
      have three := (Y26.part (51/128) v le_rfl (le_of_not_ge early) hv.2).1
      norm_num at one two three
      exact Or.inr (by intro e; linarith)
    by_cases top : v≤225/256
    · exact Or.inr (mid ⟨le_of_not_ge low,uv.le.trans top⟩ ⟨(le_of_not_ge low).trans uv.le,top⟩ uv).ne
    have one := mid.monotoneOn (a:=u) (b:=(183/256:ℝ)) ⟨le_of_not_ge low,by linarith⟩
      (by norm_num [mem_Icc]) (le_of_not_ge late)
    have two := Y45.total.1
    have three := (Y56.part (225/256) v le_rfl (le_of_not_ge top) hv.2).1
    norm_num at two three
    exact Or.inr (by intro e; linarith)
  have z : f 0=X 1 0 := by
    have e := per (-1) 2 (rhombicPeriodPair t hp).ω₁_mem_lattice
    rw [show (-1:ℂ)+2=1 by norm_num] at e
    simpa [f,F,originalPeriodPath] using congrFun e.symm 0
  have h : f 1=X 1 0 := by
    let p : ℂ := (1+I*t)/2
    have ea := per (-p) (1+I*t) (rhombicPeriodPair t hp).ω₂_mem_lattice
    rw [show -p+(1+I*t)=p by dsimp [p]; ring] at ea
    have eq := congrFun (central_half_period_spatial_test hp d per).2.2.2.1 0
    change X p 0-X 1 0=0 at eq
    change X (originalPeriodPath t 1) 0=X 1 0
    rw [show originalPeriodPath t 1= -p by dsimp [p,originalPeriodPath]; ring,← ea]
    exact sub_eq_zero.mp eq
  refine ⟨?_,z,h,?_⟩
  · intro u hu v hv e
    rcases lt_trichotomy u v with lt|eq|gt
    · exact ((sep hu hv lt).elim (fun n => n (congrArg Prod.fst e)) (fun n => n (congrArg Prod.snd e))).elim
    · exact eq
    · exact ((sep hv hu gt).elim (fun n => n (congrArg Prod.fst e.symm)) (fun n => n (congrArg Prod.snd e.symm))).elim
  · intro s hs
    change f s<X 1 0
    by_cases low : s≤51/128
    · exact (dec (by norm_num [mem_Icc]) ⟨hs.1.le,low⟩ hs.1).trans_eq z
    by_cases high : 183/256≤s
    · exact (inc ⟨high,hs.2.le⟩ (by norm_num [mem_Icc]) hs.2).trans_eq h
    rcases le_total s (17/32) with left|right
    · have v := (X23.part (51/128) s le_rfl (le_of_not_ge low) left).2
      have u := X02.total.2
      norm_num at u v
      linarith
    · have v := (X34.part s (183/256) right (le_of_not_ge high) le_rfl).1
      have u := X46.total.1
      norm_num at u v
      linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.sloping_half_generator_simple
