import TwoAxisHelicoid.SlopingGeneratorArc
import Mathlib.Topology.Instances.AddCircle.Defs

namespace TwoAxisHelicoid
open Complex Set Topology

/-- Half-turn symmetry on the full parameter interval in horizontal projection. -/
theorem sloping_generator_reflected_horizontal {t a : ℝ} (hp : 0<t) {X : ℂ → Fin 3 → ℝ}
    (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 hp)
    (per : ∀ z p, p∈(rhombicPeriodPair t hp).lattice → X (z+p)=X z)
    {s : ℝ} (hs : s∈Icc (-1:ℝ) 1) :
    let F := fun u => X (originalPeriodPath t u)
    (F (-s) 0,F (-s) 1)=(2*X 1 0-F s 0,F s 1) := by
  intro F
  let L := rhombicPeriodPair t hp
  have off := rhombic_open_rectangle_not_mem hp (originalPeriodPath_mem_rectangle hp hs)
  have h := (explicit_centered_primitive_reflections hp d per _ off).1
  let z := originalPeriodPath t s
  have shift := per (-z) (-2) (L.lattice.neg_mem L.ω₁_mem_lattice)
  have e : -z+(-2)=originalPeriodPath t (-s) := by dsimp [z,originalPeriodPath]; push_cast; ring
  rw [e] at shift
  change X (-z)-X 1= ![-(X z-X 1) 0,(X z-X 1) 1,-(X z-X 1) 2] at h
  apply Prod.ext
  · have hx := congrFun h 0
    change X (-z) 0-X 1 0= -(X z 0-X 1 0) at hx
    change X (originalPeriodPath t (-s)) 0=2*X 1 0-X z 0
    rw [shift]
    linarith
  · have hy := congrFun h 1
    change X (-z) 1-X 1 1=X z 1-X 1 1 at hy
    change X (originalPeriodPath t (-s)) 1=X z 1
    rw [shift]
    linarith

/-- The original complete sloping cycle is a Jordan curve already in
horizontal projection. Its only repeated parameter on the closed
fundamental interval is its identified pair of endpoints. -/
theorem sloping_generator_horizontal_jordan {t a : ℝ} (ht : t∈Icc (rootTLower:ℝ) rootTUpper)
    (ha : a∈Icc (rootALower:ℝ) rootAUpper) (hp : 0<t) {X : ℂ → Fin 3 → ℝ}
    (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 hp)
    (per : ∀ z p, p∈(rhombicPeriodPair t hp).lattice → X (z+p)=X z) :
    let F := fun s => X (originalPeriodPath t s)
    let H := fun s => (F s 0,F s 1)
    (∀ u∈Icc (-1:ℝ) 1, ∀ v∈Icc (-1:ℝ) 1, H u=H v ↔ u=v ∨ (u= -1 ∧ v=1) ∨ (u=1 ∧ v= -1)) ∧
      ∃ G : AddCircle (2:ℝ) → ℝ × ℝ, IsClosedEmbedding G ∧ ∀ s∈Icc (-1:ℝ) 1, G (s:AddCircle (2:ℝ))=H s := by
  intro F H
  let c := X 1 0
  let T := fun u : ℝ × ℝ => (2*c-u.1,u.2)
  obtain ⟨inj,zero,one,side⟩ := sloping_half_generator_simple ht ha hp d per
  have reflect {s : ℝ} (hs : s∈Icc (-1:ℝ) 1) : H (-s)=T (H s) :=
    sloping_generator_reflected_horizontal hp d per hs
  have edge {s : ℝ} (hs : s∈Icc (0:ℝ) 1) : (H s).1≤c ∧ ((H s).1=c → s=0 ∨ s=1) := by
    rcases hs.1.eq_or_lt with z|p
    · subst s
      exact ⟨zero.le,fun _ => Or.inl rfl⟩
    rcases hs.2.eq_or_lt with z|q
    · subst s
      exact ⟨one.le,fun _ => Or.inr rfl⟩
    have e := side s ⟨p,q⟩
    exact ⟨e.le,fun h => (e.ne h).elim⟩
  have mixed {s v : ℝ} (hs : s∈Icc (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1) (eq : H (-s)=H v) :
      s=v ∧ (s=0 ∨ s=1) := by
    rw [reflect (s:=s) ⟨by linarith [hs.1],hs.2⟩] at eq
    have real := congrArg Prod.fst eq
    change 2*c-(H s).1=(H v).1 at real
    have sr := (edge hs).1
    have vr := (edge hv).1
    have imag := congrArg Prod.snd eq
    change (H s).2=(H v).2 at imag
    have same : H s=H v := Prod.ext (by linarith) imag
    exact ⟨inj hs hv same,(edge hs).2 (by linarith)⟩
  have ends : H (-1)=H 1 := by
    rw [reflect (s:=1) (by norm_num [mem_Icc])]
    apply Prod.ext
    · change 2*c-F 1 0=F 1 0
      change F 1 0=c at one
      linarith
    · rfl
  have test (u : ℝ) (hu : u∈Icc (-1:ℝ) 1) (v : ℝ) (hv : v∈Icc (-1:ℝ) 1) :
      H u=H v ↔ u=v ∨ (u= -1 ∧ v=1) ∨ (u=1 ∧ v= -1) := by
    constructor
    · intro e
      rcases le_total 0 u with up|un <;> rcases le_total 0 v with vp|vn
      · exact Or.inl (inj ⟨up,hu.2⟩ ⟨vp,hv.2⟩ e)
      · have eq := mixed (s:= -v) ⟨neg_nonneg.mpr vn,by linarith [hv.1]⟩ ⟨up,hu.2⟩ (by simpa only [neg_neg] using e.symm)
        rcases eq.2 with h|h
        · exact Or.inl (by linarith [eq.1])
        · exact Or.inr (Or.inr ⟨by linarith [eq.1],by linarith⟩)
      · have eq := mixed (s:= -u) ⟨neg_nonneg.mpr un,by linarith [hu.1]⟩ ⟨vp,hv.2⟩ (by simpa only [neg_neg] using e)
        rcases eq.2 with h|h
        · exact Or.inl (by linarith [eq.1])
        · exact Or.inr (Or.inl ⟨by linarith,by linarith [eq.1]⟩)
      · have pair : H (-u)=H (-v) := by rw [reflect hu,reflect hv,e]
        exact Or.inl (neg_injective (inj ⟨neg_nonneg.mpr un,by linarith [hu.1]⟩ ⟨neg_nonneg.mpr vn,by linarith [hv.1]⟩ pair))
    · rintro (rfl|⟨rfl,rfl⟩|⟨rfl,rfl⟩)
      · rfl
      · exact ends
      · exact ends.symm
  let _ : Fact (0<(2:ℝ)) := ⟨by norm_num⟩
  let G := AddCircle.liftIco (2:ℝ) (-1) H
  have top : (-1:ℝ)+2=1 := by norm_num
  have co : ContinuousOn H (Icc (-1:ℝ) 1) := by
    intro s hs
    have off := rhombic_open_rectangle_not_mem hp (originalPeriodPath_mem_rectangle hp hs)
    have c := (d _ off).continuousAt.comp (originalPeriodPath_hasDerivAt t s).continuousAt
    exact (((continuous_apply 0).continuousAt.comp c).prodMk ((continuous_apply 1).continuousAt.comp c)).continuousWithinAt
  have cg : Continuous G := AddCircle.liftIco_continuous (p:=(2:ℝ)) (a:=(-1:ℝ)) (f:=H) (by simpa only [top] using ends) (by simpa only [top] using co)
  let param := AddCircle.equivIco (2:ℝ) (-1)
  have mono : Function.Injective G := by
    intro x y e
    let u := (param x).1
    let v := (param y).1
    have hu : u∈Ico (-1:ℝ) 1 := by simpa only [top,u] using (param x).2
    have hv : v∈Ico (-1:ℝ) 1 := by simpa only [top,v] using (param y).2
    have eq : H u=H v := e
    rcases (test u (Ico_subset_Icc_self hu) v (Ico_subset_Icc_self hv)).mp eq with a|a|a
    · exact param.injective (Subtype.ext a)
    · exact (hv.2.ne a.2).elim
    · exact (hu.2.ne a.1).elim
  refine ⟨test,G,cg.isClosedEmbedding mono,?_⟩
  intro s hs
  rcases hs.2.eq_or_lt with last|h
  · subst s
    have eq : ((-1:ℝ):AddCircle (2:ℝ))=((1:ℝ):AddCircle (2:ℝ)) := by
      calc
        ((-1:ℝ):AddCircle (2:ℝ))=(((-1:ℝ)+2:ℝ):AddCircle (2:ℝ)) := by rw [AddCircle.coe_add,AddCircle.coe_period,add_zero]
        _=_ := congrArg (fun u : ℝ => (u:AddCircle (2:ℝ))) top
    rw [← eq]
    exact (AddCircle.liftIco_coe_apply (p:=(2:ℝ)) (a:= -1) (f:=H) (by norm_num [mem_Ico])).trans ends
  · exact AddCircle.liftIco_coe_apply (show s∈Ico (-1:ℝ) (-1+2) from ⟨hs.1,by linarith⟩)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.sloping_generator_horizontal_jordan
