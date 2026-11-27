import TwoAxisHelicoid.RootCertifiedZero
import TwoAxisHelicoid.ThetaSigmaKernel

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaJet thetaG thetaHorizontalPeriod

noncomputable def ellipticVerticalPeriod (t a : ℝ) : ℂ := by
  classical
  exact if ht : 0 < t then
    (rhombicPeriodPair t ht).weierstrassP a+thetaEtaExpression t-(Real.pi/t:ℝ) else 0

noncomputable def sigmaHorizontalPeriod (t a : ℝ) : ℝ :=
  (1/2:ℝ)*(∫ x : ℝ in (-1)..1, thetaSigmaKernel t a ((x:ℂ)+I*((t/2:ℝ):ℂ))).re

theorem root_elliptic_periods_agree {t a : ℝ}
    (htl : (rootTLower:ℝ) ≤ t) (htu : t ≤ (rootTUpper:ℝ))
    (hal : (rootALower:ℝ) ≤ a) (hau : a ≤ (rootAUpper:ℝ)) :
    ellipticVerticalPeriod t a = thetaG t a ∧ sigmaHorizontalPeriod t a = thetaHorizontalPeriod t a := by
  have ht0 := root_t_positive htl
  have ht86 : (43/50:ℝ) ≤ t :=
    (show (43/50:ℝ) ≤ (rootTLower:ℝ) by norm_num [rootTLower]).trans htl
  have ha : (a:ℂ) ∉ (rhombicPeriodPair t ht0).lattice :=
    mt (thetaJet_zero_iff_rhombic_lattice ht86 (a:ℂ)).mpr (root_vertical_denominator htl htu hal hau)
  constructor
  · simp only [ellipticVerticalPeriod,dite_eq_left ht0]
    exact (thetaG_eq_weierstrassP ht86 ht0 a ha).symm
  · have he (x : ℝ) : thetaSigmaKernel t a ((x:ℂ)+I*((t/2:ℝ):ℂ)) =
        thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ)) := by
      apply thetaSigmaKernel_eq_thetaA ht86 ht0 _ ha
      exact mt (thetaJet_zero_iff_rhombic_lattice ht86 _).mpr (root_horizontal_regular htl htu x)
    unfold sigmaHorizontalPeriod thetaHorizontalPeriod
    simp_rw [he]

noncomputable def ellipticPeriodAlong (t : ℝ) : ℝ := sigmaHorizontalPeriod t (rootVerticalAReal t)

theorem root_elliptic_along_eq {t : ℝ} (ht : t ∈ Icc (rootTLower:ℝ) rootTUpper) :
    ellipticPeriodAlong t = rootPeriodAlong t := by
  have ha := (rootVerticalAReal_spec ht).1
  exact (root_elliptic_periods_agree ht.1 ht.2 ha.1.le ha.2.le).2

theorem ellipticPeriodAlong_deriv_neg {t : ℝ} (ht : t ∈ Ioo (rootTLower:ℝ) rootTUpper) :
    deriv ellipticPeriodAlong t < 0 := by
  have he : ellipticPeriodAlong =ᶠ[𝓝 t] rootPeriodAlong := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact root_elliptic_along_eq hs
  rw [he.deriv_eq]
  exact rootPeriodAlong_deriv_neg ht

/-- Local existence, uniqueness and simplicity after replacing the vertical
expression by the actual Weierstrass function and the horizontal kernel by its
normalized sigma/zeta formula. No geometric classification is claimed here. -/
theorem existsUnique_root_elliptic_period_zero :
    ∃! p : ℝ × ℝ, p.1 ∈ Ioo (rootTLower:ℝ) rootTUpper ∧
      p.2 ∈ Ioo (rootALower:ℝ) rootAUpper ∧ ellipticVerticalPeriod p.1 p.2 = 0 ∧
      sigmaHorizontalPeriod p.1 p.2 = 0 ∧ ellipticPeriodAlong p.1 = 0 ∧
      deriv ellipticPeriodAlong p.1 < 0 := by
  obtain ⟨p,hp,_⟩ := existsUnique_root_certified_zero
  have he := root_elliptic_periods_agree hp.1.1.le hp.1.2.le hp.2.1.1.le hp.2.1.2.le
  have hv : ellipticVerticalPeriod p.1 p.2 = 0 := he.1.trans hp.2.2.1
  have hh : sigmaHorizontalPeriod p.1 p.2 = 0 := he.2.trans hp.2.2.2.1
  have hb : ellipticPeriodAlong p.1 = 0 :=
    (root_elliptic_along_eq ⟨hp.1.1.le,hp.1.2.le⟩).trans hp.2.2.2.2.1
  refine ⟨p,⟨hp.1,hp.2.1,hv,hh,hb,ellipticPeriodAlong_deriv_neg hp.1⟩,?_⟩
  intro q hq
  have hqe := root_elliptic_periods_agree hq.1.1.le hq.1.2.le hq.2.1.1.le hq.2.1.2.le
  have hunique := root_common_period_unique hq.1 hq.2.1 hp.1 hp.2.1
    (hqe.1.symm.trans hq.2.2.1) (hqe.2.symm.trans hq.2.2.2.1) hp.2.2.1 hp.2.2.2.1
  exact Prod.ext hunique.1 hunique.2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.existsUnique_root_elliptic_period_zero
