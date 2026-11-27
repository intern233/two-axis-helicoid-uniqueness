---
title: "Uniqueness of the two-axis genus-one helicoid"
abstract: |
  We prove uniqueness, up to Euclidean isometry and positive scaling, of properly embedded genus-one minimal surfaces with one helicoidal end and two straight axes. The end condition is a single normal graph outside compact sets, with the graph function and its gradient tending to zero in the induced helicoid metric. Starting from an arbitrary surface in this class, we obtain a rhombic Weierstrass family indexed by an integer. An axial winding calculation and the even spin structure of an embedded cap select its basic branch. The vertical period equation then determines one analytic parameter, and the remaining periods reduce to one real analytic function. Analytic estimates at the degenerating end and exact interval certificates on the remaining parameter ranges establish a unique simple zero. We describe the correspondence between this geometric statement and a completed Lean development, including existence of an embedded representative, the interpretation of the Gauss map at its pole, and the scope of the supplementary statements that retain published geometric inputs.
---

# Introduction and the main statement

A genus-one helicoid combines the topology of a punctured torus with the geometry of a helicoidal end. The embedded example constructed by Weber, Hoffman and Wolf [WHW09] has a vertical straight axis and a horizontal straight line. Their existence theorem raises the corresponding uniqueness question. The present paper treats this class with both straight axes retained as hypotheses.

Two nearby results require a distinction of scope. Alarcón, Ferrer and Martín [AFM07] prove uniqueness for a singly periodic genus-one helicoid under a symmetry hypothesis. The genus in that result belongs to a periodic quotient. Bernstein and Breiner [BB11b] prove a half-turn symmetry about a normal line for an arbitrary embedded genus-one helicoid. Such a normal symmetry does not supply the two straight lines contained in the surface that are assumed here. The broader uniqueness problem for finite-genus, one-ended embedded minimal surfaces is discussed in Pérez's 2026 survey [P26, §7]. We make no classification assertion after removing the two-axis hypothesis.

We first specify the end condition. Write
$$
H_p(r,\theta)=(r\cos\theta,r\sin\theta,p\theta),
\qquad (r,\theta)\in\mathbb R^2,\quad p\ne0.
\tag{1}
$$
Its induced metric is $dr^2+(r^2+p^2)d\theta^2$. A surface has a **single $C^1$ helicoidal graph end** if, after an ambient isometry, there are compact sets $K$ in the surface and $K_H$ in $H_p$ such that the entire complement of $K$ is parametrized by
$$
q\longmapsto q+u(q)N_{H_p}(q),\qquad q\in H_p\setminus K_H,
\quad u\in C^1,
\quad |u|+|D_{H_p}u|\longrightarrow0.
\tag{2}
$$
The parametrization is a homeomorphism onto that complement. Both complements in this definition are literal complements of compact sets. The derivative is measured in the induced metric, so in the coordinates (1)
$$
|D_{H_p}u|^2=u_r^2+\frac{u_\theta^2}{r^2+p^2}.
\tag{3}
$$

Let $\mathcal C$ be the class of smooth, connected, boundaryless, complete, properly embedded minimal surfaces in $\mathbb R^3$ that are homeomorphic to a torus minus one point, satisfy (2), and contain both the axis of their asymptotic helicoid and an entire straight line whose direction is orthogonal to that axis. We initially allow this latter line to be displaced from the axis. Their intersection and its placement in the conformal marking will be derived.

Two members of $\mathcal C$ are equivalent when a map $x\mapsto\lambda U(x)$ carries one entire image onto the other, where $\lambda>0$ and $U$ is a Euclidean isometry. Isometries of either orientation are allowed.

**Theorem 1 (main theorem).** The class $\mathcal C$ has exactly one equivalence class. Its conformal compactification admits the marking
$$
T_t=\mathbb C/\Lambda_t,\qquad
\Lambda_t=\langle2,1+it\rangle,\qquad E=0,\qquad O=1,
\tag{4}
$$
where $E$ is the puncture and $O$ is the intersection of the two straight axes. The unique parameters satisfy
$$
\begin{aligned}
0.866227694384&<t_0<0.866227694385,\\
0.5936860965140&<a_0<0.5936860965150.
\end{aligned}
\tag{5}
$$
In this marking the spherical Gauss map has exactly one finite simple zero and one finite simple pole, at $a_0$ and $-a_0$, respectively. All displayed finite decimal endpoints in this paper denote exact rational numbers.

The proof separates three issues. First, every geometric candidate must belong to the same explicit family. This requires selecting an integer branch by geometry and spin, before any numerical period calculation. Second, the entire admissible parameter domain must be covered, including its degenerating end. Third, a period solution must be related to an embedded surface. We address these issues separately and then combine them.

The Lean theorem proved without additional geometric hypotheses has precisely the class (2) as its domain. A more general formulation that begins only with finite topology, or with one-sided positional proximity to a helicoid, requires additional end-structure results. The development also contains such implications with their published inputs displayed as hypotheses. They are described in §9 and are not silently incorporated into Theorem 1.

# Geometric reduction to an integer family

## Conventions and the conformal marking

We use the Weierstrass convention
$$
\Phi=\left(\frac{g^{-1}-g}{2},\frac{i(g^{-1}+g)}2,1\right)dh,
\qquad X=\operatorname{Re}\int\Phi,
\qquad \Omega=\frac{dg}{g}.
\tag{6}
$$
The flux of an oriented closed curve is $\operatorname{Im}\int\Phi$. In particular, vanishing real periods gives a single-valued position map and does not assert that its flux vanishes.

For the lattice (4), let $\wp_t,\zeta_t,\sigma_t$ have their standard normalizations
$$
\zeta_t'=-\wp_t,\qquad \frac{\sigma_t'}{\sigma_t}=\zeta_t,
\qquad \zeta_t(z)=z^{-1}+O(z^3),\qquad \sigma_t'(0)=1.
$$
Set $\tau=1+it$ and
$$
\eta(t)=\zeta_t(1),\qquad e(t)=\wp_t(1).
$$
These are half-period values. If $\widehat\eta_\omega$ denotes the increment of $\zeta_t$ under a full period $\omega$, the conventions are
$$
\widehat\eta_2=2\eta,\qquad
\widehat\eta_\tau=\eta\tau-\pi i,\qquad
\widehat\eta_{2it}=2i(t\eta-\pi).
\tag{7}
$$
In particular, no full-period increment is being denoted by $\eta$. The lattice is invariant under conjugation, and $\eta,e$ are real. Standard function identities used below can be found in [DLMF, §§20, 23].

The conformal compactification and the double poles of $dh$ and $dg/g$ follow from the finite-topology end theorem [BB11a]. In the graph class (2), the Lean development obtains the required end structure from the actual graph and minimal immersion and then constructs the compactification. The geometric conclusion used at this stage is the same in either route.

Schwarz reflection about each contained straight line acts on the surface. First, these lines must meet. A nonzero translation preserving the surface would produce arbitrarily many disjoint translates of a compact genus-one subsurface, contradicting the total genus. A screw symmetry with nonzero translation component is excluded in the same way. If the two orthogonally directed lines were disjoint, the square of the product of their half-turns would be a nonzero translation. This gives the required intersection.

After compactification the two reflections are antiholomorphic involutions. Their fixed sets, together with the embedded complete axes, determine a conjugation-invariant lattice of rhombic type. Translation and scaling of the conformal coordinate give (4), with the two reflections
$$
\mu_h(z)=\overline z,\qquad \mu_v(z)=-\overline z,
\quad\text{and their product}\quad \rho(z)=-z.
\tag{8}
$$
The fixed set associated with a complete straight axis is connected after adding the end. A rectangular real torus would have the wrong fixed-set topology. This eliminates the rectangular alternative. The two complete lines meet, and their finite crossing is the half-period $O=1$. These are conclusions about the given position map, rather than choices imposed on an already specified Weierstrass model.

## Height differential and the Gauss divisor

A meromorphic differential on a marked torus with one residue-free double pole is a constant multiple of $(\wp_t-u)dz$. The reflection identities in (8) therefore give
$$
dh=ic\bigl(\wp_t(z)-u\bigr)dz,\qquad c\in\mathbb R\setminus\{0\}.
\tag{9}
$$
Using (7), the vanishing real periods of (9) determine
$$
u=u(t)=\frac\pi t-\eta(t).
\tag{10}
$$
The height periods along $2$, $\tau$ and $2it=2\tau-2$ are then
$$
-\frac{2\pi ic}{t},\qquad -\frac{\pi ic}{t},\qquad 0,
\tag{11}
$$
respectively.

Along the real interval $(0,1)$, $\wp_t$ decreases strictly from $+\infty$ to $e(t)$. When (9) is realized by a regular two-axis immersion, its two zeros are distinct and lie at $a,-a$, where
$$
0<a<1,\qquad G(t,a):=\wp_t(a)+\eta(t)-\frac\pi t=0.
\tag{12}
$$
Regularity and nullity of $\Phi$ force the Gauss map to have a simple zero at one of these points and a simple pole at the other. A choice of orientation fixes the zero at $a$. There are no additional zeros or poles away from $E$. The Gauss map has an essential singularity at the helicoidal puncture, and it is not asserted to be meromorphic on the compact torus.

Define
$$
D_a(z)=\zeta_t(z-a)-\zeta_t(z+a).
$$
Comparison of the poles of $\Omega$ gives
$$
\Omega=(\kappa\wp_t+\beta+D_a)dz.
$$
Single-valuedness of $g$, the conjugation identities, and (7) yield
$$
\kappa=2(m-a),\qquad \beta=2m\eta,\qquad m\in\mathbb Z.
$$
Integration gives, after a possible half-turn around the vertical axis,
$$
g_m(z)=i\exp\{2(a-m)\zeta_t(z)+2m\eta z\}
\frac{\sigma_t(z-a)}{\sigma_t(z+a)}.
\tag{13}
$$
Thus every candidate has the data (9), (12), (13) for an integer $m$. It is essential to retain this integer until the next section.

# Selection of the basic branch

## Axial winding

The end principal parts determine
$$
\alpha=\frac{2(a-m)}c,\qquad
\Omega_0=\Omega-i\alpha\,dh
=\bigl(D_a+2m\eta+2(m-a)u\bigr)dz.
\tag{14}
$$
The form $\Omega_0$ is holomorphic at the puncture. Parametrize the compactified vertical axis by $z=iy$, $0\le y\le2t$. Its midpoint is $it\equiv1\pmod{\Lambda_t}$.

**Lemma 2 (axial integral).** The continuous axial phase change is
$$
\int_0^{2it}\Omega_0=2\pi i(2m-1).
\tag{15}
$$

*Proof.* Put $J(a)=\int_0^{2it}D_a(z)dz$. Differentiation under the integral gives $J'(a)=-2\widehat\eta_{2it}$. When $a\downarrow0$, each endpoint contributes $-\pi i$. At the lower endpoint the singular contribution is
$$
D_a(iy)i\,dy=-\frac{2ia}{a^2+y^2}\,dy+O(a)\,dy.
$$
The upper endpoint is identical by periodicity, and the integral away from the endpoints tends to zero. Consequently
$$
J(a)=-2a\widehat\eta_{2it}-2\pi i.
$$
Substitution into (14), using (7) and (10), proves (15). The endpoint constant is part of the ordinary integral of the regularized form. It cannot be discarded by taking an argument only modulo $2\pi$. $\square$

For an embedded two-axis candidate, the intersection theorem of Hoffman and White [HW09, Theorem 2.5] identifies its intersection with the asymptotic helicoid as exactly the two axes. Away from their crossing, a common tangent plane along the vertical axis would give an additional local intersection arc. Indeed, the first nonzero homogeneous term in the difference of two local analytic minimal graphs has the nodal structure of a harmonic polynomial of degree at least two. Infinite-order contact would imply equality of the surfaces and contradict the genus.

Choose a continuous lift of the Gauss argument on the vertical line and subtract the phase $\alpha x_3$ of the helicoid. Normalize the resulting relative angle $\delta$ to vanish at the axis crossing. On each open half-axis, $\delta$ stays within either $(0,\pi)$ or $(-\pi,0)$, since a multiple of $\pi$ would give a common tangent plane. Its endpoint limits exist by the regularity of $\Omega_0$. Their difference therefore has absolute value at most $2\pi$. Equation (15) implies
$$
|2m-1|\le1,\qquad m\in\{0,1\}.
\tag{16}
$$

## An embedded cap and its spin structure

We record why the spin argument concerns the original embedded surface and its actual compactification. After normalizing the pitch, the helicoid has a uniform tubular neighborhood. For example, with $q=(1+r^2)^{1/2}$ and a suitable choice of unit normal, its normal-coordinate map is
$$
\mathcal F(r,\theta,s)=
\left((r-is/q)e^{i\theta},\ \theta+sr/q\right),\qquad |s|<1.
\tag{17}
$$
For fixed spatial height, injectivity reduces to the map
$$
W(r,s)=(r-is/q)e^{-isr/q}.
$$
Its real derivative in $r$ is positive and its Jacobian determinant is $-q(1-s^2/q^4)<0$. A real level of $W$ therefore determines $r$ uniquely as a function of $s$, and the imaginary coordinate is strictly decreasing on that level. This proves global injectivity of (17).

Use (2) far enough out that $|u|$ is arbitrarily small. A cutoff extension $\widetilde u$ vanishes near any prescribed compact core and equals $u$ farther out. With a smooth function $\chi$ supported in the normal interval and equal to one near zero, the maps
$$
(q,s)\longmapsto(q,s+\lambda\chi(s)\widetilde u(q)),
\qquad 0\le\lambda\le1,
\tag{18}
$$
give an ambient isotopy when $\|\widetilde u\|_\infty\|\chi'\|_\infty<1$. It fixes the prescribed core. The inverse isotopy straightens the end to the helicoid. The graph is smooth on a sufficiently distant subend by the regularity of the original surface and the normal projection.

A large sphere meets the straightened end in one smooth simple closed curve. Attach one of its spherical disks, pushed slightly outward and smoothed along the common boundary. This gives a smooth embedded closed torus agreeing with the original surface on the chosen core. The attached disk need only avoid the retained core. The discarded infinite end is no longer part of the capped surface.

The spin structure induced by an embedded closed oriented surface in $\mathbb R^3$ has Arf invariant zero. One description uses the ambient spin structure restricted to the compact region bounded by the surface. The induced boundary spin structure is bounding, hence has zero Arf invariant. Equivalently, the ambient quadratic form has a zero Lagrangian given by cycles bounding in that region. The isotopy preserves the spin structure on the retained core. Since deleting a disk from a torus leaves its first cohomology with $\mathbb Z/2$ coefficients unchanged, the spin structure of the punctured surface has a unique extension to the compactification. That extension is even.

## Multipliers of the Weierstrass spinors

The sigma addition formula gives
$$
\wp_t(z)-\wp_t(a)
=-\frac{\sigma_t(z-a)\sigma_t(z+a)}{\sigma_t(z)^2\sigma_t(a)^2}.
\tag{19}
$$
A scalar factor of the spinor whose square is $g_mdh/2$ is therefore
$$
\psi_m(z)=
e^{(a-m)\zeta_t(z)+m\eta z}\frac{\sigma_t(z-a)}{\sigma_t(z)}.
\tag{20}
$$
Its multipliers along $2$ and $\tau$ are
$$
(1,(-1)^m).
\tag{21}
$$
These constant signs define a square root of the canonical bundle on the entire compact torus. If $s_1$ is the corresponding multiple of $\psi_m\sqrt{dz}$ and $s_2=dh/(2s_1)$, then $s_1^2=g_mdh/2$, $s_2^2=dh/(2g_m)$ and $2s_1s_2=dh$. The apparent division at $a$ is removable. The pair has no common zero at a finite point. It therefore induces the same spin structure as the original regular immersion, as in the spinor representation [B98, KS96].

At the puncture, $\psi_m(w)=w^{-1}e^{(a-m)/w}h(w)$ with $h$ holomorphic and nonzero. This is an essential singularity of a section of the already specified bundle. It adds no new sign monodromy to that bundle. Its extension is consequently the same one identified by the embedded cap.

On a torus the trivial square root has a one-dimensional space of holomorphic sections and is the odd spin structure. The other three square roots are even. Thus (21) is odd precisely when $m$ is even. The cap forces $m$ to be odd. Combined with (16), this proves
$$
m=1.
\tag{22}
$$
All original candidates have now been reduced to the same branch, independently of the horizontal period computation.

# The full domain of the vertical equation

Let $F(t)=\eta(t)+e(t)$. Equation (12) has a solution $a\in(0,1)$ exactly when $u(t)>e(t)$. To determine that condition globally, introduce the rectangular lattice $\mathcal R_t=\langle2,2it\rangle$ and its values $\eta_R=\zeta_{\mathcal R_t}(1)$ and $E_R=\wp_{\mathcal R_t}(1+it)$. Comparison of poles and Laurent constants gives
$$
e=-2E_R,\qquad \eta=2\eta_R+E_R,\qquad F=2\eta_R-E_R.
$$
With $q=e^{-\pi t}$, the rectangular Fourier expansion then gives
$$
F(t)=\frac{\pi^2}{4}-2\pi^2\sum_{n\ge1}b_nq^n,
\qquad
b_{2^kr}=\begin{cases}
\displaystyle\sum_{d\mid r}d,&k=0,\\
\displaystyle(2^{k+1}-3)\sum_{d\mid r}d,&k\ge1,
\end{cases}
\quad r\text{ odd}.
\tag{23}
$$
In particular $1\le b_n\le\sum_{d\mid n}d\le n^2$. The series and its derivatives converge uniformly on compact subsets of $t>0$, so
$$
F'(t)=2\pi^3\sum_{n\ge1}nb_ne^{-\pi nt}>0.
$$
Moreover $F(t)\to-\infty$ as $t\downarrow0$ and $F(t)\to\pi^2/4$ as $t\to\infty$. Let $t_*$ be its unique zero.

The scaling $\mathcal R_t=it\mathcal R_{1/t}$ and the Legendre relation yield
$$
F(t)=\frac\pi t-\frac{F(1/t)}{t^2},\qquad
u(t)-e(t)=\frac{F(1/t)}{t^2}.
\tag{24}
$$
Consequently the complete vertical domain is
$$
0<t<T_*:=t_*^{-1}.
\tag{25}
$$
There is exactly one root $a=a(t)\in(0,1)$ there. It is real analytic because $G_a=\wp_t'(a)<0$, and $a(t)\to1$ as $t\uparrow T_*$.

For a rational enclosure of the endpoint, use
$$
\sum_{n>N}b_nq^n\le q^{N+1}
\left(\frac{(N+1)^2}{1-q}
+\frac{2(N+1)q}{(1-q)^2}
+\frac{q(1+q)}{(1-q)^3}\right).
\tag{26}
$$
This is the exact tail of $\sum n^2q^n$. Machin's formula for $\pi$, alternating arctangent sums, and signed Taylor bounds for the exponential reduce (23) to rational inequalities. With $N=40$, the certificates give
$$
-\frac{48}{10^{10}}<\frac{F(0.70945978)}{\pi^2}<-\frac{47}{10^{10}},
\qquad
\frac{139}{10^{10}}<\frac{F(0.70945980)}{\pi^2}<\frac{140}{10^{10}}.
\tag{27}
$$
Thus $0.70945978<t_*<0.70945980$, and in particular $7/5<T_*<141/100$.

# Reduction of all remaining periods

On the branch $m=1$, define for independent parameters $t>0$ and $0<a\le1$
$$
A_{t,a}(z)=e^{2(a-1)\zeta_t(z)+2\eta(t)z}
\frac{\sigma_t(z-a)^2}{\sigma_t(z)^2\sigma_t(a)^2},
\qquad \alpha_{t,a}=A_{t,a}(z)dz.
\tag{28}
$$
On the vertical root, (19) implies $g\,dh=c\alpha_{t,a}$. The function $A_{t,a}$ is doubly periodic and holomorphic off the lattice. For $a<1$ it has essential singularities at the lattice points. Its residue there is zero, since opposite sides of a fundamental parallelogram cancel and the integral about its only puncture must vanish. This use of Cauchy's theorem is valid for an isolated essential singularity. At $a=1$, the special identity is $A_{t,1}=\wp_t-e(t)$.

For
$$
\gamma_t(s)=-1+\frac{s}{2}(1-it),\qquad -1\le s\le1,
$$
set
$$
P(t,a)=\int_{\gamma_t}\alpha_{t,a},\qquad
\mathcal H(t)=\operatorname{Re}P(t,a(t)).
\tag{29}
$$
The path avoids the lattice, and $\mathcal H$ is real analytic on (25).

**Lemma 3 (all-period reduction).** On the vertical root, the entire vector of real periods of (6) vanishes if and only if $\mathcal H(t)=0$.

*Proof.* Write $\omega_+=gdh$ and $\omega_-=g^{-1}dh$. Under $\rho(z)=-z$, one has $\rho^*\omega_+=\omega_-$. The action on first homology is multiplication by $-1$, so on every closed curve
$$
\int\omega_-=-\int\omega_+.
$$
The horizontal period condition $\int\omega_+=\overline{\int\omega_-}$ is therefore equivalent to $\operatorname{Re}\int\omega_+=0$. Both forms extend regularly across $a$ and $-a$, and the puncture has zero period.

Conjugation exchanges the periods $1-it$ and $1+it$, and their integrals are conjugates. These two periods generate $\Lambda_t$, since $1+it=\tau$ and $(1-it)+(1+it)=2$. Thus a single real condition suffices. Together with (11), it is precisely (29). $\square$

For computation the same period has the fixed-horizontal-path representations
$$
\begin{aligned}
H(t,a)&:=\operatorname{Re}P(t,a)
=\frac12\operatorname{Re}\int_{-1}^{1}A_{t,a}(x+it/2)\,dx\\
&=\operatorname{Re}\int_{-1/2}^{1/2}A_{t,a}(x+it/2)\,dx.
\end{aligned}
\tag{30}
$$
The second equality follows from conjugation symmetry of the integrand after translation by $1$. It does not assert that $1$ is a complex period of $A$.

If the periods close, integration of (6) gives a conformal harmonic immersion of the actual punctured torus. At $a$ and $-a$, the zero of $dh$ cancels the zero or pole of $g$, leaving a regular nonzero null differential. Near the puncture,
$$
ds=\frac{|g|+|g|^{-1}}2|dh|\ge |dh|
\ge C\frac{|dz|}{|z|^2},\qquad C>0,
\tag{31}
$$
which proves completeness. The end admits a height coordinate $\xi$ in which $dh=d\xi$ and $g=e^{i\alpha\xi+f(\xi)}$, with $f$ holomorphic at infinity and $f(\infty)=0$. The actual end is proper and embedded outside a compact set, and its normal graph satisfies (2). The two fixed circles in (8) map to complete straight axes. Properness on the remaining part follows from compactness of the parameter core.

These facts give a complete proper immersion at a closed period pair. Embeddedness of the compact core is a separate conclusion, used in §8.

# Analytic control of the degenerating end

The interval $0<t\le1/8$ cannot be covered by finitely many compact parameter rectangles bounded away from zero. We prove a uniform analytic estimate there.

## The vertical root in dual coordinates

Put
$$
s=t^{-1},\quad q=e^{-\pi/(2t)},\quad Q=-q^2,\quad
r=e^{-\pi a/t},\quad \beta=\frac{q^2}{r},\quad
\kappa_0=-\log q,\quad \kappa=-\log\beta.
\tag{32}
$$
The symbols $q$ and $r$ in this section are the dual exponential parameters, rather than the nome in (23) or the radial coordinate in (1). With $f(x)=x/(1-x)^2$, define
$$
E_q(r)=f(r)+\sum_{n\ge1}\bigl(f(Q^nr)+f(Q^n/r)\bigr).
$$
The lattice inversion $\Lambda_t=it\Lambda_{1/t}$ gives the exact identity
$$
G(t,a)=\frac{\pi^2}{t^2}E_q(e^{-\pi a/t}).
\tag{33}
$$
Absolute convergence follows from $q^2<r<1$.

At $r=q$, pairing terms gives
$$
E_q(q)=\sum_{k\ge0}\frac{4q^{4k+2}}{(1-q^{4k+2})^2}>0.
$$
Since $G$ decreases in $a$, this proves $a(t)>1/2$ throughout (25). If $t\le1/4$, then $q<1/100$. At $r=q/2$ the terms $f(q/2)$, $f(-2q)$ and $f(-q^3/2)$ have sum less than $-13q/10$, and the remaining absolute tail is less than $3q^3$. Hence
$$
\frac q2<r<q,\qquad
\frac12<a(t)<\frac12+\frac t\pi\log2.
\tag{34}
$$
Separating the first two terms in the root equation further gives
$$
0=\frac r{(1-r)^2}-\frac\beta{(1+\beta)^2}+T,
\qquad |T|\le4q^3,
\qquad 0\le\beta-r\le12q^2.
$$
Writing $r=qe^{-\varepsilon}$ and $\beta=qe^\varepsilon$ yields $0\le\varepsilon\le6q$. For $0<t\le1/8$, the consequences used below are
$$
\begin{gathered}
q\le\beta\le2q,\quad r\le q\le e^{-\kappa},\quad
\kappa_0-6q\le\kappa\le\kappa_0<\kappa+1,\\
\kappa>25/2,\qquad q<10^{-5},\qquad \kappa q<10^{-4}.
\end{gathered}
\tag{35}
$$

## An exact product comparison

Under $z=itw$, write $\alpha_{t,a}=\mathcal F(w)dw$. Reflection and period addition give
$$
\mathcal H(t)=-\operatorname{Re}
\int_{1/2-is/2}^{1/2+is/2}\mathcal F(w)dw.
\tag{36}
$$
Every path in this identity avoids the lattice. Set
$$
x=e^{i\pi w},\qquad
\mathcal P=\prod_{n\ge1}(1-Q^n),\qquad
D(x)=\prod_{n\ge1}(1-Q^nx)(1-Q^n/x).
$$
The Jacobi product, including its normalization constant, yields
$$
\begin{aligned}
\mathcal F(w)&=\mathcal F_0(w)\mathcal E(x),\\
\mathcal F_0(w)&=\frac{i\pi^2}{t\beta}\frac{x^2}{(1-x)^2}
\exp\left(\frac{2\kappa x}{1-x}\right),\\
\mathcal E(x)&=C_0
\left(\frac{(1-rx)D(rx)}{D(x)}\right)^2
\exp\left(-2\kappa\frac{xD'(x)}{D(x)}\right),\\
C_0&=\frac{\mathcal P^4}{(1-r)^2D(r)^2}.
\end{aligned}
\tag{37}
$$
On the entire integration line, $x=i\rho$ with $q\le\rho\le q^{-1}$. Let $B(\rho)=\beta/\rho+r\rho$. Then
$$
|\mathcal E(i\rho)-1|
\le100\kappa q+4B(\rho)+3B(\rho)^2.
\tag{38}
$$
For completeness, the factors that remain small uniformly on this long line can be estimated as follows. Extract $D(rx)=(1+\beta/x)R(x)$. The sum of the absolute deviations in the remaining product is at most $4q^2$, giving $|R-1|\le5q^2$. Similarly,
$$
|D(x)-1|\le4q,\quad |D(x)^{-2}-1|\le12q,\quad
\left|\frac{xD'(x)}{D(x)}\right|\le4q,\quad |C_0-1|\le20q.
$$
Thus the product of the controlled factors differs from one by at most $40\kappa q$. The extracted factor is
$$
(1-rx)(1+\beta/x)=1-q^2-iB(\rho).
$$
Its square has deviation at most $2q^2+2B+B^2$, and its squared modulus is at most $1+B^2$. Combining these inequalities with (35) proves (38). The extraction is necessary because the omitted factor is not uniformly close to one at both ends of the integration line.

## A positive comparison period and an absolute error

Let $\mathcal H_0$ be (36) with $\mathcal F$ replaced by $\mathcal F_0$. The substitution $v=\cot(\pi w/2)$ deforms the resulting right semicircle to its vertical chord. The deformation avoids the pole at $v=i$. With $h=\sech\kappa_0$ and $k=\tanh\kappa_0$, it gives
$$
\mathcal H_0(t)=\frac\pi{2t}\int_{-k}^{k}e^{-\kappa v}
\frac{(k^2-v^2)\cos(\kappa h)+2h\sin(\kappa h)}{h^2+(v-1)^2}\,dv.
\tag{39}
$$
The kernel is nonnegative. Restrict to $v=-1+\xi$ with $1/(2\kappa)\le\xi\le2/\kappa$. The bounds (35) give
$$
k^2-v^2\ge\tfrac32\xi,\qquad
h^2+(v-1)^2\le4,\qquad \cos(\kappa h)\ge9/10.
$$
Since $\int_{1/2}^{2}xe^{-x}dx>3/8$, one obtains
$$
\mathcal H_0(t)\ge\frac\pi t\frac{e^\kappa}{16\kappa^2}
>70\frac\pi t.
\tag{40}
$$
To control the original period, let
$$
I_j=\int_{-s/2}^{s/2}|\mathcal F_0(1/2+iy)|B(e^{-\pi y})^jdy.
$$
The change of variable $\rho=e^{-\pi y}$ gives the positive density
$$
|\mathcal F_0|\,|dy|
=\frac\pi t\frac\rho{1+\rho^2}
\exp\left(\kappa\frac{1-\rho^2}{1+\rho^2}\right)d\rho.
$$
Splitting at $\rho=1$, bounding the first part by a Gaussian, and using $r\beta=q^2$ gives
$$
I_0\le\frac\pi t\left(\frac{e^\kappa}{2\kappa}+\kappa_0\right),
\qquad I_1\le\frac{3\pi}t,\qquad I_2\le\frac{2\pi}t.
\tag{41}
$$
Inserting (41) into (38) proves
$$
\begin{aligned}
|\mathcal H-\mathcal H_0|
&\le100\kappa qI_0+4I_1+3I_2\\
&\le\frac\pi t(50qe^\kappa+100\kappa q\kappa_0+18)
<69\frac\pi t.
\end{aligned}
\tag{42}
$$
For the last strict bound, use $qe^\kappa\le1$ and $100\kappa(\kappa+1)e^{-\kappa}<1$ for $\kappa>25/2$. The elementary estimates $e^{25/2}>(3/2)7^6$ and monotonicity of $e^\kappa/\kappa^2$ justify (40). We have proved the uniform conclusion
$$
\boxed{\mathcal H(t)>\pi/t>0\quad(0<t\le1/8).}
\tag{43}
$$
An asymptotic expansion alone would not prove (43) on this whole interval.

# Certification on the remaining parameter ranges

## The computed functions and their tails

Remove the common nonzero factor from the odd theta function and write
$$
S(v;t)=\sum_{n=0}^{\infty}\epsilon_n e^{-\pi t n(n+1)/2}\sin((2n+1)v),
\quad (\epsilon_0,\epsilon_1,\epsilon_2,\epsilon_3)=(1,1,-1,-1),
\quad\epsilon_{n+4}=\epsilon_n.
\tag{44}
$$
Primes on $S$ always mean derivatives in $v$. The sigma normalization gives the exact formulas, with $v_a=\pi a/2$ and $v_z=\pi z/2$,
$$
\begin{aligned}
A_{t,a}(z)&=
\left(\frac{\pi S'(0;t)}{2S(v_a;t)}\right)^2
\left(\frac{S(v_z-v_a;t)}{S(v_z;t)}\right)^2
\exp\left((a-1)\pi\frac{S'(v_z;t)}{S(v_z;t)}\right),\\
G(t,a)&=\frac{\pi^2}{4}
\left(\left(\frac{S'(v_a;t)}{S(v_a;t)}\right)^2
-\frac{S''(v_a;t)}{S(v_a;t)}\right)-\frac\pi t.
\end{aligned}
\tag{45}
$$
Thus the calculation evaluates the same function as the geometric period problem, with its absolute normalization fixed.

For a parameter rectangle with $t\ge t_->0$ and $|\operatorname{Im}v|\le y$, define
$$
\begin{aligned}
B_{N,j}&=(2N+1)^j
e^{-\pi t_-N(N+1)/2+(2N+1)y},\\
\rho_{N,j}&=\left(\frac{2N+3}{2N+1}\right)^j
e^{-\pi t_-(N+1)+2y}.
\end{aligned}
$$
If $\rho_{N,j}<1$, the absolute error after the first $N$ terms of $S^{(j)}$ is bounded by
$$
\frac{B_{N,j}}{1-\rho_{N,j}}.
\tag{46}
$$
Indeed, the absolute size of the $n$th differentiated term is at most $(2n+1)^j e^{-\pi t_-n(n+1)/2+(2n+1)y}$, and its ratio to the previous bound is at most $\rho_{N,j}$ once $n\ge N$. This proves uniform control on the full complex box, including the complex neighborhoods used by the integrator.

For each rational interval $I$ in $t$, a proposed vertical enclosure $J=[a_-,a_+]$ is accepted only after proving
$$
0<a_-<a_+<1,\qquad G(I,a_-)>0,\qquad G(I,a_+)<0.
\tag{47}
$$
Strict monotonicity in $a$ then implies $a(t)\in(a_-,a_+)$ for every $t\in I$. Midpoint searches and preliminary floating-point approximations have no role in the acceptance criterion.

For small $t$, the dual expression avoids cancellation in (45). With $q=e^{-\pi/(2t)}$ and $E=e^{\pi(a-1/2)/t}$, use
$$
\begin{aligned}
D(t,a)&=-\frac{E^{-1}}{(1-q/E)^2}
+\sum_{n\ge1}(-1)^{n+1}nq^{n-1}
\frac{E^n+q^{2n}E^{-n}}{1-(-q^2)^n},\\
G(t,a)&=-\frac{\pi^2q}{t^2}D(t,a).
\end{aligned}
\tag{48}
$$
For $T_N(x)=x^N((N+1)/(1-x)+x/(1-x)^2)$, the omitted tail after $n=N$ is at most
$$
\frac{E T_N(qE)+(q^2/E)T_N(q^3/E)}{1-q^2}.
\tag{49}
$$
Every argument required to lie below one is checked on the entire rectangle. Formula (48) follows by expanding the absolutely convergent products in (33).

All arithmetic is outward enclosed. Every denominator must be separated from zero, every tail ratio must be strictly below one, and each integral enclosure must cover the full parameter rectangle. A failure of any such condition rejects the box or requires subdivision. The original numerical generation uses Arb through Python--FLINT [J17, J18]. The Lean verification proves the necessary enclosures and their connection to the analytic periods without treating the external numerical program as an axiom.

## Positive, negative, and right-end ranges

The exact finite certificates establish
$$
\mathcal H(t)>\frac3{10000}\quad(1/8\le t\le17/20),
\qquad
\mathcal H(t)<-\frac1{25}\quad(9/10\le t\le7/5).
\tag{50}
$$
The positive range consists of 558 adjacent rational parameter intervals, each equipped with a uniform enclosure (47). It uses eight terms in the dual theta representation, 112-bit working precision, and integration tolerance $3/1000$. The negative range has 59 intervals and uses ten terms in the original theta representation, 112-bit precision, and tolerance $1/100$. Tolerances are algorithm parameters. The mathematical evidence consists of the final outward bounds, not the requested tolerances.

The smallest positive lower bound and the least absolute negative upper bound satisfy
$$
\begin{aligned}
\frac{4048815533235523741519408834611}
{10384593717069655257060992658440192}&>\frac3{10000},\\
\frac{238070159187588210339310175778799}
{5192296858534827628530496329220096}&>\frac1{25}.
\end{aligned}
\tag{51}
$$
The partitions are listed in Appendix A. Endpoint equality is checked with rational arithmetic, so no gap can occur between consecutive boxes.

For the right end, take
$$
I=[7/5,141/100],\qquad J_j=[(90+j)/100,(91+j)/100],\quad 0\le j\le9.
$$
The independent rectangular checks give
$$
G(I,9/10)>1/20,\qquad H(I,J_j)<-7/5.
\tag{52}
$$
Here $H(t,a)$ is the two-variable period in (30). Since $T_*<141/100$, (47) and monotonicity imply $a(t)>9/10$ on $[7/5,T_*)$. The ten intervals $J_j$ cover $[9/10,1]$, proving
$$
\mathcal H(t)<-7/5\quad(7/5\le t<T_*).
\tag{53}
$$
Including $a=1$ in these independent rectangles is legitimate because (28) is regular as a function of this parameter along the integration path. No estimate of the possibly large derivative $a'(t)$ is used here.

## A derivative certificate near the zero

The reduced theta series satisfies the heat identity
$$
S_t=\frac\pi8(S''+S).
\tag{54}
$$
The extra $S$ term accounts for removal of the common theta factor. Set $r=S'(v_a)/S(v_a)$ and $u_j=S^{(j)}(v_a)/S(v_a)$. Direct differentiation of (45) gives
$$
\begin{aligned}
G_a&=\frac{\pi^3}{8}(3ru_2-2r^3-u_3),\\
G_t&=\frac{\pi^3}{32}\bigl(2r(u_3-ru_2)-(u_4-u_2^2)\bigr)+\frac\pi{t^2},\\
a'(t)&=-G_t/G_a.
\end{aligned}
\tag{55}
$$
With $r_z=S'(v_z)/S(v_z)$, $r_m=S'(v_z-v_a)/S(v_z-v_a)$, and analogous ratios $z_j,m_j$, define
$$
\begin{aligned}
L_a&=\partial_a\log A=\pi(r_z-r_m-r),\\
L_t&=\partial_t\log A\big|_{z,a}
=\frac\pi4\left(\frac{S'''(0)}{S'(0)}-u_2+m_2-z_2\right)
+\frac{(a-1)\pi^2}{8}(z_3-r_zz_2).
\end{aligned}
\tag{56}
$$
When (30) is differentiated, the moving path contributes the boundary term proportional to $A(1+it/2)-A(-1+it/2)$, which vanishes by the real period $2$. Hence
$$
\mathcal H'(t)=\frac12\operatorname{Re}\int_{-1}^{1}
A_{t,a(t)}(x+it/2)
\left(L_t-\frac{G_t}{G_a}L_a\right)dx.
\tag{57}
$$
Uniform analyticity on compact parameter ranges justifies the differentiation. The divisions in (55)--(57), including $G_a<0$, are checked on each full rectangle.

The 50 intervals $[(850+j)/1000,(851+j)/1000]$, $0\le j\le49$, cover $[17/20,9/10]$. At 112-bit working precision and tolerance $1/25$, their derivative upper bounds have maximum
$$
-\frac{1275145233244573066074824793433219}
{162259276829213363391578010288128}<-1.
$$
Thus
$$
\mathcal H'(t)<-1\quad(17/20\le t\le9/10).
\tag{58}
$$

## Unique zero and its rational location

The full parameter argument is summarized by the following table. The rows cover the entire admissible domain (25).

| Parameter range | Verified statement | Method |
|---|---|---|
| $(0,1/8]$ | $\mathcal H>\pi/t$ | Analytic product and integral estimates |
| $[1/8,17/20]$ | $\mathcal H>3/10000$ | 558 original positive boxes |
| $[17/20,9/10]$ | $\mathcal H'<-1$ | 50 derivative boxes |
| $[9/10,7/5]$ | $\mathcal H<-1/25$ | 59 original negative boxes |
| $[7/5,T_*)$ | $\mathcal H<-7/5$ | 10 right-end rectangles |

The signs at $17/20$ and $9/10$ give a zero by continuity. Equation (58) makes it unique and simple in the middle interval. The other four rows exclude zeros everywhere else. Global monotonicity of $\mathcal H$ is not required.

For the narrow enclosure, the 192-bit, 22-term calculation proves
$$
\begin{gathered}
t_-=0.866227694384,\qquad t_+=0.866227694385,\\
\frac{63}{10^{13}}<\mathcal H(t_-)<\frac{64}{10^{13}},\qquad
-\frac{37}{10^{13}}<\mathcal H(t_+)<-\frac{36}{10^{13}}.
\end{gathered}
\tag{59}
$$
On the whole interval $[t_-,t_+]$, the vertical root lies strictly between the two rationals
$$
\frac{4409686737850678150959633307219}
{7427640235712281649394745344000}
\quad\text{and}\quad
\frac{4409686737857433550400689051219}
{7427640235712281649394745344000}.
\tag{60}
$$
They lie inside the $a$ interval in (5). This proves the parameter part of Theorem 1. The narrow calculation locates a zero whose global uniqueness has already been established.

# Completion of the classification

Every surface in $\mathcal C$ has the data (9), (12), (13), and §3 proves $m=1$. Lemma 3 forces its parameters to solve $\mathcal H(t)=0$. Sections 4, 6 and 7 therefore give the same pair $(t_0,a_0)$ for every candidate.

At this pair, the coordinate differentials are fixed up to the nonzero real factor $c$ and rigid changes of the ambient frame. Their real primitives on the connected punctured torus differ only by a translation. Changing the sign of $c$ can be included in a Euclidean isometry, and its absolute value is a positive scale. This proves that all candidate images are equivalent in the sense preceding Theorem 1. The identification is global, including the finite Gauss zero and pole, rather than an equality on a smaller coordinate neighborhood.

Existence can be supplied in the classical argument by the embedded two-axis example of [WHW09, Theorem 1]. Applying the preceding reduction to that example puts its parameters at $(t_0,a_0)$ and identifies its image with the closed period model. Thus the class is nonempty and has exactly one element modulo similarity.

The formal development also gives a direct embedding proof for the certified model. It proves injectivity of the central height fiber, of the low positive fibers, and of the remaining positive fibers, and transfers to negative fibers by the marked half-turn. Distinct height fibers cannot intersect. The low range is covered by explicit Gauss-sign, transverse-coordinate and position bounds. Combined with properness, these results establish a closed embedding of the actual torus immersion. Thus the formal main theorem has an embedded representative as a proved conclusion and does not take the existence theorem as an additional premise. This completes the proof of Theorem 1. $\square$

# Correspondence with the Lean theorem

The development is written in Lean 4 [MU21] and uses mathlib [MC20]. The exact compiler and library revisions for the audited snapshot are given in Appendix A.

## The objects quantified over

The formalization uses an abstract smooth real surface with an actual position map into three-dimensional Euclidean space. In `OriginalSmoothHelicoid`, the assumptions are a smooth real atlas, a homeomorphism with a once-punctured torus, a smooth closed embedding with injective differential, vanishing coordinate mean curvature, and the two entire contained lines. The torus in this initial homeomorphism encodes topology. It does not prescribe the later conformal modulus.

The predicate `HasCompactComplementC1Graph` adds exactly the compact-complement graph in (2). It quantifies over a surface subset and a helicoid parameter subset, requires both complements to be compact, and identifies the actual spatial map with the normal graph through a homeomorphism. Its derivative decay is the induced metric expression (3), after pitch normalization. The graph condition does not assume the elliptic data, closed periods, the integer $m$, or the certified parameters.

Minimality is expressed by the usual mean-curvature formula. For a local coordinate map $X$, with $A=X_x$, $B=X_y$ and $N=(A\times B)/|A\times B|$, it is
$$
\frac{|B|^2\langle X_{xx},N\rangle
-2\langle A,B\rangle\langle X_{xy},N\rangle
+|A|^2\langle X_{yy},N\rangle}
{2(|A|^2|B|^2-\langle A,B\rangle^2)}=0.
\tag{61}
$$
The immersion hypothesis makes the denominator positive. The dot products are Euclidean dot products, even where coordinate tuples are represented by a function type whose auxiliary norm is a supremum norm. The final ambient metric, similarities, induced length metric, and completeness statements use Euclidean space explicitly.

A closed embedding into Euclidean space is proper. Together with smooth immersion, it gives completeness of the induced metric. This accounts for the completeness clause in the mathematical definition even though it is derived rather than stored as a redundant field in the initial Lean structure.

Arbitrary physical placements are treated by `PlacedPositionalHelicoid` and its graph predicate. The main conclusions are proved for this presentation as well as for an axis-normalized presentation. The equivalence relation on sets of points is proved equivalent to a Euclidean isometry followed by strictly positive scaling. Therefore the classification is a classification of entire surface images, not merely of parameter lists or of formal differential expressions.

## A common marking and the value at the Gauss pole

The marked conclusion constructs an induced isothermal atlas, a biholomorphic punctured-torus identification, its extension across the puncture, and a rigid spatial placement of the original map. It identifies the original axis crossing with $O=1$, the puncture with $E=0$, and the Gauss data with the same parameter pair that solves the original period equations. The embedded spin cap agrees with the original surface on a neighborhood of the marked generating curves. The topological cap, the analytic compactification and the Gauss divisor are thus compared on one common marking.

There is a representational issue at the Gauss pole. In Lean, field division is total and $0^{-1}=0$. A complex-valued formula for a meromorphic quotient therefore cannot, by its value alone at a pole, distinguish a pole from a zero. The local statements use reciprocal charts and nonzero first derivatives to express simple poles. In addition, the development constructs the spherical Gauss map with values in the one-point compactification of $\mathbb C$. Its zero fiber is precisely $a$ modulo $\Lambda_t$, and its infinity fiber is precisely $-a$ modulo $\Lambda_t$. The joint theorem `manuscript_C1_same_cap_quotient_gauss_fibers` makes these statements on the actual punctured quotient and the same cap marking. Theorem 1 uses this spherical interpretation.

## Entrypoints, checks, and their scope

The main source-level entrypoint is `TwoAxisHelicoidManuscript`. The following declarations expose the closed geometric statement and the classification using the original attachment parameters.

```{=latex}
\begin{samepage}
```

```lean
import TwoAxisHelicoidManuscript

open TwoAxisHelicoid

#check manuscript_geometric_theorem_one_one
#check manuscript_theorem_one_one
#check placed_manuscript_theorem_one_one
#check manuscript_C1_same_cap_quotient_gauss_fibers
#check PdfVertical.original_tables_classify_manuscript_C1_surfaces

#print axioms manuscript_geometric_theorem_one_one
```

```{=latex}
\end{samepage}
```

The first declaration has the complete type `ManuscriptGeometricTheoremOneOne`. Unfolding that proposition gives the unique represented similarity class, an embedded certified representative, a positive similarity for every physical candidate, the bounds (5), and the common cap marking. It has no additional theorem-valued geometric premises.

The publication project, `two-axis-helicoid-uniqueness`, was built and audited under the module and namespace names shown below. The verified source snapshot has the following scope.

| Audit item | Recorded result |
|---|---|
| Main source entrypoint | `TwoAxisHelicoidManuscript` |
| Reachable project modules | 8,419 |
| Project declarations included in the axiom audit | 368,507 |
| Distinct named manuscript witnesses | 617 |
| Original numbered statements and scoped formulations | 30 statements, 64 scopes |
| Additional indexed derivations | 36 |
| Numbered and unnumbered displayed equations | 84 and 142 |
| Axioms found | `propext`, `Classical.choice`, `Quot.sound` |

The count of 617 witnesses is unrelated to the coincidentally equal number of original positive and negative parameter boxes, $558+59$. Module and declaration counts describe the audit domain and do not measure mathematical completeness.

All 8,419 project modules were compiled from source under the publication names, starting with an empty project build directory and retaining completed outputs when the build was resumed. The pinned mathlib dependencies used their precompiled cache. The complete project build, statement checks and axiom audit passed; a final build with rebuilding disabled confirmed that all targets were up to date. A separate, earlier stock LeanChecker run replayed six selected modules in their imported environments, including the main geometric theorem and the manuscript entrypoint. That replay preceded the publication renaming and supplies additional evidence for those earlier module environments; it does not constitute a fresh replay of every dependency.

The axiom list contains Lean's standard propositional extensionality, classical choice and quotient soundness. No `sorryAx` or project-specific mathematical axiom appears in the audited dependency set. Kernel checking establishes the declared propositions relative to this foundation. The separate semantic review unfolds their definitions to compare them with the mathematical statements. The present paper reports that comparison for the main class, its markings, periods and existence conclusion, rather than treating a successful compilation as a substitute for it.

The companion file `tools/StatementCheck.lean` checks five closed conclusions, covering both geometric presentations, embedded existence and the spherical Gauss fibers. Implicit declaration of unknown identifiers is disabled in this file. It was compiled against the rebuilt publication project, and all five conclusions had only the three standard axioms listed above. These statement checks supplement the complete project build and declaration audit.

## Published inputs retained in wider statements

Two broader uses of geometry must remain visible. The general finite-topology conformal end theorem is represented by an explicit published-input hypothesis when no graph end is supplied. The implication from that input to conformal poles and the subsequent reduction is checked, but the unrestricted external theorem is not thereby independently proved in Lean.

The alternative compactness proof of finiteness in the original manuscript's Appendix B uses the fixed-axis compactness theorem of Hoffman and White [HW08, Theorem 7.1]. Its formal counterpart accepts smooth subsequential convergence of actual local position maps and their derivatives, together with the periodic-slab topology statement. It then proves the curve transport, exclusion of periodic limits, flux gap and finiteness conclusion. Its explicit hypotheses cannot be omitted merely because its type has been accepted by the kernel.

Neither of these broader inputs is an extra assumption of the closed graph-class theorem above. The separation also prevents a conditional local Jacobi estimate from being reported as a proved nondegeneracy theorem.

# Further consequences and separate geometric inputs

## Degeneration and finiteness

The dual root equation in §6 has the sharper asymptotics
$$
a(t)=\frac12+\frac{2t}\pi e^{-\pi/(2t)}
+O\bigl(te^{-\pi/t}\bigr),\qquad
\mathcal H(t)\sim\frac t\pi e^{\pi/(2t)}
\quad(t\downarrow0).
\tag{62}
$$
They follow by retaining the next balance in (33) and applying the corresponding weighted integral estimates to (37). These asymptotics are independently useful, while the explicit inequality (43) supplies the full interval statement needed for the main proof.

At unit absolute pitch, the coefficient in (14) has $|\alpha|=1$, hence $|c|=2(1-a)$. The least nonzero absolute vertical component among generating lattice fluxes is
$$
\frac{2\pi(1-a(t))}{t}\longrightarrow+\infty.
\tag{63}
$$
An alternative route to a positive lower bound for the parameter of embedded candidates uses fixed-axis smooth compactness. A periodic limit would supply two disjoint handle pieces in an approximating genus-one surface, which is impossible. For a nonperiodic smooth limit, compact generating curves and their fluxes can be transported through the convergence, giving bounded flux. Equation (63) then excludes $t\downarrow0$. The right endpoint has $\mathcal H(T_*)=-2\pi$, so it also contains no accumulating closed candidates. On a compact subinterval of $(0,T_*)$, the zeros of a nonzero analytic function are finite.

This is the compactness route of the original Appendix B. Its smooth compactness input remains explicit, as explained in §9.4. It gives a finiteness argument independent of the horizontal interval certificates. Finiteness in the class of Theorem 1 also follows directly from its stronger uniqueness conclusion.

## Fixed-data rigidity and flux

Suppose two meromorphic one-forms on a compact connected Riemann surface have the same principal parts and zero real periods on every closed curve avoiding the poles. Their difference is holomorphic, and its real part has a single-valued harmonic primitive. A harmonic function on a compact connected surface is constant, so the difference vanishes. The periods here are actual path integrals. No primitive is assumed in advance.

For (9), the nonzero flux component in (11) implies that the associate data $e^{i\vartheta}\Phi$ have zero real periods exactly when $\vartheta\in\pi\mathbb Z$. Indeed, a closed period has the form $iv$ with $v\in\mathbb R^3$, and its new real part is $-\sin\vartheta\,v$. At least one such vector has nonzero vertical component.

Fixing $dh$ and $dg/g$ fixes $g$ up to a nonzero multiplicative constant. For the embedded candidates, the corresponding amplitude rigidity gives modulus one. Combining this with the real-normalized differential argument yields rigidity for a fixed marked torus, puncture and prescribed principal parts. These statements concern fixed data; they do not replace the parameter analysis needed to compare different tori.

## Jacobi fields and the infinite Morse index

The normal components of the three translations, three rotations and dilation give seven linearly independent Jacobi fields on the complete surface. Linear independence uses the actual helicoidal end and genus-one geometry. The statement is about these seven fields and does not classify the entire Jacobi kernel in an arbitrary weighted space.

For compactly supported normal variations, the second variation is
$$
Q(v)=\int_\Sigma\bigl(|\nabla v|^2-|A|^2v^2\bigr)d\mu.
\tag{64}
$$
In height coordinates at the end, translates of the potential converge on compact rectangles to the helicoid potential. After rescaling the coordinates, its quadratic form is
$$
Q_H(v)=\int_{\mathbb R^2}
\bigl(v_x^2+v_y^2-2\sech^2(y)v^2\bigr)dx\,dy.
$$
The function $f(y)=\sech y$ satisfies $-f''-2\sech^2(y)f=-f$. Smooth compactly supported approximation therefore gives a function $\psi$ with negative one-dimensional quadratic form $q(\psi)$. For $v_L(x,y)=\chi(x/L)\psi(y)$,
$$
Q_H(v_L)=L\|\chi\|_2^2q(\psi)
+L^{-1}\|\chi'\|_2^2\|\psi\|_2^2<0
$$
when $L$ is large. Translate this fixed negative test function to sufficiently distant disjoint end rectangles. Convergence of the potential preserves negativity, and disjoint support makes all cross terms zero. There are negative subspaces of every finite dimension. The complete surface consequently has infinite Morse index.

The formal second-variation theorem applies to the actual compactly supported normal variation, using a partition of unity across charts. It is not restricted to a single preferred end chart. Infinite Morse index does not imply an infinite-dimensional Jacobi kernel or instability in every symmetry-constrained variation space.

A local uniqueness argument in a prescribed Banach space would require a separate estimate $\|u\|_{\mathcal X}\le C\|Lu\|_{\mathcal Y}$ for the appropriate Jacobi operator. If the mean-curvature map has derivative $L$ and remainder $o(\|u\|_{\mathcal X})$, that estimate implies local rigidity by absorption. No such estimate for arbitrary weights is asserted here. The simple period root in (58) is the finite-dimensional nondegeneracy used in Theorem 1.

\appendix

# Certificate partitions and reproducibility

## Exact parameter partitions

Each row below means the consecutive closed intervals of the given length from the stated left endpoint to the right endpoint. The positive partition is

| Left endpoint | Right endpoint | Step | Number |
|---|---|---|---:|
| $1/8$ | $237/1600$ | $1/6400$ | 148 |
| $237/1600$ | $3/16$ | $1/3200$ | 126 |
| $3/16$ | $47/200$ | $1/1600$ | 76 |
| $47/200$ | $121/400$ | $1/800$ | 54 |
| $121/400$ | $81/200$ | $1/400$ | 41 |
| $81/200$ | $3/4$ | $1/200$ | 69 |
| $3/4$ | $153/200$ | $1/400$ | 6 |
| $153/200$ | $157/200$ | $1/200$ | 4 |
| $157/200$ | $83/100$ | $1/400$ | 18 |
| $83/100$ | $17/20$ | $1/800$ | 16 |

The negative partition is

| Left endpoint | Right endpoint | Step | Number |
|---|---|---|---:|
| $9/10$ | $183/200$ | $1/400$ | 6 |
| $183/200$ | $24/25$ | $1/200$ | 9 |
| $24/25$ | $7/5$ | $1/100$ | 44 |

The 50 derivative intervals and ten right-end rectangles are specified in §7. The companion data include every vertical bracket and every exact outward endpoint, as well as the original generating and replay programs. All nine original program files are retained under `lean/source/attachments`. The replay record in `lean/audit/original-arb-replay.json` reports agreement of all original certificate values. The pure-rational vertical program has a separate replay of all eight printed output lines.

## Formal verification environment

The audited environment is Lean 4.35.0, compiler commit

```
eb6cafb7290e8bd5f2937522d8d804f58f02bafc
```

and mathlib commit

```
56a005855ea17e0b0958f73ec801ae140b0a1679
```

The companion source repository is `two-axis-helicoid-uniqueness`. Its `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` pin the compiler and all package dependencies. From the repository root, the complete build and audit commands are

```bash
elan toolchain install leanprover/lean4:v4.35.0
lake exe cache get
lake build
lake env lean tools/StatementCheck.lean
lake env lean tools/Audit.lean
```

The default build includes `TwoAxisHelicoidManuscript` and all of its project dependencies. The generated interval-certificate proofs are supplied as Lean source files; no private data generator or machine-specific build driver is required. The dependency cache command downloads compiled mathlib dependencies. Project compilation then checks the supplied source, and `tools/Audit.lean` checks the imported declarations against the permitted axiom set and the list of manuscript witnesses.

The file `source_inventory.json` records the path, size, SHA-256 and project imports of every proof module. The release uses a consistent mathematical module and namespace naming scheme. A file-by-file comparison tracked the naming substitution and one explicit associativity simplification needed during rebuilding; no definition or theorem statement changed. The complete project was then built and audited under the publication names, and all source hashes were checked against the inventory. Third-party dependencies used the pinned mathlib cache, so this verification does not claim a source rebuild of mathlib itself.

A permanent public archive address and final author metadata remain to be supplied for the submission version.

\clearpage
\begingroup
\setlength{\parindent}{0pt}
\setlength{\parskip}{4pt}

# References {.unnumbered}

**[AFM07]** Antonio Alarcón, Leonor Ferrer and Francisco Martín. *A uniqueness theorem for the singly periodic genus-one helicoid*. Transactions of the American Mathematical Society **359** (2007), 2819–2829. [DOI 10.1090/S0002-9947-07-04093-7](https://doi.org/10.1090/S0002-9947-07-04093-7). [Author manuscript](https://arxiv.org/abs/math/0505412).

**[BB11a]** Jacob Bernstein and Christine Breiner. *Conformal structure of minimal surfaces with finite topology*. Commentarii Mathematici Helvetici **86** (2011), 353–381. [DOI 10.4171/CMH/226](https://doi.org/10.4171/CMH/226).

**[BB11b]** Jacob Bernstein and Christine Breiner. *Symmetry of embedded genus-one helicoids*. Duke Mathematical Journal **159** (2011), 83–97. [DOI 10.1215/00127094-1384791](https://doi.org/10.1215/00127094-1384791). [Author manuscript](https://arxiv.org/abs/1011.3769).

**[B98]** Alexander I. Bobenko. *Helicoids with handles and Baker–Akhiezer spinors*. Mathematische Zeitschrift **229** (1998), 9–29. [Author copy](https://page.math.tu-berlin.de/~bobenko/papers/1998_Bob_BA.pdf).

**[DLMF]** NIST Digital Library of Mathematical Functions. [Chapter 20, Theta Functions](https://dlmf.nist.gov/20), and [Chapter 23, Weierstrass Elliptic and Modular Functions](https://dlmf.nist.gov/23). In particular, §§20.2, 20.5, 20.13, 23.2, 23.6, 23.8 and 23.10.

**[HW08]** David Hoffman and Brian White. *Genus-one helicoids from a variational point of view*. Commentarii Mathematici Helvetici **83** (2008), 767–813. [Publisher full text](https://ems.press/content/serial-article-files/43173).

**[HW09]** David Hoffman and Brian White. *The geometry of genus-one helicoids*. Commentarii Mathematici Helvetici **84** (2009), 547–569. [DOI 10.4171/CMH/172](https://doi.org/10.4171/CMH/172).

**[J17]** Fredrik Johansson. *Arb: Efficient Arbitrary-Precision Midpoint-Radius Interval Arithmetic*. IEEE Transactions on Computers **66** (2017), no. 8, 1281–1292. [Author manuscript](https://arxiv.org/abs/1611.02831).

**[J18]** Fredrik Johansson. *Numerical integration in arbitrary-precision ball arithmetic*. 2018. [arXiv:1802.07942](https://arxiv.org/abs/1802.07942).

**[KS96]** Rob Kusner and Nick Schmitt. *The Spinor Representation of Surfaces in Space*. 1996. [arXiv:dg-ga/9610005](https://arxiv.org/abs/dg-ga/9610005).

**[MC20]** The mathlib Community. *The Lean mathematical library*. Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs, 2020, 367–381. [DOI 10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824). [Author manuscript](https://arxiv.org/abs/1910.09336).

**[MU21]** Leonardo de Moura and Sebastian Ullrich. *The Lean 4 Theorem Prover and Programming Language*. Automated Deduction—CADE 28, Lecture Notes in Computer Science **12699** (2021), 625–635. [DOI 10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37).

**[P26]** Joaquín Pérez. *Minimal Surfaces of Finite Genus: Classification, Dynamics and Laminations*. Proceedings of the International Congress of Mathematicians 2026, Volume 4, 215–232. [DOI 10.1137/25M1803188](https://doi.org/10.1137/25M1803188).

**[WHW09]** Matthias Weber, David Hoffman and Michael Wolf. *An embedded genus-one helicoid*. Annals of Mathematics **169** (2009), 347–448. [DOI 10.4007/annals.2009.169.347](https://doi.org/10.4007/annals.2009.169.347).

\endgroup
