#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge
#import "@preview/cetz:0.3.4"

#import "@local/math-notes:0.3.0": *

#show: math_notes.with(title: "Riemann Surfaces")


// Overwrite the default definition
#let hatCC = $hat(CC, size: #1.00001em)$
#let acts = $arrow.cw.half$

// define commutative diagram
#let commutative_diagram(math_content) = align(center)[
  #diagram(label-size: 0.8em, math_content)
  #v(1em, weak: true)
]


#let cal(x) = math.class("unary", text(font: "Computer Modern Symbol", x))


= Basic Concepts <basic-concepts>


== Complex Manifold <complex-manifold>
=== Complex Structure <holomorphic-atlas>

#definition[Holomorphic Chart][
  A #strong[holomorphic chart] on a topological manifold $X$ is a homeomorphism $phi : U arrow.r V subset.eq bb(C)^n$ where $U$ is
  an open subset of $X$, denoted by $lr((U , phi))$.
]
We say that a chart $lr((U , phi))$ for a Riemann surface $X$ is #strong[centered at $x$] if $phi lr((x)) = 0$.

#definition[Holomorphic Atlas][
  A #strong[(compatible) holomorphic atlas] on a topological manifold $X$ is a collection of holomorphic charts $Sigma = {lr((U_i , phi_i))}$ such
  that $union.big_i U_i = X$ and for any $i , j$, the transition function
  $
    phi_i circle.stroked.tiny phi_j^(- 1) : phi_j lr((U_i inter U_j)) --> phi_i lr((U_i inter U_j))
  $
  is holomorphic, whenever $U_i inter U_j$ is nonempty.
]
#remark[
  Any compatible holomorphic atlas $Sigma$ can be extended to a maximal compatible holomorphic atlas $overline(Sigma)$
]

#definition[Complex Manifold][
  A #strong[complex manifold] of dimension $n$ is a second-countable Hausdorff topological manifold of dimension $2 n$ with a maximal compatible
  holomorphic atlas $lr({lr((U_i , phi_i))})$.
]
#remark[
  If we say $X$ is a complex manifold with compatible atlas $Sigma = lr({lr((U_i , phi_i))})$, what we mean is that $X$ is a complex manifold with the maximal compatible atlas $overline(Sigma)$ that contains $Sigma$.
]
#definition[Holomorphic Map][
  A map $f : X arrow.r Y$ between two complex manifolds is #strong[holomorphic at $x in X$] if there exists a holomorphic
  chart $lr((U , phi))$ containing $x$ and a holomorphic chart $lr((V , psi))$ containing $f lr((x))$ such that $f lr((U)) subset.eq V$ and $psi circle.stroked.tiny f circle.stroked.tiny phi^(- 1)$ is
  holomorphic.
]
We say $f$ is #strong[holomorphic] if it is holomorphic at every point of $X$.
#definition[Biholomorphism][
  A holomorphic map $f : X arrow.r Y$ is called an #strong[biholomorphism] or (#strong[isomorphism]) if $f$ is bijective.
  In this case, $f^(- 1)$ is also holomorphic and we say $X$ and $Y$ are #strong[biholomorphic] or (#strong[isomorphic]).
]
#definition[Linear Complex Structure][
  A #strong[linear complex structure] on a $bb(R)$-vector space $V$ is a $bb(R)$-linear transformation $J : V arrow.r V$ such
  that $J^2 = - upright(i d)_V$.
]
#definition[Almost Complex Structure][
  Let $M$ be a smooth manifold. An almost complex structure on $M$ is a smooth $lr((1 , 1))$-tensor field $J in Gamma lr((T^(lr((1 , 1))) M))$.
]

=== Complexified Tangent Bundle <complex-tangent-bundle>

#definition[Complex Vector Bundle][
  A #strong[complex vector bundle] of rank $k$ over a topological space $X$ is a vector bundle $p:E->X$ satisfiing that for each $x in X$, the fiber $p^(-1)(x)$ is a $CC$-vector space of dimension $k$.
]

#definition[Holomorphic Vector Bundle][
  A complex vector bundle $p:E->X$ is called a #strong[holomorphic vector bundle] if $X$ is a complex manifold and the local trivialization maps
  $
    phi_alpha : p^(-1)(U_alpha) &--> U_alpha times CC^k
  $ are biholomorphic maps.
]
#remark[
  This definition is equivalent to requiring that all the transition maps
  $
    t_(alpha, beta) : U_alpha inter U_beta &--> op("GL")_k (CC)
  $
  are holomorphic.

  If not specified, the topological space $E$ is always regarded to be a complex manifold with the holomorphic atlas ${(U_alpha , phi_alpha)}$.
]

#definition[Holomorphic Sections of a Holomorphic Vector Bundle][
  Let $p:E->X$ be a holomorphic vector bundle over a complex manifold $X$ and $U subset.eq X$ be an open subset. A section $sigma : U -> E$ is called #strong[holomorphic] if it is a holomorphic map.
]

#definition[Complexified Tangent Space][
  Let $M$ be a complex manifold of complex dimension $n$. Define $T_p^RR M$ as the tangent space of the underlying smooth manifold. The #strong[complexified tangent space] at $p in M$ is defined as the $CC$-vector space
  $
    T_p^CC M:=T_p^RR M times.circle_RR CC
  $
]
If $(U, (z^j))$ is a holomorphic chart at $p$, then $(U, (x^j,y^j))$ is a smooth chart at $p$, where $x^j = op("Re") z^j$ and $y^j = op("Im") z^j$. Then $T_p M$ as a $2n$-dimensional $CC$-vector space has a $CC$-basis
$
  lr(frac(partial, partial x^1)|)_p , med lr(frac(partial, partial x^2)|)_p , dots.h.c med, lr(frac(partial, partial x^n)|)_p ,quad lr(frac(partial, partial y^1)|)_p , med lr(frac(partial, partial y^2)|)_p ,med dots.h.c med, med lr(frac(partial, partial y^n)|)_p.
$
Define
$
  partial / (partial z^j) & := frac(1, 2) (frac(partial, partial x^j) - i lr(frac(partial, partial y^j)) ),\
  partial / (partial overline(z)^j) & := frac(1, 2) (frac(partial, partial x^j) + i lr(frac(partial, partial y^j)) ).
$
Then it is easy to check that
$
  T_p^CC M = op("span")_CC {lr(partial / (partial z^1)|)_p , med lr(partial / (partial z^2)|)_p, med dots.h.c ,med lr(partial / (partial z^n)|)_p, med lr(partial / (partial overline(z)^1)|)_p , med lr(partial / (partial overline(z)^2)|)_p, med dots.h.c ,med lr(partial / (partial overline(z)^n)|)_p}.
$
#definition[Holomorphic Tangent Space][
  Let $M$ be a complex manifold of complex dimension $n$.
  The $CC$-vector spaces
  $
    T_p^(1,0)M &:= op("span")_CC {lr(partial / (partial z^1)|)_p , med lr(partial / (partial z^2)|)_p, med dots.h.c ,med lr(partial / (partial z^n)|)_p},
  $

  is called the #strong[holomorphic tangent space] at $p$. The $CC$-vector space

  $
    T_p^(0,1)M &:= op("span")_CC {lr(partial / (partial overline(z)^1)|)_p , med lr(partial / (partial overline(z)^2)|)_p, med dots.h.c ,med lr(partial / (partial overline(z)^n)|)_p}.
  $

  is called the #strong[anti-holomorphic tangent space] at $p$.
]


We have the following direct sum decomposition
$
  T_p^CC M = T_p^(1,0)M plus.circle T_p^(0,1)M,
$
where $T^(1,0)_p M$ is the $i$-eigenspace of $T_p^CC M$ and $T^(0,1)_p M$ is the $-i$-eigenspace of $T_p^CC M$.

#definition[Complexified Tangent Bundle][
  The #strong[complexified tangent bundle] of a complex manifold $M$ is the complex vector bundle
  $
    T^CC M := union.sq.big_(p in M) T_p^CC M.
  $
]

#definition[Holomorphic Tangent Bundle][
  The #strong[holomorphic tangent bundle] of a complex manifold $M$ is the holomorphic vector bundle
  $ T^(1,0) M := union.sq.big_(p in M) T_p^(1,0) M. $
  The #strong[anti-holomorphic tangent bundle] is the holomorphic vector bundle $ T^(0,1) M := union.sq.big_(p in M) T_p^(0,1) M. $
]

We have the following direct sum decomposition
$
  T^CC M = T^(1,0)M plus.circle T^(0,1)M,
$
where $T^(1,0)M$ is the $i$-eigenbundle of $T^CC  M$ and $T^(0,1)M$ is the $-i$-eigenbundle of $T^CC  M$.

#proposition[Holomorphic Tangent Space is Holomorphic Vector Bundle][
  Let $M$ be a complex manifold. The holomorphic tangent bundle $T^(1,0)M$ is a holomorphic vector bundle over $M$, with the projection map
  $
    p: T^(1,0)M &--> M\
    (x, v) &arrow.bar.long x.
  $
]
#proof[
  Let $lr((U, phi))$ be a holomorphic chart on $M$. Then the local trivialization map
  $
    phi_* : p^(-1)(U) &--> U times CC^n\
    (x, v) &arrow.bar.long (p(x), phi lr((x)))
  $
  is a biholomorphism.
]

=== Complexified Cotangent Bundle <complex-cotangent-bundle>

#definition[Complexified Cotangent Space][
  Let $M$ be a complex manifold of complex dimension $n$. The #strong[complexified cotangent space] at $p in M$ is defined as
  $
    T_p^(*CC)M:=(T_p^CC M)^*.
  $
]
If $(U, (z^j))$ is a holomorphic chart at $p$, then $(U, (x^j,y^j))$ is a smooth chart at $p$, where $x^j = op("Re") z^j$ and $y^j = op("Im") z^j$. Then $T_p^(*CC)M$ as a $2n$-dimensional $CC$-vector space has a $CC$-basis
$
  dif x^1 , med dif x^2 ,med dots.h.c , dif x^n ,quad dif y^1 , med dif y^2 ,med dots.h.c , med dif y^n.
$
Define
$
  dif z^j & := dif x^j + i dif y^j,\
  dif overline(z)^j & := dif x^j - i dif y^j.
$
Then it is easy to check that
$
  T_p^(*CC)M = op("span")_CC {dif z^1 , med dif z^2, med dots.h.c , med dif z^n, med dif overline(z)^1 , med dif overline(z)^2, med dots.h.c , med dif overline(z)^n}.
$


#definition[Holomorphic Cotangent Space][
  Let $M$ be a complex manifold of complex dimension $n$. The #strong[holomorphic cotangent space] at $p in M$ is defined as
  $
    T_p^(*1,0)M:=(T_p^(1,0)M)^* = op("span")_CC {dif z^1 , med dif z^2, med dots.h.c , med dif z^n},
  $
  The #strong[anti-holomorphic cotangent space] at $p in M$ is defined as
  $
    T_p^(*0,1)M:=(T_p^(0,1)M)^* = op("span")_CC {dif overline(z)^1 , med dif overline(z)^2, med dots.h.c , med dif overline(z)^n}.
  $
]

We have the following direct sum decomposition
$
  T_p^(*CC)M = T_p^(*1,0)M plus.circle T_p^(*0,1)M.
$

#definition[Holomorphic Cotangent Bundle][
  The #strong[holomorphic cotangent bundle] of a complex manifold $M$ is the holomorphic vector bundle
  $
    T^(*1,0)M:=union.sq.big_(p in M) T_p^(*1,0)M.
  $
  The #strong[anti-holomorphic cotangent bundle] is the holomorphic vector bundle
  $
    T^(*0,1)M:=union.sq.big_(p in M) T_p^(*0,1)M.
  $
]

We have the following direct sum decomposition
$
  T^(*CC)M = T^(*1,0)M plus.circle T^(*0,1)M.
$
=== Complex Differential Forms <complex-differential-forms>

#definition[Complex Differential Form][
  A #strong[complex differential form of total degree $k$] on a complex manifold $M$ is a smooth section of the holomorphic vector bundle $and^k T^*M$. The space of all complex differential $k$-forms on $M$ is denoted by
  $
    cal(E)^k (M) := Gamma lr((and^k T^(*CC)M)).
  $
  And the space of all complex differential forms on $M$ is defined as the following graded algebra
  $
    cal(E) (M) := plus.circle.big_(k = 0)^n cal(E)^k (M).
  $
]

#definition[Bigraded Structure on $cal(E)(M)$][
  Suppose $M$ is a complex manifold of complex dimension $n$. Define the space of #strong[$(1,0)$-forms] on $M$ as
  $
    Omega^(1,0) (M) := Gamma lr((T^(*1,0)M)).
  $
  and the space of #strong[$(0,1)$-forms] on $M$ as
  $
    Omega^(0,1) (M) := Gamma lr((T^(*0,1)M)).
  $
  Now define the space of #strong[$(p,q)$-forms] on $M$ as
  $
    Omega^(p,q) (M) := (and^p Omega^(1,0) (M)) and.big (and^q Omega^(0,1) (M)).
  $
  Then we have the following direct sum decomposition
  $
    cal(E)^k (M) = plus.circle.big_(p+q=k) Omega^(p,q) (M)=Omega^(k,0) (M) plus.circle Omega^(k-1,1) (M) plus.circle dots.h.c plus.circle Omega^(0,k) (M),
  $
  which induces a bigraded structure on $cal(E)(M)$
  $
    cal(E) (M) = plus.circle.big_(p,q) Omega^(p,q) (M).
  $

]

#definition[Holomorphic $k$-Form][
  A #strong[holomorphic $k$-form] on a complex manifold $M$ is a holomorphic section of the complex vector bundle $and^k T^(*1,0)M$. Or equivalently, a holomorphic $k$-form on $M$ is smooth section in $Omega^(k,0) (M)$ which is also holomorphic.
]

#definition[Dolbeault Operators][
  Let $M$ be a complex manifold of complex dimension $n$. Let
  $
    d^((k)) : cal(E)^k (M) arrow.r cal(E)^(k+1) (M)
  $
  be the exterior derivative and
  $
    pi^(p,q) : cal(E)^k (M) arrow.r Omega^(p,q) (M)
  $
  be the natural projection. Suppose
  $
    omega = sum_(lr(|I|) = p \, lr(|J|) = q) med f_(I J) thin d z^I and d macron(z)^J in Omega^(p , q)(M)
  $
  is a $(p,q)$-form on $M$, where $I ,J in ZZ_(g>=0)^n$ are multi-indices.

  Define the #strong[Dolbeault operators] as $partial^(p,q)= pi^(p+1,q) compose d^((p+q))$
  $
    partial^(p,q): Omega^(p,q) (M) &--> Omega^(p+1,q) (M)\
    omega & arrow.bar.long sum_(j=1)^n frac(partial f_(I J), partial z^j) thin d z^j and omega = sum_(lr(|I|=p) \, lr(|J|=q)) sum_(j=1)^n frac(partial f_(I J), partial z^j) thin d z^j and d z^I and d macron(z)^J,
  $
  and $macron(partial)^(p,q)= pi^(p,q+1) compose d^((p+q))$
  $
    macron(partial)^(p,q): Omega^(p,q) (M) &--> Omega^(p,q+1) (M)\
    omega & arrow.bar.long sum_(j=1)^n frac(partial f_(I J), partial macron(z)^j) d macron(z)^j and omega = sum_(lr(|I|=p) \, lr(|J|=q)) sum_(j=1)^n frac(partial f_(I J), partial macron(z)^j) d macron(z)^j and d z^I and d macron(z)^J.
  $


]

#proposition[][
  The Dolbeault operators $partial^(p,q)$ and $macron(partial)^(p,q)$ satisfy the following properties

  - $partial compose partial = macron(partial) compose macron(partial) = partial compose macron(partial) + macron(partial) compose partial = 0$

  - $d|_(Omega^(p,q) (M)) = partial + macron(partial)$ .
]

#definition[Dolbeault Complex][
  The #strong[Dolbeault complex] of a complex manifold $M$ is the bigraded complex $Omega^(bullet,bullet) (M)$ with the differential operator $partial$ and $macron(partial)$.
]




== Riemann Surface <Riemann-surface>
#definition[Riemann Surface][
  A #strong[Riemann surface] is a connected complex manifold of dimension one.
]
For manifolds, connectedness and path-connectedness are equivalent. So every Riemann surface is path-connected.

#example[Complex Plane $bb(C)$][
  $bb(C)$ is a Riemann surface with the atlas $lr({lr((bb(C) , upright("id")))})$. Any open subset $U subset.eq bb(C)$ is
  also a Riemann surface with the atlas $lr({lr((U , upright("id")))})$. Some interesting cases are the unit disc $bb(D) = { z in bb(C) : lr(|z|) < 1 }$,
  the upper half-plane $bb(H) = { z in bb(C) : "Im" z > 0 }$ and the punctured complex plane $bb(C)^(\*) = bb(C) - { 0 }$.
]
#example[Riemann Sphere][
  The #strong[Riemann sphere] is the one-point compactification of $bb(C)$, denoted by $hatCC = bb(C) union { oo }$. It is
  a Riemann surface with the following two charts: $   & U_1 = bb(C) , quad phi_1 lr((z))= z\
    & U_2 = hatCC - { 0 } , quad phi_2 lr((z)) = cases(delim: "{", 1 \/ z & upright("if ") z eq.not oo, 0 & upright("if ") z = oo) $

  $hatCC$ is smoothly homeomorphic to the sphere $S^2$ through the stereographic projection
  $
    pi : S^2 &-->hatCC\
    (X,Y,Z) & arrow.r.bar.long (X + i Y) / (1 - Z)\
    (frac(2 x, x^2 + y^2 + 1) , frac(2 y, x^2 + y^2 + 1) , frac(x^2 + y^2 - 1, x^2 + y^2 + 1))
    & arrow.l.bar.long x+i y
  $
]
#align(center)[
  #cetz.canvas(
    length: 0.95cm,
    {
      import cetz.draw: *
      scale(200%)
      set-style(stroke: (paint: luma(40%), thickness: 1.2pt))

      let radius = 1.5
      let dash_pattern = (0.4em, 0.25em)
      let dash_stroke = (paint: rgb("#0fcdae"), dash: dash_pattern, cap: "round")
      let point_radius = 0.05

      let h_line = line((-3.2, 0), (3.2, 0), stroke: navy + 2pt)
      let circ = circle((0, 0), radius: radius, stroke: rgb("#6bb3ff") + 2pt)

      let circle_point_style = (radius: point_radius, stroke: 0.9pt + luma(45%), fill: red.desaturate(10%))

      let line_point_style = (radius: point_radius, stroke: 0.9pt + luma(45%), fill: rgb("#ff8b6c"))


      intersections(
        "sect_left",
        {
          h_line
          line((0, radius), (240deg, radius), stroke: dash_stroke)
        },
      )
      circle("sect_left.0", ..line_point_style)

      intersections(
        "sect_right",
        {
          circ
          line((0, radius), (3, 0), stroke: dash_stroke)
        },
      )
      circle("sect_right.1", ..circle_point_style, name: "right_intersection")
      circle((3, 0), ..line_point_style)

      circle((240deg, radius), ..circle_point_style) // left circle point

      circle((0, radius), radius: point_radius, fill: luma(80%), name: "north pole")

      content("right_intersection", anchor: "south-west", padding: .12, [$P=(X,Y,Z)$])

      content((3, 0), anchor: "north", padding: .25, [$pi(P)$])
    },
  )
]



#example[Complex Projective Line][
  The #strong[complex projective line] $bb(P)^1 lr((bb(C)))$ is the set of all complex lines through the origin in $bb(C)^2$.
  It is a Riemann surface with the following two charts: $   & V_1 = lr({lr([z_0 : z_1]) mid(|) z_0 eq.not 0}) , quad psi_1 lr((z_0 , z_1)) = z_1 \/ z_0\
    & V_2 = lr({lr([z_0 : z_1]) mid(|) z_1 eq.not 0}) , quad psi_2 lr((z_0 , z_1)) = z_0 \/ z_1 $
]
#proposition[$hatCC$ is isomorphic to $bb(P)^1 lr((bb(C)))$][
  The map $f : hatCC arrow.r bb(P)^1 lr((bb(C)))$ $ f lr((x)) = cases(delim: "{", lr([1 : x]) & upright("if ") x eq.not oo, lr([0 : 1]) & upright("if ") x = oo) $ is
  a biholomorphism.
]<riemann_sphere_isomorphic_to_complex_projective_line>
#proof[
  It is clear that $f$ is bijective. We only need to check that the transition functions are holomorphic. For any $z in phi_1 lr((U_1)) = bb(C)$, $ psi_1 circle.stroked.tiny f circle.stroked.tiny phi_1^(- 1) lr((z)) = psi_1 circle.stroked.tiny f lr((z)) = psi_1 lr((lr([1 : z]))) = z , $ which
  implies $psi_1 circle.stroked.tiny f circle.stroked.tiny phi_1^(- 1) = upright(i d)_(bb(C))$ For any $z in phi_2 lr((U_2)) = bb(C)$,
  if $z eq.not 0$, then $ psi_2 circle.stroked.tiny f circle.stroked.tiny phi_2^(- 1) lr((z)) = psi_2 circle.stroked.tiny f lr((1 / z)) = psi_2 lr((lr([1 : 1 \/ z]))) = z . $ And
  if $z = 0$, then $ psi_2 circle.stroked.tiny f circle.stroked.tiny phi_2^(- 1) lr((0)) = psi_2 circle.stroked.tiny f lr((oo)) = psi_2 lr((lr([0 : 1]))) = 0 . $ This
  implies $psi_2 circle.stroked.tiny f circle.stroked.tiny phi_2^(- 1) = upright(i d)_(bb(C))$. Therefore, $f$ is a
  biholomorphism.
]

#proposition[$DD$ is isomorphic to $HH$][
  The map
  $
    f: DD &--> HH \
    z &arrow.long.bar (z+i) / (i z+1)
  $
  is a biholomorphism and has the inverse
  $
    f^(- 1): HH &--> DD \
    w &arrow.long.bar (i w+1) / (w+i)
  $
]


#example[Affine Hyperelliptic Curves][
  Consider first the algebraic equation
  $ y^2 = product_(k = 1)^(2 g + 1) lr((x - a_k)), $
  where $lr({a_k})_(k = 1)^(2 g + 1)$ is a collection of $2 g + 1$ distinct complex numbers, and let $ accent(S, circle) = lr({lr((x , y)) in bb(C)^2 thin mid(|) thin y^2 = product_(k = 1)^(2 g + 1) lr((x - a_k))}) . $ $accent(S, circle)$ is
  called an #strong[affine hyperelliptic curve]. It is a Riemann surface with the following charts

  - If $P_alpha = lr((x_alpha , y_alpha)) in accent(S, circle)$ satisfies $y_alpha eq.not 0$, there exists $epsilon.alt_alpha > 0$ such
    that for any $k in { 1 , 2 , dots.h.c , 2 g + 1 }$, $ lr((a_k , 0)) in.not B_(accent(S, circle)) lr((P_alpha , epsilon.alt_alpha)) = lr(
      {lr((x , y)) in accent(S, circle) thin mid(|) thin lr(|x - x_alpha|)^2 + lr(|y - y_alpha|)^2 < epsilon.alt_alpha^2}
    ) $ Let $U_alpha = B_(accent(S, circle)) lr((P_alpha , epsilon.alt_alpha))$ and we can check that $ phi_alpha : U_alpha & --> bb(C)\
    lr((x , y))         & arrow.r.long.bar x . $ is holomorphic and has inverse $ phi_alpha^(- 1) lr((x)) = lr((x , sqrt(product_(k = 1)^(2 g + 1) lr((x - a_k))) #h(0em))) , $ where
    the branch of the square root is chosen so that its value at $x_alpha$ is $y_alpha$ instead of $- y_alpha$.

  - If $lr((a_j , 0)) in accent(S, circle)$ for some integer $j in lr([1 , 2 g + 1])$, there exists $epsilon.alt_j > 0$ such
    that $ a_k in.not B_(bb(C)) lr((a_j , epsilon.alt_j^2)) = lr({x in bb(C) thin mid(|) thin lr(|x - a_j|) < epsilon.alt_j^2}) , quad forall k eq.not j , $ which
    implies for all $z in B_(bb(C)) lr((0 , epsilon.alt_j)) = lr({x in bb(C) thin mid(|) thin lr(|x|) < epsilon.alt_j})$, $ lr(|z^2 + a_j - a_k|) gt.eq lr(|a_j - a_k|) - lr(|z^2|) > epsilon.alt_j^2 - epsilon.alt_j^2 = 0 , quad forall k eq.not j . $ Let $V_j = B_(bb(C)) lr((0 , epsilon.alt_j))$ and
    we can check that $ psi_j : V_j & --> accent(S, circle)\
    z           & arrow.r.long.bar lr((a_j + z^2 , z sqrt(product_(k eq.not j) lr((z^2 + a_j - a_k))))) $ is holomorphic
    with any choice of the branch of the square root. Given $z_1 , z_2 in V_j$, if $psi_j lr((z_1)) = psi_j lr((z_2))$, then $a_j + z_1^2 = a_j + z_2^2$,
    which implies $z_1 = z_2$. Hence $psi_j$ is injective and is a biholomorphism onto its image. So we can take
    $ (U_j, phi_j) = (psi_j lr((V_j)), psi_j^(- 1)) $
    as a chart. (Note we cannot set the first coordinate simply as $a_j + z$, because it would enforce a branch cut from the
    square root to intrude into the disk $B_(bb(C)) lr((0 , epsilon.alt_j))$, thereby disrupting the holomorphicity of $psi$.)

  we can check that $ phi_alpha circle.stroked.tiny phi_j^(- 1) lr((z)) = a_j + z^2 , $ which is holomorphic. Therefore, $accent(S, circle)$ is
  a Riemann surface.
]

#theorem[Identity Theorem][
  Suppose $X$ and $Y$ are Riemann surfaces and $f_1, f_2: X arrow Y$ are two holomorphic mappings which coincide on a set $A subset.eq X$,
  where $A$ has a limit point $a in X$. Then $f_1=f_2$ on $X$.
]
#proof[
  Let
  $
    G= {x in X | "there exists an open neighborhood" N "of" x "such that" f_1|_N = f_2|_N}.
  $
  We first show that $a in G$. Choose chart $(U , phi)$ centered at $a$ and chart $(V , psi)$ centered at $f_1(a)$, and
  suppose $f_1$ and $f_2$ have local expressions $F_1$ and $F_2$ in these charts. By the identity theorem for holomorphic
  functions, we have $F_1=F_2$ on $phi(U)$. Thus $f_1|_U=f_2|_U$ on $U$, which implies $a in G$.

  Then we show $G$ is open. If $x in G$, then there exists an open neighborhood $N$ of $x$ such that $f_1|_N = f_2|_N$. So
  we have $x in N subset.eq G$, which implies $G$ is open.

  We claim that $G$ is also closed. Suppose $b in partial G$. Since $f_1$ and $f_2$ are continuous, we have $f_1(b)=f_2(b)$.
  Now choose chart $(tilde(U), phi)$ centered at $b$ and chart $(tilde(V), psi)$ centered at $f_1(b)$, and suppose $f_i$ have
  local expressions $tilde(F)_i$ in this chart. Note that $b in partial G$ implies $tilde(U) inter G$ is a nonempty open
  set. Thus there exists $g in tilde(U) inter G$ and an open neighborhood $M$ of $g$ such that $M subset.eq tilde(U)$ and $f_1|_M=f_2|_M$.
  Since $phi(M)$ is an open set in $bb(C)$ and $F_1|_(phi(M))=F_2|_(phi(M))$, by the identity theorem for holomorphic
  functions, we have $F_1=F_2$ on $phi(tilde(U))$. Thus $f_1|_(tilde(U))=f_2|_(tilde(U))$ on $tilde(U)$. Hence $b in G$ and $G$ is
  closed. Since $X$ is connected and $G$ is a both open and closed nonempty subset of $X$, we have $G=X$. Therefore, $f_1=f_2$ on $X$.
]

== Meromorphic Functions <meromorphic-functions>
#definition[Meromorphic Functions][
  Let $X$ be a Riemann surface. A function on $f : X arrow.r hatCC$ is called #strong[meromorphic at $x in X$] if there is
  a chart $lr((U , phi))$ containing $x$ such that $f circle.stroked.tiny phi^(- 1)$ is meromorphic at $phi lr((x))$. The
  function $f$ is called #strong[meromorphic on $X$] if it is meromorphic at every point of $X$.
]
#definition[Singularity][
  Singularity Let $f$ be holomorphic in a punctured neighborhood of $p in$ $X$.

  - We say $f$ has a #strong[removable singularity] at $p$ if and only if there exists a chart $phi.alt : U arrow.r V$ with $p in U$,
    such that the composition $f circle.stroked.tiny phi.alt^(- 1)$ has a removable singularity at $phi.alt lr((p))$.

  - We say $f$ has a #strong[pole] at $p$ if and only if there exists a chart $phi.alt : U arrow.r V$ with $p in U$, such
    that the composition $f circle.stroked.tiny phi.alt^(- 1)$ has a pole at $phi.alt lr((p))$.

  - We say $f$ has an #strong[essential singularity] at $p$ if and only if there exists a chart $phi.alt : U arrow.r V$ with $p in U$,
    such that the composition $f circle.stroked.tiny phi.alt^(- 1)$ has an essential singularity at $phi.alt lr((p))$.
]

#pagebreak()

= Holomorphic Maps <holomorphic-maps>
== Local Structure of Holomorphic Maps <local-structure-of-holomorphic-maps>



#theorem[Local Expression of Holomorphic Map][
  Let $f : X arrow.r Y$ be a non-constant holomorphic map of Riemann surfaces. For any $x in X$ there are charts centered
  at $x , f lr((x))$, such that the local expression of $f$ using these charts is $z arrow.r.bar z^k$ for some integer $k gt.eq 1$.
]
#proof[
  Starting from any chart $(U , phi)$ centered at $x$ and any chart
  $(V , psi)$ centered at $f (x)$, we have the local expression of $f$, denoted by $F (z)$. Since $F (0) = 0$, $F$ has
  Taylor expansion at
  $z = 0$:
  $
    F (z) = psi circle.stroked.tiny f circle.stroked.tiny phi^(- 1) (z) = sum_(n = 1)^oo a_n z^n = z^k G (z) , quad ( k gt.eq 1 )
  $
  where $G (z)$ is holomorphic and $G (0) eq.not 0$. Define
  $h (z) = z root(k, G (z))$. $h$ is holomorphic at $z = 0$ and
  $F (z) = h (z)^k$. Then we can define a new chart
  $(tilde(U) , tilde(phi))$ centered at $x$ by
  $tilde(phi) = h circle.stroked.tiny phi$. Let
  $sigma_k : z arrow.r.bar z^k$. Then we have
  $
    tilde(F) (z) = psi circle.stroked.tiny f circle.stroked.tiny tilde(phi)^(- 1) ( z ) = psi circle.stroked.tiny f circle.stroked.tiny phi^(- 1) circle.stroked.tiny h^(- 1) ( z ) = F circle.stroked.tiny h^(- 1) (z) = sigma_k circle.stroked.tiny h circle.stroked.tiny h^(- 1) (z) = sigma_k ( z ) = z^k ,
  $
  which is the local expression of $f$ using these charts.
]

#corollary[Holomorphic Maps are Open][
  Let $f : X arrow.r Y$ be a non-constant holomorphic map of Riemann surfaces. Then $f$ is an open map.
]
#proof[
  For any point $x in X$, there are chart $(U , phi)$ centered at $x$ and chart $(V , psi)$ centered at $f (x)$ such that $psi circle.stroked.tiny f circle.stroked.tiny phi^(- 1) (z) = z^k$.
  Since $z^k$ is an open map, $f|_(U)$ is composition of open maps and hence open. For any open neighborhood $N$ of $x$, $f (U inter N)$ is
  a neighborhood of $f (x)$. Therefore, $f$ is open.
]
#corollary[Injective Holomorphic Maps are Biholomorphisms onto Their Images][
  Let $f : X arrow.r Y$ be a holomorphic map of Riemann surfaces. If $f$ is injective, then $f:X arrow f(X)$ is a
  biholomorphism.
]
#proof[
  For any point $x in X$, there are charts centered at $x$ and $f(x)$ such that the local expression of $f$ is $psi circle.stroked.tiny f circle.stroked.tiny phi^(- 1) (z) = z^k$.
  Since $f$ is injective, $k = 1$. Therefore, $f^(-1): f(X) arrow.r X$ has the local expression $phi circle.stroked.tiny f^(-1) circle.stroked.tiny psi^(- 1) (z) = z$,
  which means $f^(-1)$ is holomorphic at $f(x)$. Therefore, $f^(-1)$ is holomorphic on $f(X)$ and $f$ is a biholomorphism.
]

#lemma[
  Let $f : X arrow.r Y$ be a non-constant holomorphic map of Riemann surfaces, and $x in X$. Suppose that $f$ has two
  local expressions around $x$ of the form $F lr((z)) = z^k$ and $tilde(F) lr((tilde(z))) = tilde(z)^(tilde(k))$. Then $k = tilde(k)$.
]
#definition[Ramification Index][
  Let $f : X arrow.r Y$ be a non-constant holomorphic map of Riemann surfaces, and $x in X$. If there are charts centered
  at $x , f lr((x))$ such that the local expression of $f$ using these charts is $F lr((z)) = z^(k_x)$, then the positive
  integer $k_x$ is called the #strong[ramification index] of $f$ at $x$. We distinguish two cases:

  - If $f$ has ramification index $k_x = 1$, we say $f$ is #strong[unramified] at $x$.

  - If $f$ has ramification index $k_x gt.eq 2$. we say $f$ is #strong[ramified] at $x$. The point $x$ is called a #strong[ramification point] of $f$.

  The set of ramification points of $f$ is called the #strong[ramification locus] of $f$ and is denoted by $upright(R a m)_X lr((f))$,
  or simply $upright(R a m) lr((f))$.
]
#example[Ramification Index of Meromorphic Functions][
  Let $f : X arrow.r hatCC$ be a non-constant meromorphic function on Riemann surface $X$.

  - If $x in X$ is a zero of $f$, then the ramification index $k_x$ equals the order of zero of $f$ at $x$.

  - If $x in X$ is a pole of $f$, then the ramification index $k_x$ equals the order of pole of $f$ at $x$.
]
#proof[
  Suppose $x$ is a pole of order $k$ of $f$. Then there exists a chart
  $(U , phi)$ centered at $x$ such that
  $ f circle.stroked.tiny phi^(- 1) = z^(- k) $ for some positive number
  $k$. Choose a chart
  $
    & V = hatCC - {0} , quad psi (z) = cases(delim: "{", 1 \/ z & upright("if ") z eq.not oo, 0 & upright("if ") z = oo)
  $
  centered at $f (x)$. Since the local expression of $f$ under the charts
  $(U , phi)$ and $(V , psi)$ is
  $ F (z) = psi circle.stroked.tiny f circle.stroked.tiny phi^(- 1) (z) = z^k , $
  we see the ramification index of $f$ at $x$ is $k$. The case when $x$ is a zero of $f$ is similar.
]
#definition[Branch Point][
  Let $f : X arrow.r Y$ be a non-constant holomorphic map of Riemann surfaces. If $x$ is a ramification point of $X$, then $f lr((x))$ is
  called a #strong[branch point] of $f$. The set of all branch points of $f$ is called the #strong[branch locus] of $f$.
]
#lemma[
  Let $f : X arrow.r Y$ be a non-constant holomorphic map of Riemann surfaces, and $x_0 in X$. There is a neighborhood $U$ of $x_0$ such
  that $k_x = 1$ for all any $x in U - { x_0 }$.
]
#corollary[
  Ramification Locus $upright(R a m) lr((f))$ is Discrete
][
  The ramification locus $upright(R a m)_X lr((f))$ is a discrete subset of $X$. In other words, there exist open sets $U_i subset.eq X$ such
  that each $U_i$ contains exactly one $x in upright(R a m)_X lr((f))$.
]

#corollary[
  If $X$ is a compact Riemann surface and $f : X arrow.r Y$ is a nonconstant holomorphic map of Riemann surfaces, then the
  ramification locus is a finite set. Since the branch locus of $f$ is the image of $upright(R a m) lr((f))$ via $f$, the
  branch locus is also a finite set.
]
#proof[
  A discrete subset of a compact topological space is finite.
]
== Holomorphic Maps of Compact Riemann Surfaces <holomorphic-maps-of-compact-riemann-surfaces>
#theorem[
  Surjectivity of Holomorphic Maps of Compact Riemann Surfaces
][
  Let $f : X arrow.r Y$ be a holomorphic map of Riemann surfaces with $X$ compact. If $f$ is non-constant, then $f$ is
  surjective and $Y$ is compact.
]
#proof[
  Assume that $f$ is non-constant, and consider the image
  $f (X) subset.eq Y$ : by Liouville’s theorem it is an open set in $Y$. On the other hand, since $X$ is compact and $f$ continuous, $f (X)$ is
  a compact subset of a Hausdorff topological space and therefore it is closed. Finally, since $f (X)$ is an open, closed
  and nonempty subset of a connected topological space, it follows that $f (X) = Y$. Since continuous maps send compact
  sets to compact sets, $Y$ is compact.
]
#proposition[
  Let $f : X arrow.r Y$ be a non-constant holomorphic map of compact Riemann surfaces. If $y_0 , y_1 in Y$ are not in the
  branch locus of $f$, then $lr(|f^(- 1) lr((y_0))|) = lr(|f^(- 1) lr((y_1))|)$.
]
#definition[
  Degree of Holomorphic Map of Compact Riemann Surfaces
][
  Let $f : X arrow.r Y$ be a holomorphic map of compact Riemann surfaces. If $f$ is non-constant, for any $y in Y - f lr((upright(R a m) lr((f))))$ that
  is not a branch point, the number $lr(|f^(- 1) lr((y))|)$ is constant and called the #strong[degree] of $f$ at $y$ and
  is denoted by $deg lr((f))$. If $f$ is constant, we define $deg lr((f)) = 0$.
]
#proposition[
  Let $f : X arrow.r Y$ be a non-constant holomorphic map of compact Riemann surfaces. Then for any $y in Y$,
  $ deg lr((f)) = sum_(x in f^(- 1) lr((y))) k_x. $
]
#corollary[
  Let $f : X arrow.r hatCC$ be a non-zero meromorphic function on a compact Riemann surface $X$. Counting multiplicities,
  the number of poles of $f$ is equal to the number of zeros of $f$.
]
#proof[
  Since $ sum_(x in f^(- 1) lr((0))) k_x = sum_(x in f^(- 1) lr((oo))) k_x , $ we have $ sum_(x upright("is a zero")) upright("multiplicity of ") x = sum_(x upright("is a pole")) upright("multiplicity of ") x . $
]
#theorem([Riemann-Hurwitz Formula])[
  Let $f : X arrow.r Y$ be a nonconstant, degree $d$, holomorphic map of compact Riemann surfaces. Denote the genus of $X$ by $g_X$ and
  the genus of $g_Y$. Then $ 2 g_X - 2 = lr((2 g_Y - 2)) deg lr((f)) + sum_(x in upright(R a m) lr((f))) lr((k_x - 1)) , $ where $k_x$ is
  the ramification index of $f$ at $x$.
]
#proof[
  Let $Gamma_Y$ be a good graph on $Y$ with $f lr((upright(R a m)_X lr((f)))) subset.eq V_(Gamma_Y)$: the branch locus of $f$ is
  contained in the vertex set of $Gamma_Y$. Define $Gamma_X$ to be the "lift" of $Gamma_Y$ via the map $f$ : the support
  of $Gamma_X$ is $f^(- 1) lr((Gamma_Y))$ and the vertices, edges and faces of $Gamma_X$ are the connected components of
  the inverse images of vertices, edges and faces of $Gamma_Y$. Note
  $
    deg lr((f)) = sum_(x in f^(- 1) lr((y))) k_x = lr(|f^(- 1) lr((y))|) + sum_(x in f^(- 1) lr((y))) lr((k_x - 1)).
  $
  We can obtain the following equations by counting the number of vertices, edges and faces of $Gamma_X$ and $Gamma_Y$:
  $
    lr(|V_(Gamma_X)|) & = sum_(y in Gamma_Y) lr(|f^(- 1) lr((y))|) = sum_(y in V_(Gamma_Y)) deg lr((f)) - sum_(y in V_(Gamma_Y)) sum_(x in f^(- 1) lr((y))) lr((k_x - 1)) = deg lr((f)) lr(|V_(Gamma_Y)|) - sum_(x in upright(R a m) lr((f))) lr((k_x - 1)) ,\
    lr(|E_(Gamma_X)|) & = deg lr((f)) lr(|E_(Gamma_X)|) ,\
    lr(|F_(Gamma_X)|) & = deg lr((f)) lr(|F_(Gamma_X)|) .
  $
  Thus we have
  $
    chi lr((X)) & = lr(|V_(Gamma_X)|) - lr(|E_(Gamma_X)|) + lr(|F_(Gamma_X)|)\
    & = deg lr((f)) lr(|V_(Gamma_Y)|) - sum_(x in upright(R a m) lr((f))) lr((k_x - 1)) - deg lr((f)) lr(|E_(Gamma_Y)|) + deg lr((f)) lr(|F_(Gamma_Y)|)\
    & = deg lr((f)) lr((lr(|V_(Gamma_Y)|) - lr(|E_(Gamma_Y)|) + lr(|F_(Gamma_Y)|))) - sum_(x in upright(R a m) lr((f))) lr((k_x - 1))\
    & = deg lr((f)) chi lr((Y)) - sum_(x in upright(R a m) lr((f))) lr((k_x - 1)) .
  $
]
#corollary[
  Suppose that $f : X arrow.r Y$ is a non-constant holomorphic map of compact Riemann surfaces. Then we have

  #block[

    + $sum_(x in X) lr((k_x - 1))$ is even.

    + $g_X gt.eq g_Y$.

    + $f$ is unramified on $X$, namely $sum_(x in X) lr((k_x - 1)) = 0$, if and only if $g_X = g_Y deg lr((f)) - deg lr((f)) + 1$.

    + If $g_Y = 0$ and $g_X > 0$, then $f$ is ramified.

    + If $g_Y = 1 , f$ is unramified if and only if $g_X = 1$.

    + If $f$ is unramified and $g_Y > 1$, then either $g_X = g_Y$ and $deg lr((f)) = 1$, or $g_X > g_Y$.
  ]
]
#proof[
  + $ sum_(x in upright(R a m) (f)) (k_x - 1) = 2 (g_X - 1 - (g_Y - 1) deg (f)) . $

  + $
      2 g_X - 2 = (2 g_Y - 2) deg (f) + sum_(x in upright(R a m) (f)) (k_x - 1) gt.eq (2 g_Y - 2) deg ( f ) gt.eq 2 g_Y - 2 .
    $

  + $f$ is unramified on $X$, if and only if
    $ 2 g_X - 2 = (2 g_Y - 2) deg (f) <==> g_X = g_Y deg (f) - deg (f) + 1 . $

  + If $g_Y = 0$ and $g_X > 0$, then
    $ sum_(x in upright(R a m) (f)) (k_x - 1) = 2 (g_X - 1 + deg (f)) gt.eq 2 g_X > 0 . $

  + If $g_Y = 1$, then
    $ 2 (g_X - 1) = sum_(x in upright(R a m) (f)) (k_x - 1) . $ So $f$ is unramified if and only if $g_X = 1$.

  + Suppose $f$ is unramified and $g_Y > 1$. If $deg (f) = 1$, then
    $g_X = deg (f) (g_Y - 1) + 1 = g_Y$. If $deg (f) > 1$, then
    $ g_X = deg (f) (g_Y - 1) + 1 > g_Y - 1 + 1 = g_Y . $
]
== Holomorphic Function Sheaf <holomorphic-function-sheaf>
#definition[Holomorphic Function Sheaf][
  Let $X$ be a Riemann surface. The #strong[holomorphic function sheaf] $cal(O)_X$ is the sheaf of holomorphic functions
  on $X$. That is, for any open set $U subset.eq X$,
  $
    cal(O)_X lr((U)) = lr({f : U arrow.r bb(C) thin mid(|) thin f "is holomorphic"}).
  $
]
#proposition[Holomorphic Function Sheaf on Compact Riemann Surface][
  Let $X$ be a compact Riemann surface. Then the only holomorphic functions on $X$ are the constant functions, i.e. $cal(O)_X lr((X)) = bb(C)$.
]
== Meromorphic Functions <meromorphic-functions-1>
#definition[Meromorphic Function Field][
  Let $X$ be a Riemann surface and $U$ be an open set of $X$. The #strong[meromorphic function field] on $U$ is the field
  of meromorphic functions on $U$, denoted by $cal(M)_X lr((U))$ or simply $cal(M)lr((U))$.
]
#proposition[][
  Let us denote by $c_P in op("Hom") lr((X , hatCC))$ the constant morphism $c_P : x arrow.r.bar P$. Then $ cal(M)lr((X)) = op("Mor") lr((X , hatCC)) - lr({c_oo}) . $
]
#proposition[][
  Let $X$ be a Riemann surface and $U$ be an connected non-compact open set of $X$. Then $ cal(M)lr((U)) = op("Frac") lr((cal(O)_X lr((U)))) . $
]
#proposition[GAGA for Compact Riemann Surfaces][
  Let $X$ be a compact Riemann surface. Then the meromorphic function field $cal(M)lr((X))$ is the field of rational
  functions $K lr((X))$. $ cal(M)lr((X)) = K lr((X)) . $ Especially, we $hat(CC, size: #1em)$ have $cal(M)lr((hatCC)) = bb(C) lr((z))$.
]
#definition[Order of Meromorphic Function][
  Let $X$ be a Riemann surface and $f$ is meromorphic at $x in X$. Let $lr((U , phi))$ be a chart containing $x$ such that $f circle.stroked.tiny phi^(- 1)$ is
  meromorphic at $phi lr((x))$. Suppose the Laurent expansion of $f circle.stroked.tiny phi^(- 1)$ at $phi lr((x))$ is $ f circle.stroked.tiny phi^(- 1) = sum_(n = - oo)^oo a_n lr((z - phi lr((x))))^n . $ Then
  the #strong[order of $f$ at $x$] is defined as $ "ord"_p lr((f)) = inf lr({n mid(|) a_n eq.not 0}) . $ Note that the
  order of $f$ at $x$ is independent of the choice of chart containing $x$.
]
#proposition[Order is a Valuation][
  Let $X$ be a Riemann surface and $f$ is meromorphic at $p in X$. Then the order of $f$ at $p$
  $
    op("ord")_p : cal(M)_(X , p) & --> bb(Z) union { oo }\
    f & arrow.r.long.bar op("ord")_p lr((f))
  $
  is a valuation on $cal(M)_(X , p)$. That is, for any $f , g in cal(M)_(X , p)$,
  we have

  - $"ord"_p lr((f)) = oo$ if and only if $f = 0$.

  - $"ord"_p lr((f g)) = "ord"_p lr((f)) + "ord"_p lr((g))$.

  - $"ord"_p lr((f + g)) gt.eq min lr({"ord"_p lr((f)) , "ord"_p lr((g))})$.
]
#proposition[Relation between Order and Ramification Index][
  Let $f$ be a meromorphic function on a Riemann surface $X$ and $x in X$. Then $ upright(o r d)_x lr((f)) = cases(
    delim: "{",
    0 & upright("if ") f upright(" is holomorphic at ") x upright(" and ") f lr((a)) eq.not 0,
    k_x & upright("if ") f upright(" has a zero of multiplicity ") k_x upright(" at ") x,
    - k_x & upright("if ") f upright(" has a pole of multiplicity ") k_x upright(" at ") x,
    oo & upright("if ") f equiv 0,

  ) $
]

== Differential Forms <differential-forms>

// #definition[Holomorphic Tangent Space][
//   Let $X$ be a Riemann surface. We define $T_p^\mathbb{R}M$ as the tangent space of the underlying smooth manifold, and define $T_pM:=T_p^\mathbb{R}M\otimes \mathbb{C}$.
// ]

#definition[Holomorphic Differential Forms][
  Let $X$ be a Riemann surface. A #strong[differential form of degree $k$] on $X$ is a section of the $k$-th exterior power of
  the holomorphic cotangent bundle $T^(*1,0)X:=(T^(1,0) X)^*$. The space of all differential forms of degree $k$ on $X$ is denoted by
  $
    Omega^(k,0)_X = Gamma(X,  and^k (T^(*1,0)X)).
  $
]

#definition[Holomorphic 1-Forms][
  Let $X$ be a Riemann surface. A #strong[holomorphic 1-form] on $X$ is a holomorphic form of degree 1. The space of all holomorphic 1-forms on $X$ is denoted by
  $
    Omega^(1,0)_X = Gamma(X, T^(*1,0) X).
  $
]
#remark[
  If $(U,z)$ is a holomorphic chart on $X$, then any holomorphic 1-form $omega$ on $X$ can be written as
  $
    omega = f dif z
  $
  for some holomorphic function $f$ on $U$. More explicitly, $omega$ is a map
  $
    omega: U &--> T^(*1,0) X \
    p & arrow.bar.long f(z(p)) dif z.
  $


  Let ${(U_alpha,z_alpha)}$ be a holomorphic atlas on $X$. A holomorphic 1-from can be alternatively defined as a collection of holomorphic functions ${f_alpha:z_alpha (U_alpha)->CC}$ such that if $U_alpha inter U_beta eq.not emptyset$, then
  $
    f_beta (z_beta (p)) = f_alpha (z_alpha (p))T'(z_beta (p))= f_alpha (T(z_beta (p)))T'(z_beta (p)), quad forall p in U_alpha inter U_beta,
  $
  where $T= z_alpha circle.stroked.tiny z_beta^(-1)$ is the transition function. The above condition guarantees
  $
    dif z_alpha = T' dif z_beta
  $
  so that we have invariance of the 1-form under the change of coordinates
  $
    f_alpha dif z_alpha = f_beta dif z_beta.
  $
]

#definition[Order of Holomorphic 1-Form][
  Let $X$ be a Riemann surface and $omega$ be a holomorphic 1-form on $X$. The #strong[order of $omega$ at $x$] is defined as
  $
    "ord"_x lr((omega)) = "ord"_x lr((f))
  $
  where $omega = f dif z$ in a chart $(U,z)$ centered at $x$.
]
#remark[
  We need to check that the definition of the order of a holomorphic 1-form is independent of the choice of chart. This follows from that any transition function $T$ is holomorphic and $T'$ is nonzero.
]

#theorem[Poincare Lemma][
  Let $X$ be a Riemann surface and $omega in cal(E)^(med 1)(X)$ be a complex 1-form on $X$. Suppose $p in X$ and $dif omega=0$ on a neighborhood of $p$. Then there exists a smooth function $f$ defined on a neighborhood of $p$ such that $omega=dif f$.
]

#theorem[$macron(partial)$-Poincaré Lemma][
  Let $X$ be a Riemann surface and $omega in Omega^(0,1)_X$ be an anti-holomorphic 1-form on $X$. Then on some neighborhood of $p$, there exists a smooth function $f$ such that $omega=macron(partial) f$.
]

== Divisor <divisor>
#definition[Divisor Group][
  Let $X$ be a Riemann surface. The #strong[divisor group] of $X$ is the free abelian group generated by the points of $X$,
  denoted by $ op("Div") lr((X)) = ZZ^(plus.circle X)$. An element of $op("Div") lr((X))$ is called a #strong[divisor] on $X$.
  A divisor $D$ on $X$ can be written as $ D = sum_(x in X) n_x x. $
]
#definition[Degree of a Divisor][
  Let $X$ be a Riemann surface. The degree homomorphism is defined as
  $
    deg : op("Div") lr((X)) & --> bb(Z)\
    D = sum_(x in X) n_x x & arrow.r.long.bar sum_(x in X) n_x .
  $
  It can be defined by the universal property of free abelian Group

  #commutative_diagram($
    op("Div") lr((X)) edge(deg, "-->") & ZZ \
    X edge("u", iota, ->, #left) edge("ur", c_1, ->, #right)
  $)

  where $c_1 : x |-> 1$ is a constant mapping. $deg (D)$ is called the #strong[degree] of $D$. The kernel of $deg$ is
  denoted by
  $"Div"^0 (X)$ and called the #strong[divisor group of degree zero];. So we have the exact sequence

  #commutative_diagram($
    0 edge(->) & op("Div")^0 lr((X)) edge(->) & op("Div") lr((X)) edge(deg, ->) & bb(Z) edge(->) & 0
  $)
]


#definition[
  Principal Divisors: Divisors from Meromorphic Functions
][
  Let $X$ be a Riemann surface and $f$ be a nonzero meromorphic function on $X$. We have the following abelian group
  homomorphism:
  $
    op("div") : cal(M) lr((X))_(!0) & --> op("Div") lr((X))\
    f & arrow.long.bar sum_(x in X) "ord"_x lr((f)) x .
  $
  The #strong[divisor of $f$] defined as $op("div") (f)$. Any divisor of this form is called a #strong[principal divisor] on $X$.
  The group of principal divisors on $X$ is denoted by $op("PDiv") lr((X))= op("div")lr((cal(M) lr((X))_(!0)))$.
]

#proposition[Principal Divisors on Compact Riemann Surfaces][
  Let $X$ be a compact Riemann surface and $f$ be a nonzero meromorphic function on $X$. Then

  + $deg lr((upright(d i v) lr((f)))) = 0$ and $op("PDiv") lr((X)) subset.eq op("Div")^0 lr((X))$.

  + $op("div")(f)=0$ if and only if $f$ is a constant function.
]
#proof[
  $op("div")(f)=0$ implies that $f$ is holomorphic on $X$. Since $X$ is compact, $f$ is a constant function. The converse
  is trivial.
]
#definition[Picard group][
  Let $X$ be a Riemann surface. The #strong[Picard group] of $X$ is defined as $ op("Pic") lr((X)) = op("Div") lr((X)) \/ op("PDiv") lr((X)) . $
  And we have the exact sequence

  #commutative_diagram($
    cal(M) lr((X))_(!0) edge(op("div"), ->) & op("Div") lr((X)) edge(->) & op("Pic") lr((X)) edge(->) & 0
  $)

  For compact Riemann surfaces $X$, the #strong[restricted Picard group] of $X$ is defined as $ op("Pic")^0 lr((X)) = op("Div")^0 lr((X)) \/ op("PDiv") lr((X)) . $
  And we have the exact sequence

  #commutative_diagram($
    1 edge(->)& CC^* edge(->) &cal(M) lr((X))_(!0) edge(op("div"), ->) & op("Div")^0 lr((X)) edge(->) & op("Pic")^0 lr((X)) edge(->) & 0
  $)
]


#definition[
  Partial Order on $op("Div") lr((X))$
][
  Given $D_1 , D_2 in op("Div") lr((X))$ where $ D_1 = sum_(x in X) n_x x , quad D_2 = sum_(x in X) m_x . $ We define a
  partial order on $op("Div") lr((X))$ by $ D_1 lt.eq D_2 <==> n_x lt.eq m_x , quad forall x in X . $

]
#definition[Canonical Divisor][
  Let $X$ be a Riemann surface and let $omega$ be a meromorphic 1-form on $X$ which is not identically zero. The divisor
  of $omega$ is defined as $ op("div") lr((omega)) = sum_(x in X) "ord"_x lr((omega)) x . $ Any divisor of this form is
  called a #strong[canonical divisor] on $X$. The set of canonical divisors on $X$ is denoted by $"KDiv" lr((X))$.
]
#definition[Complex Vector Space $L lr((D))$][
  Let $X$ be a Riemann surface and $D$ be a divisor on $X$. The #strong[complex vector space $L lr((D))$] is defined as $ L lr((D)) = lr({f in cal(M) lr((X)) thin mid(|) thin f equiv 0 op(" or")"" op("div") lr((f)) gt.eq - D}) , $ called
  the space of meromorphic functions with poles bounded by $D$. The dimension of $L lr((D))$ is denoted as $ell lr((D)) = dim_(bb(C)) L lr((D))$.
]
If $D_1 lt.eq D_2$, then $L lr((D_1)) subset.eq L lr((D_2))$ and $ell lr((D_1)) lt.eq ell lr((D_2))$.

#theorem[Riemann-Roch Theorem][
  Let $X$ be a compact Riemann surface and $D$ be a divisor on $X$. Then $ ell lr((D)) - ell lr((K_X - D)) = deg lr((D)) + 1 - g_X . $
]
#corollary[
  Let $X$ be a compact Riemann surface.
  + $ell lr((K_X)) = g_X$.

  + $deg lr((K_X)) = 2 g_X - 2 = chi lr((X))$.

  +
  $
    ell lr((D)) cases(
    "= 0" & " if " & deg D < 0,
    gt.eq 1 - g + deg D & " if " & 0 lt.eq deg D lt.eq 2 g - 2,
    = 1 - g + deg D & " if " & deg D gt.eq 2 g - 1,

  )
  $
]
#proof[
  + Let $D = 0$. Since $upright(d i m)_(bb(C)) L (0) = 1$, we have
    $ell (0) = 1$.

  + Let $D = K_X$.
]

#pagebreak()

= Classification of Riemann Surfaces <classification-of-riemann-surfaces>
== Simply Connected Riemann Surfaces <simply-connected-riemann-surfaces>
#theorem[Uniformization Theorem][
  Every simply connected Riemann surface is isomorphic to open disk $bb(D)$, complex plane $bb(C)$ or Riemann sphere $hatCC$.
]
=== Complex Plane $bb(C)$ <complex-plane-mathbb-c>
#proposition[
  Automorphism of $bb(C)$
][
  The only automorphisms of $bb(C)$ are affine transformations $ op("Aut") lr((bb(C))) = lr({z |-> a z + b thin mid(|) thin a , b in bb(C)}) . $

]
=== Riemann Sphere $hatCC$ <riemann-sphere-widehatmathbb-c>




#definition[Möbius Transformations][
  A #strong[Möbius transformation] is a map of the form
  $
    T:hatCC &--> hatCC\
    z &arrow.long.bar frac(a z + b, c z + d) ,\
  $
  which corresponds to a projective matrix $T=mat(a, b;c, d) in upright(P G L)_2 lr((bb(C))) tilde.equiv upright(P S L)_2 lr((bb(C))) tilde.equiv upright( S L)_2 lr((bb(C)))\/(plus.minus I)$.
]
#remark[
  Here we abuse the notation and use $T$ to denote both the Möbius transformation $z arrow.bar frac(a z + b, c z + d)$ and the corresponding matrix $mat(a, b;c, d) in op("PSL")_2(lr(bb(C)))$.
]

We can use any matrix in $op("GL")_2(lr(bb(C)))$ to represent a Möbius transformation, since $op("GL")_2(lr(bb(C)))$ acts
on $hatCC$ through the quotient map $op("GL")_2(lr(bb(C))) &arrow.twohead op("PGL")_2(lr(bb(C)))$.

If we use a matrix in $op("SL")_2(lr(bb(C)))$ to represent a Möbius transformation, then we say it is a *normalized
representation* of the Möbius transformation.


#proposition[Inverse of Möbius Transformation][
  The inverse of a Möbius transformation $T(z)=frac(a z + b, c z + d)$ is given by $ T^(- 1)(z)=frac(d z - b, - c z + a) . $
]

#proposition[
  Automorphism of $hatCC$
][The only automorphisms of $hatCC$ are Möbius transformations $ op("Aut") lr((hatCC)) = lr({z arrow.r.bar frac(a z + b, c z + d) thin mid(|) thin a , b , c , d in bb(C) , a d - b c = 1}) tilde.equiv upright(P S L)_2 lr((bb(C))) . $
]
According to @riemann_sphere_isomorphic_to_complex_projective_line, the Riemann sphere $hatCC$ is isomorphic to the
complex projective line $bb(P)^1 lr((bb(C)))$. Therefore, they have the same automorphism group.
#proposition[
  Automorphism of $bb(P)^1 lr((bb(C)))$
][
  The automorphism group of $bb(P)^1 lr((bb(C)))$ is given by $ op("Aut") lr((bb(P)^1 lr((bb(C))))) = lr(
    {vec(Z_0, Z_1) arrow.r.bar mat(a, b;c, d;gap: #1em) vec(Z_0, Z_1) thin mid(|) thin a , b , c , d in bb(C) , a d - b c = 1}
  ) tilde.equiv upright(P S L)_2 lr((bb(C))) . $
]

#proposition[Decomposition of Möbius Transformations][
  Suppose $T(z)=frac(a z + b, c z + d)$ is a Möbius transformation and $c eq.not 0$. Then $T$ can be decomposed as
  $
    T( z )= frac(a z + b, c z + d) =a / c+(b c-a d) / c^2 frac(1, z+d/c) = T_4 circle.stroked.tiny T_3 circle.stroked.tiny T_2 circle.stroked.tiny T_1( z )
  $
  where

  - $T_1(z)=z+d/c$ is a translation,

  - $T_2(z)=1/z$ is the complex inversion,

  - $T_3(z)=(b c-a d)/c^2 z$ is a dilation,

  - $T_4(z)=a/c$ is a translation.
]

#proposition[][
  Nonidentity Möbius transformation has 1 or 2 fixed points.
]
#proof[
  Suppose $T(z)=(a z+b)/(c z+d)$ is a nonidentity Möbius transformation. Then $T(z)=z$ implies
  $
    c z^2+(d-a) z-b=0.
  $

  + If $T=mat(1, b;0, 1)in op("PGL")_2(lr(bb(C)))$ where $b in CC^*$, then $T$ has a single fixed point $z=oo$.

  + If $T=mat(a, b;0, d)in op("PGL")_2(lr(bb(C)))$ where $a ,d in CC^*$ and $a eq.not d$, then $T$ has a two fixed point $z_1=b/(d-a)$ and $z_2=oo$.

  + If $c eq.not 0$, then the equation has two solutions
  $
    z_(1,2) = frac(a-d plus.minus sqrt((d-a)^2+4 b c), 2 c).
  $
  If $(d - a)^2 +4b c = 0 $, then $z_1 = z_2$ and $T$ has a single fixed point. Otherwise, $T$ has two fixed points.
]

#definition[Generalized Circle][
  A #strong[generalized circle] in $hatCC$ is defined as the set
  $
    {z in hatCC thin mid(|) thin c z overline(z) + alpha z + overline(alpha) overline(z) + d = 0}
  $
  where $c , d in bb(R)$ and $alpha in bb(C)$.
]

#proposition[][
  Suppose a generalized circle is defined by
  $ c z overline(z) + alpha z + overline(alpha) overline(z) + d=0$.

  + If $c=0$, then the generalized circle is a line.

  + If $c eq.not 0$ and $|alpha|^2 -c d >0$, then the generalized circle is a circle.
]
#proof[

  Let $z=x+i y$ and $alpha=a+i b$. Then the equation becomes
  $
    c (x^2+y^2) + 2 (a x - b y) + d = 0.
  $

  + If $c=0$, then the equation becomes $2 a x - 2 b y + d = 0$ which is a line.

  + If $c eq.not 0$, by completing the square, we have
  $
    (x + a / c)^2 + (y - b / c)^2 = (|alpha|^2 - c d) / c^2.
  $
]

#proposition[Möbius Transformations Preserve Generalized Circles][
  The image of a generalized circle under a Möbius transformation is a generalized circle.
]
#proof[
  Is sufficient to prove complex inversion $z |-> 1/z$ preserves generalized circles. If $z in hatCC$ satisfies
  $
    c z overline(z) + alpha z + overline(alpha) overline(z) + d = 0,
  $
  then we have
  $
    d frac(1, z) frac(1, overline(z)) + overline(alpha) / z + alpha / overline(z) + c = 0,
  $
  which implies that $w=1/z$ satisfies
  $
    d w overline(w) + overline(alpha) w + alpha overline(w) + c = 0.
  $
]

#definition[Cross Ratio][
  Let $z_0 , z_1 , z_2 , z_3 in hatCC $ be four distinct points. The #strong[cross ratio] of $z_0 , z_1 , z_2 , z_3$ is
  defined as
  $ [z_0 , z_1 , z_2 , z_3] = ((z_0 - z_2)(z_1 - z_3)) / ((z_0 - z_3)(z_1 - z_2)) . $

]

#proposition[Möbius Transformations Preserve Cross Ratio][
  Let $T$ be a Möbius transformation. Then $ [T(z_1) , T(z_2) , T(z_3) , T(z_4)] = [z_1 , z_2 , z_3 , z_4] . $
]

#proposition[Möbius Transformations are Sharply 3-transitive][
  If $z_1 , z_2 , z_3 in hatCC$ are 3 distinct points and $w_1, w_2, w_3 in hatCC$ are 3 distinct points, then there
  exists a unique Möbius transformation $T$ such that $T(z_i) = w_i$ for $i = 1, 2, 3$.
]
#proof[
  It is enough to show that there exists a unique Möbius transformation $T$ such that $T(z_1) = 1, T(z_2) = 0, T(z_3) = oo$.
  The map
  $
    T(z) = [z , z_1 , z_2 , z_3] = ((z - z_2)(z_1 - z_3)) / ((z - z_3)(z_1 - z_2))
  $
  does the job. If there exists another Möbius transformation $S$ such that $S(z_1) = 1, S(z_2) = 0, S(z_3) = oo$, then $S$ preserves
  the cross ratio, which implies
  $
    S(z) = [S(z) , 1 , 0 , oo] = [z , z_1 , z_2 , z_3]= T(z).
  $
]

#example[][
  The Möbius transformation
  $
    T(z) = frac(z + 1, z - 1)
  $
  maps the unit disk $bb(D) = {z in bb(C) thin mid(|) abs(z) lt 1}$ to the left half plane $bb(H) = {z in bb(C) thin mid(|) op("Re")(z) < 0}$. Note that $T$ is involutory, i.e. $T^2 = id$, which implies that $T^(- 1) = T$.

]

#cetz.canvas(
  length: 0.72cm,
  {
    import cetz.draw: *

    let image_circle_from_cicle(r) = ((r * r + 1) / (r * r - 1), 2 * r / calc.abs(r * r - 1))

    let circle_color = blue.darken(70%)
    let edge_color_1 = circle_color
    let edge_thickness = 1pt
    let edge_stroke_1 = (thickness: edge_thickness)
    let edge_stroke_2 = (thickness: edge_thickness, dash: "dashed")

    let radius_arr = (calc.exp(0.5), calc.exp(1), calc.exp(1.5))
    let radius_arr = radius_arr.map(x => 1 / x).rev() + radius_arr


    let angle_n = 6
    let angles = range(angle_n).map(i => i / angle_n * 180deg)
    let angle_colors = range(angle_n).map(i => color
      .map
      .rainbow
      .at(int(i / angle_n * color.map.rainbow.len()))
      .darken(20%))

    let geodesic_stroke = edge_stroke_2

    for (theta, color) in angles.zip(angle_colors) {
      let r = radius_arr.last() + 0.5
      let color_style = (paint: color.lighten(0%))
      line((theta, r), (theta, 0), stroke: geodesic_stroke + color_style)
      line((theta, 0), (theta, -r), stroke: geodesic_stroke + color_style)
    }

    // decay of circle color
    let decay(r) = calc.log(1 + 3.8 * r / radius_arr.last())

    circle((0, 0), radius: 1, stroke: edge_stroke_1 + (paint: circle_color.lighten(100% * decay(1))))
    for r in radius_arr {
      let decay = decay(r)
      let stroke = edge_stroke_1 + (paint: circle_color.lighten(100% * decay))
      circle((0, 0), radius: r, stroke: stroke)
    }

    // right subplot
    group(
      name: "subgroup",
      {
        translate(x: 13, y: 0)
        scale(1.4)

        let w = 4.3

        for (theta, color) in angles.zip(angle_colors) {
          let denominator = (1 - 2 * calc.cos(theta) + 1)
          let color_style = (paint: color.lighten(0%))
          if denominator == 0 {
            line((-w, 0), (w, 0), stroke: geodesic_stroke + color_style)
          } else {
            let y = -2 * calc.sin(theta) / denominator
            circle-through((-1, 0), (1, 0), (0, y), stroke: geodesic_stroke + color_style)
          }
        }


        for r in radius_arr {
          let (center_x, radius) = image_circle_from_cicle(r)
          let decay = decay(r)
          let stroke = edge_stroke_1 + (paint: circle_color.lighten(100% * decay))
          circle((center_x, 0), radius: radius, stroke: stroke)
        }

        let h = 4
        line((0, -h), (0, h), stroke: edge_stroke_1 + (paint: circle_color.lighten(100% * decay(1))))
      },
    )

    arc-through((5, 5.), (6, 5.3), (7, 5.), mark: (start: "straight"))
    content((6, 5.7), [$T$])
    arc-through((5, -5.), (6, -5.3), (7, -5.), mark: (end: "straight"))
    content((6, -5.7), [$T^(-1)$])
  },
)

#proposition[][
  There exists a unique generalized circle through any three distinct points in $hatCC$.
]

#proposition[][
  Four distinct points $z_0 , z_1 , z_2 , z_3 in hatCC$ lies on a generalized circle if and only if $[z_0 , z_1 , z_2 , z_3] in RR$.
]
#proof[
  If $[z_0 , z_1 , z_2 , z_3] in RR$, we can define Möbius transformation $T(z) = [z , z_1 , z_2 , z_3]$ and obtain
  $
    T(z_0) in RR,quad T(z_1)=1,quad T(z_2)=0, quad T(z_3)=oo.
  $
  Therefore, $T(z_0) , T(z_1) , T(z_2) , T(z_3)$ lies on the generalized circle $z - overline(z)= 0$. Since $T^(-1)$ preserves
  generalized circles, $z_0 , z_1 , z_2 , z_3$ lies on a generalized circle.

  If $[z_0 , z_1 , z_2 , z_3] in.not RR$, then $T(z_0)$ does not lie on the generalized circle $z - overline(z)= 0$.
  Therefore, $z_0$ does not lie on the generalized circle determined by $z_1 , z_2 , z_3$.
]

#definition[Conjugate Möbius Transformations][
  Nonidentity Möbius transformations $T$ and $S$ are are said to be *conjugate* if one of the following equivalent conditions holds:

  + there exists a Möbius transformation $R$ such that $T = R circle.stroked.tiny S circle.stroked.tiny R^(- 1)$.

  + conjugate if and only if $op("Tr") T = plus.minus op("Tr") S$.
]
#remark[
  The trace of a Möbius transformation is only well-defined up to sign.
]

#proposition[Classification of Möbius Transformation $upright(P S L)_2 lr((bb(C)))$][
  Each Möbius transformation $T in op("PSL")_2(CC)$ is conjugate to exactly one Möbius transformation of the form $z |-> mu z (mu in CC^*)$ or $z |-> z+1$,
  where $mu$ is called the *multiplier of $T$* and is determined up to replacement by $1 / mu$. A nonidentity Möbius transformation is called

  + #strong[parabolic] if it is conjugate to $z |-> z+1$.

  + #strong[elliptic] if it is conjugate to $z |-> mu z$ with $|mu|=1$ and $mu eq.not 1$;

  + #strong[hyperbolic] if it is conjugate to $z |-> mu z$ with $ mu in bb(R)^*-{1,-1}$;

  + #strong[loxodromic] if it is conjugate to $z |-> mu z$ with $mu in.not bb(R)^*$ and $|mu| eq.not 1$;

  Suppose a Möbius transformation $f(z)=(a z+b)/(c z + d)$ has fixed points $z_1$ and $z_2$, the multiplier $mu$ can be calculated as
  follows:
  $
    mu_i = cases(f^prime (z_i)=display((a d - b c)/(c z_i + d)^2) & upright(" if ") z_i eq.not oo, \
    limits(lim)_(z arrow.r oo) display(frac(1, f^prime (z)))=display(d/a )& upright(" if ") z_i = oo)
  $

]

Let $T in op("PSL")_2(CC)-{plus.minus I}$ and $sigma = op("Tr")(T)^2$. Then we have the following classification of Möbius transformations.

#table(
  columns: (auto, auto, auto, auto, auto),
  inset: 10pt,
  align: horizon + center,
  table.header([*Transformation*], [*Trace Squared*], [*Multipliers*], table.cell(colspan: 2)[*Examples*]),
  [Elliptic],
  $ 0 lt.eq sigma<4 $,
  [
    $mu_(1,2) = e^(plus.minus i theta)$,\ $theta in (0, 2 pi)$
  ],
  $ mat(e^(i theta \/2), 0;0, e^(-i theta \/2)) $,
  $ z |-> e^(i theta) z $,

  [Parabolic], $sigma = 4$, $mu = 1$, $ mat(1, b;0, 1) $, $ z |-> z + b $,
  [Hyperbolic],
  $sigma gt 4$,
  [
    $mu_(1,2) = rho^(plus.minus 1)$,\ $rho in RR^* - {1}$
  ],
  $ mat(sqrt(rho), 0;0, 1\/sqrt(rho)) $,
  $ z |->rho z $,

  [Loxodromic],
  $sigma in CC - RR_(gt.eq 0)$,
  [
    $mu_(1,2) = rho^(plus.minus 1) e^(plus.minus i theta)$,\ $rho in RR^*-{1}$,\ $theta in (0, pi) union (pi, 2 pi)$
  ],
  $ mat(sqrt(rho)e^(i theta \/2), 0;0, 1\/lr((sqrt(rho)e^(i theta \/2)))) $,
  $ z |-> rho e^(i theta) z $,
)


#proposition[Möbius Transformations of Finite Order are Elliptic][
  A nonidentity Möbius transformation $T in op("PSL")_2 (CC)$ has finite order if and only if it is elliptic and conjugate to $z |-> e^(i theta) z$ where $theta/(2 pi) in (0,1) inter QQ$.
]
#proof[
  Suppose $T in op("PSL")_2(CC)-{plus.minus I}$ has finite order. First, we assert $T$ is not parabolic. If $T$ is parabolic, since $T$ is conjugate to $z |-> z+1$, $z |-> z+1$ must have finite order, which is a contradiction. Let $M=mat(a,b;c,d) in op("SL")_2(CC)$ be a lift of $T$. Then we have $M^n=plus.minus I$ for some $n >= 2$, which implies any eigenvalue $lambda$ of $M$ satisfies $lambda^n=plus.minus 1$. Therefore, $lambda$ is a root of unity. Suppose the $z_1 in CC$ is a fixed point of $T$, then we have
  $
    T(z_1)=(a z_1+b) / (c z_1 +d)=z_1 ==> mat(a, b;c, d) mat(z_1;1) = mat(a z_1 + b;c z_1 + d) = (c z_1 + d) mat(z_1;1),
  $
  Hence $c z_1 + d$ is an eigenvalue of $M$. Note that the multiplier of $T$ is
  $
    mu_1 = T'(z_1) = (a d - b c) / (c z_1 + d)^2=1 / (c z_1 + d)^2.
  $
  We have $abs(mu_1)=1$. Therefore, $T$ is elliptic and conjugate to $z |-> e^(i theta) z$. Since $T^q (1)=e^(i q theta)=e^(i theta)$ for some $q >= 2$, we have $q theta = 2 pi k$ for some $k in ZZ$. Therefore, $theta/(2 pi) in (0,1) inter QQ$.

  Conversely, suppose $T$ is elliptic and conjugate to $z |-> e^(i theta) z$ where $theta/(2 pi) in (0,1) inter QQ$. Suppose $T(z)=e^(2 pi i p /q) z$ for some $p in ZZ$ and $q >= 2$. Then we have $T^q = op("id")$. Therefore, $T$ has finite order.
]

=== Upper Half Plane $bb(H)$ <upper-half-plane-mathbb-h>




#proposition[Fixed Points of $op("PSL")_2 lr((bb(R))) acts hat(CC)$][
  Let $op("PSL")_2 lr((bb(R)))$ acts on $hat(CC)$ by Möbius transformations. Or equivalently, $op("PSL")_2 lr((bb(R)))$ acts on $upright(bold(P))_(CC)^1$ by matrix multiplication
  $
    op("PSL")_2 lr((bb(R))) times upright(bold(P))_(CC)^1 &--> upright(bold(P))_(CC)^1 \
    (mat(a, b;c, d), mat(z;dot dot ;w)) &arrow.bar.long mat(a z + b w;dot dot;c z + d w)
  $
  Then the fixed points of $T in op("PSL")_2 lr((bb(R)))-{plus.minus I}$ can be classified as follows:

  + Elliptic: $op("Tr")(T)^2 lt 4$, fixed points are $z_1=tau in HH$ and $z_2=overline(tau) in -HH$.

  + Parabolic: $op("Tr")(T)^2=4$, fixed points are $z_1=z_2 in RR union.sq {oo}$.

  + Hyperbolic: $op("Tr")(T)^2 gt 4$, fixed points are $z_1eq.not z_2 in RR union.sq {oo}$.

]
#proof[
  $mat(z;dot dot;w) in upright(bold(P))_(CC)^1$ is a fixed point of $mat(a, b;c, d) in op("PSL")_2 lr((bb(R)))$ if and only if $mat(z;w) in CC^2$ is a eigenvector of $T=mat(a, b;c, d) in op("SL")_2 lr((bb(R)))$. Since the characteristic polynomial of $T$ is
  $
    det(lambda I- T)=lambda^2 - op("Tr")(T) lambda + 1,
  $
  we have the following classification of fixed points:

  + $Delta = op("Tr")(T)^2 - 4 lt 0$ implies that $T$ has two distinct complex conjugate eigenvalues $lambda_1 = c in HH$ and $lambda_2 = overline(c) in -HH$.

  + $Delta = op("Tr")(T)^2 - 4 = 0$ implies that $T$ has a double real eigenvalue $lambda_1=lambda_2 = c in RR$.

  + $Delta = op("Tr")(T)^2 - 4 gt 0$ implies that $T$ has two distinct real eigenvalues $lambda_1 = c in RR$ and $lambda_2 = d in RR$.
]
Let $T in op("PSL")_2(RR)-{plus.minus I}$ and $sigma = op("Tr")(T)^2$. Then we have the following classification of Möbius transformations.

#table(
  columns: (auto, auto, auto, auto, auto, auto),
  inset: (top: 10pt, bottom: 10pt),
  align: horizon + center,
  table.header(
    [*Transformation*],
    [*Trace Squared*],
    [*Fixed Points*],
    [*Multipliers*],
    table.cell(colspan: 2)[*Examples*],
  ),

  [Elliptic],
  $sigma<4$,
  [$
      z_1=tau in HH\
      z_2=overline(tau) in -HH
    $],
  [
    $mu_(1,2) = e^(plus.minus i theta)$,\ $theta in (0, 2 pi)$
  ],
  $ mat(cos theta/2, -sin theta/2;sin theta/2, cos theta/2) $,
  $ z |-> (z cos theta / 2-sin theta / 2) / (z sin theta / 2 + cos theta / 2) $,

  [Parabolic], $sigma = 4$, $ z_1=z_2 \ in RR union.sq {oo} $, $mu = 1$, $ mat(1, b;0, 1) $, $ z |-> z + b $,
  [Hyperbolic],
  $sigma gt 4$,
  $ z_1eq.not z_2 \ in RR union.sq {oo} $,
  [
    $mu_(1,2) = rho^(plus.minus 1)$,\ $rho in RR^*-{1}$
  ],
  $ mat(sqrt(rho), 0;0, 1\/sqrt(rho)) $,
  $ z |->rho z $,
)

Before we prove this result, we should first see how $op("SL")_2(RR)$ can be uniquely decomposed into 3 different types of transformations.

#lemma[Iwasawa Decomposition of $op("SL")_2(RR)$][
  Any $M in op("SL")_2 lr((bb(R)))$ can be uniquely written as
  $
    M = K A N= mat(cos phi, -sin phi;sin phi, cos phi) mat(lambda, 0;0, lambda^(-1)) mat(1, x;0, 1)
  $

  When we consider $op("SL")_2 lr((bb(R))) acts HH$

  + $K =mat(cos phi, -sin phi;sin phi, cos phi) in op("SO")_2(RR)$ means hyperbolic rotations around $i$, where $2 phi in [0,2pi )$ is the rotation angle,

  + $A=mat(lambda, 0;0, lambda^(-1))$ is positive diagonal matrix, where $lambda in RR^+$ means scaling by $lambda^2$,

  + $N=mat(1, x;0, 1)$ is an unitriangular matrix, where $x in RR$ is the translation.
]


#proposition[
  Automorphism of $bb(H)$
][The automorphism group of $bb(H)$ is given by
  $
    op("Aut") lr((bb(H))) = lr({z arrow.r.bar frac(a z + b, c z + d) thin mid(|) thin a , b , c , d in bb(R) , a d - b c = 1}) tilde.equiv op("PSL")_2 lr((bb(R))) = op("SL")_2 lr((bb(R))) \/ { plus.minus I }.
  $
  The action of $op("PSL")_2(RR)$ on $HH$ is smooth and transitive.
]<automorphism-of-upper-half-plane>
#proof[
  It is clear that the map
  $
    op("PSL")_2 lr((bb(R))) times bb(H) &--> bb(H)\
    (mat(a, b;c, d), z) &arrow.bar.long frac(a z + b, c z + d)
  $
  is smooth. To show that the action is transitive, note that for any $z=x+i y in bb(H)$, there exists
  $
    T=mat(1,x;0,1) mat(sqrt(y),0;0,1/sqrt(y)) = mat(sqrt(y),x/sqrt(y);0,1/sqrt(y)) in op("PSL")_2 lr((bb(R))),
  $
  such that $T(i)=z$.
]



#proposition[Stabilizer of $i$ in $op("PSL")_2 lr((bb(R)))$][
  Let $op("PSL")_2 lr((bb(R)))$ acts on $bb(H)$ by Möbius transformations. Then the stabilizer of $i$ is given by
  $
    op("Stab")_(op("PSL")_2 lr((bb(R))))( i ) = lr({mat(cos phi, -sin phi;sin phi, cos phi) thin mid(|) thin phi in bb(R)}) = op("SO")_2(RR).
  $
  And we have differential homeomorphism between smooth manifolds
  $
    op("PSL")_2 lr((bb(R))) \/ op("SO")_2(RR) & -->^tilde bb(H)\
    T op("SO")_2(RR) &arrow.bar.long T(i).
  $
]
#proof[
  Let $T in op("PSL")_2 lr((bb(R)))$ be a Möbius transformation such that $T(i) = i$. Then $T$ can be written as
  $
    T(z) = frac(a z + b, c z + d)
  $
  where $a , b , c , d in bb(R)$ and $a d - b c = 1$. Since $T(i) = i$, we have
  $
    frac(a i + b, c i + d) = i ==> (b+c)+(a-d)i=0
  $
  By comparing the real and imaginary parts, we have $b=-c$ and $a=d$, which implies $a^2+d^2=1$. Therefore, $T$ can be written as
  $
    T = mat(cos phi, -sin phi;sin phi, cos phi)
  $
  for some $phi in bb(R)$.
]

#proposition[
  Properties of $op("PSL")_2 lr((bb(R))) acts upright(bold(P))^1_RR$
][
  - Any $(x:y)in upright(bold(P))^1_RR$ can be written as #h(1fr)
    $
      mat(x;dot dot;y)=T(oo)=mat(x,b;y,d) mat(1;dot dot;0)
    $
    for some $T= mat(x,b;y,d) in op("PSL")_2 lr((bb(R)))$. Therefore, $op("PSL")_2 lr((bb(R)))$ acts transitively on $upright(bold(P))^1_RR$.
  - The stabilizer of $oo$ in $op("PSL")_2 lr((bb(R)))$ is given by
    $
      op("Stab")_(op("PSL")_2 lr((bb(R))))(oo) = lr({mat(a ,b;0, d) thin mid(|) thin a,b,d in bb(R)}).
    $
    As a result, we have
    $
      op("Stab")_(op("PSL")_2 lr((bb(R))))(T(oo))= T op("Stab")_(op("PSL")_2 lr((bb(R))))(oo) T^(- 1).
    $
]<properties-of-PSL2R-on-P1R>

#proposition[
  Orbit Decomposition of $op("PSL")_2 lr((bb(R))) acts upright(bold(P))^1_CC$
][
  $op("PSL")_2 lr((bb(R)))$ as a subgroup of $op("PSL")_2 lr((bb(C)))$
  acts on $hatCC$ and produces 3 orbits:

  + Real line plus a point at infinity : $bb(R) union.sq {oo}$,

  + Upper half plane: $bb(H)$,

  + Lower half plane: $- bb(H)$
]
#proof[
  This is corollary of @automorphism-of-upper-half-plane and @properties-of-PSL2R-on-P1R.
]


#definition[Fuchsian Group][
  A #strong[Fuchsian group] is a discrete subgroup of $op("PSL")_2 lr((bb(R)))$.
]

$op("SL")_2(ZZ)$ is a Fuchsian group.

=== Open Disk $bb(D)$ <open-disk-mathbb-d>



#proposition[
  Automorphism of $bb(D)$
][
  The automorphism group of $bb(D)$ is given by
  $
    op("Aut") lr((bb(D))) & = lr(
    {z arrow.r.bar e^(i theta) frac(z - alpha, 1 - overline(alpha) z) thin mid(|) thin alpha in bb(C) ,thick lr(|alpha|) < 1 ,thick theta in bb(R)}
  )\
    & = lr({z arrow.r.bar frac(a z + b, overline(b) z + overline(a)) thin mid(|) thin a, b in bb(C) , thick lr(|a|)^2 - lr(|b|)^2 = 1}) \
    &tilde.equiv { mat(a,b;overline(b),overline(a)) thin mid(|) thin a, b in bb(C) , thick lr(|a|)^2 - lr(|b|)^2 = 1 } \/ lr({ plus.minus I }) \
    &=op("SU")(1,1)\/ lr({ plus.minus I }) = upright(P U)(1,1).
  $
]
#proof[
  Since
  $
    f: DD &--> HH \
    z &arrow.long.bar (z+i) / (i z+1)
  $
  is a biholomorphic map, we have
  $
    op("Aut") lr((bb(D))) = { f^(- 1) circle.stroked.tiny T circle.stroked.tiny f thin mid(|) thin T in op("Aut") lr((bb(H))) }
  $
]

#proposition[][
  Let $op("PU")(1,1)$ acts on $bb(D)$ by Möbius transformations. Then the stabilizer of $0$ is given by
  $
    op("Stab")_(op("PSL")_2 lr((bb(R))))( 0 ) = lr({z |-> e^(i theta)z thin mid(|) thin theta in bb(R)}) tilde.equiv op("SO")_2(RR).
  $
]


== Compact Riemann Surfaces <compact-riemann-surfaces>


#theorem[Uniformization of Compact Riemann Surfaces][
  Compact Riemann surfaces can be classified as follows
  + Genus $g = 0$: $hatCC$.

  + Genus $g = 1$: $bb(C) \/ Lambda$ where $Lambda = w_1 bb(Z) xor w_2 bb(Z) lr((w_1 \/ w_2 in.not bb(R)))$ is a lattice in $bb(C)$.

  + Genus $g gt.eq 2$: $bb(H) \/ Gamma$ where $Gamma$ is a Fuchsian group.
]


=== Complex Torus $bb(C) \/ Lambda$ <complex-torus-mathbb-c-lambda>

A *lattice* in $RR^m$ is a discrete subgroup of $RR^m$.
#lemma[General Form of Lattice in $RR^m$][
  A lattice in $RR^m$ can be written as $Lambda = b_1 bb(Z) xor b_2 bb(Z) xor dots.c xor b_n bb(Z)$ where $b_1 , b_2 , dots.c , b_n in RR^m$ are linearly independent over $RR$.
]

#definition[Basis of Lattice][
  If $Lambda = b_1 bb(Z) xor b_2 bb(Z) xor dots.c xor b_n bb(Z)$ is a lattice in $RR^m$ where $b_1 , b_2 , dots.c , b_n in RR^m$ are linearly independent, then $B = [b_1 thin b_2 thin dots.c thin b_n] in RR^(m times n)$ is called a #strong[basis] of $Lambda$. In this case, we say $Lambda$ is generated by $B$ and write $Lambda = op("Lat") lr((B))$.
]

#definition[Equivalent Basis of Lattice][
  Two bases $B_1,B_2$ of a lattice $Lambda$ are *equivalent* if $op("Lat") lr((B_1))=op("Lat") lr((B_2))$.
]

#proposition[][
  Two bases $B_1, B_2 in RR^(m times n) $ of a lattice $Lambda$ are equivalent if and only $B_2 = B_1 M$ where $M in op("GL")_n (ZZ)$.
]
#proof[
  First assume that $op("Lat") lr((B))=op("Lat") lr((B^prime))$. Then for each of the $n$ columns $b_i$ of $B_2 , b_i in op("Lat")(B_1)$. This implies that
  there exists an integer matrix $U in bb(Z)^(n times n)$ for which $B_2 = B_1 U$. Similarly, there exists a $V in bb(Z)^(n times n)$ such that $B_1 = B_2 V$. Hence $B_2 = B_1 U = B_2 V U$, and we get
  $
    B_2 zws^top B_2 = (V U)^top B_2^top B_2 (V U) .
  $

  Taking determinants, we obtain that
  $
    det (B_2 zws^top B_2) = (det (V U))^2 det (B_2 zws^top B_2),
  $
  which implies $det (U)det (V)  = plus.minus 1$. Since $V , U in bb(Z)^(n times n)$, we get $V , U in op("GL")_n (ZZ)$.

  For the other direction, assume that $B_2 = B_1 M$ for some unimodular matrix $M in op("GL")_n (ZZ)$. Then we have $op("Lat") (B_2) subset.eq op("Lat")  (B_1)$. In
  addition, $B_1 = B_2 M^(- 1)$, we similarly get that $op("Lat")(B_1) subset.eq op("Lat") (B_2)$. So we can conclude that $op("Lat")  (B_1) = op("Lat") (B_2)$ as required.
]

#definition[Complex Lattice][
  A *complex lattice* is a rank-2 discrete subgroup of $bb(C)$, written as $Lambda = w_1 bb(Z) xor w_2 bb(Z)$ where $w_1$ and $w_2$ are linearly independent over $bb(R)$.
]

We can always assume that $tau = w_2 \/ w_1 in bb(H)$ because if this is not the case, we can simply replace $w_2$ with $-w_2$.

#corollary[][
  Consider two complex lattices $Lambda = w_1 bb(Z) xor w_2 bb(Z)$ and $Lambda^prime = w_1^prime bb(Z) xor w_2^prime bb(Z)$. Then $Lambda = Lambda^prime$ if and only if
  $
    vec(w_1^', w_2^') = mat(a,b;c,d) vec(w_1^', w_2^')quad "for" M=mat(a,b;c,d) in op("GL")_2 (ZZ).
  $
]

#proposition[Holomorphic Maps between Complex Tori][
  Suppose $Lambda_1, Lambda_2$ are two complex lattices.
  A map $f:bb(C) \/ Lambda_1 --> bb(C) \/ Lambda_2$ is holomorphic if and only if there exists $a , b in bb(C)$ such that $a Lambda_1 subset.eq Lambda_2$ and
  $
    f(z+ Lambda_1) = a z + b + Lambda_2 .
  $
]

#proof[
  Suppose $f:bb(C) \/ Lambda_1 --> bb(C) \/ Lambda_2$ is a holomorphic map. Since $pi_2 : bb(C) --> bb(C) \/ Lambda_2$ is a covering map, there exists a unique continuous map $tilde(f) : bb(C) --> bb(C) $ such that $pi_2 circle.tiny tilde(f) = f circle.tiny pi_1$, that is, the following diagram commutes.


  #square_cd(
    A11: $bb(C)$,
    A12: $bb(C)$,
    A21: $bb(C)\/ Lambda_1$,
    A22: $bb(C)\/ Lambda_2$,
    Ff: $tilde(f)$,
    Gf: $f$,
    theta_l: $pi_1$,
    theta_r: $pi_2$,
    Ff_arrow: "-->",
  )

  We can further show that $tilde(f)$ is holomorphic on $CC$. For any $z in bb(C)$, there exists an open neighborhood $U$ of $f circle.tiny pi_1(z)$ in $bb(C) \/ Lambda_2$, and a biholomorphism $(pi_2)^(-1)|_U:U -> V$ such that $tilde(f)(z) in V$. Therefore, as $tilde(f)$ is the composition of holomorphic maps, it is holomorphic at $z$.

  For any $lambda in Lambda_1$, consider the holomorphic function $g_lambda (z) = tilde(f)(z + lambda) - tilde(f)(z)$. Since
  $
    pi_2 circle.tiny g_lambda(z)= pi_2 circle.tiny tilde(f)(z + lambda) - pi_2 circle.tiny tilde(f)( z ) = f circle.tiny pi_1(z + lambda) - f circle.tiny pi_1(z) = 0,
  $
  we have $g_lambda (z) in Lambda_2$. Then we see that $g_lambda (z)$ is constant, because any continuous
  map from a connected space to a discrete
  space is constant. Differentiating $g_lambda (z)$ gives $tilde(f)^' (z + lambda) = tilde(f)^' (z)$, which implies that $tilde(f)^'$ is $Lambda_1$-periodic and hence bounded. By Liouville's theorem, $tilde(f)^'$ is constant, and we can write $tilde(f)(z) = a z + b$ for some $a , b in bb(C)$. Thus for any $z in CC$, we have
  $
    f(z + Lambda_1) = f circle.tiny pi_1(z) = pi_2 circle.tiny tilde(f)(z)= a z + b + Lambda_2.
  $
  For any $lambda in Lambda_1$, we have
  $
    pi_2(a lambda + b)= f circle.tiny pi_1(lambda) = f(0) = b + Lambda_2 ==> a lambda in Lambda_2,
  $
  which implies that $a Lambda_1 subset.eq Lambda_2$.

  Conversely, if $a Lambda_1 subset.eq Lambda_2$ and $f$ is given by $z |-> a z + b + Lambda_2$, then $f$ can be lifted to a holomorphic map
  $
    tilde(f):bb(C) &--> bb(C)\
    z &arrow.long.bar a z + b
  $
  The holomorphicity of $f$ follows from the fact that $pi_1$ is a local homeomorphism.
]

#corollary[][
  Suppose $Lambda_1, Lambda_2$ are two complex lattices. A holomorphic map $f:bb(C) \/ Lambda_1 --> bb(C) \/ Lambda_2$ is biholomorphic if and only if there exists $a in bb(C)$ such that $a Lambda_1 = Lambda_2$ and
  $
    f(z+ Lambda_1) = a z + b + Lambda_2 .
  $
]
#proof[
  If $f:bb(C) \/ Lambda_1 -> bb(C) \/ Lambda_2$ is a biholomorphism, then there exists $a, b, c, d in bb(C)$ such that $a Lambda_1 subset.eq Lambda_2$, $c Lambda_2 subset.eq Lambda_1$ and
  $
    f^(-1) circle.tiny f(z+ Lambda_1) = c(a z + b) + d + Lambda_1 = z + Lambda_1,quad "for all" z in bb(C),
  $
  which means $h(z)=(c a -1)z +c b - d in Lambda_1$ for all $z in bb(C)$. Hence $h$ is constant and $c = a^(-1)$. For any $lambda in Lambda_2$, there exists $mu in Lambda_1$ such that
  $
    a^(-1) lambda =mu <==> lambda = a mu in a Lambda_1,
  $
  which implies $Lambda_2  subset.eq a Lambda_1 $. Therefore, $a Lambda_1 = Lambda_2$.

  Conversely, if $a Lambda_1 = Lambda_2$, then we have $a^(-1)Lambda_2=Lambda_1$, which implies that
  $
    g:bb(C) \/ Lambda_2 &--> bb(C) \/ Lambda_1\
    z + Lambda_2 &arrow.long.bar a^(-1)(z - b) + Lambda_1
  $
  is a well-defined holomorphic map. Then we can check that $g circle.tiny f = id$ and $f circle.tiny g = id$, which implies that $f$ is a biholomorphism.
]

Complex torus $bb(C) \/ Lambda$, as a quotient group of $bb(C)$, has a abelian group structure compatible with its holomorphic structure. Next we always regard complex tori as objects in the category of complex Lie groups and holomorphic homomorphisms.

#lemma[][
  Suppose $Lambda_1, Lambda_2$ are two complex lattices. We know
  $
    f : bb(C) \/ Lambda_1 &arrow.r.long bb(C) \/ Lambda_2\
    z + Lambda &arrow.r.long.bar a z + b + Lambda_2
  $
  is a holomorphic map if $a Lambda_1 subset.eq Lambda_2$. The following are equivalent:

  + $f$ is a group homomorphism,

  + $b in Lambda_2$, so $f (z + Lambda_1) = a z + Lambda_2$,

  + $f(0) = 0$.

]

#proposition[Holomorphic Homomorphisms between Complex Tori][
  Suppose $Lambda_1, Lambda_2$ are two complex lattices.
  A map $f:bb(C) \/ Lambda_1 --> bb(C) \/ Lambda_2$ is a holomorphic homomorphism if and only if there exists $a in bb(C)$ such that $a Lambda_1 subset.eq Lambda_2$ and
  $
    f(z+ Lambda_1) = a z + Lambda_2 .
  $
  A map $f:bb(C) \/ Lambda_1 --> bb(C) \/ Lambda_2$ is an isomorphism if and only if there exists $a in bb(C)$ such that $a Lambda_1 = Lambda_2$ and
  $
    f(z+ Lambda_1) = a z + Lambda_2 .
  $
]

#definition[Isogeny between Complex Tori][
  A nonzero holomorphic homomorphism between two complex tori is called an #strong[isogeny].
]

#example[Multiply-by-$N$ Map is an Isogeny][
  Let $N$ be a postive integer. The map
  $
    [N]:bb(C) \/ Lambda &--> bb(C) \/ Lambda \
    z + Lambda &arrow.long.bar n z + Lambda
  $
  is called the #strong[multiply-by-$N$ map]. Since $N Lambda subset.eq Lambda$, we see $[N]$ is an isogeny. Let $E$ denote the complex torus $bb(C) \/ Lambda$. The kernel of $[N]$ is denoted by
  $
    E[N] = ker [N] = {z + Lambda in bb(C) \/ Lambda | N z in Lambda} = (N^(-1) Lambda) \/ Lambda tilde.equiv ( ZZ \/ N ZZ )^(2),
  $
  where the isomorphism is given by
]


