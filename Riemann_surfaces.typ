#import "@preview/fletcher:0.5.0" as fletcher: diagram, node, edge

#import "@local/math-notes:0.1.0": math_notes, definition, proposition, lemma, theorem, corollary, example, proof

#show: math_notes

// Overwrite the default definition
#let hatCC = $hat(CC, size: #1.00001em)$


// define commutative diagram
#let commutative_diagram(math_content) = align(center)[
  #diagram(label-size: 0.8em, math_content)
]


// Title Page
#v(1fr)
#align(center)[
  #text(font: "Noto Serif", size: 45pt, weight: 500)[Riemann Surfaces]
  #v(1.5fr)
  #text(font: "Noto Serif", size: 15pt, datetime.today().display())
]
#v(1.2fr)

#pagebreak()

#block(inset: (left: -0.5em, right: -0.5em))[
  #outline(title: text(font: "Noto Sans", size: 23pt, weight: 700, stretch: 150%)[Contents #v(1em)], depth: 3)
]

#pagebreak()

#let cal(x) = math.class("unary", text(font: "Computer Modern Symbol", x))


= Basic Concepts <basic-concepts>


== Complex Manifold <complex-manifold>
#definition[Holomorphic Chart][
  A #strong[holomorphic chart] on a topological manifold $X$ is a homeomorphism $phi : U arrow.r V subset.eq bb(C)^n$ where $U$ is
  an open subset of $X$, denoted by $lr((U , phi))$.
]
We say that a chart $lr((U , phi))$ for a Riemann surface $X$ is #strong[centered at $x$] if $phi lr((x)) = 0$.

#definition[Holomorphic Atlas][
  A #strong[\(compatible\) holomorphic atlas] on a topological manifold $X$ is a collection of holomorphic charts $lr((U_i , phi_i))$ such
  that $union.big_i U_i = X$ and for any $i , j$, the transition function $ phi_i circle.stroked.tiny phi_j^(- 1) : phi_j lr((U_i sect U_j)) --> phi_i lr((U_i sect U_j)) $ is
  holomorphic, whenever $U_i sect U_j$ is nonempty.
]
#definition[Complex Manifold][
  A #strong[complex manifold] of dimension $n$ is a topological manifold of dimension $2 n$ with a holomorphic atlas $lr({lr((U_i , phi_i))})$.
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
  Let $M$ be a smooth manifold. An almost complex structure on $M$ a smooth $lr((1 , 1))$-tensor field $J in Gamma lr((T^(lr((1 , 1))) M))$.
]
== Riemann Surface <Riemann-surface>
#definition[Riemann Surface][
  A #strong[Riemann surface] is a connected complex manifold of dimension one.
]
For manifolds, connectedness and path-connectedness are equivalent. So every Riemann surface is path-connected.

#example[Complex Plane $bb(C)$][
  $bb(C)$ is a Riemann surface with the atlas $lr({lr((bb(C) , upright("id")))})$. Any open subset $U subset.eq bb(C)$ is
  also a Riemann surface with the atlas $lr({lr((U , upright("id")))})$. Some interesting cases are the unit disc $bb(D) = { z in bb(C) : lr(|z|) < 1 }$,
  the upper half-plane $bb(H) = { z in bb(C) : "Im" z > 0 }$ and the punctured complex plane $bb(C)^(\*) = bb(C) \\ { 0 }$.
]
#example[Riemann Sphere][
  The #strong[Riemann sphere] is the one-point compactification of $bb(C)$, denoted by $hatCC = bb(C) union { oo }$. It is
  a Riemann surface with the following two charts: $   & U_1 = bb(C) , quad phi_1 lr((z))= z\
    & U_2 = hatCC - { 0 } , quad phi_2 lr((z)) = cases(delim: "{", 1 \/ z & upright("if ") z eq.not oo, 0 & upright("if ") z = oo) $
]
#example[Complex Projective Line][
  The #strong[complex projective line] $bb(P)^1 lr((bb(C)))$ is the set of all complex lines through the origin in $bb(C)^2$.
  It is a Riemann surface with the following two charts: $   & V_1 = lr({lr([z_0 : z_1]) mid(|) z_0 eq.not 0}) , quad psi_1 lr((z_0 , z_1)) = z_1 \/ z_0\
    & V_2 = lr({lr([z_0 : z_1]) mid(|) z_1 eq.not 0}) , quad psi_2 lr((z_0 , z_1)) = z_0 \/ z_1 $
]
#proposition[$hatCC$ is isomorphic to $bb(P)^1 lr((bb(C)))$][
  The map $f : hatCC arrow.r bb(P)^1 lr((bb(C)))$ $ f lr((x)) = cases(delim: "{", lr([1 : x]) & upright("if ") x eq.not oo, lr([0 : 1]) & upright("if ") x = oo) $ is
  a biholomorphism.
]
#proof[
  It is clear that $f$ is bijective. We only need to check that the transition functions are holomorphic. For any $z in phi_1 lr((U_1)) = bb(C)$, $ psi_1 circle.stroked.tiny f circle.stroked.tiny phi_1^(- 1) lr((z)) = psi_1 circle.stroked.tiny f lr((z)) = psi_1 lr((lr([1 : z]))) = z , $ which
  implies $psi_1 circle.stroked.tiny f circle.stroked.tiny phi_1^(- 1) = upright(i d)_(bb(C))$ For any $z in phi_2 lr((U_2)) = bb(C)$,
  if $z eq.not 0$, then $ psi_2 circle.stroked.tiny f circle.stroked.tiny phi_2^(- 1) lr((z)) = psi_2 circle.stroked.tiny f lr((1 / z)) = psi_2 lr((lr([1 : 1 \/ z]))) = z . $ And
  if $z = 0$, then $ psi_2 circle.stroked.tiny f circle.stroked.tiny phi_2^(- 1) lr((0)) = psi_2 circle.stroked.tiny f lr((oo)) = psi_2 lr((lr([0 : 1]))) = 0 . $ This
  implies $psi_2 circle.stroked.tiny f circle.stroked.tiny phi_2^(- 1) = upright(i d)_(bb(C))$. Therefore, $f$ is a
  biholomorphism.
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
    G= { x in X | "there exists an open neighborhood" N "of" x "such that" f_1|_N = f_2|_N }.
  $
  If $x in G$, then there exists an open neighborhood $N$ of $x$ such that $f_1|_N = f_2|_N$. So we have $x in N subset.eq G$,
  which implies $G$ is open. We claim that $G$ is also closed. Suppose $b in partial G$, then $f_1(b)=f_2(b)$ since $f_1$ and $f_2$ are
  continuous. Now choose charts $(U , phi)$ centered at $x$ and any chart
  $(V , psi)$ centered at $f_1(b)$, and suppose $f_i$ have local expressions $F_i =psi circle.stroked.tiny f_i circle.stroked.tiny phi^(-1)$ in
  this chart. Note that $U sect G$ is a nonempty open set containing $b$. By the identity theorem for holomorphic functions, we have $F_1=F_2$ on $phi(U)$. Thus $f_1|_U=f_2|_U$ on $U$. Hence $b in G$ and $G$ is closed. Now since $X$ is connected, $G$ is either $X$ or empty set. But $a in G$, so $G=X$.
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
  $ F (z) = psi circle.stroked.tiny f circle.stroked.tiny phi^(- 1) (z) = sum_(n = 1)^oo a_n z^n = z^k G (z) , quad (k gt.eq 1) $
  where $G (z)$ is holomorphic and $G (0) eq.not 0$. Define
  $h (z) = z root(k, G (z))$. $h$ is holomorphic at $z = 0$ and
  $F (z) = h (z)^k$. Then we can define a new chart
  $(tilde(U) , tilde(phi))$ centered at $x$ by
  $tilde(phi) = h circle.stroked.tiny phi$. Let
  $sigma_k : z arrow.r.bar z^k$. Then we have
  $ tilde(F) (z) = psi circle.stroked.tiny f circle.stroked.tiny tilde(phi)^(- 1) (z) = psi circle.stroked.tiny f circle.stroked.tiny phi^(- 1) circle.stroked.tiny h^(- 1) (z) = F circle.stroked.tiny h^(- 1) (z) = sigma_k circle.stroked.tiny h circle.stroked.tiny h^(- 1) (z) = sigma_k (z) = z^k , $
  which is the local expression of $f$ using these charts.
]

#corollary[Holomorphic Maps are Open][
  Let $f : X arrow.r Y$ be a non-constant holomorphic map of Riemann surfaces. Then $f$ is an open map.
]
#proof[
  For any point $x in X$, there are chart $(U , phi)$ centered at $x$ and chart $(V , psi)$ centered at $f (x)$ such that $psi circle.stroked.tiny f circle.stroked.tiny phi^(- 1) (z) = z^k$.
  Since $z^k$ is an open map, $f|_(U)$ is composition of open maps and hence open. For any open neighborhood $N$ of $x$, $f (U sect N)$ is
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
  $   & V = hatCC - { 0 } , quad psi (z) = cases(delim: "{", 1 \/ z & upright("if ") z eq.not oo, 0 & upright("if ") z = oo) $
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
#theorem(
  [Riemann-Hurwitz Formula],
)[
  Let $f : X arrow.r Y$ be a nonconstant, degree $d$, holomorphic map of compact Riemann surfaces. Denote the genus of $X$ by $g_X$ and
  the genus of $g_Y$. Then $ 2 g_X - 2 = lr((2 g_Y - 2)) deg lr((f)) + sum_(x in upright(R a m) lr((f))) lr((k_x - 1)) , $ where $k_x$ is
  the ramification index of $f$ at $x$.
]
#proof[
  Let $Gamma_Y$ be a good graph on $Y$ with $f lr((upright(R a m)_X lr((f)))) subset.eq V_(Gamma_Y)$: the branch locus of $f$ is
  contained in the vertex set of $Gamma_Y$. Define $Gamma_X$ to be the "lift" of $Gamma_Y$ via the map $f$ : the support
  of $Gamma_X$ is $f^(- 1) lr((Gamma_Y))$ and the vertices, edges and faces of $Gamma_X$ are the connected components of
  the inverse images of vertices, edges and faces of $Gamma_Y$. Note $ deg lr((f)) = sum_(x in f^(- 1) lr((y))) k_x = lr(|f^(- 1) lr((y))|) + sum_(x in f^(- 1) lr((y))) lr((k_x - 1)) . $ We
  can obtain the following equations by counting the number of vertices, edges and faces of $Gamma_X$ and $Gamma_Y$: $ lr(|V_(Gamma_X)|) & = sum_(y in Gamma_Y) lr(|f^(- 1) lr((y))|) = sum_(y in V_(Gamma_Y)) deg lr((f)) - sum_(y in V_(Gamma_Y)) sum_(x in f^(- 1) lr((y))) lr((k_x - 1)) = deg lr((f)) lr(|V_(Gamma_Y)|) - sum_(x in upright(R a m) lr((f))) lr((k_x - 1)) ,\
  lr(|E_(Gamma_X)|) & = deg lr((f)) lr(|E_(Gamma_X)|) ,\
  lr(|F_(Gamma_X)|) & = deg lr((f)) lr(|F_(Gamma_X)|) . $ Thus we have $ chi lr((X)) & = lr(|V_(Gamma_X)|) - lr(|E_(Gamma_X)|) + lr(|F_(Gamma_X)|)\
              & = deg lr((f)) lr(|V_(Gamma_Y)|) - sum_(x in upright(R a m) lr((f))) lr((k_x - 1)) - deg lr((f)) lr(|E_(Gamma_Y)|) + deg lr((f)) lr(|F_(Gamma_Y)|)\
              & = deg lr((f)) lr((lr(|V_(Gamma_Y)|) - lr(|E_(Gamma_Y)|) + lr(|F_(Gamma_Y)|))) - sum_(x in upright(R a m) lr((f))) lr((k_x - 1))\
              & = deg lr((f)) chi lr((Y)) - sum_(x in upright(R a m) lr((f))) lr((k_x - 1)) . $
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
   
  + $ 2 g_X - 2 = (2 g_Y - 2) deg (f) + sum_(x in upright(R a m) (f)) (k_x - 1) gt.eq (2 g_Y - 2) deg (f) gt.eq 2 g_Y - 2 . $
   
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
  on $X$. That is, for any open set $U subset.eq X$, $ cal(O)_X lr((U)) = lr({f : U arrow.r bb(C) thin mid(|) thin f upright(" is holomorphic")}) . $
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
  Let $X$ be a Riemann surface and $f$ is meromorphic at $p in X$. Then the order of $f$ at $p$ $ "ord"_p : cal(M)_(X , p) & --> bb(Z) union { oo }\
  f                        & arrow.r.long.bar "ord"_p lr((f)) $ is a valuation on $cal(M)_(X , p)$. That is, for any $f , g in cal(M)_(X , p)$,
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
== Divisor <divisor>
#definition[Divisor Group][
  Let $X$ be a Riemann surface. The #strong[divisor group] of $X$ is the free abelian group generated by the points of $X$,
  denoted by $op("Div") lr((X))$. An element of $op("Div") lr((X))$ is called a #strong[divisor] on $X$. A divisor $D$ on $X$ can
  be written as $ D = sum_(x in X) n_x x. $
]
#definition[Degree of a Divisor][
  Let $X$ be a Riemann surface. The degree homomorphism is defined as 
  $ deg : op("Div") lr((X)) & --> bb(Z)\
  D = sum_(x in X) n_x x  & arrow.r.long.bar sum_(x in X) n_x . $ 
  It can be defined by the universal property of free abelian Group 
   
  #commutative_diagram($
    op("Div") lr((X)) edge(deg, "-->") & im(f) \
    X edge("u", iota, ->, #left) edge("ur", c_1, ->, #right)
  $)
   
  where $c_1 : x |-> 1$ is a constant mapping. $deg (D)$ is called the #strong[degree] of $D$. The kernel of $deg$ is
  denoted by
  $"Div"^0 (X)$ and called the #strong[divisor group of degree zero];. So we have the exact sequence
   
  #commutative_diagram($
    0 edge(->) & op("Div")^0 edge(->) & op("Div") lr((X)) edge(deg, ->) & bb(Z) edge(->) & 0
  $)
]


#definition[
  Principal Divisors: Divisors from Meromorphic Functions
][
  Let $X$ be a Riemann surface and $f$ be a nonzero meromorphic function on $X$. The #strong[divisor of $f$] is defined as $ op("div") lr((f)) = sum_(x in X) "ord"_x lr((f)) x . $ Any
  divisor of this form is called a #strong[principal divisor] on $X$. The set of principal divisors on $X$ is denoted by $op("PDiv") lr((X))$.
]

#proposition[Degree of Principal Divisors on Compact Riemann Surfaces][
  Let $X$ be a compact Riemann surface and $f$ be a meromorphic function on $X$. Then $deg lr((upright(d i v) lr((f)))) = 0$ and $ op("PDiv") lr((X)) subset.eq op("Div")^0 lr((X)) . $
]
#definition[Picard group][
  Let $X$ be a Riemann surface. The #strong[Picard group] of $X$ is defined as $ op("Pic") lr((X)) = op("Div") lr((X)) \/ op("PDiv") lr((X)) . $ The #strong[restricted Picard group] of $X$ is
  defined as $ op("Pic")^0 lr((X)) = op("Div")^0 lr((X)) \/ op("PDiv") lr((X)) . $
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
  $ ell lr((D)) cases(
    "= 0" & " if " & deg D < 0,
    gt.eq 1 - g + deg D & " if " & 0 lt.eq deg D lt.eq 2 g - 2,
    = 1 - g + deg D & " if " & deg D gt.eq 2 g - 1,

  ) $
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
#proposition[
  Automorphism of $hatCC$
][The only automorphisms of $hatCC$ are Möbius transformations $ op("Aut") lr((hatCC)) = lr({z arrow.r.bar frac(a z + b, c z + d) thin mid(|) thin a , b , c , d in bb(C) , a d - b c = 1}) tilde.equiv upright(P S L) lr((2 , bb(C))) . $
]
=== Upper Half Plane $bb(H)$ <upper-half-plane-mathbb-h>
#proposition[
  Automorphism of $bb(H)$
][The automorphism group of $bb(H)$ is given by $ op("Aut") lr((bb(H))) = lr({z arrow.r.bar frac(a z + b, c z + d) thin mid(|) thin a , b , c , d in bb(R) , a d - b c = 1}) tilde.equiv upright(P S L) lr((2 , bb(R))) . $
]
=== Open Disk $bb(D)$ <open-disk-mathbb-d>
#proposition[
  Automorphism of $bb(D)$
][
  The automorphism group of $bb(D)$ is given by $ op("Aut") lr((bb(D))) & = lr(
    {z arrow.r.bar e^(i theta) frac(z - alpha, 1 - overline(alpha) z) thin mid(|) thin alpha in bb(C) , lr(|alpha|) < 1 , theta in bb(R)}
  )\
                        & = lr(
    {z arrow.r.bar frac(overline(a) z + overline(b), b z + a) thin mid(|) thin a, b in bb(C) , lr(|a|)^2 - lr(|b|)^2 = 1}
  ) tilde.equiv upright(P U)(1,1). $
]
== Compact Riemann Surfaces <compact-riemann-surfaces>


#theorem[Uniformization of Compact Riemann Surfaces][ 
  Compact Riemann surfaces can be classified as follows
  + Genus $g = 0$: $hatCC$.
   
  + Genus $g = 1$: $bb(C) \/ Lambda$ where $Lambda = w_1 bb(Z) xor w_2 bb(Z) lr((w_1 \/ w_2 in.not bb(R)))$ is a lattice in $bb(C)$.
   
  + Genus $g gt.eq 2$: $bb(H) \/ Gamma$ where $Gamma$ is a Fuchsian group.
]

