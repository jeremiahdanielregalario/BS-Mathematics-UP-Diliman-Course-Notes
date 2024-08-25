#set text(font: "Fira Sans Math")
#set page(paper: "a4")
#set text(size: 30pt)
#set align(horizon)
= Math 110.1
ABSTRACT ALGEBRA I: Unit III

#set text(size: 14pt, )
#emph[Course Notes by: Jeremiah Daniel Regalario] \
#emph[II-BS Mathematics] \
#emph[University of the Philippines - Diliman]  \
#emph[Dr. Lilibeth Valdez]


#pagebreak()
#set page(
  margin: (top: 60pt, bottom: 60pt),
  numbering: "1",
)

#set text(font: "Fira Sans Math", size: 12pt)
#set align(top)

= Rings
#line(length: 100% )

#underline[=== Definition:]

A _#underline[ring]_ $angle.l R, +, · angle.r$ is a set together with two binary operations $bold(+)$ (called
_addition_) and $bold(·)$ (called _multiplication_) such that the following axioms are
satisfied:

+ $angle.l R, + angle.r$ is an #underline[_abelian group_].
+ Multiplication is #underline[_associative_], that is, for all $a, b, c, ∈ RR$, $(a · b) · c = a · (b · c)$
+ For all $a, b, c ∈ RR$, $a · (b + c) = a · b + a · c$ and $(a + b) · c = a · c + b · c$ (#underline[_left and right distributive laws holds_].)


#underline[=== Examples:]
+ $ZZ$ is closed under the usual addition $+$ and multiplication $dot$.
  + : $angle.l ZZ, + angle.r$ is an abelian group.
  + : $·$ is associative.
  + : Left and right distributive laws holds
  Thus, $angle.l ZZ, +, dot angle.r$ is a ring.
  
+ $angle.l QQ, +, dot angle.r$ , $angle.l RR, +, dot angle.r$ and $angle.l CC, +, dot angle.r$ are rings.

#underline[=== Remarks:]
+ If the operations $+$ and $·$ are clear from context we denote the ring $angle.l R, +, dot angle.r$ simply by $R$.
+ The identity of the group $angle.l R, + angle.r$ is denoted $0$ and is called the _#underline[zero element]_ of $R$.
+ The inverse of $a$ in the group $angle.l RR, + angle.r$ is denoted $−a$.
+ We write $a − b$ for $a + (−b)$.
+ To simplify notations, we write $a b$ for $a · b$.
+ In the absence of parentheses, multiplication is assumed to be performed before addition, that is, $a b + c = (a b) + c$

\

== #underline[Commutative Rings, Rings with Unity, and Units]


#underline[=== Definition:]

Let $R$ be a ring.

+ If multiplication in $R$ is commutative, then $R$ is called a #underline[_commutative ring_].
+ An element $1_R$ such that $∀r ∈ R, 1_R r = r = r 1_R$ is called a _#underline[multiplicative identity]_ or a #underline[_unity_].
+ If $R$ has a multiplicative identity, then $R$ is called a _#underline[ring with unity]_.
+ Suppose $R$ is a ring with unity $1_R eq.not 0$. An element $u ∈ R$ is a #underline[_unit_] if $u$ has a multiplicative inverse, that is $∃u^(−1) ∈ RR$ such that $u u^(−1) = 1_R = u^(−1)u$.

#underline[=== Remarks:]
+ Some rings are #underline[not commutative] and some have #underline[no unity].
+ If $R$ has unity, then this unity is unique.
+ If $R$ has unity $1_R$, then $1_R$ is a unit in $R$.
+ If $R$ has unity, #underline[not all] elements in the ring are units.

#underline[=== Examples:]
+ $angle.l ZZ, +, dot angle.r$ is a commutative ring with unity $1$. The units of $ZZ$ : $1, −1$.
+ $angle.l QQ, +, dot angle.r$ , $angle.l RR, +, dot angle.r$ and $angle.l CC, +, dot angle.r$ are commutative rings with unity $1$. 

  Every nonzero element in these rings is a unit.
+ $angle.l ZZ_n, +_n, dot_n angle.r$ is a commutative ring with unity 1. The set of units of $ZZ_n$ is denoted $U(n)$. Exercise: Determine the elements of $U(4)$ and $U(5)$.

  #block(stroke: 1pt, radius: 5pt, inset: 10pt, width: 100%)[
    - $U(4) = {a in ZZ_4 | exists k in ZZ "s.t." a dot_4k = 1} = {1, 3}$ 
    - $U(5) = {a in ZZ_5 | exists k in ZZ "s.t." a dot_5k = 1} = {1, 2, 3, 4}$
  ]
+ $angle.l 2ZZ, +, dot angle.r$ is a commutative ring with no unity.

+ Let $display(M_2(RR) = {mat(a, b; c, d; delim: "[") mid(|) a, b, c, d, ∈ RR})$. Define $+$ and $·$ on $M_2(RR)$ as:
$
mat(a, b; c, d; delim: "[") + mat(e, f; g, h; delim: "[") = mat(a + e, b + f; c + g, d + h; delim: "[") \
mat(a, b; c, d; delim: "[")mat(e, f; g, h; delim: "[") = mat(a e + b g, a f + b h; c e + d g, c f + d h; delim: "[")
$

Then $M_2(RR)$ is a noncommutative ring with unity:
- $+$ is associative and commutative (Exercise)
- $·$ is associative but not commutative (Exercise)
- left and right distributive laws hold (Exercise)

- zero element: $display(mat(0,0; 0, 0; delim: "["))$; additive inverse: $display(mat(-a, -b; -c, -d; delim: "["))$; unity: $display(mat(1, 0; 0, 1; delim: "["))$



\

#underline[== Theorem 2.13]

#underline[=== Definition:]

Let $R$ be a ring with additive identity $0$. Let $a, b, c ∈ R$.

+ $a · 0 = 0 · a = 0$
+ $a(−b) = (−a)b = −(a b)$.
+ $(−a)(−b) = a b$
+ $a(b − c) = a b − a c "and" (a − b)c = a c − b c$.

#block(stroke: 1pt, radius: 5pt, inset: 15pt)[
    === Proof: 
    #set enum(numbering: "(1.)")
  + $a · 0 + a · 0 = a(0 + 0) = a · 0$. By left cancellation, $a · 0 = 0$. The proof for $0 · a = 0$ follows analogously.
  + $a b + a(−b) = a(b − b) = a · 0 = 0$. Since the additive inverse of $a b$ is unique, $−(a b) = a(−b)$. The proof that $(−a)b = −(a b)$ proceeds analogously.
  + $(−a)(−b) = −[a(−b)] = −[−(a b)] = a b$
]

#underline[=== Remarks:]
+ If $R$ is a nonzero ring with unity then $1 eq.not 0$. (Why?)
+ If $R$ is a ring with unity and $a ∈ R$ then $(−1)a = −a$. In particular $(−1)(−1) = 1$.
+ Let $R$ be a ring and $a, b, c ∈ R$. If $a eq.not 0$ and $a b = a c$, then $b$ and $c$ are not necessarily equal. ($a eq.not 0 and a b = a c cancel(==>) b = c$)
  
  - e.g. in $ZZ_4$, $2 ·_4 1 = 2 = 2 ·_4 3$ but $1 eq.not 3$.
+ In a ring $R$, $a b = 0$ does not necessarily mean that either $a = 0$ or $b = 0$.
  - e.g. in $ZZ_6$, $2 ·_6 3 = 0$

\


#underline[== Group of Units of _R_ (Theorem 2.14) ]

#underline[=== Definition:]

Let $R$ be a ring with unity. The units of $R$ form a group
under multiplication.

#underline[=== Remark:]
The group of units of a ring with unity $R$ is denoted $U(R)$.

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  === Proof: 
  - Closure under multiplication: Let $a, b ∈ U(R)$. (WTS: $a b ∈ U(R)$). Since $a, b ∈ U(R)$, $∃a^(−1), b^(−1) ∈ R$ such that $a a^(−1) = b b^(−1) = 1$. Note that $b^(−1)a^(−1) ∈ R$ and
    $
    (b^(-1)a^(-1))(a b) &= b^(-1)[(a^(-1))(a b)] \
    &= b^(-1)[(a^(-1) a)b] \
    &= b^(-1)[1 dot b] \
    &= b^(-1)b \= 1
    $
    Thus $(a b)^(−1) = b^(−1)a^(−1)$ and so $a b ∈ U(R)$.
  - Associativity of multiplication: Follows from $cal(R)_2$.
  - Identity element under multiplication: unity $1 ∈ U(R)$ has the property that $ ∀a ∈ U(R) ⊆ R, a · 1 = 1 · a = a. $
  - Inverse under multiplication: Let $a ∈ U(R)$. Then $∃a^(−1) ∈ R$ such that $a · a^(−1) = a^(−1) · a = 1$. From this, we see that $a^(−1) ∈ U(R)$.
  $∴ angle.l U(R), · angle.r$ is a group.
]

#underline[=== Examples:]

+ $U(ZZ) = {1, −1} tilde.equiv ZZ_2$
+ $U(QQ) = QQ^(∗)$, $U(RR) = RR^(∗)$, $U(CC) = CC^(∗)$
+ $U(ZZ_n) = U(n)$ = set of all elements of $ZZ_n$ that are relatively prime to $n$
+ $U(M_2(RR)) = op("GL")(2, RR)$



#pagebreak()


= Fields and Division Rings
#line(length: 100% )

#underline[=== Definition:]

Let $R$ be a ring with unity $1 eq.not 0$. If every nonzero element of $R$ is a unit then $R$ is called a _#underline[division ring]_.

If $R$ is a commutative division ring, then $R$ is called a #underline[_field_].

#underline[=== Remarks:]
Let $R$ be a ring with unity $1 eq.not 0$.

+ If $R$ is a field, we write $display(a/b)$ for $a b^(−1) = b^(−1) a$. In particular, we write $b^(−1) = display(1/b).$

+ A division ring can be thought of as an algebraic structure that is closed under addition, subtraction, multiplication and division by nonzero elements.
+ $R$ is a division ring if and only if $R^(*) := R backslash {0}$ is a group.

+ $R$ is a field if and only if $R^(∗) := R backslash {0}$ is an abelian group.

#underline[=== Examples:]

+ $ZZ$ is not a division ring, and hence not a field.
+ $QQ, RR, CC$ are fields.
+ $ZZ_4$ is not a division ring. $because$ $0 eq.not 2 in ZZ_4$ is not a unit.
+ $ZZ_5$ is a field.
In $ZZ_5$:

  - $display(3/4) = 3 dot_5 4^(−1) = 3 dot_5 4 = 2$
  
  - $2 display(1/3) = 2 plus_5 display(1/3) = 2 plus_5 3^(-1) = 2 plus_5 2 = 4$


#pagebreak()



= Subrings and Subfields

#line(length: 100%)

#underline[== Subring]

#underline[=== Definition:]

A subset $S$ of a ring $R$ which is also a ring itself under the same operations as in $R$ is called a _#underline[subring]_ of $R$.

#underline[== Theorem 2.15]
Let $R$ be a ring and $S$ a nonempty subset of $R$. Then $S$ is
a subring of $R$ if and only if for all $a, b ∈ S$, $a − b ∈ S$ and $a b ∈ S$.

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  === Proof: 
  $(==>)$ Since $S$ is a ring, then $angle.l S, + angle.r$ is an abelian group hence $a − b ∈ S$.
  
  Also, $a b ∈ S$ since $·$ is a binary operation on $S$.

  $(<==)$ Suppose $a − b ∈ S$ and $a b ∈ S$ for all $a, b ∈ S$.
  $cal(R)_1$ : $a − b ∈ S$ for all $a, b ∈ S ==>$  $angle.l S, + angle.r$ is a subgroup of $angle.l R, + angle.r$. Thus, $angle.l S, + angle.r$ is an abelian group.

  $cal(R)_2$ : and $cal(R)_3$ : follows since operations in $S$ and $R$ are the same.
]

#underline[=== Remarks:]
Let $R$ be a ring and $S$ a subring of $R$.
+ If $R$ is commutative, then $S$ is also commutative.
+ $S$ may be #underline[without] unity even if $R$ has unity.
\

#underline[== Subfields]

#underline[=== Definition:]

A subset $S$ of a field $F$ which is also a field itself under the same operations as in $F$ is called a #underline[_subfield_] of $F$.

#underline[=== Theorem 2.16]
Let $F$ be a field and $S$ a nonempty subset of $F$. Then $S$ is
a subfield of $F$ if and only if the following hold:

+ $S eq.not {0}$
+ for all $a, b ∈ S$, $a − b ∈ S $ and $ a b ∈ S$
+ for all $0 eq.not a ∈ S$, $a^(−1) ∈ S space.quad$ (_i.e. every nonzero element is a unit._)

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  === Proof: 
  Exercise!
]

#underline[=== Examples:]
+ If $R$ is a ring then ${0}$ (trivial subring) and $R$ (improper subring) are subrings of $R$.
+ $QQ$ is a subfield of $RR$.
+ For any $n ∈ ZZ$, $n ZZ$ is a subring of $ZZ$. (Why?) Note that if $n eq.not 1, −1$, then $n ZZ$ has no unity.
+ Let $display(D_2(RR) = {mat(a, 0; 0, b; delim: "[") mid(|) a, b ∈ RR})$. Let $display(mat(a, 0; 0, b; delim: "[")), display(mat(c, 0; 0, d; delim: "[")) in D_2(RR),$
  $
  mat(a, 0; 0, b; delim: "[")-mat(c, 0; 0, d; delim: "[") = mat(a-c, 0; 0, b-d; delim: "[") in D_2(RR) \
  mat(a, 0; 0, b; delim: "[")mat(c, 0; 0, d; delim: "[") = mat(a c, 0; 0, b d; delim: "[") in D_2(RR) \
  $
  $∴ D_2(RR)$ is a subring of $M_2(RR)$. $square.filled$
\

#underline[== Zero Divisors]

#underline[=== Definition:]

Let $R$ be a commutative ring. A nonzero element $a in R$ is called a _#underline[zero divisor]_ (or a divisor of zero) if there is a non-zero element $b in R$ such that $a b = 0$. 

#underline[=== Example:]

+ zero divisors of $ZZ_12$: $2,3,4,6,7,8,9,10$\
+ $ZZ$ has no zero divisors.


#underline[=== Theorem 2.17:]
The zero divisors of $ZZ_n$ are its non-zero elements that are not relatively prime to $n$.

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  *#underline[Proof]*. Let $0 eq.not a in ZZ_n $.
  
  $(==>)$ Suppose $a$ is a zero divisor of $ZZ_n$. Then, $exists (0 eq.not b in ZZ_n)$ s.t. $a b =0 ==> n divides a b$. 
  
  Suppose (on the contrary) that $a$ is relatively prime to $n$, then $n divides b ==> b = 0. arrow.zigzag$

  $therefore$ $a$ is NOT relatively prime to $n$.

  $(<==)$ Suppose $d = gcd(a, n) > 1$. Let $a = d k_1$ and $n = d k_2$ for some $k_1, k_2 in ZZ$. Note that $0 eq.not k_2 in ZZ_n$. Then 
  $
  a k_2 = d k_1 k_2 = d k_2 k_1 = n k_1 = 0.
  $
  $therefore $ $a$ is a zero divisor. $square.filled$
]




#pagebreak()

= Integral Domain

#line(length: 100% )

#underline[=== Definition:]

A commutative ring with unity $1 eq.not 0$ is said to be an #underline[_integral domain_] if it has no zero divisors.

#underline[=== Remark:]
In an integral domain $D$, if $a b = 0$, then either $a = 0$ or $b = 0$.

#underline[=== Example:]
 Division rings that are integral domains.
+ $ZZ space checkmark$
+ $QQ, CC, RR space checkmark$
+ $ZZ_p space checkmark$, where $p$ is prime.
+ $cancel(ZZ times ZZ)$ -  has zero divisors $(0,a)$ and $(b,0)$ for some $0 eq.not a, b in ZZ$.
+ $cancel(M_2(RR) )$ - not a commutative ring
+ $cancel(2ZZ)$ - has no unity


#underline[=== Theorem 2.18:]
Let $R$ be a commutative ring with unity $1 eq.not 0$. Then, the cancellation law for multiplication holds in $R$ if and only if $R$ is an integral domain.

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  *#underline[Proof]*. 
  
  $(==>)$ Suppose that $forall a, b, c in R$ with $a eq.not 0$ , $a b = a c  ==> b = c$.

  Let $a in R$ with $a eq.not 0$. Suppose that $a b  = 0 = a dot 0$ for some $b in R$. Then, $ b = 0$. Hence, $a$ is a non-zero divisor of $R$.
  
  $therefore $ $R$ is an integral domain.
 
  $(<==)$ Suppose that $R$ is an integral domain. Let $a, b, c in R$ with $a eq.not 0$ and $a b = a c$.

  $
  a b = a c &==> a b - a c = 0 \
  &==> a(b - c) = 0 \
  &==> b - c = 0 \
  &==> b = c
  $
  
  $therefore $ $forall a, b, c in R$ with $a eq.not 0$ , $a b = a c  ==> b = c$.

  $therefore $ Cancellation law for multipilcation holds if and only if $R$ is an integral domain. $square.filled$
]

#underline[=== Remarks:]
Let $R$ be an integral domain. Let $a, b in R$ with $a eq.not 0$.

+ Then $a x + b$ has at most one solution.
+ If $a$ is a unit in $R$, then $a x = b$ has exactly one solution, given by $x = display(b/a) = a^(-1)b$.

#underline[=== Theorem 2.19:]
Every field is an integral domain.

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  *#underline[Proof]*. 
  
  Let $F$ be a field. Then, $F$ is commutative with unity $1 eq.not 0$.

  Let $a in F$ s.t. $a eq.not 0$.

  Suppose $a b  = 0$ for some $b in F$. 
  $
  &==> 1/a (a b) = 1/a dot 0 \
  &==> (1/a dot a)b =  0 \
  & ==> 1 dot b = 0\
  &==> b = 0
  $
  $therefore a$ is not a zero divisor.
  
  $therefore F$ is an integral domain. $square.filled$
]

#underline[=== Theorem 2.20:]
Every finite integral domain is a field.

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  *#underline[Proof]*. 
  
  Let $D$ be a finite integral domain. Then, $D$ is commutative  with unity $1 eq.not 0$. 

  Let $0 eq.not a in D$. (WTS: $a$ is a unit.)

  Consider the function $f$ defined as:
  $ f: D &-> D \
  x &|-> a x
  $

  Suppose $f(x) = f(y)$ for some $x, y in D$. Then, $a x = a y ==> x = y$. (via C. L.)

  So, $f$ is one-to-one $==>$ $f$ is onto.

  Since $1 in D ==> exists b in D$ s.t. $f(b) = 1$.
  $
  &==> a b = 1 \
  &==> a "is a unit"
  $
  
  $therefore D$ is a field. $square.filled$
]

#underline[=== Example:]
Let $p$ be prime. Then $ZZ_p$ is an integral domain $==> ZZ_p $ is a field.

Recall: $R$ is a ring, $a in R, n in NN$.
- $n dot a = underbrace(a + a + dots.c + a, n)$
- $(-n) a = underbrace(-a - a - dots.c - a, n)$
- $0 dot a = 0$

#underline[=== Example:]
+ In $M_2(RR)$,
  $
  3 dot mat(1, 1; 1, 1; delim: "[") = mat(1, 1; 1, 1; delim: "[") + mat(1, 1; 1, 1; delim: "[") + mat(1, 1; 1, 1; delim: "[") = mat(3, 3; 3, 3; delim: "[").
  $
+ In $ZZ_6$: $underbrace(2, in ZZ) dot underbrace(3, in ZZ_6) = 3 +_6 3 = 0$.

#underline[=== Remark:]
If $R$ is a ring and $a, b in R$, $m, n in ZZ$, then
+ $(m + n)dot a = m dot a + n dot a$
+ $m (a + b) = m a + m b$
+ $(m n) a = m(n a)$
+ $m(a b) = (m a)b = a(m b)$
+ $(m a)(n b) = (m n) (a b)$

\
== #underline[Characteristic of a Ring]

#underline[=== Definition:]

The characteristic of a ring $R$ is the least positive integer $n$ such that $forall a in R, n dot a = 0$. If no such integer exists, $R$ is said to be of characteristic $0$.

#underline[=== Example:]

+ $ZZ_6 = {0, 1, 2, 3, 4, 5}$. $"char"(ZZ_6) = 6$.
+ char$(ZZ) = 0$.
+ $RR, QQ, CC$ are of characteristic $0$.

#underline[=== Theorem 2.21:]

Let $R$ be a ring with unity $1$. 
+ If $1$ has infinite order, then $"char"(R) = 0.$
+ If $1$ has order $n$, then $"char"(R) = n$.

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  *#underline[Proof]*. (Exercise)
]

#underline[=== Example:]
+ $"char"(ZZ_n) = n$
+ $"char"(M_2(RR)) = 0$ 


#underline[=== Theorem 2.22:]

The characteristic of an integral domain is $0$ or prime.

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  *#underline[Proof]*. (Exercise)
]



#pagebreak()

= Ideals and Factor Rings (Part I)

#line(length: 100% )

#underline[== Ideals]

#underline[=== Definition:]

A subring $I$ of a ring $R$ is called an #underline[ideal of _R_] if $forall r in R, forall a in I, r a in I "and" a r in I$.

#underline[=== Example:]

+ Let $R$ be a ring. Then, ${0}$ (#underline[_trivial ideal_]) and $R$ (#underline[_improper ideal_]) are ideals of $R$.

  Ideal $I$ s.t. $I eq.not R$ is a #underline[_proper ideal_] of $R$.
+ $n ZZ subset.eq ZZ$ ($n in ZZ^(+)$)
  $n ZZ$ is an ideal of $ZZ$.

  $(because)$ Let $r in ZZ, x in n ZZ ==> x = n k$ for some $k in ZZ$. $x r = r x = r(n k) = (r n)k = (n r) k in n ZZ$.
  
  $therefore n ZZ$ is an ideal of $ZZ$. 

#underline[=== Ideal Subring Test (Theorem 2.23):]

Let $R$ be a ring and $cancel(circle) eq.not I subset.eq R$. Then, $I$ is an ideal if and only if the following hold:
+ $forall a, b in I, a -b in I$,
+ $forall r in R, a in I, r a in I "and" a r in I$.

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  #underline[=== Principal Ideal]
  Let $R$ be a commutative ring with unity. Fix $a in R$. Consider ${a r | r in R} =: angle.l a angle.r = I$ 
  - $a dot 1 = a in I$ so $I eq.not cancel(circle)$.
  - Let $x, y in I ==> x = a r_1, y = a r_2$ for some $r_1, r_2 in R$.
  $
  x - y = a r_1 - a r_2 = a underbrace((r_1-r_2), in R) in I.
  $
  - Let $r in R, x in I ==> x = a r_1$ for some $r_1 in R$. 
  $
  x r =  r x = r (a r_1) = (r a)r_1 = (a r) r_1 = a (r r_1) in I.
  $
  $therefore I$ is an ideal of $R$.

  $I$ is called the #underline[_principal ideal generated by $a$_], denoted $(a)$ or $angle.l a angle.r$.
]

#underline[=== Example:]
+ $ZZ$. Let $n in ZZ$. The principal ideal of $ZZ$ generated by $n$
$
angle.l n angle.r = {n dot k | k in ZZ} = n ZZ
$


#pagebreak()

#underline[== Factor Rings]


#underline[=== Concept:]



Consider $S$, subring of $R$. $angle.l S, + angle.r$ is a(n) (abelian) subgroup of the abelian group $angle.l R, + angle.r$. So, $S lt.tri.eq R$.

$R slash S ={r + S | r in R}$ is an abelian group under addition of left cosets.

$(*)$ Define multiplication of left cosets as follows:

$
(r_1 + S)(r_2 + S) = (r_1 r_2) + S
$
Note: It is not well-defined on some cases.


#underline[=== Lemma 2.24:]

Let $R$ be a ring and $I$ an ideal of $R$. Then, multiplication of left cosets of $I$ is a well-defined operation on the set $R slash I = {a + I | a in R}.$

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  *#underline[Proof]*. Suppose $a + I = c + I$ and $b + I = d + I$ for some $a, b, c, d in R$. 
  
  (WTS: $(a + I)(b + I) = (c + I)(d + I) ==> a b + I = c d + I ==> -a b + c d in I$)

  $
  a + I = c + I &<==> -a + c in I \
  &<==> -a + c = x, exists x in I \
  &==> c = a + x
  $

  $
  b + I = d + I &<==> -b + d in I \
  &<==> -b + d = y, exists y in I \
  &==> d = b + y
  $

  Now, 
  $
  c d &= (a + x) (b + y) \
  &= a(b + y) + x(b + y) \
  &= a b + a y + x b + x y \
  &==> - a b + c d = underbrace(underbrace(a, R) underbrace(y, I), I) + underbrace(underbrace(x, I) underbrace(b, R), I) + underbrace(underbrace(x, I) underbrace(y, I), I) in I
  $

  $therefore$ multiplication of left cosets is well-defined. $square.filled$
]

#underline[=== Theorem 2.25:]

Let $I$ be an ideal of a ring $R$. Then, $R slash I$ is a ring under addition and multiplication of left cosets

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  *#underline[Proof]*. Note that addition and multiplication of left cosets are binary operators in $R slash I$

  $cal(R)_1$: $R slash I$ is an abelian group under addition of left cosets.

  $cal(R)_2$: Let $a + I, b + I, c + I in R slash I$.

  $
  (a + I)[(b + I)(c + I)] &= (a + I)( b c + I) \
  &= a (b c) + I \
  &= (a b) c + I \
  &= (a b + I)(c + I) = [(a + I)(b + I)](c + I)
  $

  $cal(R)_3$: Let $a + I, b + I, c + I in R slash I$.

  $
  (a+I)[(b + I)+ (c + I)] &= (a+I)[(b+c)+ I] \
  &= a(b+c)+ I \
  &= (a b+ a c)+ I \
  &= (a b+ I) + (a b+ I) \
  $

  $
  [(a+I) +(b + I)](c + I)] &= [(a +b)+ I](c + I) \
  &= (a + b)c+ I \
  &= (a c+ b c)+ I \
  &= (a c+ I) + (b c+ I) \
  $

  $therefore R slash I$ is a ring under addition and multiplication of left cosets. $square.filled$

  === #underline[Remark]:
  $R slash I$ is called the factor ring or _#underline[quotient ring]_ of _#underline[$R$ modulo $I$]_.
  
]

#underline[=== Remarks:]
+ If $R$ is commutative, then $R slash I$ is commutative.
+ If $R$ has unity 1, then $R slash I$ has unity $1 + I$.

#underline[=== Examples:]
- $ZZ slash 3 ZZ = {3 ZZ, 1 + 3 ZZ, 2 + 3ZZ}$

#align(center)[
  #table(
      columns: (auto, auto, auto, auto),
      inset: (x: 5pt, y: 5pt),
      stroke: 0.5pt,
      align: center,
      [*$plus$*], [*$3ZZ$*], [*$1 + 3ZZ$*], [*$2 +3ZZ$*],
      [*$3 ZZ$*], [$3 ZZ$], [$1 + 3ZZ$], [$2 + 3ZZ$],
      [*$1 + 3ZZ$*], [$1 + 3ZZ$], [$2 + 3ZZ$], [$3ZZ$],
      [*$2 + 3ZZ$*], [$2 + 3ZZ$], [$3ZZ$], [$1 + 3ZZ$],

    )

    #table(
      columns: (auto, auto, auto, auto),
      inset: (x: 5pt, y: 5pt),
      stroke: 0.5pt,
      align: center,
      [*$dot$*], [*$3ZZ$*], [*$1 + 3ZZ$*], [*$2 +3ZZ$*],
      [*$3 ZZ$*], [$3 ZZ$], [$3ZZ$], [$3ZZ$],
      [*$1 + 3ZZ$*], [$3ZZ$], [$1 + 3ZZ$], [$2+3ZZ$],
      [*$2 + 3ZZ$*], [$3ZZ$], [$2+3ZZ$], [$1 + 3ZZ$],

    )
]

$ZZ slash 3 ZZ$ is commutative and has unity $1 + 3 ZZ$. $(1 + 3ZZ)^(-1) = 1 + 3ZZ, (2 + 3ZZ)^(-1) = 2+3ZZ$

$therefore ZZ slash 3ZZ $ is a field.

- Consider $8 ZZ subset.eq 2ZZ$. $8 ZZ$ is an ideal of $2ZZ$. (Theorem 2.23)

  (a) $2ZZ slash 8 ZZ = {8ZZ, 2+8ZZ, 4 + 8ZZ, 6 + 8ZZ}$

  (b) 
  
#align(center)[
  #table(
      columns: (auto, auto, auto, auto, auto),
      inset: (x: 5pt, y: 5pt),
      stroke: 0.5pt,
      align: center,
      [*$plus$*], [*$8ZZ$*], [*$2 + 8ZZ$*], [*$4 +8ZZ$*], [*$6 +8ZZ$*],
      [*$8 ZZ$*], [$8 ZZ$], [$2 + 8ZZ$], [$4 + 8ZZ$], [$6 + 8ZZ$],
      [*$2 + 8ZZ$*], [$2 + 8ZZ$], [$4 + 8ZZ$], [$6 + 8ZZ$], [$8ZZ$],
      [*$4 + 8ZZ$*], [$4 + 8ZZ$], [$6 +8ZZ$], [$8ZZ$], [$2 + 8ZZ$],
      [*$6 + 8ZZ$*], [$6 + 8ZZ$], [$8ZZ$], [$2+8ZZ$], [$4 + 8ZZ$],

    )

    #table(
      columns: (auto, auto, auto, auto, auto),
      inset: (x: 5pt, y: 5pt),
      stroke: 0.5pt,
      align: center,
      [*$dot$*], [*$8ZZ$*], [*$2 + 8ZZ$*], [*$4 +8ZZ$*], [*$6 +8ZZ$*],
      [*$8 ZZ$*], [$8 ZZ$], [$8ZZ$], [$8ZZ$], [$8ZZ$],
      [*$2 + 8ZZ$*], [$8ZZ$], [$4 + 8ZZ$], [$8ZZ$], [$4+8ZZ$],
      [*$4 + 8ZZ$*], [$8ZZ$], [$8ZZ$], [$8ZZ$], [$8ZZ$],
      [*$6 + 8ZZ$*], [$8ZZ$], [$4+8ZZ$], [$8ZZ$], [$4 + 8ZZ$],

    )
]

(c) $2ZZ slash 8 ZZ$ is not an integral domain.


#pagebreak()

= Ring Homomorphism

#line(length: 100% )

#underline[=== Definition:]

A ring homomorphism from a ring $R$ to a ring $R'$ is a mapping $phi.alt$ from $R$ to $R'$ that preserves both ring operations, that is, $ ∀a, b ∈ R, phi.alt(a + b) = phi.alt(a) + phi.alt(b) "and" phi.alt(a b) = phi.alt(a)phi.alt(b). $

#underline[=== Remarks:]

Let $phi.alt  : R → R'$ be a ring homomorphism.

+ If $phi.alt$ is one-to-one, we call $phi.alt$ a #underline[_ring monomorphism_].
+ If $phi.alt$ is onto, we call $phi.alt$ a #underline[_ring epimorphism_].
+ If $phi.alt$ is a bijection, then $phi.alt$ is called a #underline[_ring isomorphism_].
+ If $phi.alt$ is bijective and $R'= R$, then $phi.alt$ is called a #underline[_ring automorphism_].

#underline[=== Definition:]

Two rings $R$ and $R'$ are said to be #underline[_isomorphic_], written $R tilde.equiv R'$, if there exists an isomorphism from $R$ to $R'$.

#underline[=== Remarks:]
If $phi.alt : R → R'$ is a ring homomorphism, then $phi.alt : angle.l R, + angle.r → angle.l R', +' angle.r$ is a group homomorphism. In particular,

+  If $0$ and $0'$ are the zero elements of $R$ and $R'$, then $phi.alt(0) = 0'$.
+ If $a ∈ R$, then $phi.alt(−a) = − phi.alt(a)$.
+ If $a ∈ R$ and $n ∈ ZZ$, then $phi.alt(n a) = n phi.alt(a)$.


#underline[=== Properties of Ring Homomorphisms (Theorem 2.26):]
+ If $a ∈ R$ and $n ∈ NN$, then $phi.alt(a n) = [phi.alt(a)]n.$
+ If $S$ is a subring of $R$, then $phi.alt(S) = {phi.alt(a)| a ∈ S}$ is a subring of $R'$.
+ If $R$ is commutative, then $phi.alt(R)$ is commutative.
+ If $I$ is an ideal of $R$, then $phi.alt(I)$ is an ideal of the ring $phi.alt(R)$ (but not necessarily of $R'$).
+ If $S'$ is a subring of $R'$, then $phi.alt^(−1)(S') = {a ∈ R | phi.alt(a) ∈ S'}$ is a subring of $R$.
+  Let $R$ be a ring with unity $1_R$.
  + Then $phi.alt(R)$ is a ring with unity $phi.alt(1_R)$.
  + If $a$ is a unit in $R$, then $phi.alt(a)$ is a unit in the ring $phi.alt(R)$ with $[phi.alt(a)]^(−1) = phi.alt(a^(−1))$.

  #block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  *#underline[Proof]*. (Exercise!)
5. Suppose $S'$ is a subring of $R'$. Show: $phi.alt^(−1)(S')$ is a subring of $R$.

Note that $angle.l S', + angle.r$ is a subgroup of $angle.l R', + angle.r$. Since $phi.alt$ is a group homomorphism, $angle.l phi.alt−1(S'), + angle.r$ is a subgoup of $angle.l R, + angle.r$.

It remains to be shown that $phi.alt^(−1)(S')$ is closed under multiplication.

Let $x, y ∈ phi.alt^(−1)(S')$. WTS: $x y ∈ phi.alt^(−1) (S')$, i.e. $phi.alt(x y) ∈ phi.alt^(−1)(S')$.

Now, $x, y ∈ phi.alt^(−1)(S') ⇒ phi.alt(x), phi.alt(y) ∈ S' ⇒ phi.alt(x y) = φ(x)φ(y) ∈ S'$

Since $S'$ is a subring of $R'$. Thus $x y ∈ phi.alt^(−1)
(S').

∴ phi.alt^(−1) (S') $ is a subring of $ R$.  
]

#underline[=== Examples:]
+ Consider the map $phi.alt : ZZ → 2ZZ$ given by $phi.alt(k) = 2k$.

  Let $a, b ∈ ZZ$. Then
  - $phi.alt(a + b) = 2(a + b) = 2a + 2b = phi.alt(a) + phi.alt(b)$
  - $phi.alt(a b) = 2a b $ but $ phi.alt(a)phi.alt(b) = (2a)(2b) = 4a b$
  Thus $phi.alt$ is not ring homomorphism.

+ Consider the map $phi.alt : ZZ → ZZ × ZZ$ given by $phi.alt(x) = (x, 0)$. Then $phi.alt$ is a ring homomorphism. (Why?) 

  $phi.alt(ZZ) = {(x, 0)| x ∈ ZZ}$ is a commutative ring with unity (unity in $phi.alt(ZZ)$ is $phi.alt(1) = (1, 0)$). The units of $phi.alt(ZZ)$ are $phi.alt(1) = (1, 0)$ and $phi.alt(−1) = (−1, 0)$.

\
#underline[== Kernel of a Homomorphism]


#underline[=== Definition:]
Let $R, R'$ be rings with $0'$, the zero element in $R'$. Let $phi.alt : R → R'$ be a ring homomorphism.
The kernel of $phi.alt$ is the set

$
ker phi.alt := {a ∈ R | phi.alt(a) = 0'} = phi.alt^(−1)({0'})
$

#underline[=== Remarks:]
+ $phi.alt$ is one-to-one if and only if $ker phi.alt = {0}$.
+ $phi.alt$ is a ring isomorphism if and only if $phi.alt$ is onto and $ker phi.alt = {0}$.
+ If $a ∈ R$ and $phi.alt(a) = a'$ then 
$
phi.alt^(−1)(a') = {r ∈ R | phi.alt(r) = a'} = a + ker phi.alt
$

#underline[=== The Kernel is an Ideal (Theorem 2.27):]
Let $phi.alt : R → R'$ be a ring homomorphism. Then $ker phi.alt$ is an ideal of $R$.

  #block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  *#underline[Proof]*. Let $0'$ be the zero element of $R'$. Since ${0'}$ is a subring of $R'$, then $phi.alt^(−1)({0'}) = ker phi.alt$ is a subring of $R$ (by Theorem 2.26).

  Let $a ∈ ker phi.alt$ and $r ∈ R$. (WTS: $a r$ and $r a$ are in $ker phi.alt$)

  $
  phi.alt(a r) = phi.alt(a)phi.alt(r) = 0' · phi.alt(r) = 0'
  $

  Since $phi.alt(a r) = 0'$, then $a r ∈ ker phi.alt$.
  
  Using a similar argument, we can show that $r a ∈ ker phi.alt$.
  
  $∴ ker phi.alt$ is an ideal of $R$.
]
\

#underline[== First Isomorphism Theorem for Rings (Theorem 2.28):]
Let $phi.alt : R → R'$ be a ring homomorphism. Then
$ μ : R slash ker phi.alt → phi.alt(R) $
given by $μ(a + ker phi.alt) = phi.alt(a)$ is a ring isomorphism.
In particular, $R slash ker phi.alt tilde.equiv phi.alt(R)$ (as rings).

  #block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  *#underline[Proof]*. It follows from the First Isomorphism Theorem for Groups that $μ$ is a group isomorphism. (WTS: $μ$ preserves multiplication.)
  
  Let $a + ker phi.alt, b + ker phi.alt ∈ R slash  ker phi.alt$. Then,
  $
  μ[(a + ker phi.alt)(b + ker phi.alt)] &= μ(a b + ker phi.alt)\ 
  &= phi.alt(a b) = phi.alt(a)phi.alt(b)  \
  &= μ(a + ker phi.alt)μ(b + ker phi.alt)
  $
  $∴ μ$ is a ring isomorphism.
]

#underline[=== Remark:]
The isomorphism $μ$ is called the #underline[_natural_] or #underline[_canonical isomorphism_] from $R slash ker phi.alt$ to $phi.alt(R)$.

#underline[=== Examples:]

+ Let $phi.alt : ZZ → ZZ_n$ be the mapping such that $phi.alt(m) =$ the remainder when $m$ is divided by $n$. Then $phi.alt$ is a ring epimorphism. (Verify this!)
  $ ker phi.alt = n ZZ $

  By the FITR,

  $ ZZ slash n ZZ = ZZ slash ker phi.alt tilde.equiv phi.alt(ZZ) = ZZ_n $

  Thus,

  $ ZZ slash n ZZ tilde.equiv ZZ_n "as rings." $  

+ Consider the ring homomorphism $phi.alt : ZZ → ZZ × ZZ$ where $phi.alt(x) = (x, 0)$.

  $ ker phi.alt = {0} $

  By the FITR,

  $ ZZ slash {0} = ZZ slash ker phi.alt tilde.equiv phi.alt(ZZ) = {(x, 0)| x ∈ ZZ} $
  
  Noting that $ZZ slash {0} tilde.equiv ZZ$, we get
  
  $ ZZ tilde.equiv {(x, 0)| x ∈ ZZ} $
  
\
#underline[== Canonical Isomorphism from _R_ to _R/I_ (Theorem 2.29):]
Let $I$ be an ideal of a ring $R$. Then $γ : R → R slash I$ given by $γ(a) = a + I$ is a ring homomorphism with $ker γ = I$.

  #block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  *#underline[Proof]*. It follows from Theorem 2.12 that $γ$ is a group homomorphism with $ker γ = I$. (WTS: $γ$ preserves multiplication.)
  
  Let $a, b ∈ R$. Then $γ(a b) = a b + I = (a + I)(b + I) = γ(a)γ(b)$.
  
  $∴ γ$ is a ring homomorphism.
]


#pagebreak()

= Ideals and Factor Rings (Part II)

#line(length: 100% )

#underline[=== Concept:]
Given: $R$, a commutative ring with unity. 

$I$, ideal of $R$
$==> R slash I$ is a commutative ring with unity

- _Question 1_: If $R$ is a field, what are the possible factor rings $R slash I$ ?
- _Question 2_: When is the factor ring $R slash I$ a field?
- _Question 3_: When is the factor ring $R slash I$ an integral domain?


#underline[== Ideals of a Field (Theorem 2.30):]
Let $R$ be a ring with unity $1$ and let $I$ be an ideal of $R$. If $I$
contains a unit of $R$ then $I = R$.

  #block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  *#underline[Proof]*. Suppose $u ∈ I$ is a unit of $R$. Then $∃u^(−1) ∈ R$ such that $1 = u^(−1)u ∈ I$ since $I$ is an ideal of $R$. Thus $1 ∈ I$.

  Clearly $I ⊆ R$. (NTS: $R ⊆ I$).
  Let $r ∈ R$. Now, $r = r · 1 ∈ I$ since $I$ is an ideal of $R$. Thus $R ⊆ I$ and so $I = R$.
]

#underline[=== Corollary 2.31:]
A field has no proper nontrivial ideals. That is, the only
ideals of a field $F$ are ${0}$ or $F$ itself.

  #block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
  *#underline[Proof]*. Let $F$ be a field and $I$ an ideal of $F$. Note that either $I$ is trivial (that is $I = {0}$) or $I$ is nontrivial.
  Suppose $I eq.not {0}$. Let $0 eq.not a ∈ I ⊆ F$. Thus $a$ is a unit of $F$. Hence $I = F$.
]

#underline[=== Remark:]
Let $F$ be a field and $I$ an ideal of $F$. Then either $I = {0}$ or
$I = F$. Then the factor rings $F slash I$ are
- $F slash {0} tilde.equiv F$
- $F slash F tilde.equiv {0}$


#underline[== Maximal Ideals]


#underline[=== Definition:]
A proper ideal $M$ of a ring $R$ is said to be #underline[_maximal_] if whenever $J$ is an ideal of $R$ such that $M ⊆ J ⊆ R$, either $J = M$ or $J = R$.


#underline[=== Examples:]
$3ZZ$ and $4ZZ$ are ideals of $ZZ$.

- Note that $4ZZ ⊂ 2ZZ ⊂ ZZ$. Thus $4ZZ$ is not a maximal ideal of $ZZ$.
- Suppose $n ZZ$ is an ideal of $ZZ$ such that $3ZZ ⊆ n ZZ ⊆ ZZ$. Since $3 ∈ 3ZZ ⊆ n ZZ$, then $n divides 3$. Hence $n = 3$ or $n = 1$. So $n ZZ = 3ZZ$ or $n ZZ = ZZ$. Thus $3ZZ$ is a maximal ideal of $ZZ$.

#underline[=== Remarks:]
Let $R$ be a ring.
+ The only ideal that properly contains a maximal ideal of $R$ is $R$.
+ A maximal ideal of $R$ may not be unique. That is, $R$ may have more than one maximal ideal. (e.g. $2ZZ$ and $5ZZ$ are both maximal ideals of $ZZ$)

#underline[=== Examples:]
The ideals of $ZZ_12$:
- $ZZ_12$
- $angle.l 2 angle.r = {0,2,4,6,8,10}$
- $angle.l 3 angle.r = {0,3, 6, 9}$
- $angle.l 4 angle.r = {0,4, 8}$
- $angle.l 6 angle.r = {0,6}$
- ${0}$

Is $angle.l 4 angle.r$ a maximal ideal of $ZZ_12$?

Is $angle.l 4 angle.r$ a maximal ideal of $angle.l 2 angle.r$?

What are the maximal ideals of $ZZ_12$?

\

#underline[== Factor Rings from Maximal Ideals are Fields (Theorem 2.32):]

Let $R$ be a commutative ring with unity and let $I$ be an
ideal of $R$. Then

$
R slash I "is a field" <==> I "is a maximal ideal of" R.
$

  #block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
    *#underline[Proof.]*
    $(==>)$ Suppose $R slash I$ is a field. Let $J$ be an ideal of $R$ such that $I ⊆ J ⊆ R$. (NTS: Either $J = I$ or $J = R$).

    Suppose $J eq.not I$. Then $∃b ∈ J slash I ==> I eq.not b + I ∈ R slash I ==> b + I$ is a unit in $R slash I ⇒ ∃(a + I) ∈ R slash I$ such that $(b + I)(a + I) = 1 + I ==> −b a + 1 ∈ I ⊂ J$.
    
    Thus $1 = b a + (−b a + 1) ∈ J ==> J = R$. 
    
    $∴ I$ is a maximal ideal of $R$.

    $(<==)$ Suppose $I$ is a maximal ideal of $R$. Since $R$ is commutative with unity, then so is $R slash I$. Note also that $I eq.not R$ since $I$ is maximal and so $1 in.not I$. Thus $1 + I eq.not I$. 
    
    (NTS: Every nonzero element of $R slash I$ is a unit.)
    
    Let $a + I$ be a nonzero element in $R slash I$ (i.e. $a ∈ R$ but $a in.not I$).

    Form $J := {r a + b |r ∈ R, b ∈ I }$. Claim: $J$ is an ideal of $R$.
    If $x ∈ I$ then $x = 0 · a + x ∈ J ⇒ I ⊆ J ⊆ R ⇒ J = I or J = R$. However, $a in.not I$ but $a = 1 · a + 0 ∈ J ==> J eq.not I$. Thus $J = R$.
    
    Now, $1 ∈ R = J ==> 1 = r a + b$ for some $r ∈ R, b ∈ I $  
    $ &==>  −r a + 1 = b ∈ I \ 
    &==> r a + I = 1 + I \
    &==> (r + I)(a + I) = (a + I)(r + I) = 1 + I  \
    &==> a + I "is a unit".
    $
    
    $∴ R slash I$ is a field.

    === #underline[Proof of claim that _J_ is an ideal of R]:
    #underline[Claim]: $J = {r a + b |r ∈ R, b ∈ I }$ is an ideal of $R$.

    #underline[_Proof._]
    - $J$ is nonempty: $0 = 0 · a + 0 ∈ J ==> J eq.not cancel(circle)$
    - If $x, y ∈ J$, show that $x − y ∈ J$. (Exercise!)
    - If $s ∈ R$ and $x ∈ J$, show that $s x ∈ J$ and $x s ∈ J$.
    
    $∵ x ∈ J ==> x = r a + b$ for some $r ∈ R, b ∈ I$. So $s x = s(r a + b) = (s r)a + s b ∈ J$. Note that $R$ is commutative so $ x s = s x ∈ J$. $square.filled$
    
]

#underline[=== Appplication of Theorem 2.32:]
Consider the ideals $3ZZ$ and $4ZZ$ of $ZZ$.
- $ZZ slash 3ZZ tilde.equiv ZZ_3$ is a field, thus $3ZZ$ is a maximal ideal of $ZZ$.
- $ZZ slash 4ZZ tilde.equiv ZZ_4$ is not a field, thus $4ZZ$ is not a maximal ideal of $ZZ$.

#underline[=== Remark:] 
$n ZZ$ is a maximal ideal of $ZZ$ if and only if $n$ is prime.


#underline[=== Converse of Corollary 2.31 holds (Corollary 2.33):]
A commutative ring with unity is a field if and only if it has
no proper nontrivial ideals.

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
    *#underline[Proof.]* 

    $(==>)$ Follows from Corollary 2.31.
    
    $(<==)$ Suppose a commutative ring $R$ with unity has no proper nontrivial ideals. Then ${0}$ is a maximal ideal. Thus $R tilde.equiv R slash {0}$ is a field.
  
  ]

\

#underline[== Prime Ideals]

#underline[=== Definition:]
A proper ideal $P$ of a commutative ring $R$ is said to be #underline[_prime_] if whenever $a, b ∈ R$ such that $a b ∈ P$ then either $a ∈ P$ or $b ∈ P$.

#underline[=== Examples:]
+ Consider $6ZZ$. Note that $2 · 3 ∈ 6ZZ$ but neither $2$ nor $3$ are in $6ZZ$. Thus $6ZZ$ is not a prime ideal of $ZZ$.

+ Consider the trivial ideal ${0} in ZZ_12$. Is ${0}$ a prime ideal of $ZZ_12$?
+ ${0}$ is a prime ideal of an integral domain $D$.

$∵$ Let $a, b ∈ D$ such that $a b ∈ {0} ==> a b = 0 ==> a = 0$ or
$b = 0 ==> a ∈ {0} "or" b ∈ {0}$.

\

#underline[== Factor Rings from Prime Ideals (Theorem 2.34):]
Let $R$ be a commutative ring with unity and let $I$ be an ideal of $R$. Then
$
R slash I "is an integral domain" <==> I "is a prime ideal of" R.
$

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
    *#underline[Proof.]* 

    $(==>)$ Suppose $R slash I$ is an integral domain. Let $a, b ∈ R$ such that $a b ∈ I$. Then $a b + I = I ==> (a + I)(b + I) = I$. Since $R slash I$ is an integral domain, either $a + I = I$ or $b + I = I$, which means that either $a ∈ I$ or $b ∈ I$.
    
    $(<==)$ Suppose $I$ is a prime ideal of $R$. Since Then $R$ is a commutative ring with unity $1$, then so is $R slash I$. Note also that $I eq.not R$ since$ I$ is prime and so $1 in.not I$. Thus $1 + I eq.not I$. (NTS: $R slash I$ has no zero divisors.)
    
    Let $a + I, b + I ∈ R slash I$ such that $(a + I)(b + I) = I$. Then, $a b + I = I ==> a b ∈ I$. Since $I$ is prime, then either $a ∈ I$ or $b ∈ I ==> a + I = I "or" b + I = I$
    
    $∴ R slash I$ is an integral domain.
  
  ]

#underline[=== Applications of Theorem 2.34:]
+ $ZZ slash 4ZZ tilde.equiv ZZ_4$ is not an integral domain. Thus $4ZZ$ is not a prime ideal of $ZZ$. Indeed $2 · 2 ∈ 4ZZ$ but $2 in.not 4ZZ$.

  #underline[Remark]: $n ZZ$ is a prime ideal of $ZZ$ if and only if $n$ is prime.
  
+ Let $I = {(x, 0)| x ∈ ZZ} ⊆ ZZ × ZZ$. Then $I$ is an ideal of $ZZ × ZZ$. (Exercise!)

Suppose $(a, b),(c, d) ∈ ZZ × ZZ$ such that $(a, b)(c, d) = (a c, b d) ∈ I$.
Then $ b d = 0 ==> b = 0$ or $d = 0 ==> (a, b) ∈ I$ or $(c, d) ∈ I$. Hence $I$ is prime.
Thus $(ZZ × ZZ) slash I$ is an integral domain.

(Exercise:) Use FITR (First Isomorphism Theorem for Rings) to show
that $(ZZ × ZZ) slash I tilde.equiv ZZ$.

\

#underline[== Maximal Ideals are Prime Ideals (Corollary 2.35):]
Every maximal ideal of a commutative ring $R$ with unity is
a prime ideal of $R$.

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
    *#underline[Proof.]* 
    Let $I$ be a maximal ideal of $R$. By Theorem 2.32, $R slash I$ is a field. Hence $R slash I$ is an integral domain. Thus $I$ is a prime ideal of $R$. $square.filled$
  ]

#underline[=== Remarks:]
+ The converse of Corollary 2.35 does not hold. That is, a prime ideal of a commutative ring $R$ with unity may not be a maximal ideal of R. 

  e.g., $I = {(x, 0)| x ∈ ZZ}$ is a prime ideal of $ZZ × ZZ$ which is not a maximal ideal of $ZZ × ZZ$. (Why?)

+ Corollary 2.35 does not hold if $R$ has no unity. 

  e.g. $2ZZ$ has no unity and $4ZZ$ is a maximal ideal of $2ZZ$ but $4ZZ$ is not a prime ideal of $2ZZ$. (Why?)



#pagebreak()

= Field of Quotients of Integral Domains and Prime Fields

#line(length: 100% )

#underline[== R with unity contains a homomorphic image of $ZZ$ (Lemma 2.36):]
Let $R$ be a ring with unity $1$. The mapping $phi.alt : ZZ → R$ given
by $phi.alt(m) = m · 1$ is a ring homomorphism.

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
    *#underline[Proof.]* 
    Let $m, n ∈ ZZ$. Then 
    $ 
    phi.alt(m + n) &= (m + n) · 1 = m · 1 + n · 1 = phi.alt(m) + phi.alt(n) \
    phi.alt(m n) &= (m n) · 1 = (m n) · 1 · 1 = (m · 1)(n · 1) = phi.alt(m)phi.alt(n)
    $

  ]

#underline[=== Remark:]
Note that $phi.alt(ZZ)$ is a subring of $R$.

#underline[=== The Characteristic of Rings with Unity]
$"char" R =$ smallest positive integer $n$ such that $n · a = 0$ for all $a ∈ R$.

If no such positive integer exists, then $"char" R = 0$.

#underline[Recall]: $R$, a ring with unity 1
- $"char" R = n <==> |1| = n$ in the group $angle.l R, + angle.r$
- $"char" R = 0 <==> 1$ has infinite order in the group $angle.l R, + angle.r$

#underline[ === Structure of R based on its Characteristic (Theorem 2.37)]
Let $R$ be a ring with unity.
+ $"char" R = n > 1 ==> R$ contains a subring isomorphic to $ZZ_n$
+ $"char" R = 0 ==> R$ contains a subring isomorphic to $ZZ$

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
    *#underline[Proof.]* 
    Consider the ring homomorphism $phi.alt : ZZ → R$ given by $phi.alt(m) = m · 1$. 
    
    By the FITR, $ZZ slash ker phi.alt tilde.equiv phi.alt(ZZ)$. 
    
    Note that $ker phi.alt = {m ∈ Z | phi.alt(m) = 0} = {m ∈ Z | m · 1 = 0}$. 
    - Suppose $"char" R = n > 1$. So $|1| = n$. That is, $n · 1 = 0$ and  $ m · 1 = 0 <==> n | m <==> m ∈ n ZZ. $
    
      Thus $ker phi.alt = n ZZ$. Hence by FITR, 
      $ phi.alt(ZZ) tilde.equiv ZZ slash ker phi.alt = ZZ slash n ZZ tilde.equiv ZZ_n. $

    - Suppose $"char" R = 0$. Then $1$ has infinite order. Thus $m · 1 = 0 <==> m = 0$. Thus $ker phi.alt = {0}$. Hence by FITR, 
    $
    phi.alt(ZZ) tilde.equiv ZZ slash  ker phi.alt = ZZ slash {0} tilde.equiv ZZ.
    $
  ]
\
#underline[=== Examples:] 
Consider the ring $R = M_2(RR)$ with unity $display(mat(1, 0; 0, 1; delim: "["))$. Note that the order of $display(mat(1, 0; 0, 1; delim: "["))$ is infinite.(Why?)

Hence $"char" M_2(RR) = 0$.

Thus $M_2(RR)$ has a subring isomorphic to $ZZ$ by Theorem 2.37.
This subring is $phi.alt(ZZ)$ where $phi.alt : ZZ → M_2(RR)$ is given by

$
phi.alt(m) = m mat(1, 0; 0, 1; delim: "[") = mat(m, 0; 0, m; delim: "[")
$

Thus
$
phi.alt(ZZ) = {phi.alt(m)| m ∈ ZZ} = {mat(m, 0; 0, m; delim: "[") mid(|) m ∈ ZZ} tilde.equiv ZZ
$

\

== #underline[Field of Quotients of an Integral Domain]
Consider the integral domain $ZZ$.

Note that $ZZ$ is not a field. But $ZZ$ is a subring of the field $QQ$.
- #underline[_Question_]: Given any integral domain $D$, is there a field $F$ that contains $D$? If so, what is the smallest field that will contain $D$?

#underline[_Construction of $QQ$ from $ZZ$_]: 
$
ZZ ”⊂” {(a, b)| a, b ∈ ZZ, b eq.not 0} &--> QQ = {a/b mid(|) a, b ∈ ZZ, b eq.not 0} \
(a, b) + (c, d) = (a d + b c, b d) &-->
a/b  + c/d = (a d + b c)/(b d)\

(a, b)(c, d) = (a c, b d) &--> (a/b)(c/d) = (a c)/(b d) \

(1, 2),(2, 4),(3, 6)· · · &--> 1/a \
(a, b) ∼ (c, d) <==> a d = b c &--> a/b = c/d <==> a d = b c
$

\

== #underline[Theorem 2.38]: 

Let $D$ be an integral domain. Then there exists a field that
contains a subring which is isomorphic to $D$.

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
    *#underline[Proof.]* 
    Consider $S = {(a, b)| a, b ∈ D, b eq.not 0)} ⊂ D × D$.\
    
    Define the relation on $S$ by $(a, b) ∼ (c, d) <==> a d = b c$.
    
    #underline[Claim 1]: $∼$ is an equivalence relation on $S$. (Exercise!) 
    Denote the equivalence class of $(a, b)$ by $[a, b]$. 
    
    Note that $[a, b] = [c, d] <==> a d = b c$
    
    Let $F := {[a, b] |(a, b) ∈ S}$
    
    Define the following operations on $F$:

$
"addition"&: [a, b] + [c, d] = [a d + b c, b d] \
"multiplication"&: [a, b] · [c, d] = [a c, b d]
$

#underline[Claim 2]: The defined operations are well-defined binary operations on $F$. (Exercise!)

#underline[Claim 3]:
#set enum(numbering: "a.")
  + If $0 eq.not b ∈ D$ then $[0, b] = [0, 1]$.
  + If $0 eq.not k ∈ D$ and $[a, b] ∈ F$ then $[k a, k b] = [a, b]$.
  + If $0 eq.not a ∈ D$ then $[a, a] = [1, 1]$ 
(Exercise!)

We now show that $F$ is a field.

#underline[$F$ is a ring]:

$cal(R_1)$: $angle.l  F, + angle.r$ is an abelian group.

- $+$ is commutative: Let $[a, b], [c, d] ∈ F$.
$ [a, b] + [c, d] = [a d + b c, b d] = [c b + d a, d b] = [c, d] + [a, b] $
- $+$ is associative: (Exercise!)
- additive identity: Consider $[0, 1] ∈ F$. For any $[a, b] ∈ F$,
$ [0, 1] + [a, b] = [a, b] + [0, 1] = [a · 1 + b · 0, b · 1] = [a, b] $
- additive inverse: Let $[a, b] ∈ F$. Its additive inverse is $[−a, b]$ since 
$ [a, b] + [−a, b] = [−a, b] + [a, b] = [−a b + a b, b^2] = [0, b^2] = [0, 1] $

$cal(R)_2$: Multiplication is associative. (Exercise!)

$cal(R)_3$: Left and Right Distributive Laws: (Exercise!) (Hint: You may need to use Claim 3(b).)

#underline[$F$ is commutative]: Given $[a, b], [c, d] ∈ F$,

$ [a, b][c, d] = [a c, b d] = [c a, d b] = [c, d][a, b] $

#underline[$F$ has unity]: unity in $F$ is $[1, 1]$ since $[a, b][1, 1] = [1, 1][a, b] = [a, b] ∀[a, b] ∈ F$. Clearly,
$[1, 1] eq.not [0, 1]$. $(∵ 1 · 1 6= 1 · 0.)$

#underline[$F$ is a division ring]: Let $[a, b] ∈ F$ such that $[a, b] eq.not [0, 1]$. Then $a · 1 eq.not b · 0 ==> a eq.not 0 ==> [b, a] ∈ F$. Note that $[a, b][b, a] = [a b, b a] = [a b, a b] = [1, 1]$.
Thus $[a, b]^(−1) = [b, a]$.

$∴ F$ is a field under the operations addition and multiplication as defined.

Lastly, we show that $F$ contains a subring which is isomorphic to $D$.

Consider $phi.alt : D → F$ given by $phi.alt(a) = [a, 1]$.
Let $a, b ∈ D$. Then $phi.alt(a) + phi.alt(b) = [a, 1] + [b, 1] = [a + b, 1] = phi.alt(a + b)$ and $phi.alt(a)phi.alt(b) = [a, 1][b, 1] = [a b, 1] = phi.alt(a b)$

Thus, $phi.alt$ is a ring homomorphism.

Note that $ker phi.alt = {a ∈ D | phi.alt(a) = [0, 1]} = {a ∈ D | [a, 1] = [0, 1]}$.
But $[a, 1] = [0, 1] <==> a · 1 = 1 · 0 <==> a = 0$.
Thus $ker phi.alt = {0}$.
So by the FITR,

$ phi.alt(D) tilde.equiv D slash ker phi.alt = D slash {0} tilde.equiv D $
$∴ D$ is isomorphic to $phi.alt(D) = {[a, 1] | a ∈ D}$ which is a subring of $F$.

]

=== #underline[Remarks]: 
+ The field $F$ in Theorem 2.38 is called the field of quotients of $D$.
+ We say that the integral domain $D$ is embedded in its field of quotients $F$ and we write $D arrow.hook F$.

=== #underline[Example]: 
+ $QQ $ is the field of quotients of $ZZ$.

\

== #underline[Theorem 2.39]: 
Let $D$ be an integral domain and $F$ its field of quotients. Suppose $K$ is a field that contains $D$. Then $K$ contains a subfield $L$ such that $D ⊆ L ⊆ K$ and $L$ is isomorphic to $F$.

=== #underline[Remark]: 
The field of quotients $F$ of $D$ is the smallest field that contains $D$ and is unique (up to isomorphism).

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
    *#underline[Proof.]* Let $[a, b] ∈ F$. Then $a, b ∈ D$ and $b eq.not 0$. Thus $a, b ∈ K$ and $b$ is a unit in $K$.

    Define $phi.alt : F → K$ given by $phi.alt([a, b]) = a b^(−1)$. Then $phi.alt$ is a well-defined monomorphism. (Exercise!)
    
    Set $L = phi.alt(F)$. By FITR, 
    $ L = phi.alt(F) tilde.equiv F slash ker phi.alt = F slash {0} tilde.equiv F $
    Thus $L$ is a subfield of $K$ which is isomorphic to $F$.
    For every $a ∈ D, a = a · 1 = a · 1 −1 = phi.alt([a, 1])$. Thus $D ⊆ L ⊆ K$.
  ]


  #pagebreak()

= Prime Subfield of a Field

#line(length: 100% )

_Recall_: The characteristic of an integral domain is either $0$ or prime $p$.

#underline[== Theorem 2.40:]
Let $F$ be a field.
+ $F$ is of prime characteristic $p ==> F$ contains a subfield isomorphic to $ZZ_p$
+ $F$ is of characteristic $0 ==> F$ contains a subfield isomorphic to $QQ$.

#block(stroke: 1pt, radius: 5pt, inset: 15pt, width: 100%)[
    *#underline[Proof.]* 
    + Since $"char" F = p, F$ contains a subring $S$ isomorphic to $ZZ_p$.
    
      Since $p$ is prime, $ZZ_p$ is a field. Thus $S$ is a subfield of $F$ isomorphic to $ZZ_p$.
    
    + If $"char" F$ is $0$, then $F$ contains a subring $S$ isomorphic to $ZZ$. So $S$ is an integral domain contained in the field $F$. By Theorem 2.39, $F$ contains a subfield $L$ which is isomorphic to the field of quotients $F_S$ of $S$.
    
    Since $S tilde.equiv ZZ$, $F_S tilde.equiv QQ$. Thus $L tilde.equiv QQ$.

  ]

  #underline[=== Definition:]
The subfield of a field $F$ that is isomorphic to either $ZZ_p$ or $QQ$ is called a prime subfield of $F$.

  #underline[=== Remark:] 
  A prime subfield of $F$ is the smallest subfield of $F$. Equivalently, every subfield of $F$ must contain the prime subfield of $F$.


#underline[=== Examples:] 
+ Identify the prime subfield of the field $QQ(√2) = {a + b√2 | a, b ∈ QQ}.$

+ Suppose $F$ is a field with $81$ elements. The prime subfield of $F$ is isomorphic to which field?

#underline[=== Solution:] 
+ The unity in $QQ(√2)$ is $1$. Since order of $1$ is infinite $==>$ $"char" Q(√2) = 0$. Thus the prime subfield of $QQ(√2)$ is $QQ$.

+ Note: order of $angle.l F, + angle.r$ is $81$.

  order of $1 = "char" F = p$ for some prime $p ==> p$ divides $81 = 3^4 ==> p = 3$

Thus the prime subfield of $F$ is isomorphic to $ZZ_3$.