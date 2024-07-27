 #set text(font: "Fira Sans Math")
#set page(paper: "a4")
#set text(size: 30pt)
#set align(horizon)
= Math 110.1
ABSTRACT ALGEBRA I: Unit I

#set text(size: 14pt, )
#emph[Course Notes by: Jeremiah Daniel Regalario] \
#emph[II-BS Mathematics] \
#emph[Lilibeth Valdez]


#pagebreak()
#set page(
  margin: (top: 60pt, bottom: 60pt),
  numbering: "1",
)

#set text(font: "Fira Sans Math", size: 12pt)
#set align(top)

= The Division Algorithm in $ZZ$ (Theorem 1.1)

#line(length: 100% )

#underline[=== Statement:]

Let $n in ZZ$ such that $n > 0$. Let $m in ZZ$. Then, there exist unique $q, r in ZZ $ with the property $m=n q+r$ where $0 <= r <= n$.

$ (forall n in NN)(forall m in ZZ)(exists!q, r in ZZ | m = n q + r and 0 <= r < n) $

#underline[=== Remark:]

- We call $q$ and $r$ as the #underline[_quotient_] and #underline[_remainder_], respectively, when $m$ is divided by $n$.
- The dividend $m$ #underline[may be] a _negative number_.

#underline[=== Example:]
- $n = 3 and m = -17 arrow.double.long m = 3(-6) + 1$

\

#underline[== The Divides ($divides$) Notation]

#underline[=== Definition:]

Let $m, n in ZZ$ with $n > 0$. We say that $n$ divides $m$ (or, equivalently, $n$ is a factor of $m$, or $n$ is a divisor of $m$) written $n divides m$ if (and only if):
$ exists k in ZZ, m = n k $

#underline[=== Example:]
- $6 divides -18$ since $-18=6(-3)$
- $3divides.not -16$

#underline[=== Remark:]

- Let $a, b, n in ZZ$ with $n>0$. $n|(a - b)$ if and only if $a$ and $b$ leave the same remainder when divided by $n$.
  #block(stroke: 1pt, radius: 5pt, inset: 15pt)[
    #underline[*Proof*].
  By the division algorithm, there exists unique integers $q_1, r_1, q_2, r_2 in ZZ$ such that $a = n q_1 + r_1$ and $b = n q_2 + r_2$ where $0 <= r_1, r_2 < n$.
  
  ($arrow.double.long.l$) Assume that $r_1 = r_2$. Then, $r_1 - r_2 = 0$. It follows that:
  $ a - b &= (n q_1 + r_1) - (n q_2 + r_2) \
  &= a - b \
  &= n q_1 - n q_2 + (r_1  - r_2) \
  &= n(q_1 - q_2)
  $
  where $q_1 - q_2 in ZZ$. Hence, $n|(a - b). $ 
  
  ($arrow.double.long$) Assume that $n divides (a - b)$. Then, there exists $k in ZZ$ such that $a-b=n k$. It follows that:
  $ n k &= a - b \
  &= (n q_1 + r_1) - (n q_2 + r_2) \
  &= n (q_1 - q_2) + (r_1  - r_2) \
  $
  From here, we get that:
  $ r_1  - r_2 = n(k - (q_1 - q_2)), \
  space space k - (q_1 - q_2) in ZZ \
  arrow.long.double n divides (r_1 - r_2)
  $
  Note that $0 <= r_1, r_2 < n arrow.double.long -n < r_1 -r_2 < n$.
  
  where $q_1 - q_2 in ZZ$. Hence, $n divides (a - b). $ Since $0$ is the only integer between $-n$ and $n$ which is divisble by $n$, then $r_1 - r_2 = 0 arrow.long.double r_1 = r_2.$ 
  $square.filled$
]
- The definition also holds for $n < 0$, so $n eq.not 0$ is a more powerful statement of the defintion.

\

#underline[== Congruence Modulo _n_]

#underline[=== Definition:]

Let $a, b, n in ZZ$ such that $n > 0$. We say that #underline[$a$ is congruent to $b$ modulo $n$] written $a equiv b space (mod n)$ or $a scripts(equiv)_n b$ if (and only if):
$ n divides( a - b) $

#underline[=== Example:]
- $17 equiv 5 space. (mod 6)$
- $5 equiv.not 25 space.en (mod 7)$
- $6 equiv -4 space (mod 5)$

#underline[=== Remark:]

- Let $a, b, n in ZZ$ with $n>0$. Then, $ a scripts(equiv)_n b arrow.double.l.r.long$  $a$ and $b$ have the same remainder when divided by $n $.

\

#underline[== Equivalence Relation
]
#underline[=== Definition:]

An #underline[equivalence relation] is a special type of a relation $tilde$ written $x tilde y$ when $x$ is related to $y$ such that for every elements $a, b, c in S$, where $S$ is a set:
- (_reflexive_) $a tilde a$
- (_symmetric_) $a tilde b arrow.double.long b tilde a $
- (_transitive_) $a tilde b and b tilde c arrow.double.long b tilde c $

#underline[=== Example:]
- Let $S = ZZ$. Define the relation $tilde$ on $ZZ$ by 
$ a tilde b arrow.long.double.l.r a equiv b space (mod 3) $
(_reflexive_) Let $a in ZZ.$ Then, 
$a tilde a arrow.long.double.l.r 3 divides (a - a) arrow.long.double.l.r a equiv a space (mod 3)$. \
(_symmetric_) Let $a, b in ZZ.$ Suppose that $a tilde b$. (Show: $b tilde a$)

$ a tilde b &arrow.double.long 3 divides (a - b)\
&arrow.double.long a - b = 3k, space.quad exists k in ZZ \
&arrow.double.long b - a = 3(-k), space.quad -k in ZZ \
&arrow.double.long 3 divides (b - a )\
&arrow.double.long b tilde a $

(_transitive_) Let $a, b, c in ZZ.$ Suppose that $a tilde b$ and $b tilde c$. (Show: $a tilde c$)

$ a tilde b and b tilde c &arrow.double.long 3 divides (a - b) and 3 divides (b - c)\
&arrow.double.long a - b = 3k and b - c = 3 ell, space.quad exists k, ell in ZZ \
&arrow.double.long a = 3k + b and b = 3 ell + c, space.quad \
&arrow.double.long a = 3k + (3 ell + c) \
&arrow.double.long a - c = 3(k + ell), space.quad k + ell in ZZ \

&arrow.double.long 3 divides (a - c )\
&arrow.double.long a tilde c $

\

#underline[== Equivalence Classes]

#underline[=== Definition:]

Let $tilde$ be an equivalence relation on $S$. Let $a in S$. The #underline[equivalence class] determined by $a$ is the set:
$ [a]_(tilde)=a slash tilde = {x in S | x tilde a} $

#underline[=== Remarks:]
- $[a]_tilde eq.not diameter$
- An element of an equivalence class is called a #underline[representative] of the equivalence class.


\
#underline[== Partition]

#underline[=== Definition:]

A #underline[partition] of a set $S$ is a collection of non-empty disjoint subsets of $S$ whose union is $S$. 

In other words, $cal(P)$ is a partion of $S$ if and only if the following holds
- $forall P, Q in cal(P), P = Q or P sect Q = cancel(circle)$

- $display(union.big_(P in cal(P))) P = S$

\

#underline[== Theorem 1.2]

#underline[=== Statement:]

If $tilde$ is an equivalence relation on $S$, then the equivalence class form a partition of $S$.


#underline[=== Examples:]
- $S = RR^(*), a tilde b <==> a b > 0$

  Equivalence classes of $tilde$:
    - $
    [1] &= {x in S | 1 dot x >0} \= {x in RR^(*) | x >0}
    &= (0, + infinity)
    $
    - $
    [1] &= {x in S | (-1) x >0} \= {x in RR^(*) | x < 0}
    &= (-infinity, 0)
    $
- $S = ZZ, a <==> a equiv b space (mod 3) <==> 3divides (a-b)$

  Equivalence classes:
  - $[0] = {dots, -6, -3, 0,3,6,dots} =: 3ZZ = [-3] = [6]$ 
  - $[1] = {dots, -5, -2, 1,4,7,dots} =: 1+ 3ZZ = [-5] = [4]$
  - $[2] = {dots, -4, -1, 2,5,8,dots} =: 2+ 3ZZ = [-1] = [8]$

#underline[=== Remark:]

- When the equivalence relation is clearly defined, we can denote $[a]_(tilde)$ simply as $[a]$.
- The equivalence relation congruence modulo $n$ $(scripts(equiv)_n)$ partitions $ZZ$ into $n$ equivalence classes:
$ [0], [1], dots, [n - 1] $



#pagebreak()
#set page(
  margin: (top: 60pt, bottom: 60pt),
  numbering: "1",
)

#set text(font: "Fira Sans Math", size: 12pt)
#set align(top)

= Binary Operations and Groups

#line(length: 100% )

#underline[=== Definition:]

A binary operation $*$ on a non-empty set $S$ is a function from $S times S$ to $S$.
$
*: S times S &-> S \
(a,b) &|-> a * b
$

#underline[*Examples*]:
+ $S = RR$

