#import "environments.typ": *

#let Enc = $sans("Enc")$

#let check = $sans("check")$
#let fold = $sans("fold")$
#let batch = $sans("batch")$
#let pret = math.sans("pret")

// Define functions:
#let show-comments = true   // set to false to hide every comment for the final version
#let comment(author, color) = body => if show-comments {
  text(fill: color)[*\[#author:* #body*\]*]
}
#let albert = comment("Albert", olive)
#let remco  = comment("Remco", blue)
#let todo   = comment("TODO", orange)


= Batch version

== Zero-evaders

We use the notion of a zero evader from @BCFW25, expressed as an indexed family of linear maps with vector-valued outputs.

#definition[Zero evader][
  A _zero evader_ is a family of linear maps $φ_z : 𝔽^n → 𝔽^m$ indexed by a finite non-empty set $𝒵$. For a nonempty family $𝒲$ of linear subspaces of $𝔽^n$, we call $ε_𝒲 ∈ [0,1]$ an _error bound_ if
  $
    max_(W ∈ 𝒲) thick Pr_(z ← 𝒵) thick [W ⊆ ker φ_z] ≤ ε_𝒲.
  $
]

#albert[it would be good to add an example of how a zero evader would look like for a nontrivial family of subspaces. i think some readers will replace the subspace by a tuple of codewords after staring at the definition]

#remark[
  In a given basis $φ_z$ is a $m × n$ matrix such that $φ_z (𝐯) = φ_z · 𝐯$. When $m=1$ we call it a _scalar zero evader_.
]

#remark[
  For $1 ≤ d ≤ n$ we write $ε_d$ for an error bound where $𝒲$ consists of all $d$-dimensional subspaces. By subspace containment, these bounds may be chosen so that $ε_d ≥ ε_(d+1)$ for $1 ≤ d < n$, which we require.

  In particular $ε_1$ recovers the error bound from @BCFW25.
  Intuitively, $ε_d$ bounds the probability of annihilating any fixed collection of $d$ linearly independent vectors simultaneously.

]

#lemma[Few folding vectors lie in a subspace][  #albert[Are Lemma 31, 33, 34 needed here? If not they could be placed after the statement of the main thm]
  Let $(ψ_z)_(z ∈ 𝒵)$ be a scalar zero evader on $𝔽^n$ with error bounds $ε_d$. 
  For every $j$-dimensional subspace $H ⊂ 𝔽^n$ with $0 ≤ j < n$,
  $
    abs({z | ψ_z ∈ H}) &≤ abs(𝒵) ε_(n - j).
  $
]
#proof[
 #albert[it was not clear to me what $psi in H$ means] The condition $ψ_s ∈ H$ is equivalent to $H^⟂ ⊆ ker ψ_s$ and $dim H^⟂ = n - j$. The result follows from the definition of $ε_(n - j)$.
]
#corollary[
  Given $S ⊆ 𝒵$ such that $abs(S) > abs(𝒵) ε_1$, the family $(ψ_z)_(z ∈ S)$ contains a basis for $𝔽^n$.
] <thm:ze-basis>
#proof[
  If their span had dimension $j < n$ we would have a contradiction $abs(S) ≤ abs(𝒵) ε_(n - j) ≤ abs(𝒵) ε_1$.
]

#definition[Univariate evader][
  Define the $m$-sample _univariate evader_ with index family $𝒵 ≔ 𝔽^m$ and $φ_𝐳$ for $𝐳 = (z_1, …, z_m)$ as the map given by the $m × n$ Vandermonde matrix on $𝐳$.
]

#lemma[
  The $m$-sample univariate zero evader has error bounds
  $
    ε_d = min(1, ((n - d) / q)^m).
  $ 
]

#proof[To do.]

#remark[
  We do not require the $z_i$ to be distinct. When applied to message coordinates, the univariate zero evader matches the $m$-repeated out of domain samples in WHIR @whir, and the codeword queries in the Reed-Solomon instantiation of Ligerito @ligerito, etc.
]

#definition[Multilinear evader][
  Let $k = ceil(log_2 n)$ and fix a basis. We define the scalar _multilinear evader_ with index family $𝒵 ≔ 𝔽^k$ and $φ_𝐳$ for $𝐳 = (z_1, …, z_k)$ as the first $n$ values of the MLE tensor product
  $
    φ_𝐳 = (⨀_(i ∈ [k]) mat(1 - z_i; z_i))_[n] .
  $
]

#lemma[
  For $1 ≤ d ≤ n$ let $r = ceil(log_2 n) - floor(log_2 d)$. The multilinear evader
  has error bounds
  $
    ε_d = 1-(1-1/q)^r ≤ min(1, r/ q).
  $
]

#proof[To do.]


#definition[Product zero evader][
  For $j ∈ [k]$, let $ψ^j_(z_j) : 𝔽^(b_j) → 𝔽$
  be scalar zero evaders indexed by $𝒵_j$, with
  error bounds $ε^(j)_d$.
  Their _product zero evader_ has domain $𝔽^b$,
  where $b = product_(j ∈ [k]) b_j$, index set  and maps
  $
    𝒵 &= 𝒵_1 × ⋯ × 𝒵_k, &quad
    ψ_𝐬 &= ψ^(k)_(s_k) ⊗ ⋯ ⊗ ψ^(1)_(s_1).
  $
]

== Main Theorem (batch version)

- Denote with $(q)_(n+1)$ the falling factorial $q(q-1)⋯(q-n)$.

- Let $𝔽$ be a finite field of size $q = abs(𝔽)$.

- Let $ℓ$ be the message length, $n$ the code length, $b$ the folding size, $m$ the check size.

- Let $𝒞 ⊆ 𝔽^n$ with dimension $ℓ$ be a code that is $(δ, L)$-list decodable and has MCA bound $E$.

- Let $ψ_s ∈ 𝔽^(1 × b)$ be a scalar zero evader  used for folding with seeds #albert[seed sounds strange to me, but i think we havent established any name for z yet. we should do that when defining zero evaders. maybe "sample seeds"?] $s ∈ 𝒵_fold$ and error bounds $ε^fold_d$. Abbreviate $N = abs(𝒵_fold)$.

  #albert[I think having a zero evader for folding may not be worth the generality. The problem I see is that it introduces several symbols that replaces commonly recognized symbols. For example $N=|cal(Z)_(sans("fold"))|$ being an abstraction of $|FF|$ has a relatively high cognitive tax when combined with the rest of the new things happening in this section (at least for me). Maybe keeping $|cal(Z)_(sans("fold"))|$ instead of $N$ would already help]

- Let $φ_z ∈ 𝔽^(m × ℓ)$ be a zero evader used for checking with seeds $z ∈ cal(Z)_check$ and error bounds $ε^check_d$. Define $hat(φ)_z ∈ 𝔽^(m × n)$ as $φ_z Enc_𝒞^(-1)$ where $Enc_𝒞^(-1)$ is a left inverse of $Enc_𝒞$.

- Let $γ_z ∈ 𝔽^(1 × (m + 1))$ be a scalar zero evader used for batching with seeds $z ∈ 𝒵_batch$ and error bounds $ε^batch_d$ used for batching.

*Setup.* Abstractly, the protocol we are interested in is as follows:

1. The prover binds, e.g. through a commitment, to $b$ words $U ∈ 𝔽^(b × n)$. In the honest case these are codewords $D ∈ 𝒞^b$.
2. The verifier challenges with $z ← 𝒵_check$ and the prover provides $B(z) ∈ 𝔽^(b × m)$. In the honest case $B(z) = D hat(φ)_z^⊤$.
3. The verifier challenges with $s ← 𝒵_fold$ so that the prover is now bound to $𝐮_s = ψ_s U$. In the honest case $𝐮_s = ψ_s D$ is a codeword and $𝐮_s hat(φ)_z^⊤ = ψ_s B(z)$.
4. The prover and verifier establish, by any protocol, that there exists a codeword $𝐜 ∈ 𝒞$ and $S ⊆ [n]$ such that proximity and consistency hold
   $
     abs(S) &> (1 - δ)n, &quad
     𝐜_S = (𝐮_s)_S, 
   $ <eq:proximity>
   $
     𝐜 hat(φ_z)^⊤ = ψ_s B(z).
   $ <eq:consistency>

Our goal is that every witness $(𝐜, S)$ satisfying step 4 admits codewords $D ∈ 𝒞^b$ that satisfy $D_S = U_S$. We quantify failures of this property by bounding the number of bad folding seeds for a randomly sampled checking seed.

Ignoring the consistency checking part of the protocol we define pretenders as witness codewords that survive just the proximity check.

#definition[Pretender][
  We call a witness $𝐜 ∈ 𝒞$ a _pretender_ if there exists an $S ⊆ [n]$ satisfying the proximity equation @eq:proximity but there exists no codewords $D ∈ 𝒞^b$ satisfying $D_S = U_S$. Let $𝒫_s$ be the set of pretenders for $s$.
]

Without a consistency check, our only hope is to bound the number of folding seeds that can have pretenders. Such bounds are known as _mutual correlated agreement_ (MCA) theorems for code and folding evader.

#definition[MCA bound][
  An integer $0 ≤ E ≤ N$ is an _MCA bound_ if $abs({s ∈ 𝒵_fold : 𝒫_s ≠ ∅}) ≤ E$. The trivial MCA bound is $N$.
]

With the consistency check added, we define bad seeds as those that let pretenders slip through.

#definition[Bad seeds][
  A pair of seeds $(z, s)$ is _bad_ if it admits a pretender that also satisfies the consistency equation @eq:consistency. For given $z$, define the bad set $A_z = {s ∈ 𝒵_fold: (z,s) "is bad"}$.
]

The main theorem is that for uniform random checking seed $z$, the set of bad folding seeds is bounded.

#theorem[The bad set is likely small][
  Let $β = ceil(δ n) N ε^fold_1$ then $abs(A_z) ≤ E$ and for any $β < t ≤ E$, #albert[I would only use falling factorial notation inside the proof. Also I'd define $beta$ only inside the proof, no reason to have it in the statement IMO] 

  
  #albert[We should make very clear that we don't necessarily need E to be small, i.e. we can set it to $N$ so we don't need MCA at all]
  $
    Pr_(z ← 𝒵\ check)[ abs(A_z) ≥ t] ≤ 
        ((E)_(b+1) L^(b+1) ε^check_1) /
    ((t - β) product_(d ∈ [b]) (t - N ε^fold_d)).
  $
] <thm:main_batch>

In particular, for sumcheck folding we obtain a bound cubic in the list size.

#corollary[Sumcheck folds][
  Sumcheck rounds fold using a multilinear evader $ψ_α = (1-α, α)$, so we have $b = 2$, $N = q$, $ε^fold_1 = 1/q$ and $ε^fold_2 = 0$ and hence for $t > ceil(δ n)$,
  
  $
    Pr_(z ← 𝒵\ check)[ abs(A_z) ≥ t] ≤ 
        ((E)_3 L^3 ε^check_1) /
    (t (t - 1) (t - ceil(δ n))).
  $
]

=== Proof of @thm:main_batch

We will show that $b$ linearly independent folding vectors #albert[folding zero evaders?], together with their codewords, determine a unique explanation $D$ #albert[not defined?]. An additional codeword can contradict that explanation; any fixed such collection #albert[not sure what such refers to here :)] passes checking with probability at most $ε^check_1$.

#lemma[Explanation][
  Let $ψ_s_1, …, ψ_s_b$ form a basis #albert[why does the set of evader have dimension b?] and let $𝐜_1, …, 𝐜_b ∈ 𝒞$. They determine a unique $D ∈ 𝒞^b$ satisfying $ψ_s_i D = 𝐜_i$. If these pairs each satisfy the checking equation @eq:consistency, then $D hat(φ)_z^⊤ = B(z)$. #albert[I think $psi_s$ and $phi_z$ may look to similar. I'd use $psi^(sans("fold"))_s$ and $psi^(sans("sample"))_z$ or something of the likes]
]<thm:explanation>
#proof[
  Since $ψ_s_i$ form a basis, the system $ψ_s_i D = 𝐜_i$ for $i ∈ [d]$ has a unique solution $D$. It's rows are linear combinations of $𝐜_i$ so $D ∈ 𝒞^b$. For $i ∈ [b]$ we have $ψ_s_i (D hat(φ)_z^⊤ - B(z)) = 𝟎$ and since $ψ_s_i$ form a basis it follows $D hat(φ)_z^⊤ - B(z) = 𝟎$.
]

#lemma[Contradiction][
  Fix the $b$ pairs #albert[it would be good to explicitly refer to the pairs or to say instead "assuming the notation of Lemma 44"] from @thm:explanation and their explanation $D$ , independently of $z$. Fix an additional pair $(s, 𝐜)$ with $𝐜 ∈ 𝒞$ and $𝐜 ≠ ψ_s D$. If all $b+1$ pairs satisfy @eq:consistency, then $(𝐜 - ψ_s D) hat(φ)_z^⊤ = 𝟎$. The probability over $z ← 𝒵_check$ of this event is at most $ε^check_1$.
]<thm:contradiction-check>
#proof[
  If all checking equations hold, the preceding lemma gives $D hat(φ)_z^⊤ = B(z)$. Therefore
  $
    (𝐜 - ψ_s D) hat(φ)_z^⊤
      = 𝐜 hat(φ)_z^⊤ - ψ_s B(z) = 𝟎.
  $
  The difference is a fixed nonzero codeword, so the checking
  evader bounds this by $ε^check_1$.
]

To turn many bad seeds into many contradictions, we need to
bound how many folding seeds can produce pretenders consistent
with a single explanation $D$.

#lemma[Codewords have few pretenders][
  For every $D ∈ 𝒞^b$,
  $
    abs({s ∈ 𝒵_fold | ψ_s D ∈ 𝒫_s})  &≤ β, &quad
    β &≔ ceil(δ n) N ε^fold_1 .
  $
] <thm:pretender-bound>
#proof[
  Fix $D ∈ 𝒞^b$, let $I &= {i ∈ [n] : U_(*i) ≠ D_(*i) }$ and choose a set $J ⊆ I$ such that $abs(J) = min(ceil(δ n), abs(I))$. Every witnessing agreement set $S$ for a pretender $ψ_s D$ intersects $J$. If $J=I$, disjointness would mean $D_S=U_S$, contradicting pretenderhood. Otherwise, $abs(J) = ceil(δ n)$, while $S$ omits fewer than $δ n ≤ ceil(δ n)$ columns.

  At an intersecting column $i$ we have $ψ_s (U_(*i) - D_(*i)) =  𝟎$. Each discrepancy is fixed and nonzero. A union bound therefore gives
  $
    abs({s ∈ 𝒵_fold | ψ_s D ∈ 𝒫_s}) ≤ abs(J) N ε^fold_1 ≤ ceil(δ n) N ε^fold_1.
  $
]

We now count collections that contradict their explanation while passing all checks. Each fixed collection passes rarely, but many bad seeds produce many such collections.

#definition[
  Let $M(z)$ count ordered collections of $b+1$ pairs $(s_i, 𝐜_i)$ with distinct folding seeds $s_i$ and pretender codewords $𝐜_i ∈ 𝒫_(s_i)$ that all satisfy consistency check @eq:consistency such that $(ψ_(s_i))_(i∈ [b])$ is a basis and $𝐜_(b+1) ≠ ψ_(s_(b+1)) D$, where $D$ is the explanation from @thm:explanation.
]

#lemma[Upper bound][
  $
     limits(𝔼)_(z ← cal(Z)\ check) [M(z)] ≤ (E)_(b+1) L^(b+1) ε^check_1.
  $
]
#proof[
  The lists $𝒫_s$ are fixed independently of $z$. By @eq:proximity and $(δ, L)$-list decodability of $𝒞$, each satisfies $abs(𝒫_s) ≤ L$ and is nonempty for at most $E$ folding seeds. There are therefore at most $(E)_(b+1) L^(b+1)$ possible ordered collections with distinct seeds. Each fixed collection whose final pair contradicts the explanation of its first $b$ pairs passes all checks with probability at most $ε^check_1$, by @thm:contradiction-check. Summing these probabilities gives the bound.
]

#lemma[Lower bound][
  Let $a = abs(A_z)$, if $a > β$ then
  $
    M(z) ≥ (a - β) product_(d ∈ [b]) (a - N ε^fold_d).
  $
]
#proof[
  For each $s ∈ A_z$, fix a pretender $𝐜_s$ such that $𝐜_s hat(φ)_z^⊤ = ψ_s B(z)$. Membership in $A_z$ guarantees such a choice.
  
  After choosing $j < b$ independent folding vectors, their span contains at most $N ε^fold_(b -j)$ seeds. Thus there are at least
  $
    product_(d ∈ [b]) (a - N ε^fold_d)
  $
  ordered choices for the first $b$ pairs.

  The first $b$ pairs determine the unique $D ∈ 𝒞^b$ satisfying $ψ_(s_i) D = 𝐜_i$. By @thm:pretender-bound at most $β$ seeds satisfy $𝐜_s = ψ_s D$, since every such seed satisfies $ψ_s D = 𝐜_s ∈ 𝒫_s$. Hence at least $a - β$ choices satisfy $𝐜_s ≠ ψ_s D$. These choices automatically differ from the first $b$ seeds.
]

#proof[Proof of @thm:main_batch][
  By definition $A_z ⊆ {s ∈ 𝒵_fold: 𝒫_s ≠ ∅}$ so $abs(A_z) ≤ E$. On the event $abs(A_z) ≥ t$, the lower bound lemma gives
  $
    M(z) ≥ (t - β) product_(d ∈ [b])(t - N ε^fold_d).
  $
  Taking expectations and applying the upper bound lemma gives
  $
    Pr_(z ← 𝒵\ check)[abs(A_z) ≥ t] (t - β) product_(d ∈ [b]) (t - N ε^fold_d) ≤ (E)_(b+1) L^(b+1) ε^check_1.
  $
  The result follows from dividing by the positive left hand factors.
]

== Composition

Assume the folding evader is a product zero evader such that:

$
 ψ_s &= ψ^((1))_s_1 ⊗ ⋯ ⊗ ψ^((1))_s_k &quad "and" quad
 𝒵_fold &= 𝒵^((1))_fold × ⋯ × 𝒵^((k))_fold .
$

Then define the parameters from @thm:main_batch componentwise, e.g.:

$
  N_j &= abs(𝒵^((j))_fold), &quad
  β_j &= ceil(δ n) N_j ε^((j))_1,
$
$
  p_j (t) = ((N_j)_(b_j+1) L_j^(b_j+1) ε^check_1) /
    ((t - β_j) product_(d ∈ [b_j]) (t - N_j ε^((j))_d))
$

where $L_j$ is the list size bound of the intermediate interleaved code $C^(≡r_j)$.

#theorem[Composition conjecture][
  For $t_j > β_j$, we have
  $
    Pr_(z ∈ 𝒵\ check)[
      abs(A_z)/(product_(j ∈ [k]) N_j) ≥ sum_(j ∈ [k]) t_j / N_j
    ] ≤ sum_(j ∈ [k]) p_j (t_j)
  $
]

If all the $b_j$, $N_j$, $ε^((d))_j$ and $t_j$ are the same (but not necessarily the list bounds $L_j$), we have the stronger conjecture

#theorem[Homogenous composition conjecture][
  For $t > β$, we have
  $
    Pr_(z ∈ 𝒵\ check)[
      abs(A_z)/N^k ≥ (k t) / N
    ] ≤ 1/k sum_(j ∈ [k]) p_j (t)
  $
]
