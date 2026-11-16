#import "layout.typ": *
#import "environments.typ": *

#show: trivial.init
#show: template.with(
  title: "BEEP: Better Elimination of Pretenders",
  authors: (
    (
      name: "Remco Bloemen",
      affiliation: "World Foundation",
      email: "remco@world.org",
    ),
    (
      name: "Albert Garreta",
      affiliation: "World Foundation",
      email: "albert@world.org"
    ),
  ),
  date: "November 2026"
)
// Number definitions, theorems, ... as <section>.<n> (see environments.typ). It must come after
// `template`: the heading rule of the template does not hand the heading on to earlier rules.
#show: theorems-per-section

// Link color
#let linkcolor = rgb("#1c8699") 
#show link: set text(fill: linkcolor)    
#show ref:  set text(fill: linkcolor)    
#show cite: set text(fill: linkcolor)   


// Define functions:
#let show-comments = true   // set to false to hide every comment for the final version
#let comment(author, color) = body => if show-comments {
  text(fill: color)[*\[#author:* #body*\]*]
}
#let albert = comment("Albert", olive)
#let remco  = comment("Remco", blue)
#let todo   = comment("TODO", orange)
// [AI-edited (claude-fable-5-2), 2026-11-12, at the author's request] `aiedit` colors the text changed or added by AI on 2026-11-12 (the edits marked `[AI-edited ...]` in Sections 3 and 4).
#let show-ai-edits = true   // set to false to remove this color
#let aiedit(body) = if show-ai-edits { text(fill: red, body) } else { body }

#let vb(x) = $upright(bold(#x))$
#let Enc = $sans("Enc")$
#let Pack = $sans("Pack")$
#let bits = $sans("bits")$
#let codedim = $ell$
#let blockclength = $n$
#let numsamples = $m$
#let evalmap = $phi$
#let interleavedcode(k) = $cal(C)^(equiv #k)$
#let langle = $⟨$
#let rangle = $⟩$
#let MLE(x) = $sans("MLE")[#x]$
#let hamming = $Delta$

#let prover = $sans("P")$
#let verifier = $sans("V")$
#let Relation = $cal(R)$
#let inp = $bb(x)$
#let oracle = $bb(y)$
#let wit = $bb(w)$
#let provermsg = $m$
#let verifiermsg = $rho$
#let kstate = $sans("State")$
#let tr = $sans("tr")$
#let kswit = $vb(w)$
#let knowledgeerror = $kappa$
#let rbrextractor = $sans("Ext")$

#let check = $sans("check")$
#let fold = $sans("fold")$
#let batch = $sans("batch")$

// Abstract 
#abstract[
  
  We present an improved soundness analysis of the DEEP technique @deep (after a minor modification), which, unlike its predecessor, results in negligible error bounds for all  parameters typically used in practice. We then modify typical code-based IOPPs with this technique, such as WHIR, Ligerito, etc. @whir @ligerito. As a result, we obtain code-based IOPPs that only require list decodability of the underlying codes, instead of (Mutual) Correlated Agreement (MCA),  with a folding error bound that is linear on the code dimension and list size, improving upon the standard MCA error in typical instantiations. 
  
  The modified DEEP technique consists only in performing $4$-$5$ DEEP samples. As a result the cost overhead of these IOPPs, compared to the original ones (WHIR, Ligerito, etc.), is negligible in prover and verifier time, and leads to ???? #albert[fill in] smaller proof sizes when using Reed-Solomon codes and a proximity parameter $delta$ up to the Johnson bound. 
  
  Further, since it does not rely on MCA for its soundness, this improved DEEP technique allows to use arbitrary linear codes in code-based IOPPs with $delta$ up to the Johnson bound. In particular, this opens the door to using  codes (e.g. Reed-Solomon codes) with $delta$ beyond the Johnson bound, assuming the code is $delta$-list decodable, even if it does not have $delta$-MCA #albert[should we say "assuming such codes exists"].
  
]

// Table of contents
#show outline.entry: set text(fill: linkcolor)
#outline(depth: 2) 

// Rest of paper

= Introduction [DO NOT READ!]

The soundness of most code-based Polynomial Commitment Schemes and IOPPs requires using codes satisfying the Mutual Correlated Agreement (MCA) property, for a proximity parameter $delta$ as large as possible. DEEP @deep, a prior approach, required from the code only to be list decodable at radius $delta$, with small list sizes. However, the resulting soundness error was impra

  

Domain Evaluation for Elimination of Pretenders (DEEP)

#albert[Say somewhere that we could use affine folding like in the new Chiesa, Yogev and Zheng paper to get L/q error]


  ---
  
  so as to replace the need of the underlying code $cal(C)$ satisfying the Mutual Correlated Agreement property, with that of list decodability. 
  
  The majority of code-based PCS's  rely, for soundness, on the underlying code $cal(C)$ having  (Mutual) Correlated Agreement, for a large proximity parameter. BEEP allows to replace this requirement by that of list decodability of the code, after performing a minor modification of the PCS. Concretely, this modification consists on performing a few out of domain samples every time a word is folded, right before the folding challenge is sampled. 
  
  A consequence is that all typical code-based PCS's can be instantiated with an arbitrary linear code $cal(C)$ with proximity parameter up to the Johnson bound, after undergoing the aforementioned minor modification. 

  #albert[More consequences: we can do 128 bits of security with a 128 bit field, with any code]

  --

  "The proof basically shows that if there are many bad codewords corresponding to different folding challenges (consistent with the DEEP queries), then there’s many triples of codewords that are not colinear, and then the deep queries are zeros of some determinant-like nonzero polynomial associated to a triple"

== Contributions

The fold error is about (δn + 3L)/|𝔽| instead of an MCA error with large polynomial factors or large constant or restrictive parameters #albert[From some conversation with Ulrich I think this may be a big deal (I haven't told him about this work though)]

== Related work

== Use of AI
#albert[Revise]  This document was written without the use of AI, except for making small refactorings. The novel results in this work were obtained through a long interactive process with an AI #albert[And the batched BEEP too?]. The Lean formalization of the results (concretely, of @?,@? and @?, see #albert[ref to repo]) was done by an AI and its statements were reviewed by us subsequently. Similarly, the experiments from Section @s:experiments were prepared with an AI and reviewed by us #albert[make sure this is the case].

== Acknowledgements

The second author was  affiliated at Nethermind during part of the preparation of this work. 


= Preliminaries

== General notation and terminology

A #emph[relation] $cal(R)$ consists of triples  $(bb(x), bb(y), bb(w))$, where $bb(x)$ is the explicit instance, $bb(y)$ the implicit instance or oracle, and $bb(w)$ the witness.

Given an integer $n ≥ 1$, we write $[n]$ to denote the set ${1,dots, n}$. 
We often denote vectors with boldface letters, e.g. $vb(u),vb(v)$. By $vb(u)_i$ we denote the $i$-th position of $vb(u)$. When a vector $vb(u)$ is indexed by ${0,1}^k$ we denote its multilinear extension with $MLE(vb(u))$.

Denote with $Pr_(s ← 𝒮)$ the probability under uniform random sampling of $s ∈ 𝒮$.



== Linear codes 
 Let $cal(C) subset FF^(blockclength)$ be a linear code over $FF$ of dimension $codedim$ and blocklength $blockclength$. We fix an injective linear encoding map $Enc_cal(C): FF^codedim arrow cal(C)$.  Given two words $w_1, w_2 in FF^blockclength$, the relative Hamming distance between $w_1$ and $w_2$ (the fraction of positions in which they differ) is denoted $hamming(w_1,w_2)$. The #emph[relative minimum distance] of $cal(C)$, denoted $hamming(cal(C))$, is the minimum of $hamming(c_1,c_2)$ over distinct codewords $c_1,c_2 in cal(C)$. 

Given $delta in (0,1)$ and an integer $L ≥ 1$, we say $cal(C)$ is #emph[$(delta, L)$-list-decodable] if for every word $w in FF^blockclength$ there are at most $L$ codewords that are #emph[$delta$-close] to $w$, i.e. such that $hamming(w,c) ≤ delta$.  


We denote codewords and words with non-boldface letters such as $w,c,f$, etc. We do not use boldface for these, even though they are vectors. We do use boldface letters for messages. For example, we often let $f in FF^blockclength$ denote the encoding of a message $vb(f) in FF^codedim$ with a linear code $cal(C)$.

Given a word $u in FF^blockclength$ and $x in [blockclength]$, we let $u(x)$ denote the $x$-th entry of $u$. Given $S subset [blockclength]$, we write $u_S$ for the restriction of $u$ to the positions in $S$. We say that two words _agree on $S$_ if their restrictions to $S$ are equal, and that $u$ _agrees with $cal(C)$ on $S$_ if $u$ agrees on $S$ with some codeword of $cal(C)$.

#paragraph[Interleaved codes]

== Zero-evaders<s:zero_evaders>

We use the notion of a zero evader from @BCFW25 #albert[Why does the citation not appear as BCFW25?], expressed as an indexed family of linear maps with vector-valued outputs.

#let evaderdim = $e$

#definition[Zero evader][
  A _zero evader_ is a family of linear maps ${φ_z : 𝔽^evaderdim → 𝔽^numsamples | z in cal(Z)}$ indexed by a finite non-empty set $𝒵$. We call $ε ∈ [0,1]$ an _error bound_ of the evader if #albert[For consistency we should write $phi_z(vb(b))$]
  $
    max_(𝐯 ∈ 𝔽^evaderdim \ 𝐯 ≠ 𝟎) thick Pr_(z ← 𝒵) thick [φ_z 𝐯 = 𝟎] ≤ ε.
  $
]

#remark[
  In a given basis $φ_z$ is an $numsamples × evaderdim$ matrix. When $numsamples=1$ we call it a _scalar zero evader_.
]

#definition[Univariate evader][
  Define the $numsamples$-sample _univariate evader_ with index family $𝒵 ≔ 𝔽^evaderdim$ and $φ_𝐳$ for $𝐳 = (z_1, …, z_numsamples)$ as the map given by the $numsamples × evaderdim$ Vandermonde matrix on $𝐳$. #albert[Maybe let's now write the evader explicitly]
]

#lemma[
  The $numsamples$-sample univariate zero evader has error bound
  $
  ε = min(1, ((evaderdim- 1) / (|FF|))^numsamples).
  $ 
]

#proof[
  Fix a nonzero $𝐯 ∈ FF^evaderdim$. The polynomial
  $ P(X) = sum_(j∈[evaderdim]) v_j dot X^(j - 1)$
  is nonzero and has degree at most $evaderdim - 1$, so it has
  at most $evaderdim - 1$ roots in $𝔽$. By construction, $φ_𝐳 (𝐯) = (P(z_1), …, P(z_k))$. Since the coordinates of $𝐳$ are independent and uniform,
  $
    Pr_(𝐳 ← 𝔽^numsamples)[φ_𝐳 (𝐯) = 𝟎]
    = product_(i ∈ [numsamples]) med Pr_(z_i ← 𝔽) med [P(z_i) = 0]
    ≤ ((evaderdim - 1) / abs(𝔽))^numsamples.
  $
]

#remark[
  We do not require the $z_i$ to be distinct. When applied to message coordinates, the univariate zero evader matches the $m$-repeated out of domain samples in WHIR @whir #albert[Why don't we get the normal citation format here?], and the codeword queries in the Reed-Solomon instantiation of Ligerito @ligerito, etc.
]

#definition[Multilinear evader][
  Let $e_0 := ceil(log_2 evaderdim)$ and fix a basis. We define the scalar _multilinear evader_ with index family $𝒵 ≔ 𝔽^(e_0)$ and $φ_𝐳$ for $𝐳 = (z_1, …, z_numsamples)$ as the first $evaderdim$ values of the MLE tensor product:
  $
    φ_𝐳 = (⨀_(i ∈ [e_0]) mat(1 - z_i; z_i))_[evaderdim] .
  $
  #albert[As with the other one, let's write the application of $phi_z$ explicitly now]
]

#lemma[
  The _multilinear evader_ has error bound $ε = min(1, e_0\/ q)$.
]

#proof[
  Fix a nonzero $𝐯 ∈ FF^evaderdim$ and pad its coordinates with zeros to obtain a vector of length $2^(e_0)$. Its multilinear extension $tilde(𝐯)$ #albert[We are using MLE in most sections so far] has total degree at most $e_0$, and $φ_𝐳 𝐯 = tilde(𝐯)(𝐳)$. The result follows from the Schwartz–Zippel bound.
]


== Interactive Oracle Reductions (IOR)<s:IOR>

An _Interactive Oracle Reduction (IOR) of proximity_ $Pi = (prover, verifier)$ from a relation $Relation$ to a relation $Relation'$ is specified as follows. The prover $prover$ receives $(inp, oracle, wit) in Relation$. The verifier $verifier$ receives $inp$ and query access to $oracle$. They interact for $k$ rounds. In round $j in [k]$, the prover sends an oracle $provermsg_j$ and the verifier sends a uniformly random message $verifiermsg_j in {0,1}^(r_j)$. After the $k$ rounds, the verifier makes queries to $oracle$ and to $provermsg_1, dots, provermsg_k$. Then:
- $verifier$ either rejects or outputs a new pair $(inp', oracle')$, where $oracle'$ is specified implicitly in terms of the oracles $oracle$ and $provermsg_1, dots, provermsg_k$.
- $prover$ outputs a witness $wit'$ such that $(inp', oracle', wit') in Relation'$.
We write $⟨prover, verifier⟩(inp, oracle, wit)$ for the interaction of prover and verifier during the IOR.

#definition[Completeness][
  $Pi$ has _(perfect) completeness_ if for every $(inp, oracle, wit) in Relation$,
  $
    Pr_(verifiermsg_1, dots, verifiermsg_k) lr([ (inp', oracle'; wit') in Relation' mid(|) (inp', oracle'; wit') <- ⟨prover, verifier⟩(inp, oracle, wit) ]) = 1.
  $
] <def:ior-completeness>

#remark[
  An IOP for a relation $Relation$ is an IOR from $Relation$ to the trivial relation $Relation_sans("triv") = {(inp = bot, oracle = bot, wit = bot)}$.
]

We proceed to define round-by-round knowledge soundness of an IOR, following @BCFW25 in the formulation with relaxed relations of @zook.

#definition[Knowledge state function with relaxation][
  Let $Pi = (prover, verifier)$ be an IOR from a relation $Relation$ to $Relation'$. A _knowledge state function with relaxation $(tilde(Relation), tilde(Relation'))$_ for $Pi$ is a (possibly inefficient) function $kstate$ that, on input $(inp, oracle)$, interaction transcript $tr$, and knowledge state witness $kswit$, outputs a bit and has the following properties.
  - *Empty transcript.* If $tr = emptyset$ is the empty transcript, then $kstate(inp, oracle, tr, kswit) = 1$ if and only if $(inp, oracle; kswit) in tilde(Relation)$.
  - *Prover moves.* If $tr$ is a transcript where the prover is about to move and $kstate(inp, oracle, tr, kswit) = 0$, then $kstate(inp, oracle, tr, provermsg, kswit) = 0$ for every prover message $provermsg$.
  - *Full transcript.* If $tr = (provermsg_1, verifiermsg_1, dots, provermsg_k, verifiermsg_k)$ is a full transcript, then $kstate(inp, oracle, tr, kswit) = 1$ if and only if $verifier$ on $tr$ outputs $(inp', oracle')$ such that $(inp', oracle'; kswit) in tilde(Relation')$.
] <def:knowledge-state-function>

#definition[Round-by-round knowledge soundness][
  A $k$-round IOR $Pi$ has _round-by-round knowledge soundness with relaxation_ $(tilde(Relation), tilde(Relation'))$ with errors $(knowledgeerror_1, dots, knowledgeerror_k)$ if there exists a knowledge state function $kstate$ as in @def:knowledge-state-function and a deterministic extractor $rbrextractor$ such that for every $(inp, oracle)$, every $j in [k]$, and every transcript $tr$ where the verifier is about to send $verifiermsg_j$,
  $
    Pr_(verifiermsg_j) lr([ exists kswit "such that" cases(delim: #none,
      and kstate(inp, oracle, tr, rbrextractor(inp, oracle, tr, verifiermsg_j, kswit)) = 0,
      and kstate(inp, oracle, tr, verifiermsg_j, kswit) = 1,
    ) ]) <= knowledgeerror_j (inp, oracle).
  $
  If $(tilde(Relation), tilde(Relation')) = (Relation, Relation')$ then we say the round-by-round knowledge soundness of $Pi$ is _without relaxation_.
] <def:rbr-knowledge-new>

#lemma[Composition of IORs @zook[Theorem 4.5]][
  Let $Pi_1$ be a perfectly complete $k_1$-round IOR from $Relation_1$ to $Relation_2$ with round-by-round knowledge soundness with relaxation $(tilde(Relation_1), tilde(Relation_2))$ and errors $kappa_(11), dots, kappa_(1 k_1)$, and let $Pi_2$ be a perfectly complete $k_2$-round IOR from $Relation_2$ to $Relation_3$ with round-by-round knowledge soundness with relaxation $(tilde(Relation_2), tilde(Relation_3))$ and errors $kappa_(21), dots, kappa_(2 k_2)$. Then the IOR from $Relation_1$ to $Relation_3$ that runs $Pi_1$ and then $Pi_2$ on the output of $Pi_1$ is perfectly complete, has $k_1 + k_2$ rounds, and has round-by-round knowledge soundness with relaxation $(tilde(Relation_1), tilde(Relation_3))$ and errors $kappa_(11), dots, kappa_(1 k_1), kappa_(21), dots, kappa_(2 k_2)$.
] <r:ior_compositoin>



= Better Elimination of Pretenders <s:better_pretenders>

== The MCA property, pretender codewords, and consistency

Let $FF$ be a finite field and let $cal(C) subset FF^blockclength$ be a linear code of blocklength $blockclength$ and dimension $codedim$, with $blockclength$ a power of two. Let $delta in (0,1)$ be a proximity parameter.

// [AI-edited (claude-fable-5-2), 2026-11-12, at the author's request: words are folded with two linear maps lambda_1, lambda_2 of alpha instead of the weights (1, alpha). Edited: the next paragraph; the MCA, MCA-bad, pretender and consistency definitions; the proofs of l:few_bad_points_on_line and l:colinear_zero; one sentence in the proof of t:main_thm. Please review]
#aiedit[We fix two linear maps $lambda_1, lambda_2: FF arrow FF$, so that $lambda_i (alpha) = a_i + alpha dot d_i$ for some $a_i, d_i in FF$, and we assume that $a_1 dot d_2 != a_2 dot d_1$. We use $lambda_1(alpha)$ and $lambda_2(alpha)$ as the weights when folding two words with a challenge $alpha in FF$. For example, $(lambda_1(alpha), lambda_2(alpha))$ can be $(1, alpha)$, or $(1-alpha, alpha)$ as in Section @s:BEEP_fold. The assumption $a_1 dot d_2 != a_2 dot d_1$ guarantees that the vectors $(lambda_1(alpha), lambda_2(alpha))$ and $(lambda_1(alpha'), lambda_2(alpha'))$ are linearly independent for all distinct $alpha, alpha' in FF$.]




#paragraph[Correlated Agreement (CA) and Mutual Correlated Agreement (MCA)] Let $u_1, u_2 in FF^blockclength$ be two words. Given $S subset [blockclength]$, we say $(u_1,u_2)$ has #emph[Correlated Agreement with $C$ over $S$] if there exist codewords $c_1,c_2 in cal(C)$ such that $u_1$ agrees with $c_1$ on $S$ and $u_2$ agrees with $c_2$ on $S$. 



  Let  $u_1,u_2 in FF^blockclength$ be two words. We say that a field element $alpha in FF$ satisfies the #emph[$delta$-Mutual Correlated Agreement (MCA) property] with respect to $u_1,u_2$, if for every subset $S subset [blockclength]$ with $|S|≥ (1-delta) dot blockclength$ such that #aiedit[$lambda_1(alpha) dot u_1 + lambda_2(alpha) dot u_2$] agrees with $cal(C)$ on $S$, the pair $(u_1,u_2)$ has Correlated Agreement (CA) with $cal(C)$ over $S$.


#definition[MCA-bad element.][
   We say $alpha$ is #emph[MCA-bad] if it does not satisfy the $delta$-MCA property.
]

The code $cal(C)$ is said to have #emph[$delta$-Mutual Correlated Agreement (MCA)] with error $epsilon$, if for any two words $u_1,u_2 in FF^blockclength$, there are at most $epsilon dot |FF|$ MCA-bad field elements.

#definition[Pretender codeword][
  Fix two words $u_1,u_2 in FF^blockclength$, and let $alpha in FF$ be an MCA-bad field element. We say that a codeword $c in cal(C)$ is an #emph[$alpha$-pretender] if, intuitively speaking, it is a witness to the failing of the MCA property for $alpha$. Formally, $c$ is an $alpha$-pretender if #aiedit[$lambda_1(alpha) dot u_1 + lambda_2(alpha) dot u_2$] and $c$ agree on a set $S subset [blockclength]$ of size $|S| ≥ (1-delta) dot blockclength$ and $(u_1,u_2)$ does not have CA with $cal(C)$ over $S$.
]

Fix a zero-evader $(φ_z)_(z ∈ 𝒵)$, i.e. a famility of linear maps $phi_z : FF^codedim -> FF^numsamples$, with error bound $ε$.  Abusing the notation, we also define $phi_z$ on $cal(C)$ by letting $phi_z(Enc_cal(C)(vb(w))) := phi_z(vb(w))$. Since $Enc_cal(C)$ is linear and injective, $phi_z$ is linear on $cal(C)$ and $Pr_(z <- Z)[phi_z(c) =0] ≤ epsilon$ for all nonzero codeword $c$.

Let $𝐛_(1), 𝐛_(2) ∈ 𝔽^numsamples$. For intuition, for an honest prover, $𝐛_1, 𝐛_2$ will be the values $φ_z (c_1), φ_z (c_2)$, where $c_1, c_2 ∈ 𝒞$ are two codewords that are $δ$-close to $u_1$  and $u_2$.

#definition[Consistency of MCA-bad elements $α ∈ 𝔽$  with $z ∈ cal(Z)_(sans("evader"))$][
  Let $α ∈ 𝔽$ and $c ∈ 𝒞$. Given $z ∈ 𝒵$ and $vb(b)_(1), vb(b)_(2) in FF^numsamples$,  we say that $(α, c)$ is _consistent_ with $(z, vb(b)_(1), vb(b)_(2))$ if 
  $
    φ_z (c) = aiedit(λ_1 (α) ·) 𝐛_(z,1) + aiedit(λ_2 (α)) · 𝐛_(z,2).
  $
  When $α$ is an MCA-bad element and there exists an $α$-pretender $c in cal(C)$ such that $(α, c)$ is consistent with  $(z, vb(b)_(1), vb(b)_(2))$, then we say that $α$ is a _DEEP-MCA-bad element_ with respect to $z,vb(b)_(1), vb(b)_(2)$ and $u_1, u_2$. 

  When clear from the context, we omit referring to $z, vb(b)_(1), vb(b)_(2), u_1, u_2$ when speaking of DEEP-MCA-bad elements.
]

== Most out of domain samples admit few DEEP-MCA-bad challenges

In this section we state and prove the main result of this work.



#theorem[For most $z ∈ 𝒵$, there are few DEEP-MCA-bad elements $alpha in FF$][
  Let $delta in (0,1)$ and let $L$ be such that  $cal(C)$ is $(delta, L)$-list decodable.
  Let $u_1, u_2 in FF^blockclength$ be two words, and let $(φ_z)_(z ∈ 𝒵)$ be a zero evader with error $epsilon_(sans("evader"))$. 

  For each $z ∈ cal(Z)_(sans("evader"))$ and $vb(b)_1, vb(b)_2 in FF^numsamples$, let $A_(z, vb(b)_1, vb(b)_2) ⊂ 𝔽$ be the set of DEEP-MCA-bad field elements $α ∈ 𝔽$ with respect to $z, vb(b)_1, vb(b)_2, u_1, u_2$. Let $vb(b)_1^*, vb(b)_2^*$ be such that $|A_(z, vb(b)_1^*, vb(b)_2^*)|$ is maximal  for fixed $z, u_1,u_2$, and denote $A_z := A_(z, vb(b)_1^*, vb(b)_2^*)$. 
  
  Then for any $t≥ delta dot blockclength +2$,
  $
    Pr_(z ← cal(Z)_(sans("evader")))[ abs(A_(z)) ≥ t] ≤ ((|FF| dot L)^3 dot epsilon_(sans("evader"))) / (t dot (t-1) dot (t-delta dot blockclength -1))
  $<e:beep_bound>
]<t:main_thm>

#albert[We should aim to allowsel a skimmer to understand or guess what the theorem says in a more self-contained way. Also we should provide an example of $epsilon_(sans("evader"))$.]

#remark[Using @t:main_thm to replace the MCA error with the list decodability size in code-based PCS][Looking ahead, we will use this result as follows: before performing the fold of two words during a code-based PCS, we have the verifier sample an element $z in cal(Z)$, and the prover replies with $vb(b)_1, vb(b)_2 in FF^numsamples$, supposedly the evaluations on $evalmap_z$ of the two words (which are supposedly codewords). Now, due to @t:main_thm, with high probability over $z$, there are very few folding challenges $alpha in FF$ that result in a failure of the MCA property and which are consistent with $(z, vb(b)_1, vb(b)_2)$. Hence, at this point we can fold as usual, and obtain knowledge soundness even if  the code $cal(C)$ is not known to possess (or is known to not possess) MCA at the proximity parameter $delta$ used by the PCS. We formalize this intuition in Section @s:BEEP_fold.] 


\

We proceed to prove @t:main_thm. We assume the notation of its hypothesis. // We fix $vb(b)_1, vb(b)_2 in FF^numsamples$ and show that $Pr_(z <- cal(Z)) sans("Pr")[ |A_(z,vb(b)_1, vb(b)_2)|≥ t ]$ is at most the right-hand side of @e:beep_bound. This implies that $Pr_(z <- cal(Z)) sans("Pr")[ max_(vb(b)_1, vb(b)_2 in FF^numsamples) |A_(z,vb(b)_1, vb(b)_2)| ≥ t ]$ satisfies the same bound.

#let lmap = $theta$
#let linfuns = $cal(L)^(1)[FF arrow cal(C)]$
#let im = math.sans("Graph")

\

#definition[Parameterized lines][We let $linfuns$ be the set of all linear maps $lmap: FF arrow cal(C)$, so that $lmap(alpha) = c_(theta,1) + alpha dot c_(theta,2)$ for some codewords $c_(theta,1), c_(theta,2) in cal(C)$.  Given $lmap in linfuns$, we let $im(lmap)= {(alpha, theta(alpha)) | alpha in FF} subset FF times cal(C)$ and we call $im(lmap)$ a #emph[parameterized line in $cal(C)$].]

//Let $c_1, c_2 in cal(C)$ be two (not necessarily distinct) codewords. The  #emph[line] in $cal(C)$ spanned by  $c_1,c_2$  is the set $cal(C)_(c_1,c_2):={c_1 + alpha dot c_2 | alpha in FF}$.  // Given a MCA-bad $alpha in FF$ and an $alpha$-pretender (w.r.t. $(u_1,u_2)$) $c in cal(C)$, we say $c$ is in the  

The following result is well-known, see for example @?. We include a proof for completeness. 


#lemma[A parameterized line contains few pretenders][
 Let $lmap in linfuns$. Let $A_(lmap)^(sans("pret")) subset FF$ be the set of all field elements $alpha in FF$ that are MCA-bad and such that the codeword $lmap(alpha) = c_(lmap,1) + alpha dot c_(lmap, 2) in cal(C)$ is an $alpha$-pretender.   Then
  $
|A_(lmap)^(sans("pret"))| ≤ delta dot blockclength +1.
  $
]<l:few_bad_points_on_line>
#proof[
  #aiedit[Since $a_1 dot d_2 != a_2 dot d_1$, there exist codewords $c_1, c_2 in cal(C)$ such that $lmap(alpha) = lambda_1(alpha) dot c_1 + lambda_2(alpha) dot c_2$ for all $alpha in FF$ (they are the solution to the system $a_1 dot c_1 + a_2 dot c_2 = c_(lmap,1)$, $d_1 dot c_1 + d_2 dot c_2 = c_(lmap,2)$).] Let $D subset [blockclength]$ be the set
  $
  D := {x in [blockclength] | u_1(x) != aiedit(c_1(x)) " or " u_2(x) != aiedit(c_2(x))}.
  $
  Let $alpha in A_lmap^(sans("pret"))$. Since $theta(alpha)$ is an $alpha$-pretender, there is a set $S_alpha subset [blockclength]$  where $lmap(alpha)$ and #aiedit[$lambda_1(alpha) dot u_1 + lambda_2(alpha) dot u_2$] agree, with $|S_alpha|≥ (1-delta) dot blockclength$ and such that $(u_0,u_1)$ do not have correlated agreement with $cal(C)$ over $S_alpha$. Hence $S_alpha inter D != emptyset$.

  We claim that for every distinct $alpha, alpha' in A_lmap^(sans("pret"))$ we have $(S_alpha inter D) inter (S_(alpha') inter D) = emptyset$. Indeed, assume to the contrary that $x in [blockclength]$ belongs to such set. Then #aiedit[$lambda_1(alpha) dot u_1(x) + lambda_2(alpha) dot u_2(x)= lambda_1(alpha) dot c_1(x) + lambda_2(alpha) dot c_2(x)$] and #aiedit[$lambda_1(alpha') dot u_1(x) + lambda_2(alpha') dot u_2(x)= lambda_1(alpha') dot c_1(x) + lambda_2(alpha') dot c_2(x)$]. #aiedit[Since $alpha != alpha'$, the vectors $(lambda_1(alpha), lambda_2(alpha))$ and $(lambda_1(alpha'), lambda_2(alpha'))$ are linearly independent, and so] we obtain $u_1(x)=aiedit(c_1(x))$ and $u_2(x)=aiedit(c_2(x))$, contradicting the fact that $x in D$, and thus proving the claim.

  This immediately implies that $|A_lmap^(sans("pret"))| ≤ |D|$, since each set $S_alpha$ intersects $D$ non-trivially, and the sets $S_alpha inter D$ are pairwise disjoint. Now if $|D|≤  delta dot blockclength +1$ we are done. Hence assume this is not the case.

  Since $|S_alpha| ≥ (1-delta) dot blockclength$ and $S_alpha = (S_alpha inter D) union (S_alpha \\ D)$, we obtain  $|S_alpha inter D| ≥ (1-delta) dot blockclength - |S_alpha \\ D|  ≥ (1-delta) dot blockclength - |[blockclength] \\ D| = |D| - delta dot blockclength$. Now since the sets $S_alpha inter D$ are pairwise disjoint and contained in $D$,
  $
  |A_lmap^(sans("pret"))|dot (|D| - delta dot blockclength) ≤ lr(|union.big_(alpha in A_lmap^(sans("pret"))) (S_alpha inter D)|)  ≤ |D|.
  $
  Since we assumed $|D|> delta dot blockclength +1$, the factor $(|D| - delta dot blockclength)$ is positive.  Dividing by it and using the inequality on $|D|$ again:
  $
  |A_lmap^(sans("pret"))| ≤ frac(|D|,|D|-delta dot blockclength) = 1 + frac(delta dot blockclength, |D|- delta dot blockclength) < 1 + delta dot blockclength,
  $
  as required.
]

Given two codewords $c_1,c_2 in cal(C)$, we let $lmap_(c_1,c_2):FF arrow cal(C)$ be the linear map from $linfuns$ defined as $lmap_(c_1,c_2)(alpha)=c_1+alpha dot c_2$.

The following is an elementary characterization of colinearity:

#lemma[Colinearity of codewords][Let $(alpha_i, v_i)_(i in [3]) in (FF times cal(C))^3$ with $alpha_1, alpha_2, alpha_3$ pairwise distinct. Then the three tuples $(alpha_i, v_i)_(i in [3])$  belong to the same parameterized line (i.e. there exists $lmap in linfuns$ such that $(alpha_i, v_i)in im(lmap)$ for all $i in [3]$) if and only if 
$
U((alpha_i, v_i)_(i in [3])) := (alpha_3 -alpha_1) dot (v_2 - v_1) - (alpha_2 -alpha_1) dot (v_3-v_1) = 0,
$
//
// Moreover, if $U((alpha_i, v_i)_(i in [3])) =0$, then $v_1, v_2, v_3$ belong to the line spanned by $c_1 = v_1$ and $c_2 = (v_2 -v_1)/(alpha_2 -alpha_1)$, and $v_3 = c_1 + (alpha_3- alpha_1) dot c_2$
]<l:colinear>

#proof[
  Assume $(alpha_i, v_i) in im(lmap_(c_1,c_2))$ for some $c_1,c_2in cal(C)$. Then $v_i = c_1 + alpha_i dot c_2$ for all $i=1,2,3$. Now $v_2-v_1 = (alpha_2-alpha_1) dot c_2$ and $v_3-v_1 = (alpha_3-alpha_1) dot c_2$. Plugging this into the definition of $U((alpha_i, v_i)_(i in [3]))$ yields $U((alpha_i, v_i)_(i in [3]))=0$.

  Conversely, assume $U((alpha_i, v_i)_(i in [3]))=0$, so that $(v_2-v_1)/(alpha_2-alpha_1) = (v_3-v_1)/(alpha_3-alpha_1)$. Then taking $c_2 = (v_2-v_1)/(alpha_2 - alpha_1)$ and $c_1= v_1 - alpha_1 dot c_2$ we have $v_1 = c_1 + alpha_1 dot c_2$, $v_2 = v_1 + (alpha_2-alpha_1)dot c_2 = c_1 + alpha_2 dot c_2$ and  $v_3 = v_1 + (alpha_3-alpha_1)dot c_2 = c_1 + alpha_3 dot c_2$, and so $(alpha_i, v_i) in im(lmap_(c_1,c_2))$ for all $i in [3]$.
]

Note that, for any $(alpha_i, v_i)_(i in [3]) in (FF times cal(C))^3$, the element $U((alpha_i, v_i)_(i in [3]))$ is a codeword from $cal(C)$.



#lemma[$U((alpha_i, v_i)_(i in [3]))$ vanishes under $evalmap_z$  for consistent $vb(alpha)$][
  Let $z ∈ 𝒵$, let $vb(b)_1, vb(b)_2 in FF^numsamples$, and  let $(alpha_i,v_i)_(i in [3]) in (FF times cal(C))^3$   be such that $(alpha_i,v_i)$ is consistent with  $(z,vb(b)_1, vb(b)_2)$ for each $i=1,2,3$. Then 
  $
  evalmap_z (U((alpha_i, v_i)_(i in [3]))) = 𝟎
  $
]<l:colinear_zero>
#proof[
  It follows by direct evaluation, using the linearity of $evalmap_z$ and the assumption that $evalmap_z (v_i) = aiedit(lambda_1(alpha_i) dot 𝐛_1 + lambda_2(alpha_i) dot 𝐛_2)$ for $i=1,2,3$. #aiedit[Writing $lambda_j (alpha) = a_j + alpha dot d_j$ and $𝐛' := d_1 dot 𝐛_1 + d_2 dot 𝐛_2$, this gives $evalmap_z (v_i) - evalmap_z (v_1) = (alpha_i - alpha_1) dot 𝐛'$ for $i=2,3$, and so:] 
  $  
     evalmap_z (U((alpha_i, v_i)_(i in [3]))) &=
     (alpha_3-alpha_1) dot (evalmap_z (v_2) - evalmap_z (v_1))-(alpha_2-alpha_1) dot (evalmap_z (v_3) - evalmap_z (v_1)),\
     &= (alpha_3-alpha_1) dot (alpha_2-alpha_1) dot aiedit(𝐛') - (alpha_2-alpha_1) dot (alpha_3-alpha_1) dot aiedit(𝐛') = 𝟎,
  $
  as required.
]

Let $z ∈ 𝒵$,  and let $T_z$ be the set of triples $(alpha_i, v_i)_(i in [3]) in (FF times cal(C))^3$ such that: 
+ $(alpha_i, v_i)$ is consistent with $(z, vb(b)_1^*, vb(b)_2^*)$ for all $i=1,2,3$; 
+ $U((alpha_i, v_i)_(i in [3])) != 0$.
+ $alpha_i$ is an MCA-bad point and $v_i$ is an $alpha_i$-pretender, for all $i=1,2,3$. 
+ $alpha_i != alpha_j$ for all $1 ≤ i <j≤3$.

@l:few_bad_points_on_line states that a parameterized line in $cal(C)$ contains few points $(alpha, c) in FF times cal(C)$ with $c$ being an $alpha$-pretender. On the other hand, for every $alpha in A_z$,  there exists an $alpha$-pretender $c in cal(C)$. Hence, intuitively, if $|A_z|$ is large, then we expect $|T_z|$ to be large too. We formalize this intuition in the next result.

#lemma[Bounding $|A_z|^3$ with $|T_z|$][
  Let $z ∈ 𝒵$ and let $T_z$ be defined as above. Then 
  $
    |A_z| dot (|A_z| -1) dot (|A_z| -delta dot blockclength -1) ≤ |T_z|.
  $
]<l:third_moment_bound>
#proof[
   For each $alpha in A_z$, fix an $alpha$-pretender $c_alpha in cal(C)$ such that $(alpha, c_alpha)$ is consistent with $(z, vb(b)_1^*, vb(b)_2^*)$. Such $c_alpha$ exists by the definition of $A_z$. Let $Y = {(alpha, c_alpha) | alpha in A_z}$ and note that $|Y|=|A_z|$.
  Every triple $(alpha_i, c_alpha_i)_(i in [3]) in Y^3$ with $alpha_i != alpha_j$ for all $i !=j$ satisfies Conditions 1, 3 and 4 in the definition of $T_z$. Hence it suffices  to lower bound the number of such triples for which $U((alpha_i, c_alpha_i)_(i in [3])) != 0$. 
  
  We claim that for every pair $(alpha, v), (alpha',v') in FF times cal(C)$ with $alpha != alpha'$, we have that there exists a unique $lmap in linfuns$ such that $(alpha,v)$ and $(alpha',v')$ both belong to $im(lmap)$.  Indeed, let $c_2 = (v - v')/(alpha - alpha') in cal(C)$ and $c_1=v - alpha dot c_2$. Now $v = c_1 + alpha dot c_2$, and $c_1 + alpha' dot c_2 = v - alpha dot c_2 + alpha' dot c_2 = v'$, hence $(alpha,v)$ and $(alpha',v')$ both belong to $im(theta_(c_1,c_2))$. On the other hand, if $theta_(v_1,v_2)(alpha)=v$ and $theta_(v_1,v_2)(alpha')=v'$ for some $v_1,v_2 in cal(C)$, then 
  $
    v = v_1 + alpha dot v_2, quad quad 
    v'= v_1 + alpha' dot v_2
  $
  Subtracting, $(v - v')/ (alpha-alpha') = v_2 = c_2$, and then $v_1 = v - alpha dot v_2= v - alpha dot c_2 = c_1$, hence $theta_(v_1,v_2)=theta_(c_1,c_2)$, completing the proof of the claim.
  


   There are exactly  $|A_z| dot (|A_z|-1)$  pairs $(alpha_1,c_alpha_1), (alpha_2,c_alpha_2) in Y$ with $alpha_1 != alpha_2$. Fixing such $(alpha_1,c_alpha_1), (alpha_2,c_alpha_2) in Y$,  by @l:few_bad_points_on_line,  there are at most $delta dot blockclength +1$ pairs $(alpha_3, c_alpha_3) in Y$ belonging to the parameterized line $im(theta_(c_alpha_1, c_alpha_2))$. Hence there are at least $|A_z| -delta dot blockclength -1$ tuples $(alpha_3, c_alpha_3) in Y$ that do not belong to  $im(theta_(c_alpha_1, c_alpha_2))$.  Each of them satisfies $alpha_3 != alpha_1$ and $alpha_3 != alpha_1$ because otherwise $(alpha_3, c_3)$ would be either $(alpha_1, c_1)$ or $(alpha_2, c_2)$ #albert[What if $(alpha_1, c_1)$ is one of the bad points?]. 


    Overall, there are at least $|A_z| dot (|A_z|-1) dot (|A_z| -delta dot blockclength -1)$ triples $(alpha_i, c_alpha_i)_(i in [3]) in Y^3$ with $alpha_i != alpha_j$ for all $i!= j$ #albert[have I forgotten to substract/add $2$ somewhere because $alpha_3$ is not $alpha_1,alpha_2$?],  such that  $(alpha_3, c_alpha_3) in.not im(theta_(c_alpha_1, c_alpha_2))$. By @l:colinear, for such triple we have $U((alpha_i, c_alpha_i)_(i in [3])) != 0$. The lemma then follows, since, as we discussed before, $T_z$ is exactly set of triples $(alpha_i, c_alpha_i)_(i in [3]) in Y^3$ with $alpha_i != alpha_j$ for all $i!=j$ such that $U((alpha_i, c_alpha_i)_(i in [3])) != 0$.
]


We are ready to prove @t:main_thm.

#proof[Proof of @t:main_thm][
  #albert[Where do we use $t≥ delta dot blockclength +2$?] Let $cal(Z)_t subset cal(Z)$ be the set of all $z in cal(Z)$ such that $|A_z| ≥ t$ for all $z in cal(Z)_t$. Then by @l:third_moment_bound,
  $
  cases(delim: #none,
  sum_(z in cal(Z)_t) |T_z| &≥ sum_(z in cal(Z)_t) |A_z| dot (|A_z| -1) dot (|A_z| - delta dot blockclength -1) dot |cal(Z)_t|, &≥ t dot (t -1) dot (t - delta dot blockclength -1) dot |cal(Z)_t|
  )
  $<e:proof_thm_1>
  We now claim that 
  $
  sum_(z in cal(Z)) |T_z| ≤ (|FF| dot L)^3 dot epsilon_(sans("evader")) dot |cal(Z)|.
  $
  Indeed, let $P subset FF times cal(C)$ be the set of all tuples $(alpha, c)$ such that $c$ is an $alpha$-pretender. We have $|P| ≤ |FF| dot L$,
  where the list size factor $L$ is due  to the fact that an $alpha$-pretender is $delta$-close to #aiedit[$lambda_1(alpha) dot u_1 + lambda_2(alpha) dot u_2$], and since $cal(C)$ is $(delta, L)$-list decodable, there are at most $L$ codewords in $cal(C)$ that are $delta$-close to #aiedit[$lambda_1(alpha) dot u_1 + lambda_2(alpha) dot u_2$].
  
  Now, for each triple $(alpha_i, c_i)_(i in [3]) in T_z$, we have by definition that $U((alpha_i, c_i)_(i in [3])) != 0$ and $(alpha_i, c_i)$ is consistent with $(z, vb(b)_1^*, vb(b)_2^*)$ for all $i in [3]$. By @l:colinear_zero, $evalmap_z (U((alpha_i, c_i)_(i in [3])))=0$. Since $0!=U((alpha_i, c_i)_(i in [3])) in cal(C)$, by the definition of zero evader there are at most $epsilon_(sans("evader")) dot |cal(Z)|$ elements $z in cal(Z)$ such that $evalmap_z (U((alpha_i, c_i)_(i in [3])))=0$. 

  Recapping, there are at most $(|FF| dot L)^3$ triples  $(alpha_i, c_i)_(i in [3]) in P^3$, and every triple that belongs to some $T_z$ is one of these triples. Now, for each such triple, if $U(((alpha_i, c_i)_(i in [3])))!=0$  there are at most $epsilon_(sans("evader")) dot |cal(Z)|$ elements $z in cal(Z)$ such that $(alpha_i,c_i)$ is consistent with $(z, vb(b)_1^*, vb(b)_2^*)$ for all $i in [3]$. Since the latter is a necessary condition for a triple $(alpha_i, c_i)_(i in [3]) in P^3$  to belong to $T_z$, we have that 
 $
sum_(z in cal(Z)_t) |T_z| ≤ sum_(z in cal(Z)) |T_z| &= lr(|{ (z,(alpha_i,c_i)_(i in [3])) in cal(Z) times P^3 mid(|) (alpha_i,c_i)_(i in [3]) in T_z}|)
\ &=sum_((alpha_i, c_i)_(i in [3]) in P^3) lr(|{z in cal(Z) mid(|) (alpha_i, c_i)_(i in [3]) in T_z}|) \
      &<= sum_((alpha_i, c_i)_(i in [3]) in P^3) epsilon_(sans("evader")) dot |cal(Z)| <= (|FF| dot L)^3 dot epsilon_(sans("evader")) dot |cal(Z)|,
$<e:proof_thm_2> as claimed. Combining @e:proof_thm_1 and @e:proof_thm_2 we now obtain 
  $
  t dot (t-1) dot (t -delta dot blockclength -1) dot |cal(Z)_t| ≤ (|FF| dot L)^3 dot epsilon_(sans("evader")) dot |cal(Z)|
  $
  and, since $t> delta dot blockclength-1$, both sides of the inequality are positive and then the theorem follows since $Pr_(z <- cal(Z))[ |A_z| ≥ t ] = |cal(Z)_t| \/ |cal(Z)|$.
]


= Folding of constrained interleaved  codes with BEEP <s:BEEP_fold>

== The BEEP IOR
// [AI-edited (claude-fable-5-2), 2026-11-12, at the author's request: this section uses lambda_1(alpha) = 1-alpha, lambda_2(alpha) = alpha throughout. Edited: the second sentence below; the weights (1, alpha) became (1-alpha, alpha) in c:BEEP (Rounds 2, 3 and Output) and in Round 2 of the proof of t:beep_soundness. Please review]
We assume the notation from Section @s:better_pretenders. #aiedit[Throughout this section, the linear maps $lambda_1, lambda_2$ fixed there are $lambda_1(alpha) = 1-alpha$ and $lambda_2(alpha) = alpha$ (they satisfy the assumption made there), i.e. two words $u_1, u_2$ are folded as $(1-alpha) dot u_1 + alpha dot u_2$.] Define the following relation:
$ cal(R)_(cal(C)) := lr({
    lr(( cases(delim: #none,
      bb(x) = (mu, vb(v)) in FF times FF^(codedim) \,,
      bb(y) = f in FF^blockclength\,,
      bb(w) = vb(f) in FF^(codedim),
    ) ))
    mid(|)
    cases(delim: #none,
      f = Enc_cal(C)(vb(f)) \,,
      lr(⟨vb(f), vb(v) ⟩) = mu,
    )
  }) . $

Let $interleavedcode(k) subset (FF^k)^blockclength$ be the $k$-interleaving of the code $cal(C)$. We think of codewords $f in cal(C)^(equiv k)$ as matrices of $k times blockclength$ field elements, where each row of the matrix is a codeword. We write the rows of $f$ as
$
f = (f_(1*), dots, f_(k*)) in cal(C)^k subset (FF^blockclength)^k, quad quad quad f_(i*) in cal(C) "for all" i in [k].
$
Similarly, we think of messages $vb(f)in FF^(k dot codedim)$ to be encoded with $interleavedcode(k)$ as $k times codedim$  matrices with rows $vb(f)_(1*), dots, vb(f)_(k*) in FF^codedim$.


We define an Interactive Oracle Reduction (IOR) from $cal(R)_(interleavedcode(2))$ to $cal(R)_cal(C)$ with a soundness analysis that does not require Mutual Correlated Agreement (MCA).


In @c:BEEP below, we look at the linear constraint $langle vb(f), vb(v) rangle = mu$ from $cal(R)_(interleavedcode(2))$ as a sumcheck claim for the product of the MLE's of $vb(f)$ and $vb(v)$, exploiting that
$
langle vb(f), vb(v) rangle = sum_(vb(b)in {0,1}^(1+ codedim)) MLE(vb(f))(vb(b)) dot MLE(vb(v))(vb(b)).
$
where here we index the entries of the $2 times codedim$ matrices $vb(f)$ and $vb(v)$ over the set ${0,1}^(1+log codedim)$, so that the first bit in the index indicates the row of the matrix. This way $MLE(vb(f))(X, vb(Y)) = (1-X) dot MLE(vb(f)_(1*))(vb(Y)) + X dot MLE(vb(f)_(2*))(vb(Y))$, and similarly for $MLE[vb(v)](X, vb(Y))$, where $vb(Y)=(Y_1, dots, Y_(log(codedim)))$.


#construction[BEEP, an IOR from $cal(R)_(interleavedcode(2))$ to $cal(R)_(cal(C))$][
  The prover and verifier receive as input  $bb(x)=(mu, vb(v)) in FF times FF^(2 dot codedim)$. The verifier also receives $bb(y)=f in FF^blockclength$, and the prover  receives $bb(w)=vb(f)in FF^(2 dot codedim)$ such that $(bb(x), bb(y), bb(w)) in cal(R)_(interleavedcode(2))$.

  // Fix a scalar zero-evader $(γ_z)_(z ∈ 𝒵_batch)$ on $𝔽^(m+1)$ with error $ε_batch$ for batching linear claims.
  
  + *Round 1 (Zero evader for the two matrix rows).* The verifier samples and sends uniformly at random $z ∈ 𝒵$. The prover replies with two vectors $𝐛_1, 𝐛_2 ∈ 𝔽^m$, supposedly 
    $
      𝐛_1 &= φ_z  𝐟_(1*), &quad quad
      𝐛_2 &= φ_z  𝐟_(2*)
    $
  + *Round 2 (Fold and sumcheck round).* 
    The prover sends the quadratic univariate polynomial#footnote[We do not discuss optimizations related to sumcheck that may be used in this step, see e.g. @Gru24 and @BDDT25.]
    $
      h(X):= sum_(vb(b)in {0,1}^(log codedim)) MLE(vb(f))(X,vb(b)) dot MLE(vb(v))(X,vb(b)) in FF^(<3)[X]
    $
    The verifier checks that $h(0)+h(1) = mu$, and uniformly samples and sends a #emph[folding and sumcheck challenge] $alpha in FF$. Define
    $
      g &:= (1-alpha) dot f_(1*) + alpha dot f_(2*) in FF^blockclength, \
      vb(g) &:= (1-alpha) dot  vb(f)_(1*) + alpha dot vb(f)_(2*) in FF^codedim, \
      vb(v)_alpha &:= (1-alpha) dot  vb(v)_(1*) + alpha dot vb(v)_(2*) in FF^codedim
    $
    Note that $MLE(vb(f))(alpha,vb(X))= MLE(aiedit((1-alpha) dot) vb(f)_(1*) + alpha dot vb(f)_(2*))(vb(X))= MLE(vb(g))(vb(X))$,   and similarly $MLE(vb(v))(alpha,vb(X)) = MLE(vb(v)_alpha)(vb(X))$ #albert[Place some remark about this]. If the prover is honest, then $vb(g)$ satisfies all of the following linear claims: #albert[We moved from using codewords inside the eval maps to using the message]
    $
      h(alpha) &= sum_(vb(b)in {0,1}^(log codedim)) MLE(vb(g))(vb(b)) dot MLE(vb(v)_alpha)(vb(b)) = langle vb(g)\, vb(v)_alpha rangle,\
      φ_z 𝐠 &= φ_z (aiedit((1-alpha) dot) vb(f)_(1*)+alpha dot vb(f)_(2*)) = aiedit((1-alpha) dot) 𝐛_1 + alpha dot 𝐛_2 .
    $<BEEP_new_lin_claims>

    #remco[This uses $1,α$ instead of $1-α,α$ from above def of $𝐠$. But I really want to rewrite it as some $α_z upright(F)$ for interleaving matrix $upright(F)$ and some multilinear evader $α_z$.]

  + *Round 3 (Batching of linear claims).* The verifier uniformly samples $vb(γ) ∈ 𝔽^(m + 1)$ to batch the linear claims from @BEEP_new_lin_claims, so that the claims are reduced to the single claim
    $
      vb(gamma) dot mat(vb(v)_alpha; φ_z) dot vb(g) =
      vb(gamma) dot mat(h(alpha); aiedit((1-alpha) dot) 𝐛_1 + alpha dot 𝐛_2)
    $
  + *Output.*  The prover and verifier output
    $
      bb(x)' := (mu', vb(v)'), quad
      bb(y)' := g in FF^blockclength, quad
      bb(w)' := vb(g) in FF^codedim, \
      vb(v)' := vb(gamma) dot mat(vb(v)_alpha; φ_z)  ∈ 𝔽^ℓ, quad
      mu' := vb(gamma) dot mat(h(alpha); aiedit((1-alpha) dot) 𝐛_1 + alpha dot 𝐛_2) ∈ 𝔽
    $
    For an honest prover, it holds that $(bb(x)', bb(y)', bb(w)')in cal(R)_cal(C)$.
  ]<c:BEEP>

== Completeness and round-by-round knowledge soundness
Before stating and proving the completeness and knowledge soundness of @c:BEEP, we define relaxed versions of the relations  $cal(R)_(interleavedcode(2))$ and  $cal(R)_(cal(C))$:

#definition[The relaxed relation $(cal(R)_(cal(C')))^delta$][ Let $cal(C') subset FF^blockclength$ be a linear code of blocklength $blockclength$ and dimension $codedim$. Let $delta in (0,1)$ be a proximity parameter. We define the $delta$-relaxation of the relation $cal(R)_(cal(C'))$ as:
  $ cal(R)_(cal(C'))^delta := lr({
    lr(( cases(delim: #none,
      bb(x) = (mu, vb(v)) in FF times FF^(codedim) \,,
      bb(y) = f in FF^blockclength\,,
      bb(w) = vb(f) in FF^(codedim),
    ) ))
    mid(|)
    cases(delim: #none,
      hamming(f, Enc_cal(C')(vb(f))) ≤ delta \,,
      lr(⟨vb(f), vb(v) ⟩) = mu,
    )
  }) . $
  The relation $cal(R)_(cal(C'))^delta$ is exactly the same as $cal(R)_(cal(C'))$, but replacing the constraint $f = Enc_cal(C')(vb(f))$ with $ hamming(f, Enc_cal(C')(vb(f))) ≤ delta$. The relaxation $cal(R)_(interleavedcode(2))^delta$ of $cal(R)_(interleavedcode(2))$ is defined in the same way.
]

  
#theorem[Completeness and round-by-round knowledge soundness of @c:BEEP][
   Let $cal(C) subset FF^blockclength$ be a linear code of blocklength $blockclength$ and dimension $codedim$, and with minimum relative distance  $cal(C)$. Let $delta in (0,Delta(cal(C)))$ be a proximity parameter, and let $L_(cal(C)), L_(interleavedcode(2))$ be such that $cal(C)$ is $(delta, L_(cal(C)))$-list decodable and  $interleavedcode(2)$ is $(delta, L_(interleavedcode(2)))$-list decodable, respectively,  (we do not require decodability to be efficient).  Let $(φ_z)_(z ∈ cal(Z)_(sans("evader")))$ be a zero evader with error $epsilon_(sans("evader"))$.
  
  Then @c:BEEP is a perfectly complete three-round IOR from $cal(R)_(interleavedcode(2))$ to $cal(R)_(cal(C))$ with round-by-round knowledge soundness with relaxation $(cal(R)_(interleavedcode(2))^delta, cal(R)_(cal(C))^delta)$, with errors
  $
  kappa_1 &:= ((|FF| dot L_cal(C))^3 dot epsilon_"evader")/((delta dot blockclength + 1)^2) \
  kappa_2 &:= (delta dot blockclength +1 + 2dot LL_(interleavedcode(2))/ (|FF|) \
  kappa_3 &:= (L)/(|FF|)
  $
]<t:beep_soundness>

#proof[
 Let $Pi$ denote @c:BEEP. In our formalization of IORs (Section @s:IOR), every round starts with the prover sending a message, and then the verifier replies with a challenge. Since, as described, Rounds 1 and 3 of @c:BEEP start off with a verifier challenge, we modify $Pi$ so that the prover sends  empty messages at the beginning of those rounds. 

It is clear that $Pi$ is perfectly complete #albert[review]?. We prove soundness of $Pi$.  Let $inp=(mu,vb(v))in FF times FF^(2 times codedim)$ and  $oracle=f in FF^(2 times blockclength)$, with $f=(f_(1*), f_(2*))$. Let $tr$ be a partial interaction transcript for $Pi$.

We progressively describe a knowledge state function $kstate$ for $Pi$. For all $kswit$, if  $tr = emptyset$ is the empty transcript, then we set $kstate(inp, oracle, tr, kswit) = 1$ if and only if $(inp, oracle; kswit) in cal(R)_(interleavedcode(2))^delta$, for all $kswit in FF^codedim$. If $tr$ is a transcript where the prover is about to move and $kstate(inp, oracle, tr, kswit) = 0$, then we define $kstate(inp, oracle, tr, provermsg, kswit) = kstate(inp, oracle, tr, kswit)$ for every prover message $provermsg$. If $tr = (provermsg_1, verifiermsg_1, provermsg_2, verifiermsg_2, provermsg_3, verifiermsg_3)$ is a full transcript, then we define $kstate(inp, oracle, tr, kswit) = 1$ if and only if $verifier$ on $tr$ outputs $(inp', oracle')$ such that $(inp', oracle'; kswit) in cal(R)_(cal(C))^delta$.

So far $kstate$ satisfies the conditions of Knowledge State function from @def:knowledge-state-function. We now complete our definition of $kstate$ on the rest of partial transcripts $tr$ for which $kstate(inp, oracle, tr, kswit)$ has not yet been defined. These are precisely the nonempty transcripts where the prover is about to move. 

#paragraph[Round 1.] Let $m_1=emptyset$ be an empty first prover message. For every first verifier challenge $z in cal(Z)$, we let 
$
kstate(inp, oracle, m_1, z, kswit) = 1 " " <==>  " " |A_z| ≥ delta dot blockclength +2, " or " (inp,oracle,kswit) in cal(R)_(interleavedcode(2))^delta,
$ 
where, $A_z$ is the set of elements $alpha in FF$ that are DEEP-MCA-bad with respect to $(z, vb(b)_1^*, vb(b)_2^*)$ and the words $f_(1*), f_(2*) in FF^blockclength$.  

We define an extractor $rbrextractor$ for transcripts of the form $tr=(m_1, z)$ as $rbrextractor(inp, oracle, m_1, z, kswit)= kswit$. We now bound the following probability:
$
  s_1:=Pr_(z <- cal(Z)) lr([ exists kswit "such that" cases(delim: #none,
  and kstate(inp, oracle, m_1, rbrextractor(inp, oracle, m_1,z, kswit)) = 0,
  and kstate(inp, oracle, m_1, z, kswit) = 1,
  ) ])
$<e:beep_soundness_prob_1>
We show that @e:beep_soundness_prob_1 is at most $kappa_1$ as defined in the statement of the present @t:beep_soundness. Indeed, assume $kstate(inp, oracle, m_1,  kswit) = 0$. Then by definition we have $(inp,oracle, kswit) in.not cal(R)_(interleavedcode(2))^delta$.  The only way we can have  $kstate(inp, oracle, m_1, z, kswit) = 1$ then is if $ abs(A_z) ≥ delta dot blockclength +2$. By @t:main_thm taking $t= delta dot blockclength+2$,  we have $Pr_(z <- cal(Z))[ abs(A_z) ≥ delta dot blockclength+2] ≤ (|FF| dot L_cal(C))^3 dot ε_check \/ ((delta dot blockclength + 2) dot (delta dot blockclength + 1)) ≤ kappa_1$. It follows that $s_1 ≤ kappa_1$.

//Indeed, assume $kstate(inp,oracle, m_1, kswit) = 0$. Then either $langle kswit, vb(v) rangle != mu$ or $hamming(f, Enc_cal(interleavedcode(2))(wit)) > delta$. Assume first that $langle kswit, vb(v) rangle != mu$. Then by definition $kstate(inp,oracle, m_1 || z, kswit)=0$ as well, hence $S_1=0$. Otherwise  

#paragraph[Round 2.] Let $m_1=emptyset$ be an empty first prover message; $z in cal(Z)$ a verifier first challenge; and $m_2=(vb(b)_1, vb(b)_2 , h(X))  in FF^numsamples times FF^numsamples times FF^(<3)[X]$ a second prover message. Let $tr=(m_1, z, m_2)$. For every second verifier challenge $alpha in FF$, we let 
$
kstate(inp, oracle, tr, alpha, kswit) = 1 " " <==>  " " |A_z|≥ delta dot blockclength +1 " or "
lr((cases(delim:#none,
& kswit  in FF^(codedim),
and & h(0)+h(1) = mu,
and & langle kswit\, (1-alpha) dot vb(v)_(1*) + alpha dot vb(v)_(2*)  rangle = h(alpha),
and &  φ_z kswit =  aiedit((1-alpha) dot) 𝐛_(1) + alpha dot 𝐛_(2),
and & hamming(aiedit((1-alpha) dot) f_(1*) + alpha dot f_(2*), Enc_cal(C)(kswit)) ≤ delta 
))) //" or " langle kswit, vb(v)  rangle != mu,
$ 
We define an extractor $rbrextractor$ for transcripts of the form $(tr, alpha)$ as follows. #albert[Mention somewhere this is similar to the techniques from "linear time accumulation schemes"] The extractor proceeds under the assumption that $Delta(aiedit((1-alpha) dot) f_(1*) + alpha dot f_(2*), Enc_cal(C)(kswit))≤delta$. If that is not the case, the extractor may fail and output $bot$.  The extractor computes $Enc_cal(C)(kswit)$ and finds the maximal set $S_alpha subset [blockclength]$ where $Enc_cal(C)(kswit)$ and $aiedit((1-alpha) dot) f_(1*) + alpha dot f_(2*)$ agree. If $|S_alpha| < (1-delta) dot blockclength$, the extractor outputs $bot$.

Next, the extractor computes $kswit_(1*), kswit_(2*) in FF^codedim$ such that  $Enc_cal(C)(kswit_(i*))$ agrees with $f_(i*)$ on $S_alpha$ for both $i=1,2$, with the following procedure: let $M_cal(C) in FF^(blockclength times codedim)$ be an encoding matrix for $cal(C)$. The extractor sets up the following system of linear equations  on variables $(kswit_(1*), kswit_(2*))$: #albert[Notation $f_S$]
$
&(M_cal(C) dot vb(w)_(i*))_(S_alpha) =  (f_(i*))_(S_alpha) " for " i=1,2,\
&(1-alpha) dot kswit_(1*) + alpha dot kswit_(2*) = kswit
$<e:system_beep_soundness>   and finds a solution  $(vb(w)_(1*),vb(w)_(2*))$ to it. If the system does not have a solution, the extractor outputs $bot$, and otherwise it outputs $kswit' := (vb(w)_(1*),vb(w)_(2*)) in FF^(2 times codedim)$.

We claim that @e:system_beep_soundness has a solution if and only if $f_(1*), f_(2*)$ have correlated agreement with $cal(C)$ over $S_alpha$, and in that case $kswit= aiedit((1-alpha) dot) kswit_(1*) + alpha dot kswit_(2*)$. Indeed, the direct implication is clear. Conversely, assume $f_(1*)$ and $f_(2*)$ agree with codewords $c_1, c_2 in cal(C)$ over $S_alpha$ with $c_i = Enc_cal(C)(kswit_(i*))$, $i=1,2$ for some $kswit_(i*) in FF^codedim$. Now $kswit = aiedit((1-alpha) dot) kswit_(1*) + alpha dot kswit_(2*)$ because $Enc_cal(C)(kswit)$ agrees with $aiedit((1-alpha) dot) f_(1*) + alpha dot f_(2*)$ on $S_alpha$, and so $Enc_cal(C)(kswit - (aiedit((1-alpha) dot) kswit_(1*) + alpha dot kswit_(2*)))$ is zero on $S_alpha$ and  $|S_alpha|≥ (1-delta)dot blockclength > (1-Delta(cal(C))) dot blockclength$  by assumption, forcing $kswit = aiedit((1-alpha) dot) kswit_(1*) + alpha dot kswit_(2*)$ by definition of minimum distance of the code $cal(C)$. This proves the claim. 

We now bound the following probability:
$
  s_2:=Pr_(alpha <- FF) lr([ exists kswit "such that" cases(delim: #none,
  and kstate(inp, oracle, tr,rbrextractor(inp, oracle, tr, alpha, kswit)) = 0,
  and kstate(inp, oracle, tr, alpha, kswit) = 1,
  ) ])
$<e:beep_soundness_prob_2>
We show that $s_2$ is at most $kappa_2$ as defined in the statement of the present @t:beep_soundness.  

First, if $z$ is such that $|A_z|≥ delta dot blockclength +2$, then $kstate(inp, oracle, tr, kswit)=1$ for all $kswit$, and so there is nothing to prove since $s_2=0$ in that case. Hence we assume $|A_z|≤ delta dot blockclength+1$ from now on. Second, if $h(0)+h(1) != mu$, then $kstate(inp, oracle, tr, alpha,  kswit)=0$ for all $alpha, kswit$ and there is nothing to prove. Hence we also assume $h(0)+h(1) = mu$. 


Let $B_1 subset FF$ be the set of DEEP-MCA-bad elements with respect to $(z, vb(b)_1, vb(b)_2, f_(1*), f_(2*))$. This is precisely the set $A_(z,vb(b)_1, vb(b)_2)$. Its cardinality is at most $|A_z|≤ delta dot blockclength +1$.  

We further define a subset of challenges  $B_2 subset FF$ as follows. Let $W subset FF^(2 times codedim)$ be the set of messages $kswit'$ such that $hamming_(interleavedcode(2))(Enc_(interleavedcode(2))(kswit'), f) ≤ delta$.  agrees with $f in FF^(2 times blockclength)$ on $S_alpha$. Since $cal(C)$ is $(delta, L)$-list decodable, $|W|≤ L$ #albert[I need to discuss list decodability of interleaved codes]. Then we let $B_2 subset FF$ be the set of all $alpha in FF$ such that for some $kswit'=(kswit_(1*), kswit_(2*)) in W$, we have
$
h_(kswit')(X) != h(X) quad " and " quad h_(kswit')(alpha) = h(alpha)
$
where $h_(kswit')(X)$ is the quadratic polynomial $h_(kswit')(X) := langle aiedit((1-X) dot) kswit_(1*) + X dot kswit_(2*), aiedit((1-X) dot) vb(v)_(1*) + X dot vb(v)_(2*) rangle$. If $h_(kswit')(X) != h(X)$, then there are at most $2$ field elements $alpha$ such that  $h_(kswit')(alpha) != h(alpha)$, and so $|B_2| ≤ 2 dot |W|≤ 2 dot L_(interleavedcode(2))$.

We show that if $alpha in.not B_1 union B_2$, then $kstate(inp,oracle, tr, alpha, kswit)=1$ implies that $kstate(inp,oracle, tr, rbrextractor(inp,oracle,tr, alpha,kswit))=1$. Once this claim is proved, it follows that
$
s_2 ≤ (|B_1| + |B_2|)/(|FF|) ≤ (delta dot blockclength + 1 + 2 dot L_(interleavedcode(2)))/(|FF|) = kappa_2 
$
To prove the claim, assume $kstate(inp,oracle, tr, alpha, kswit)=1$. Then $aiedit((1-alpha) dot) f_(1*) + alpha dot f_(2*)$ and  $Enc_cal(C)(kswit)$ agree on the set $S_alpha subset [blockclength]$ computed by the extractor, with $|S_alpha| ≥ (1-delta) dot blockclength$. Since $alpha in.not B_1$, $alpha$ is not DEEP-MCA-bad with respect to $(z, vb(b)_1, vb(b)_2, f_(1*), f_(2*))$. Now, $(alpha, $ must be consistent with $(z, vb(b)_1, vb(b)_2)$ because $phi_z kswit = aiedit((1-alpha) dot) vb(b)_(1) + alpha dot vb(b)_(2)$ and $hamming(aiedit((1-alpha) dot) f_(1*)+alpha dot f_(2*), Enc_cal(C)(kswit))≤ delta$ due to  $kstate(inp,oracle, tr, alpha, kswit)=1$. Hence, $Enc_cal(C)(kswit)$ is not an $alpha$-pretender. This means that $f_(1*), f_(2*)$ have correlated agreement with $cal(C)$ over $S_alpha$. By our previous claim, the system of equations @e:system_beep_soundness has a solution $kswit'=(kswit_(1*), kswit_(2*))in FF^(2 times codedim)$, which is output by the extractor. Now, $kstate(inp,oracle, tr, kswit')=1$ if and only if $|A_z|≥ delta dot blockclength +2$ or $(inp, oracle, kswit') in cal(R)_(interleavedcode(2))^delta$.  We assumed the former does not occur, and so we now have to show that $(inp, oracle, kswit') in cal(R)_(interleavedcode(2))^delta$, i.e. we must prove that $langle kswit', vb(v) rangle = mu$ and $hamming_(interleavedcode(2))(f, Enc_(interleavedcode(2))(kswit')) ≤ delta$ . The second holds because $f_(1*), f_(2*)$ agree with with $Enc_cal(C)(kswit_(1*)), Enc_cal(C)(kswit_(2*))$ on $S_alpha$. We now prove the first. We know that $langle kswit, aiedit((1-alpha) dot vb(v)_(1*) + alpha dot vb(v)_(2*))  rangle= h(alpha)$ and that $kswit=(1-alpha) dot kswit_(1*) + alpha dot kswit_(2*)$, and so $h_(kswit')(alpha) = h(alpha)$. Since $kswit' in W$ and  $alpha in.not B_2$, we must have that $h_(kswit')(X) = h(X)$. Since $h(0) + h(1)= mu$, we obtain 
$
mu = h_(kswit')(0) + h_(kswit')(1) = langle kswit_(1*), vb(v)_(1*) rangle  + aiedit(langle kswit_(2*)\, vb(v)_(2*) rangle) =  langle kswit', vb(v) rangle,
$
as needed. This completes the proof of our claim.




#paragraph[Round 3.] Let $m_1,m_2$ be a first and second message; $m_3$ an empty third prover message; and $z in cal(Z)$ and $alpha in FF$  verifier first and second challenges.  Let $tr=(m_1, z, m_2, alpha, m_3)$. By definition, for every third verifier challenge  $vb(gamma) in FF^(1+numsamples)$, we have
$
kstate(inp, oracle, tr, vb(gamma), kswit) = 1 " " <==>  " "  (inp', oracle', kswit) in cal(R)_(cal(C))^delta " and " verifier(inp, oracle, tr, vb(gamma)) =1
$ 
where 
   $
      bb(x)' := (mu', vb(v)'), quad
      bb(y)' := g = (1-alpha) dot f_(1*) + alpha dot f_(2*)\
      vb(v)' := vb(gamma) dot mat(vb(v)_alpha; φ_z)  ∈ 𝔽^ℓ, quad
      mu' := vb(gamma) dot mat(h(alpha); aiedit((1-alpha) dot) 𝐛_1 + alpha dot 𝐛_2) ∈ 𝔽.
    $
We define an extractor $rbrextractor$ for transcripts of the form $(tr, vb(gamma))$ as $rbrextractor(inp, oracle, tr, vb(gamma), kswit)= kswit$. We now bound the following probability:
$
  s_3:=Pr_(vb(gamma) <- FF^(1+numsamples)) lr([ exists kswit "such that" cases(delim: #none,
  and kstate(inp, oracle, tr,rbrextractor(inp, oracle, tr, vb(gamma), kswit)) = 0,
  and kstate(inp, oracle, tr, vb(gamma), kswit) = 1,
  ) ])
$<e:beep_soundness_prob_2>
We show that $s_3 ≤ 1 \/ |FF|$. Indeed, assume $kstate(inp, oracle, tr, kswit) = 0$  and $kstate(inp, oracle, tr, vb(gamma), kswit) = 1$ for some $kswit$. Since $verifier(inp, oracle, tr, vb(gamma))=1$, we have $h(0)+h(1)=mu$. Moreover since $(inp',oracle',kswit)in cal(R)_cal(C)^delta$, we have $kswit in FF^codedim$ and $hamming(g, Enc_cal(C)(kswit)) = hamming(aiedit((1-alpha) dot) f_(1*) + alpha dot f_(2*), Enc_cal(C)(kswit)) ≤ delta$. Hence, to have $kstate(inp, oracle, tr, kswit) = 0$ either $phi_z kswit != (1-alpha) dot vb(b)_1 + alpha dot vb(b)_2$, or $langle kswit, vb(v)_alpha rangle != h(alpha)$. On the other hand, since $(inp',oracle',kswit)in cal(R)_cal(C)^delta$, the linear combination with the challenge $vb(gamma)$ of these two inequalities  Further 
$
 vb(gamma) dot (vb(v)_alpha, phi_z)^(sans("T")) dot kswit = vb(gamma) dot (h(alpha),(1-alpha) dot vb(b)_1 + alpha dot vb(b)_2)^(sans("T")), 
$ 
By Schwartz-Zippel lemma the probability over $vb(gamma)$ that the above equality holds, for fixed $kswit$, is  $≤ (1)/(|FF|)$.  Finally, there are at most $L$ tuples $kswit in FF^codedim$ such that $(inp',oracle', kswit) in cal(R)_(cal(C))^(delta)$, and so, by a union bound, $s_3 ≤ L \/ |FF|$. ]




== BEEP-WHIR and BEEP-Ligerito

#albert[For this one I had an AI draft the subsection first and then I edited it heavily]

For completeness, we now obtain an IOR from $cal(R)_(interleavedcode(k))$ to $cal(R)_(cal(C)')$, where $cal(C)'$ is a new linear code of the same dimension as $cal(C)$. The oracle part $oracle'$ output of this IOR consists of a single oracle, which is supposdly an oracle to a codewords from $cal(C)'$ (this is in constrast to @c:BEEP, where the output $oracle'$ is a linear combination of other oracles). One can then repeatedly apply this IOR in order to obtain an IOPP (or, more intuiviely, a PCS) for $cal(R)_(interleavedcode(k))$. The resulting IOPP is a ``BEEP variant'' of Ligerito @ligerito, or of WHIR @whir when using Reed-Solomon codes of different rates. One can equally envision BEEP variants of other code-based PCSs.


 We moslty follow the blueprint of the Zook paper @zook[Theorem 9.10] (though we do not consider zk in our case). Concretley, we first compose  @c:BEEP with itself $log k$ times, so as to obtain an IOR from  $cal(R)_(interleavedcode(k))$ to $cal(R)_(cal(C))$, and then we compose this IOR with a  the code-switching IOR from @zook, without zero-knowledge.

 Besides the fact that our folding step uses the BEEP sampling technique, this construction is well-known @whir@ligerito@blaze@zook. Because of this we discuss it only in broad terms.

 #construction[BEEP folding and code switching: an IOR from $cal(R)_(interleavedcode(k))$ to $cal(R)_(cal(C)')$][
    *Parameters.* The code $cal(C)$; a power of two $k$; a linear code $cal(C)'$ with message space $FF^codedim$ (possibly an interleaved code); zero evaders $(phi^((j))_z)_(z in cal(Z)_j)$ on $FF^(k dot codedim \/ 2^j)$ for $j in [log k]$, and $(phi'_z)_(z in cal(Z)')$ with $phi'_z : FF^codedim -> FF^(m')$; a number of queries $Q ≥ 1$. \
  *Inputs.* The prover and verifier receive as input $inp = (mu, vb(v)) in FF times FF^(k dot codedim)$ and $oracle = f in (FF^k)^blockclength$. The prover also receives $wit = vb(f) in FF^(k dot codedim)$ such that $(inp, oracle, wit) in cal(R)_(interleavedcode(k))$.
  
  + *Folding.* Let $(inp_0, oracle_0, wit_0) := (inp, oracle, wit)$ and $cal(C)_j = interleavedcode(2^k\/2^j)$ for $j≥ 0$. Note that $cal(C)_(j-1) = cal(C)_j^(equiv 2)$ for all $j≥ 1$. For $j in [log k]$, the prover and verifier engage in @c:BEEP to reduce the claim that 
    $
      (inp_(j-1), oracle_(j-1), wit_(j-1)) in cal(R)_(cal(C)_(j)^(equiv 2))
    $
    to a claim of the form
    $
      (inp_(j), oracle_(j), wit_(j)) in cal(R)_(cal(C)_(j))
    $
    for $inp_j, oracle_j, wit_j$ output by @c:BEEP.  Write $((hat(mu), hat(vb(v))), g, vb(g)) := (inp_(log k), oracle_(log k), wit_(log k))$. If the prover is honest, we have $((hat(mu), hat(vb(v))), g, vb(g)) in cal(R)_cal(C)$. 

    An important property of $g$ is that it is a linear combination of the rows of $f in FF^(k times blockclength)$. Hence the verifier can obtain $g(x)$ for any $x in [blockclength]$ by querying $f$.

  + *Code switching.* We apply the IOR from @?. The prover and verifier start with the claim $((hat(mu), hat(vb(v))), g, vb(g)) in cal(R)_cal(C)$ and proceed as follows:
    + *Round 1 (New oracle and out of domain samples).* The prover sends a word $g'$, supposedly $g' = Enc_(cal(C)')(vb(g))$. The verifier uniformly samples and sends  $z' in cal(Z)'$. The prover replies with $vb(b)' in FF^(m')$, supposedly $vb(b)' = phi'_(z') vb(g)$.
    + *Round 2 (Queries).* The verifier uniformly samples and sends $x_1, dots, x_Q in [blockclength]$. If the prover is honest, then $vb(g)$ satisfies the following linear claims:
      $
        langle vb(g), hat(vb(v)) rangle &= hat(mu), \
        phi'_(z') vb(g) &= vb(b)', \
        (M_cal(C))_(x_i) dot vb(g) &= g(x_i) quad "for all" i in [Q],
      $<e:codeswitch_lin_claims>
      where $(M_cal(C))_x$ denotes the $x$-th row of an encoding matrix $M_cal(C)$ of $cal(C)$.
      The verifier obtains the values $g(x_1), dots, g(x_Q)$ by querying $f$, as explained previously.
    + *Round 3 (Batching of linear claims).* The verifier uniformly samples and sends $vb(gamma)' in FF^(1 + m' + Q)$ to batch the linear claims from @e:codeswitch_lin_claims into a single claim.

  + *Output.*  The prover and verifier output $inp' := (mu', vb(v)')$, $oracle' := g'$ and $wit' := vb(g)$, where
    $
      vb(v)' := vb(gamma)' dot (hat(vb(v)), phi'_(z'), (M_cal(C))_(x_1), dots, (M_cal(C))_(x_Q))^(sans("T")), quad
      mu' := vb(gamma)' dot (hat(mu), vb(b)', g(x_1), dots, g(x_Q))^(sans("T")).
    $
    For an honest prover, it holds that $(inp', oracle', wit') in cal(R)_(cal(C)')$.
 ]<c:BEEP_codeswitch>

#theorem[Completeness and round-by-round knowledge soundness of @c:BEEP_codeswitch][
 Let $(epsilon_j)_(j in [log k])$ and $epsilon'$ be error bounds of the zero evaders used in @c:BEEP_codeswitch. Let $delta in (0, Delta(cal(C)))$ and $delta' in (0,1)$. Let $L_0, dots, L_(log k)$ and $L'$ be such that $interleavedcode(k\/2^j)$ is $(delta, L_j)$-list decodable for all $j$, and $cal(C)'$ is $(delta', L')$-list decodable.

  Then @c:BEEP_codeswitch is a perfectly complete IOR from $cal(R)_(interleavedcode(k))$ to $cal(R)_(cal(C)')$ with #box[$3 dot log k + 3$] rounds and with round-by-round knowledge soundness with relaxation $(cal(R)_(interleavedcode(k))^delta, cal(R)_(cal(C)')^(delta'))$. Its errors are $(kappa_(j,1), kappa_(j,2), kappa_(j,3))_(j in [log k])$ for the three rounds of each execution of @c:BEEP during the Folding process, and  $(kappa'_1, kappa'_2, kappa'_3)$ for the three rounds of Step 2, where
  $
    kappa_(j,1) := ((|FF| dot L_j)^3 dot epsilon_j) / ((delta dot blockclength + 1)^2), quad
    kappa_(j,2) := (delta dot blockclength + 1 + 2 dot L_(j-1)) / (|FF|), quad
    kappa_(j,3) := L_j / (|FF|), \
    kappa'_1 := ((L')^2 dot epsilon') / 2, quad
    kappa'_2 := (1 - delta)^Q, quad
    kappa'_3 := L' / (|FF|).
  $
]<t:beep_codeswitch>

#proof[Proof outline][Once the completeness and round-by-round knowledge of the code-switching step are established, the theorem follows from
   @t:beep_soundness and the lemma for composing IORs (@r:ior_compositoin). The code switching step is exactly #albert[review] @zook[Construction 9.7] without zero-knowledge, for the relations $cal(R)_cal(C)$ and $cal(C)_cal(C')$. This IOR is clearly perfectly complete, and, by @zook[Lemma 9.9] #albert[review lemma], this IOR  has round-by-round knowledge soundness with  relaxation $(cal(R)^delta_cal(C), cal(R)^(delta')_(cal(C)'))$ and errors $kappa'_1, kappa'_2, kappa'_3$ #albert[Check if I should be more explicit mapping our notation to Zook's].
]
= BEEP with affine folding for Reed-Solomon codes <s:affine>

// [AI-drafted in the author's register (claude-fable-5-2), 2026-11-14, at the author's request ("Write a section in the typst paper titled 'Beep with affine folding for Reed Solomon codes'. Match the style of the paper. Regarding constructions from section 4, let's only discuss the modification and state a theorem with the errors"): this whole section, up to the heading of the Experiments. Status of its claims: @t:affine_main_0, @l:affine_line and the examples of the two remarks that follow the theorem and its proof were checked by brute force over small fields with two independent programs, and the count of bad challenges behind the error kappa_2 of @t:affine_beep with one of them (scripts and logs: .claude/scratch/affine-beep-20261114 of the repository, which git ignores); the proof of @t:affine_beep is only outlined; the last remark (more than two rows) was not checked. Nothing here is formalized in Lean. Please review]
// [AI-revised (claude-fable-5-2), 2026-11-14, after an independent read of the written section by a fresh agent: the statement of the theorem of CWYZ26 in the introduction of the section, the comparison of the bounds after @t:affine_main_0, the note that the definition of pretender does not ask c = c_1 + y c_2, the explicit example in the remark on the zero evader, the caveat on the first row in the paragraph on the relations, the remark on more than two rows (rewritten: what the composition needs), and small fixes of notation. Please review]
// [AI-revised (claude-fable-5-2), 2026-11-14, at the author's request (their two notes at the definition of the affine fold, and their decisions "Let's use this one" for sigma + tau X and "I think I prefer to do folds like this" for the weights): challenges are denoted alpha = sigma + tau X instead of y = alpha + beta X; two words are folded as lambda_1(alpha) u_1 + lambda_2(alpha) u_2 with the linear maps of Section 3, and the pairs of codewords that explain a fold are those of the set C_lambda defined in Section 5.1 (for the weights (1, alpha) it is the earlier C+ x C); Section 5.3 uses the weights (1 - alpha, alpha) of c:BEEP, so its relation is for that set and the check of Round 2 is h(0,0) + h(1,0) = mu. Edited: the paragraphs on affine folds and on pretenders, both definitions, the remark on the threshold, the proof of l:affine_line (its first lines, the two cases and the claim), the second step of the proof of t:affine_main, the remark on the zero evader, Section 5.3 except the three errors, and the last remark (its third item, and the weights of CWYZ26 in our notation). The author's two notes were removed, since the edit resolves them. Status: the statements for general weights follow from those for the weights (1, alpha) by a change of variables; this, the description of the set C_lambda and the formulas of Round 2 were checked with affine_weights_check.py and affine_weights_check2.py (same scratch folder). Later the same day, after the author asked why the messages of C_lambda in Section 5.3 are the pairs with equal last entries: the paragraph on the relations now derives this from the definition of the set (same set, no change of content). Then, at the author's request ("Place in a remark"), the two sentences on the coefficient of X^ell moved from that paragraph to the remark r:affine_degree; its second paragraph is new and answers the author's question on removing that coefficient from a witness. Then, at the author's request ("Let's add g = coeff(g) = coeff(...) = [current expression]. Use a similar formatting for h"): Round 2 shows h and the message of g as chains through coeff(...), with one sentence on the last equality; coeff is defined in the paragraph on the relations; the variables of h are Y_1, Y_2 instead of X, Y, since in this section X is the variable of the codewords (the author was told). Then, at the author's choice ("I would choose Option 1"): t:affine_beep is stated from R_{C^{equiv 2}}, as c:BEEP, with the relaxed relation R^{delta,+} defined in the paragraph on the relations (the witness is a pair of messages of C; f is close to their encoding up to a common coefficient of X^ell); the relation for C_lambda, its messages and the map shift are gone, and Round 2 pads with zeros instead; the remark r:affine_degree and three paragraphs of the proof outline were rewritten accordingly (the extractor removes the last entries). Same protocol and same errors; the formulas were checked with affine_option1_check.py (same scratch folder). Please review]
// [AI-revised (claude-fable-5-2), 2026-11-15, at the author's request ("Would it be possible to avoid describing the BEEP IOR with affine folding if we explain route 2 in broad terms, so that we obtain a result that concerns codewords from C^(equiv 2), and not from C_lambda^(equiv 2)? Ideally I would prefer to not spend more than one page on that"; then, on the draft, "Yes, the draft is good. Let's use that"): Section 5.3 is rewritten and takes one page. The fold has one more challenge xi, as in CWYZ26 Section 5 (weights 1 - (1 - xi) alpha and alpha), so the relaxed relation is the relaxation of R_{C^{equiv 2}} of Section 4, and t:affine_beep no longer has the relation "up to a common coefficient of X^ell" of the previous marker. Gone: the relation R^{delta,+}, the remark r:affine_degree, the list of modifications with the formulas of Round 2, and the remark on more than two rows (now two sentences). New in the statement: the term L_2/|F| of the first error, and L_2 is the list size of the interleaving of C+. Status: the proof is only outlined; its round-2 step was checked by brute force on toy sizes with affine_xi_check.py (.claude/scratch/affine-beep-20261114 of the repository, which git ignores; logs xi_check.log and xi_check2.log); nothing here is formalized in Lean. The previous text of this subsection is kept in that folder (sec53_option1_as_of_20261115.typ). Please review]
// [AI-revised (claude-fable-5-2), 2026-11-15, at the author's requests ("Ok, let's do Option 1, and let's have as well an IOR where P and V start with u_1 and u_2, V sends \xi, and they end up with two new words satisfying (H)"; then, on the result, "I would prefer to keep Theorem 5.4 and Lemma 5.8 without having this hypothesis, and then getting a corollary where we add the hypotehsis"; "Option 1" and "(H)" are from the chat of that day: for words that satisfy (H), pretenders can be defined with pairs of codewords of C in place of pairs of C_lambda). Sections 5.1 and 5.2, up to the remark on the zero evader, are as the author had them in commit 4c3dc3f (pretenders with respect to C_lambda, no hypothesis in t:affine_main and l:affine_line). New at the end of Section 5.2, under the paragraph heading "Overflowing pairs": Correlated Agreement with C up to one position; overflowing pairs (the pairs of C_lambda that are not pairs of codewords of C); d:no_overflow, which is (H): no overflowing pair agrees with the two words on (1 - delta) n - 1 positions; cor:affine_C (under (H), a codeword is a pretender if and only if it is one when C replaces C_lambda in d:affine_pretender, so t:affine_main holds with that definition), with its proof; and the remark r:affine_overflow (this fails without (H)). Section 5.3 is rewritten: the weights are again those of Section 4; new l:overflow, c:overflow (the verifier sends xi, the new words are f_1 and f_2 + xi f_1) and t:overflow, with the relation R_overflow; t:affine_beep is now for the fold without xi, its input relaxation is R^{delta + 1/n} union R_overflow, its first error no longer has the term L_2/|F|, and its proof outline uses cor:affine_C in Round 2; new cor:affine_beep for the two IORs together (the protocol and the errors of the previous t:affine_beep, with xi in a round of its own). Status: cor:affine_C (in the form: with C in the definition and under (H), a line has at most N pretenders) and l:overflow with the map of witnesses of t:overflow were checked by brute force over small fields (c2def_check.py and xi_lemma_check.py, with their logs, in .claude/scratch/affine-beep-20261114 of the repository, which git ignores); the proofs of cor:affine_C and t:overflow are complete; the proof of t:affine_beep is still an outline. t:affine_main and l:affine_line are the statements of the Lean file typst/lean/BEEP/AffineMain.lean; cor:affine_C is not formalized. By this date the author had rewritten by hand the introduction of the section and parts of Section 5.1, so the markers above no longer describe those parts. Please review]
// [AI-revised (claude-fable-5-2), 2026-11-15, at the author's request, after a review of the author's own edits of Sections 5.1 and 5.2 in commit a1208d1 ("For issue 1, let's use option 1. Issues 2: please fix. Issues 3: fix 933 and 939. Minor: fix 806, the issue with z bold non bold, 863, 887-888, 900, 904, 907, 917, 941, 943"; the numbers are lines of that commit). Changed: d:affine_pretender and the sentence before it ask again for Correlated Agreement with C_lambda (the author had put C, for which t:affine_main_0 and l:few_bad_points_on_line_0 do not hold). In the proof of l:few_bad_points_on_line_0: the set V is a translate of a linear subspace W (the map theta is affine, not linear); the three codewords are theta(0), theta(1) - theta(0) and theta(X) - theta(0); F_1 and F_2 are shown to be in C+; the argument for |S_alpha cap D| >= 2 is replaced by a direct one; the claim on common elements no longer starts "to the contrary"; a_1 is restored in the determinant; "degree at most one"; the set of the double counting is called E and is written with subsets of S_alpha cap D. In the proof of t:affine_main_0: the vanishing step says that phi_z is multiplicative; three sentences on the line through two tuples (its G is a rational function); the sentence on the roots of U; |F|^2. Small fixes: "for all alpha" in the description of C_lambda, "parameterized line", a doubled equality sign, the reference to the affine lemma, punctuation. The vector of samples z is bold everywhere in Section 5, including the paragraph on overflowing pairs and Section 5.3. Nothing else of the author's text was changed. The statements of t:affine_main_0 and l:few_bad_points_on_line_0 are again those of typst/lean/BEEP/AffineMain.lean. Please review]
// [AI-revised (claude-fable-5-2), 2026-11-15, at the author's request ("I think I don't want to do Section 5.3 and all the stuff about overflowing pairs. I want to basically provide an alternative to the affine paper. The affine paper does not really work out a PCS using affine folding, so I don't want to get into it either. Let's just add an explanation at the beginning of Section 5 and say we just prividing an alternative to the affine work. We can briefly mention how to make sure that in a wider protocol an extractor outputs pairs from C^(equiv 2) instead of Cpairs, refering to the corresponding section of the affine paper"). Removed: Section 5.3 (the BEEP IOR with an affine fold: l:overflow, c:overflow, t:overflow, t:affine_beep, cor:affine_beep) and the paragraph "Overflowing pairs" at the end of Section 5.2 (d:no_overflow, cor:affine_C, r:affine_overflow). So the section is now its introduction, Section 5.1 and Section 5.2, and the markers above describe text that is gone wherever they speak of these results. The removed text is kept in .claude/scratch/affine-beep-20261114/sec5_removed_20261115.typ of the repository, which git ignores. In the introduction of the section: "Sections 3 and 4" is now "Section 3"; the sentence of the author on the error kappa_2 of c:BEEP, which rested on Section 5.3, is replaced by one on the fraction of DEEP-MCA-bad challenges (theorem against theorem); two new paragraphs (the section only provides an alternative to the result of CWYZ26 and describes no IOR and no PCS, as CWYZ26 describes no PCS; an extractor obtains a pair from C_lambda, with a pointer to the new remark). New remark r:affine_pairs at the end of Section 5.2: why an extractor obtains a pair from C_lambda and not from C^{equiv 2}, and the additional challenge xi of CWYZ26, Section 5 ("Equal degree bounds", Theorem 5.1 there, read in the PDF dated November 11, 2026), stated for our weights. Status: the claim of the remark (a pair of codewords of C+ outside C x C gives a pair of C_lambda for at most one xi, for the words u_1, u_2 + xi u_1 if d_2 != 0 and u_1 + xi u_2, u_2 if d_1 != 0) has a two-line proof and was checked by brute force over small fields for five pairs of weights (xi_general_check.py and its log, in the same scratch folder); it is not formalized in Lean. Nothing else of the author's text was changed. Then, at the author's request ("Maybe let's not mention extractor, since we haven't described a protocol?"): the last paragraph of the introduction and the remark r:affine_pairs (now titled "Correlated Agreement with C^{equiv 2} instead of C_lambda") no longer speak of an extractor, a verifier or a wider protocol; they say the same in terms of Correlated Agreement (a codeword that agrees with a fold and is not a pretender gives a pair from C_lambda), and the additional challenge xi is "sampled". Later that day the author rewrote the remark by hand (its first two paragraphs are theirs, with the verifier and an IOR again) and asked: "In the last paragraph, isn't there an order problem? We say that there's few words in Cpair that are close to the new words, but these words depend on xi, no? Can you clarify a bit the paragraph?". The last paragraph is rewritten as three short ones: the set Lambda of the pairs of codewords of C+ close to the original words, which does not depend on xi, comes first; the pairs close to the new words are its images; each pair of Lambda outside C^{equiv 2} gives a pair of C_lambda for at most one xi (with the equation on the coefficients of X^ell); so at most |Lambda| values of xi are excluded. In it: the clause "and d_1 c_1 + d_2 c_2 in C" of the author's version is gone (the pair is any pair of codewords of C+); the assumption d_2 != 0, which the author's version had dropped and the claim needs, is stated where it is used; |Lambda| <= L_2 for the list size of the interleaving of C+ at delta + 1/n. Also restored: the closing bracket of the aiedit block after the remark (the file did not compile). In the author's second paragraph only the place of the primes changed (u'_1, u'_2 in place of u_1', u_2', which Typst renders with the prime on the subscript). Please review]

#aiedit[
#let Cplus = $cal(C)^+$
#let chal = $FF^(sans("lin"))[X]$
#let RS(e) = $sans("RS")_(#e)$
#let ratlines = $cal(L)^(1)[chal arrow FF(X)]$
#let emul = $dot.o$
#let Cpair = $cal(C)_lambda^(equiv 2)$

In the context of Reed-Solomon codes, in @CWYZ26, the authors propose, instead of sampling folding challenges $alpha$ in $FF$, to sample them on the set of linear polynomials $chal$, so that $alpha=alpha(X)= sigma + tau dot X$ for some random $sigma, tau in FF$.  sampling folding challenges of the form $alpha$. As shown in @CWYZ26, doing so results in a folding error term of $4\/|FF| + blockclength\/|F|^2$ instead of the usual $O(sans("poly")(blockclength)\/|F|)$. #albert[Mention Polygero?]

In this section we adapt the results from Section @s:better_pretenders to the same setting as @CWYZ26, i.e. we sample folding challenges $alpha$ in $chal$ instead of in $FF$. As a result, for most samples, the fraction of folding challenges that are DEEP-MCA-bad goes from $(delta dot blockclength + 1)\/|FF|$ (@t:main_thm) to about $1\/|FF|$ (@t:affine_main_0). In practical terms this can, for example, reduce the amount of grinding required, if any, in @c:BEEP and @c:BEEP_codeswitch..
Our proofs are elementary and essentially only require tweaking the definitions and adapting @l:few_bad_points_on_line to this new setting. This contrasts with the technical complexity in @CWYZ26. We emphasize that these technique apply specifically to Reed-Solomon codes, and not to any linear codes as those of Sections @s:better_pretenders and @s:BEEP_fold.

We stress that in this section we only provide an alternative to the result of @CWYZ26, i.e. a bound on the number of bad challenges of an affine fold, which in our case relies on out of domain samples (@t:affine_main_0). As in @CWYZ26, we do not describe a PCS that uses affine folds. In particular, we do not adapt the IORs of Section @s:BEEP_fold to this setting.

We only mention one point to keep in mind when using @t:affine_main_0. As we explain below, for affine folds we consider Correlated Agreement with a set of pairs of codewords $Cpair$, which is slightly larger than the interleaved code $interleavedcode(2)$ of the Reed-Solomon code $cal(C)$ at hand. In @r:affine_pairs we briefly explain how to obtain Correlated Agreement with $interleavedcode(2)$ instead, following @CWYZ26[Section 5].

== Affine pretender codewords and consistency


Fix $blockclength$ distinct elements $x_1, dots, x_blockclength in FF$. For an integer $e$ with $1 ≤ e ≤ blockclength$, we let $RS(e) subset FF^blockclength$ be the Reed-Solomon code of dimension $e$ with evaluation domain ${x_1, dots, x_blockclength}$, i.e.
$
RS(e) := {(p(x_1), dots, p(x_blockclength)) | p in FF[X], thick deg(p) < e}.
$
We identify each codeword of $RS(e)$ with its polynomial of degree less than $e$. This way, given a codeword $c$ and $x in FF$, we write $c(x)$ for the value of this polynomial at $x$.

We fix a code dimension $codedim ≥ 1$ and we let
$
cal(C) := RS(codedim), quad quad Cplus := RS(codedim + 1).
$
Given a polynomial $p in FF[X]$ and a word $u in FF^blockclength$, we write $p dot u$ for the word
$
(p(x_1) dot u_1, dots, p(x_blockclength) dot u_blockclength) in FF^blockclength
$<e:poly_times_word>



 Let $chal := {sigma + tau dot X | sigma, tau in FF} subset FF[X]$ be the set of linear polynomials on $FF$. As in Section @s:better_pretenders, fix two linear maps #albert[Replace $lambda$ by another symbol everywhere] $lambda_i (Y):= a_i + d_i dot Y$, $i=1,2$, with, as in @s:better_pretenders $a_1 dot d_2 != a_2 dot d_1$. Looking ahead, given two words $u_1, u_2in FF^blockclength$ and a folding challenge $alpha in chal$, the $alpha$-fold of $u_1, u_2$ is the word (recall our notation convention from @e:poly_times_word)
$
lambda_1(alpha) dot u_1 + lambda_2(alpha) dot u_2 in FF^blockclength.
$
Note that  if $c_1, c_2 in cal(C)$, then the folded word $lambda_1(alpha) dot c_1 + lambda_2(alpha) dot c_2$ belongs to $Cplus$ for all $alpha in chal$. We are interested in pairs of codewords $c_1, c_2 in Cplus$ whose fold belongs to $Cplus$ for all $alpha in chal$ #albert[Explain why. Overall, I need a good intutive explanation of the role of the degree differences in the affine fold]. These are precisely those in
$
Cpair := {(c_1, c_2) in Cplus times Cplus | d_1 dot c_1 + d_2 dot c_2 in cal(C)}.
$

\
\
Let $u_1, u_2 in FF^blockclength$ be two words and let $delta in (0,1)$. Given $S subset [blockclength]$, we say that $(u_1, u_2)$ has #emph[Correlated Agreement with $Cpair$ over $S$ up to one position] if there exist a pair $(c_1, c_2) in Cpair$ and a set $S' subset S$ with $|S'| ≥ |S| - 1$ such that $u_1$ agrees with $c_1$ on $S'$ and $u_2$ agrees with $c_2$ on $S'$.

#definition[Pretender codeword][
  Let $u_1, u_2 in FF^blockclength$ be two words and let $alpha in chal$. We say that a codeword $c in Cplus$ is an #emph[$alpha$-pretender] (with respect to $u_1, u_2$) if $lambda_1(alpha) dot u_1 + lambda_2(alpha) dot u_2$ and $c$ agree on a set $S subset [blockclength]$ of size $|S| ≥ (1-delta) dot blockclength$ such that $(u_1, u_2)$ does not have Correlated Agreement with $Cpair$ over $S$ up to one position. We say that $alpha$ is #emph[MCA-bad] (with respect to $u_1, u_2$) if there exists an $alpha$-pretender.
]<d:affine_pretender>



#let evalmap = $vb(phi)$
#let samples = $vb(z)$

\
Let $numsamples≥ 1$ be a parameter. Given $samples=(z_1, dots, z_numsamples) in FF^numsamples$, let $evalmap_vb(z): FF[X] -> FF^numsamples$ consist on evaluating a polynomial at the entries of $samples$, i.e.
$
evalmap_samples (p) := (p(z_1), dots, p(z_numsamples)) in FF^numsamples.
$
This will be our zero evader, and is precisely the univariate evader from Section @s:zero_evaders  applied to the coefficients of $p$. 

Given $vb(b), vb(b)' in FF^numsamples$ we write $vb(b) emul vb(b)' in FF^numsamples$ for their entrywise product. Notice that for any two $p,p' in FF[X]$ we have $evalmap_samples (p dot p') = evalmap_vb(z) (p) emul evalmap_vb(z) (p')$.

#definition[Consistency of MCA-bad elements $alpha in chal$ with $samples in FF^numsamples$][
  Let $alpha in chal$ and $c in Cplus$. Given $vb(z) in FF^numsamples$ and $vb(b)_1, vb(b)_2 in FF^numsamples$, we say that $(alpha, c)$ is _consistent_ with $(vb(z), vb(b)_1, vb(b)_2)$ if
  $
    evalmap_vb(z) (c) = evalmap_vb(z) (lambda_1(alpha)) emul vb(b)_1 + evalmap_vb(z) (lambda_2(alpha)) emul vb(b)_2.
  $
  When $alpha$ is MCA-bad and there exists an $alpha$-pretender $c in Cplus$ such that $(alpha, c)$ is consistent with $(vb(z), vb(b)_1, vb(b)_2)$, we say that $alpha$ is a _DEEP-MCA-bad challenge_ with respect to $vb(z), vb(b)_1, vb(b)_2$ and $u_1, u_2$.
]<d:affine_consistency>

For intuition, for an honest prover $vb(b)_1, vb(b)_2$ will be the values $evalmap_vb(z) (c_1), evalmap_vb(z) (c_2)$, where $(c_1, c_2) in interleavedcode(2)$  are $delta$-close to $u_1$ and $u_2$. 


== The affine version of @t:main_thm

#theorem[For most $vb(z) in FF^numsamples$, there are few DEEP-MCA-bad challenges $alpha in chal$][
  Let $delta in (0,1)$ and let $L$ be such that $Cplus$ is $(delta, L)$-list decodable. Let $u_1, u_2 in FF^blockclength$ be two words.

  For each $vb(z) in FF^numsamples$ and $vb(b)_1, vb(b)_2 in FF^numsamples$, let $A_(vb(z), vb(b)_1, vb(b)_2) subset chal$ be the set of DEEP-MCA-bad challenges with respect to $vb(z), vb(b)_1, vb(b)_2, u_1, u_2$. Let $vb(b)_1^*, vb(b)_2^*$ be such that $|A_(vb(z), vb(b)_1^*, vb(b)_2^*)|$ is maximal for fixed $vb(z), u_1, u_2$, and denote $A_vb(z) := A_(vb(z), vb(b)_1^*, vb(b)_2^*)$. Let
  $
    N := max lr(( |FF|, thick ((delta dot blockclength + 2) dot (delta dot blockclength + 1)) / 2 )).
  $
  Then for any integer $t ≥ N + 1$,
  $
    Pr_(vb(z) <- FF^numsamples)[ abs(A_vb(z)) ≥ t] ≤ ((|FF|^2 dot L)^3 dot ((codedim + 1) \/ |FF|)^numsamples) / (t dot (t-1) dot (t - N)).
  $<e:affine_bound_0>
]<t:affine_main_0>

Assuming $N=|FF|$ and taking $t =2N$ we obtain 
 $
    Pr_(vb(z) <- FF^numsamples)[ abs(A_vb(z)) ≥ t] ≤ frac((|FF| dot L)^3,3)dot lr(( frac(codedim+1,|FF|) ))^numsamples
  $
We proceed to prove @t:affine_main_0. The proof is almost a word-by-word adaptation of that of @t:main_thm to the new definitions introduced above. The main difference is in @l:few_bad_points_on_line, which states that a parameterized line contains few pretenders. When using affine folds, we obtain an analogous lemma whose proof is a generalization of that of @l:few_bad_points_on_line.

 We start with a new definition of parameterized lines. Below, $FF(X)$ denotes the set of all rational functions over $FF$, on the variable $X$.

#definition[Parameterized lines for the affine fold][
  We let $ratlines$ be the set of all maps $lmap: chal arrow FF(X)$ of the form $lmap(alpha) = F_lmap + alpha dot G_lmap$ for some $F_lmap, G_lmap in FF(X)$. Given $lmap in ratlines$, we let $im(lmap) = {(alpha, lmap(alpha)) | alpha in chal} subset chal times FF(X)$, and we call $im(lmap)$ a #emph[parameterized line].
]


#lemma[A parameterized line contains few pretenders, for the affine fold; analogue of @l:few_bad_points_on_line][
  Let $u_1,u_2 in FF^blockclength$ be two words, and let $lmap in ratlines$. Let $A_(lmap)^(sans("pret")) subset chal$ be the set of all  $alpha in chal$ such that $lmap(alpha) in Cplus$ and $lmap(alpha)$ is an $alpha$-pretender with respect to $u_1,u_2$. Then
  $
    |A_(lmap)^(sans("pret"))| ≤ max lr(( |FF|, thick ((delta dot blockclength + 2) dot (delta dot blockclength + 1)) / 2 )) = N.
  $ 
]<l:few_bad_points_on_line_0>
#proof[
  As in the proof of @l:few_bad_points_on_line, since $a_1 dot d_2 != a_2 dot d_1$ there exist $F_1, F_2 in FF(X)$ such that $lmap(Y) = lambda_1(Y) dot F_1 + lambda_2(Y) dot F_2$ as polynomials on $Y$ (it suffices to solve the system of equations obtained by equating coefficients on both sides) #albert[update original lemma with this explanation].

  Let $V subset chal$ be the set of all  $alpha in chal$ such that $lmap(alpha) in Cplus$. Note that $chal$ is a linear space of dimension two over $FF$. Now, $lmap(dot)$ is an affine map from $chal$ to $FF(X)$, i.e. for any two $alpha, alpha_0 in chal$ we have $lmap(alpha) = lmap(alpha_0) + (alpha - alpha_0) dot G_lmap$. We claim that either $V = chal$ or $|V| ≤ |FF|$. If $V$ is empty there is nothing to prove, so assume that $V$ contains some $alpha_0$. Let $W subset chal$ be the set of all $beta in chal$ such that $beta dot G_lmap in Cplus$. Since $Cplus$ is an $FF$-vector space, $W$ is an $FF$-vector subspace of $chal$, of $FF$-dimension $0,1$, or $2$. Now, since $lmap(alpha_0) in Cplus$, an element $alpha in chal$ belongs to $V$ if and only if $(alpha - alpha_0) dot G_lmap in Cplus$, i.e. if and only if $alpha - alpha_0 in W$. It follows that $V = {alpha_0 + beta | beta in W}$, and so $|V| = |W|$. Hence either $W$ has dimension at most $1$ and $|V| ≤ |FF|$, or $W = chal$ and then $V = chal$.

  By definition $A_lmap^(sans("pret")) subset V$. Hence if $V != chal$, we have $|A_lmap^(sans("pret"))| ≤ |FF|$ and we are done. 
  
  Hence assume $V=chal$. We claim that  $(F_1, F_2) in Cpair$. Indeed, since $V=chal$, we have $(theta(0), theta(1) - theta(0), theta(X) - theta(0)) = (F_lmap, G_lmap, X dot G_lmap) in Cplus^3$, meaning $F_lmap in Cplus$ and $G_lmap in cal(C)$.  We know that the following equality of polynomials holds
  $
  lmap(Y) = lambda_1(Y) dot F_1 + lambda_2(Y) dot F_2 = (a_1 dot F_1+ a_2 dot F_2) +  (d_1 dot F_1 + d_2 dot F_2) dot Y
  = F_lmap + Y dot G_lmap 
  $
  and so $a_1 dot F_1 + a_2 dot F_2 = F_lmap in Cplus$ and $d_1 dot F_1 + d_2 dot F_2 = G_lmap in cal(C)$. Since $a_1 dot d_2 != a_2 dot d_1$, solving this system we obtain that $F_1$ and $F_2$ are linear combinations of $F_lmap$ and $G_lmap$ with coefficients in $FF$, and so $F_1, F_2 in Cplus$. Hence  $(F_1, F_2) in Cpair$, as claimed.
  
  Similarly as in @l:few_bad_points_on_line, define $
    D := {i in [blockclength] | u_1(i) != F_1(x_i) " or " u_2(i) != F_2(x_i)} subset [blockclength].
  $
  \
  Looking ahead, from here on the proof is analogous to that of @l:few_bad_points_on_line, except that the sets $S_alpha inter D$ (for $alpha in A_lmap^(sans("pret"))$) contain at least $2$ elements instead of $1$, and, for $alpha != alpha'$, these sets pairwise intersect on at most one element, instead of being pairwise disjoint.
  
  Let $alpha in A_lmap^(sans("pret"))$. Since $lmap(alpha)$ is an $alpha$-pretender, there is a set $S_alpha subset [blockclength]$ where $lmap(alpha)$ and $lambda_1(alpha) dot u_1 + lambda_2(alpha) dot u_2$ agree, with $|S_alpha| ≥ (1-delta) dot blockclength$ and such that $(u_1, u_2)$ does not have Correlated Agreement with $Cpair$ over $S_alpha$ up to one position. We argue that $|S_alpha inter D| ≥ 2$. Indeed, assume towards contradiction that $|S_alpha inter D| ≤ 1$, and let $S_alpha ' := S_alpha \\ D$. Then $S_alpha ' subset S_alpha$ is a set of size $≥ |S_alpha| -1$ over which $u_1,u_2$ agree with $F_1, F_2$, respectively (by definition of $D$). Since $(F_1, F_2) in Cpair$, this means that $(u_1, u_2)$ has Correlated Agreement with $Cpair$ over $S_alpha$ up to one position, a contradiction. Hence $|S_alpha inter D| ≥ 2$ for all $alpha in A_lmap^(sans("pret"))$.

  We now claim that for every two distinct  $alpha, alpha' in A_lmap^(sans("pret"))$ the set $(S_alpha inter D) inter (S_(alpha') inter D)$ has at most one element. Indeed, let $i in [blockclength]$ be an element of such set. Then #albert[Isn't it weird how $u_i$'s are indexed with $[blockclength]$?]
  $
    lambda_1(alpha(x_i)) dot u_1(i) + lambda_2(alpha(x_i)) dot u_2(i) =   lambda_1(alpha(x_i)) dot F_1(x_i) + lambda_2(alpha(x_i)) dot F_2(x_i),
  $
  and similarly for $alpha'$. Since $i in D$, the vector $(u_1(i) - F_1(x_i), u_2(i) - F_2(x_i))$ is nonzero, and so the vectors $(lambda_1(alpha(x_i)), lambda_2(alpha(x_i)))$ and $(lambda_1(alpha'(x_i)), lambda_2(alpha'(x_i)))$ are linearly dependent. Hence the determinant of $((a_1 + alpha(X) dot d_1, a_2 + alpha(X) dot d_2), (a_1 + alpha'(X) dot d_1, a_2 + alpha'(X) dot d_2))$ vanishes at $x_i$.  This determinant equals $(alpha(X)-alpha'(X)) dot (a_2 dot d_1 - d_2 dot a_1)$. Since we assumed $a_2 dot d_1 != d_2 dot a_1$, we have $alpha(x_i) = alpha'(x_i)$. Since $alpha!= alpha'$ are polynomials of degree at most one, there is at most one $i in D$ satisfying  $alpha(x_i) = alpha'(x_i)$.  This proves the claim.

  
  Because of the claim, every subset of $D$ with two elements is contained in $S_alpha$ for at most one $alpha in A_lmap^(sans("pret"))$. By the same argument as in the proof of @l:few_bad_points_on_line we have $|S_alpha inter D| ≥ |D| - delta dot blockclength$. Let $s := max(2, |D| - delta dot blockclength)$ so that $|S_alpha inter D|≥ s$ for all $alpha in A_lmap^(sans("pret"))$. Now,  double counting the set $E= {(alpha, {i,j}) | alpha in A_lmap^(sans("pret")),  {i,j} subset S_alpha inter D, thick i!=j}$,
  $
   |A_lmap^(sans("pret"))| dot (s dot (s-1)) / 2 ≤ |E| ≤  (|D| dot (|D| - 1)) / 2
  $
  If $|D| ≤ delta dot blockclength + 2$ then $s = 2$ and we are done. Otherwise $s = |D| - delta dot blockclength$ and
  $
    |A_lmap^(sans("pret"))| ≤ frac(|D|, |D| - delta dot blockclength) dot frac(|D| - 1, |D| - delta dot blockclength - 1) < frac(delta dot blockclength + 2, 2) dot (delta dot blockclength + 1),
  $
  completing the proof.
]
Equipped with @l:few_bad_points_on_line_0, we now prove @t:affine_main_0 by adapting word by word the proof of @t:main_thm to the affine folding setting.

\
#proof[Proof of @t:affine_main_0, outline][
  We follow the proof of @t:main_thm, instantiated with $cal(C)$ a Reed-Solomon code, taking challenges $alpha in chal$ instead of in $FF$, and using the parameterized lines $ratlines$ instead of $linfuns$. We go through such proof and explain in what ways it is the same as that of @t:main_thm and, when it is not, we explain how to modify the proof to our setting.
  
  First, let $(alpha_i, v_i)_(i in [3]) in (chal times Cplus)^3$ with $alpha_1, alpha_2, alpha_3$ pairwise distinct, and let
  $
    U((alpha_i, v_i)_(i in [3])) := (alpha_3 - alpha_1) dot (v_2 - v_1) - (alpha_2 - alpha_1) dot (v_3 - v_1).
  $
   $U((alpha_i, v_i)_(i in [3]))$ is a polynomial of degree at most $codedim + 1$ (unlike in @t:main_thm where it would have degree $≤ codedim$). The analogue of @l:colinear holds: $(alpha_i, v_i)_(i in [3])$ belongs to the same parameterized line from $ratlines$ if and only if $U((alpha_i, v_i)_(i in [3])) = 0$ as a polynomial. The proof goes through exactly as in @l:colinear #albert[Double check],  where now operations take place in $FF(X)$ rather than in $FF$.

  The analogue of @l:colinear_zero holds as well. Concretely,  let $vb(z) in FF^numsamples$ and assume that $(alpha_i, v_i)$ is consistent with $(vb(z), vb(b)_1, vb(b)_2)$ for all $i in [3]$. Then we claim that
  $
    evalmap_vb(z) (U((alpha_i, v_i)_(i in [3]))) = vb(0).
  $
  Indeed, following the proof of @l:colinear_zero, let $vb(b)' := d_1 dot vb(b)_1 + d_2 dot vb(b)_2$. By the consistency assumption, $evalmap_vb(z) (v_i) - evalmap_vb(z) (v_1) = (evalmap_vb(z) (alpha_i) - evalmap_vb(z) (alpha_1)) emul vb(b)'$ for both $i = 2, 3$. Now the proof follows as in @l:colinear_zero, using the definition of $U((alpha_i, v_i)_(i in [3]))$ and that $evalmap_vb(z)$ is linear and multiplicative, so that for example $evalmap_vb(z) ((alpha_3 - alpha_1) dot (v_2 - v_1)) = (evalmap_vb(z) (alpha_3) - evalmap_vb(z) (alpha_1)) emul (evalmap_vb(z) (v_2) - evalmap_vb(z) (v_1))$ #albert[check].

  Next, let $T_vb(z)$ be defined in the exact same way as in Section @s:better_pretenders, using  triples of tuples from $chal times Cplus$ instead of $FF times cal(C)$, and, of course, using the affine versions of the definitions of $alpha$-pretenders and consistency. Then the same proof as that of  @l:third_moment_bound yields
  $
    |A_vb(z)| dot (|A_vb(z)| - 1) dot (|A_vb(z)| - N) ≤ |T_vb(z)|.
  $
  It suffices to use @l:few_bad_points_on_line_0 with the bound $|A_lmap^(sans("pret"))|≤ N$ instead of the bound $|A_lmap^(sans("pret"))|≤ delta dot blockclength +1$ given by @l:few_bad_points_on_line. The other difference is in the claim that any two tuples $(alpha, v), (alpha', v') in chal times Cplus$ with $alpha != alpha'$ belong to exactly one parameterized line. Here this is the line with $G_lmap = (v - v') \/ (alpha - alpha')$ and $F_lmap = v - alpha dot G_lmap$, and $G_lmap$ is in general a rational function, not a codeword. This is why the parameterized lines of $ratlines$ have coefficients in $FF(X)$, and why @l:few_bad_points_on_line_0 only counts the challenges $alpha$ such that $lmap(alpha) in Cplus$.
  
  Finally, let $P subset chal times Cplus$ be the set of all tuples $(alpha, c)$ such that $c$ is an $alpha$-pretender. Since $Cplus$ is $(delta, L)$-list decodable, $|P| ≤ |chal| dot L = |FF|^2 dot L$. Let $(alpha_i, c_i)_(i in [3]) in P^3$ be such that $U((alpha_i, c_i)_(i in [3])) != 0$. This is a nonzero polynomial of degree at most $codedim + 1$. If the triple belongs to $T_vb(z)$ then, by definition of $T_vb(z)$ and the analogue of @l:colinear_zero above, this polynomial vanishes at all the entries of $vb(z)$. Hence there are at most $((codedim + 1) \/ |FF|)^numsamples dot |FF|^numsamples$ elements $vb(z) in FF^numsamples$ such that the triple belongs to $T_vb(z)$. Using an argument similar to the proof of @t:main_thm,  and using $|chal| = |FF|^2$, we have
  $
    sum_(vb(z) in FF^numsamples) |T_vb(z)| ≤ (|FF|^2 dot L)^3 dot ((codedim + 1) \/ |FF|)^numsamples dot |FF|^numsamples.
  $
  Now the theorem follows as in @t:main_thm #albert[check].
]


#remark[On the choice of the zero evader][
  In @t:affine_main_0 the samples are evaluations at points of $FF$, and we used that $evalmap_vb(z)$ is multiplicative. This is why the prover only needs to provide two vectors $vb(b)_1, vb(b)_2$, and why three consistent tuples make the polynomial $U$ vanish at $vb(z)$.

  With a general zero evader (for example, the multilinear evader) the prover would need to provide a third vector $vb(b)_3$, supposedly the image of $X dot (d_1 dot c_1 + d_2 dot c_2)$, and $(alpha, c)$ would be consistent if $evalmap_vb(z) (c) = lambda_1(sigma) dot vb(b)_1 + lambda_2(sigma) dot vb(b)_2 + tau dot vb(b)_3$, where $alpha = sigma + tau dot X$. In that case there can be about $2 dot |FF|$ challenges with a consistent pretender, for every $vb(z)$.

  For example, take the weights $(1, alpha)$. Let $u_1 = 0$, and let $u_2$ agree with a polynomial $q$ of degree exactly $codedim$ on a set $S_A subset [blockclength]$, and with $p \/ (X - x_0)$ on a set $S_B subset [blockclength]$. Here $p$ is a polynomial of degree at most $codedim$, and $x_0 in FF$ is such that $p(x_0) != 0$ and $x_0 != x_i$ for all $i in S_B$. Assume that both sets have at least $(1 - delta) dot blockclength$ positions, and that $(1 - delta) dot blockclength ≥ codedim + 2$ (such words exist when $2 dot (1 - delta) dot blockclength ≤ blockclength + codedim + 1$). Then, for all $sigma, tau in FF$, the challenges $sigma$ and $tau dot (X - x_0)$ have the pretenders $sigma dot q$ and $tau dot p$, respectively. All these pretenders are consistent with $vb(b)_1 = vb(0)$, $vb(b)_2 = evalmap_vb(z) (q)$ and $vb(b)_3 = evalmap_vb(z) (p) + x_0 dot evalmap_vb(z) (q)$.

  It is unclear to us whether one can obtain a result like @t:affine_main_0 in that setting with a similar number of samples.
]

#remark[Correlated Agreement with $interleavedcode(2)$ instead of $Cpair$][
  In @d:affine_pretender we ask for Correlated Agreement with $Cpair$, and not with $interleavedcode(2)$, i.e. with pairs of codewords of $cal(C)$ as in Section @s:better_pretenders. The set $Cpair$ strictly contains $interleavedcode(2)$, and so, when a codeword $c in Cplus$ agrees with the $alpha$-fold of two words $u_1, u_2$ on a subset of $[blockclength]$ of size at least $(1-delta) dot blockclength$ positions, and $c$ is not an $alpha$-pretender, we obtain a pair from $Cpair$ that is close to $(u_1, u_2)$, and this pair need not belong to $interleavedcode(2)$. Here and below, we say that a pair of codewords $(c_1, c_2)$ is #emph[close] to a pair of words $(w_1, w_2)$ if there is a subset of $[blockclength]$ of size at least $(1-delta) dot blockclength - 1$  where $w_1$ agrees with $c_1$ and $w_2$ agrees with $c_2$.

  In a bigger protocol, for example when aiming to build an IOR from $cal(R)_(interleavedcode(2))$ to $cal(R)_cal(C)$ using affine folds, one would instead prefer to obtain a pair from $cal(R)_(interleavedcode(2))$ instead of $Cpair$. This can be ensured  using the methods described in @CWYZ26[Section 5]. To do so, one can have an initial communication round where the verifier samples an additional challenge $xi in FF$, and replaces the words $u_1$ and $u_2$ by $u'_1:=u_1$  and $u'_2=u_2 + xi dot u_1$, and then proceeds to perform the DEEP sampling and the affine folding with these two words instead of $u_1$ and $u_2$. One also performs analogous linear changes on the witness and any linear constraints place on the witness.

  The reason this works is the following. Let $Lambda$ be the set of all pairs of codewords of $Cplus$ that are close to the original words $(u_1, u_2)$. Note that $Lambda$ does not depend on $xi$, since $u_1, u_2$ are fixed before $xi$ is sampled. On the other hand, the pairs of codewords of $Cplus$ that are close to the new words $(u'_1, u'_2)$ do depend on $xi$: for each $xi in FF$, they are exactly the pairs $(c_1, c_2 + xi dot c_1)$ with $(c_1, c_2) in Lambda$. This is because $u_1, u_2$ agree with $c_1, c_2$ on a set if and only if $u'_1, u'_2$ agree with $c_1, c_2 + xi dot c_1$ on this set.

  Now let $(c_1, c_2) in Lambda$. If $(c_1, c_2)$ belongs to $interleavedcode(2)$, then so does $(c_1, c_2 + xi dot c_1)$, for all $xi in FF$. Otherwise, $(c_1, c_2 + xi dot c_1)$ belongs to $Cpair$ for at most one $xi in FF$. Indeed, let $s_1, s_2 in FF$ be the coefficients of $X^codedim$ of $c_1$ and $c_2$, which are not both zero. By definition of $Cpair$, the pair $(c_1, c_2 + xi dot c_1)$ belongs to $Cpair$ if and only if $d_1 dot s_1 + d_2 dot (s_2 + xi dot s_1) = 0$. Here we assume that $d_2 != 0$, as is the case for the weights $(1, alpha)$ and $(1-alpha, alpha)$. Then this equation has at most one solution $xi$ (if $s_1 = 0$ it has none, since $d_2 dot s_2 != 0$).

  Hence there are at most $|Lambda|$ elements $xi in FF$ for which some pair from $Cpair$ that is close to the new words does not belong to $interleavedcode(2)$. Note that $|Lambda| ≤ L_2$ if $(Cplus)^(equiv 2)$ is $(delta + 1\/blockclength, L_2)$-list decodable. For all the other $xi$, every pair $(c'_1, c'_2)$ from $Cpair$ that is close to $(u'_1, u'_2)$ belongs to $interleavedcode(2)$, and one obtains from it the pair $(c'_1, c'_2 - xi dot c'_1) in interleavedcode(2)$, which is close to $(u_1, u_2)$.
]<r:affine_pairs>
]


= Experiments <s:experiments>

// [AI-drafted in the author's register (claude-fable-5-2), 2026-11-13, at the author's request: this whole section, up to the include of batch.typ (the fold comparison, the three-way comparison of Ligerito variants, and the cost of the samples). Every number and every table row is read from tables/experiments.json, which scripts/make_tables.py writes: the fold comparison from 7-beep-ligerito/scripts/beep_params.py, the measurements from the run 7-beep-ligerito/bench_results/three-way-20261113. A number that the script did not write prints as a highlighted "pending". The code is 7-beep-ligerito/flock (Flock's affine branch, with crates/flock-core/src/pcs/ligerito/beep.rs added). Research, unaudited. Please review]
// [AI-revised (claude-fable-5-2), 2026-11-13, at the author's request and after an independent review of the first draft: the run is now 7-beep-ligerito/bench_results/three-way-20261113b (BEEP-Ligerito samples its binding points in one message and grinds the batching of the queries for the list of the next code; the affine variant also runs at its least certified slack; proofs of work at the measured cost per search); the affine column of the fold table comes from a wider search for the parameters of [CWYZ26, Theorem 4.10]; new subsection "The parts of a proof" (Merkle leaves apart from inner paths, per level and per variant); a placeholder subsection for a code that is not known to have MCA up to the Johnson radius. Please review]
// [AI-revised (claude-fable-5-2), 2026-11-13, at the author's request ("expand table 4 with more results for smaller rates"): the run is now 7-beep-ligerito/bench_results/three-way-20261113c, with ten instances (rates 1/2 to 1/16); @tab:main, @tab:bytes_all and @tab:time have a group of rows per instance; at rates 1/8 and 1/16, for which Flock ships no configuration, Ligerito (Flock) runs on the configuration that Flock's code derives at that rate; new paragraph "Smaller rates" in the results; the paragraph on the check of the prover times of the affine variant follows what we found about it. Please review]
// [AI-revised (claude-fable-5-2), 2026-11-14, at the author's request (drop the out of domain sample on the first commitment; "run and record experiments" on short messages; "work heavily in optimizing the sampling step"; "research and implement" a proof of work whose threshold is not a power of two): the run is now 7-beep-ligerito/bench_results/three-way-20261113e, with thirteen instances (also 2^16 to 2^18 words); BEEP-Ligerito has no sample on its first commitment, its proofs of work have a threshold, and its prover makes one pass per fold round; the list of differences with the affine variant, the measurements, the limitations, the results and @s:exp_cost are rewritten for this (for long messages at rate 1/2 the prover of BEEP-Ligerito is no longer slower than that of the affine variant); new @tab:steps; the check of the prover times follows this run, with a footnote on the earlier runs. Please review]
// [AI-revised (claude-fable-5-2), 2026-11-14, at the author's request ("try to bring the affine version to a similar level of optimization as BEEP"; "remove the sample on the first commitment for the affine version [...] so as to match beep"): the run is now 7-beep-ligerito/bench_results/three-way-20261114g. The affine variant of the tables is no longer Flock's as it ships: it has no sample on its first commitment (the fold rounds of its first level are ground for the list of the code, an accounting of ours), and its prover is ours, with one pass per fold round, and writes the same proofs as Flock's. New paragraph "The affine variant as we run it" and new @tab:affine_steps (Flock's variant as it ships, and each change apart); @tab:time has the fold rounds of the affine prover; the limitations, the results on the prover and @s:exp_cost are rewritten for this (BEEP-Ligerito is now slower than the affine variant in every instance). Please review]
// [AI-revised (claude-fable-5-2), 2026-11-14, at the author's request ("Provide numbers for n=2^15 and rate 1/8 for table 4"): one more instance, a message of 2^15 words with a first level of rate 1/8, in @tab:main and in the other tables that have a group of rows per instance (fourteen instances). We read "n" as the number of words of the message. It was measured on its own with the program of the run 20261114g (7-beep-ligerito/bench_results/three-way-20261114g-add1). One sentence on its proof sizes in the results, and one on how it was measured. Please review]
// [AI-revised (claude-fable-5-2), 2026-11-14, at the author's request ("Let's now run experiments for 100 bits of security, same parameter regimes as for 128 bits of security"): new subsection @s:exp_100 with @tab:params100 and @tab:main100, from the run 7-beep-ligerito/bench_results/three-way-20261114h (Flock's profiles fast100 and slim100; the affine and BEEP ladders for a target of 100 bits). The machine was short of memory during that run: the times of its large instances are in parentheses and are to be measured again (a todo note says so); the sizes and the parameters are final. Please review]
// [AI-revised (claude-fable-5-2), 2026-11-15, for the same request: @s:exp_100 now reads the run 7-beep-ligerito/bench_results/three-way-100bits-3, made at night with the same cells, on a machine with less unused memory than for the run at 128 bits. All its times are used: the todo note and the parentheses of @tab:main100 are gone, the paragraphs on the measurements are rewritten (the processes with compressed memory, what this does to single proofs and why we use the medians, the check against the times with proofs of work, the two processes that were a few percent slow), and the results on the prover quote all fourteen instances. The proof sizes and the parameters did not change. After an independent check of this subsection against the raw results (no wrong number; wording and scope): which ladders are the same at the two targets, the sentence on the bound of DKT26, the samples (4 against 4 to 5 at 128 bits), and the saving in proof size by rate. The numbers that the text quotes as bounds ("within", "at most") are now rounded in the safe direction, which moves six numbers of @s:exp_ligerito by one unit. Please review]
#aiedit[
#let expdata = json("tables/experiments.json")
#let num(key) = if key in expdata.numbers { eval(expdata.numbers.at(key), mode: "markup") } else { highlight[pending] }
// `group`: a thin rule after every `group` rows (the rows of one instance in the long tables).
#let exprows(name, group: 0) = {
  let rows = expdata.tables.at(name, default: ())
  if rows.len() == 0 { (table.cell(colspan: 2, highlight[pending]),) } else {
    rows.enumerate().map(((i, r)) => {
      let cells = r.map(c => eval(c, mode: "markup"))
      if group > 0 and calc.rem(i + 1, group) == 0 and i + 1 < rows.len() { cells + (table.hline(stroke: 0.25pt),) } else { cells }
    }).flatten()
  }
}
#let exptable(columns, header, name, size: 9pt, group: 0, inset-y: 2.5pt) = text(size: size, table(
  columns: columns, stroke: none, align: center + horizon, inset: (x: 3.5pt, y: inset-y),
  table.hline(), ..header, table.hline(stroke: 0.4pt), ..exprows(name, group: group), table.hline(),
))

We report five experiments. In @s:exp_fold we compute the errors of the first two rounds of @c:BEEP for several codes and proximity parameters, and we compare them with the error of a fold in other analyses. In @s:exp_ligerito we measure a BEEP variant of Ligerito @ligerito against Ligerito itself and against a recent variant with "affine" folds. In @s:exp_bytes we split the proofs of these variants into the parts of the protocol. In @s:exp_cost we look at what the out of domain samples cost the prover in that implementation, at what we do to reduce this cost, and at the prover of the affine variant. In @s:exp_100 we repeat the comparison at $100$ bits of security.

Everything in this section is research code, and it is not audited. The code, the scripts and the raw outputs are in the folder `7-beep-ligerito` of our repository #albert[ref to repo], and every number below is written by a script from these outputs.

== The error of a fold <s:exp_fold>

#paragraph[Setting.] We look at one fold of two words, as in @c:BEEP, where $cal(C)$ is an interleaved Reed-Solomon code of rate $rho$ on $blockclength$ points, and $FF$ has $2^128$ elements. We take the proximity parameter slightly below the Johnson radius, i.e. $delta = 1 - sqrt(rho) - eta$ for a small "slack" $eta > 0$ (rounded so that $delta dot blockclength$ is an integer). By the Johnson bound, $cal(C)$ and its interleavings are then $(delta, L)$-list decodable with $L = floor(1 \/ (2 dot eta dot sqrt(rho)))$.

The codes that we consider are those of the levels of the Ligerito instances of @s:exp_ligerito. As zero evader we take $numsamples$ independent samples of the multilinear evader, i.e. the verifier samples $numsamples$ points and the prover answers with the multilinear extension of each message at these points. For messages with $2^mu$ entries its error is $epsilon_"evader" = (mu \/ |FF|)^numsamples$.

#paragraph[The two rounds.] @t:beep_soundness uses @t:main_thm with the threshold $t = delta dot blockclength + 2$. The same proof works with any integer $t >= delta dot blockclength + 2$, and then the errors of the first two rounds of @c:BEEP are
$
kappa_1(t) = ((|FF| dot L)^3 dot epsilon_"evader") / (t dot (t-1) dot (t - delta dot blockclength - 1)), quad quad kappa_2(t) = (t - 1 + 2 dot L) / (|FF|).
$
A larger threshold makes the first error smaller and the second one larger. Note that $t$ only appears in the analysis.

In what follows we count $g$ bits of proof of work ("grinding") on a challenge as $g$ bits of security, as it is usual in practice @whir @flock, and we ask that every round has $128$ bits. We choose $numsamples$ and $t$ as follows. For each $numsamples <= 8$ we take the least $t$ such that $kappa_1(t) <= 2^(-128)$, so that the first round needs no grinding. Among these we take the $numsamples$ that needs the least grinding in the second round, and the smallest such $numsamples$.

In our implementation (@s:exp_ligerito) the challenges of the second and third rounds of @c:BEEP are sampled together, right before the samples of the next fold. So the grinding that we report for the second round covers $kappa_2(t) + kappa_3$ and the first round of the next fold, i.e. an error of at most $(t + 3 dot L) \/ |FF|$.

#figure(
  exptable(12,
    (table.cell(colspan: 2)[code], [unique], [], [], table.cell(colspan: 2)[fold with MCA], [DEEP], [affine], table.cell(colspan: 3)[BEEP],
     [$blockclength$], [$rho$], [decoding], [$eta$], [$L$], [@BCHKS25], [@DKT26], [@BGKS19], [@CWYZ26], [$numsamples$], [round 1], [round 2]),
    "fold"),
  caption: [Bits of security (i.e. $-log_2$ of the error) of the fold of two words of an interleaved Reed-Solomon code of rate $rho$ on $blockclength$ points, over a field with $2^128$ elements, at the proximity parameter $delta = 1 - sqrt(rho) - eta$, before any grinding. "Unique decoding": the fold challenge in the unique decoding regime, i.e. at $delta$ about $(1-rho)\/2$ @BCHKS25[Corollary 1.4]. "Fold with MCA": the fold challenge, with the MCA bounds of @BCHKS25[Theorem 4.6] (in the form that Flock uses @flock[Appendix C.3]) and of @DKT26[Theorem 5.12]. "DEEP": the DEEP theorem of DEEP-FRI @BGKS19[Theorem 4.1], which bounds the sample and the fold challenge together, with one sample and a loss in $delta$ that we optimize. "Affine": a fold round of the affine fold, i.e. the bound of @CWYZ26[Theorem 4.10], with one coordinate of agreement loss, plus $2\/|FF|$ for the claims that the round carries, as in Flock's affine variant for a level whose commitment has an out of domain sample (see @s:exp_ligerito). The bound has parameters that we search for (see the text); "--" means that our search finds none. "BEEP": the number of samples $numsamples$ that we select, and the two rounds $kappa_1(t)$ and $kappa_2(t)$ of @c:BEEP at the threshold $t$ that we select. By `7-beep-ligerito/scripts/beep_params.py`, which also checks the BEEP columns in exact arithmetic.],
) <tab:fold>

#paragraph[What we see.] @tab:fold has the results. We go through its columns.

- *Folds with MCA.* The error grows quickly when $eta$ decreases. At $eta = 0.02$ the fold challenge has #num("fold:bchks:0.02") bits with the bound of @BCHKS25 and #num("fold:dkt:0.02") bits with that of @DKT26. At $eta = 0.001$ it has #num("fold:bchks:0.001") and #num("fold:dkt:0.001") bits. So over a field of this size one cannot reach $128$ bits at the Johnson radius with these bounds and a reasonable amount of grinding. This is why Flock samples its fold challenges from a larger field (see @s:exp_ligerito).

- *The DEEP theorem.* The theorem of @BGKS19 gives at most #num("fold:deepfri-max") bits here. Its error has a term of the form $L dot (ell\/|FF| + epsilon)^(1\/3)$ and a term $4\/(epsilon^2 dot |FF|)$, where $epsilon$ is a loss in the proximity parameter, and over a field with $2^128$ elements no choice of $epsilon$ makes both small.

- *Affine folds.* The bound of @CWYZ26[Theorem 4.10] depends on two integers, a multiplicity and a degree, which have to satisfy an inequality. So one has to search for them. We do this with the formulas of the script of Flock's affine variant, and we search further than this script does#footnote[The script is `scripts/affine_fold_params.py` of the branch of Flock that we describe in @s:exp_ligerito. It states the bound as in an earlier draft of @CWYZ26, with one more free parameter ($B$ in @CWYZ26[Section 4], which the published statement fixes), and it stops at multiplicity $40$. We go up to #num("fold:affine-max-m"), and we check every pair that we use with the function of the script. With $B$ as in @CWYZ26[Theorem 4.10] the bounds are #num("fold:affine-paper-loss") bits weaker. As it ships, the script finds parameters for #num("fold:affine-shipped:0.005") of the codes at $eta = 0.005$, and for #num("fold:affine-shipped:0.001") at $eta = 0.001$.]. Where the search succeeds, the affine fold has the smallest error of the table: #num("fold:affine:0.02") bits at $eta = 0.02$, in all the #num("fold:shapes") codes, so that #num("fold:affine-grind:0.02") bits of grinding suffice. (This is for a level whose commitment has an out of domain sample, as in Flock's variant. See @s:exp_ligerito for the first level as we run it.)

  For a smaller $eta$ the inequality needs a longer code. At $eta = 0.005$ the search finds parameters for #num("fold:affine-certified:0.005") of the codes. At $eta = 0.001$ it finds them for #num("fold:affine-certified:0.001"), those with #num("fold:affine-points:0.001") points, where the round has #num("fold:affine:0.001") bits. This is expected: the closed form of the bound, @CWYZ26[Theorem 1.1], asks for $blockclength dot eta^2 >= 4 \/ rho$, and the search does somewhat better than this.

- *BEEP.* The second round has #num("fold:beep-fold") bits, for every $eta$. This is within #num("fold:beep-vs-udr") bits of the error of a fold in the unique decoding regime (#num("fold:udr") bits), since both are about $delta dot blockclength \/ |FF|$. So BEEP needs #num("fold:beep-grind") bits of grinding in the second round. The first round reaches $128$ bits with #num("fold:beep-m") samples. With $numsamples = 3$ and the least threshold it has at most #num("fold:points3-max") bits, since then $epsilon_"evader"$ only cancels the factor $|FF|^3$ of $kappa_1$.

To sum up, over a field with $2^128$ elements the affine fold and BEEP are the two analyses that reach $128$ bits with a moderate amount of grinding. Where the affine fold has a bound, it needs less grinding than BEEP: #num("fold:affine-grind") bits, against #num("fold:beep-grind"). On the other hand, BEEP has the same bound for every code and every $eta$, while the affine fold needs $eta$ to be large enough for the block length.

A small $eta$ matters for the number of queries. For example, for a code of rate $1\/2$, and with $16$ bits of grinding on the queries, a level needs #num("ex:queries:0.02") queries at $eta = 0.02$ and #num("ex:queries:0.001") at $eta = 0.001$, against #num("ex:udr-queries") in the unique decoding regime. Recall also that @t:main_thm holds for any linear code, while the other columns of @tab:fold are specific to Reed-Solomon codes (see @s:exp_other_code).

#paragraph[Larger fields.] @tab:fields repeats the BEEP columns over larger fields, for two of the codes. Over a field with $2^192$ elements we select #num("fields:m:192") samples, and over one with $2^256$ elements #num("fields:m:256"), with a threshold of about $2^52$ to $2^57$. In both cases no round needs grinding.

#figure(
  exptable(9,
    ([$|FF|$], [$blockclength$], [$rho$], [$eta$], [$numsamples$], [$log_2 t$], [round 1], [round 2], [grinding]),
    "fields"),
  caption: [The first two rounds of @c:BEEP over fields of different sizes, as in @tab:fold: the number of samples and the threshold $t$ that we select for $128$ bits, the bits of $kappa_1(t)$ and $kappa_2(t)$, and the bits of grinding that the second round needs.],
) <tab:fields>

== BEEP-Ligerito, Ligerito and affine Ligerito <s:exp_ligerito>

#paragraph[The variants.] We start from the implementation of Ligerito in Flock @flock. At $128$ bits of security, Flock analyzes Ligerito at $eta = 0.02$ from the Johnson radius, with the MCA bound of @BCHKS25 for the folds. As we saw in @tab:fold, this bound is too weak over a field with $2^128$ elements. Because of this, Flock commits to words over $"GF"(2^128)$ but samples the fold challenges from $"GF"(2^256)$, and it then commits to each folded table as two tables over $"GF"(2^128)$. We call this variant "Ligerito (Flock)".

Flock's repository also has a variant with the affine folds of @CWYZ26, in which all the challenges are in $"GF"(2^128)$#footnote[Branch `affine-fold-f128` of #link("https://github.com/succinctlabs/flock"), commit `14b78c0`. Its design note follows a draft of @CWYZ26. It lists as open the bound for interleaved words with challenges in the base field, which @CWYZ26 now has (in the proof of its Theorem 5.2), and the round by round accounting of the agreement loss of the fold.]. We call it "affine Ligerito", or the affine variant. We run it with two changes of ours, which we describe below.

Our variant, "BEEP-Ligerito", is the affine variant with its fold round replaced by @c:BEEP. Before each fold challenge the verifier samples $numsamples$ points, and the prover answers with the multilinear extensions of the two halves of the current table at these points. The fold itself is the usual fold of a sumcheck round, with all the challenges in $"GF"(2^128)$. The rest of the protocol (the commitments, the out of domain samples after each new commitment, the queries and the batching of claims) is that of the affine variant, up to a few differences that we explain below. In other words, it is @c:BEEP_codeswitch applied recursively, for Reed-Solomon codes.

#paragraph[Parameters.] All the variants open the same commitment, and they follow the accounting of Flock @flock[Appendix C.3]: every challenge has error less than $2^(-128)$ after grinding, where grinding is counted as in @s:exp_fold, and the queries of every level have #num("params:qgrind") bits of grinding. Ligerito (Flock) runs with Flock's own configurations at $128$ bits (`fast` at rate $1\/2$ and `slim` at rate $1\/4$). Flock has no configuration for the rates #num("run:derived-rates"). For these we use the configuration that Flock's code derives for `slim` when it starts from the smaller rate, i.e. the rules of `slim` with another rate at the first level#footnote[The function `derive_profile_ladder` of Flock, to which we add the rate of the first level as an argument. With the rate of `slim` it returns the configuration of `slim`.]. The affine variant and BEEP-Ligerito run on the same "ladder", i.e. with the same number of levels and the same rates.

We run the affine variant with two choices of $eta$. The first is $eta = 0.02$ at every level, as in Flock. In the second, each level has the least $eta$ among #num("params:affine-slacks") for which the search of @s:exp_fold finds parameters for all the fold rounds of the level. This is #num("params:affine-small-first") at the first level, depending on the length of its code, and #num("params:affine-small-last") at the last one. For $2^16$ words it is #num("affine-small-etas:fast16") at the two levels, so there the two choices coincide. In both cases the grinding of the fold challenges is the one that these parameters give (at the first level, with the change that we explain below)#footnote[With the sample on the first commitment, at $eta = 0.02$ this is the output of Flock's script, and for $2^25$ words, and for $2^22$ words at rate $1\/4$, the ladder is one that Flock registers.].

We run BEEP-Ligerito with $eta = 0.02$ and with $eta = 0.001$, at every level. In both cases we choose $numsamples$ and the threshold of each level as in @s:exp_fold. @tab:params shows the parameters of all the variants for #num("params:cell") words.

BEEP-Ligerito differs from the affine variant in three more points.

- *The points that bind a commitment.* After each new commitment, Flock's variants sample the out of domain points that bind it one after the other, with a batching coefficient in between, and they account for them as points that are sampled together. It is unclear to us how to justify this round by round, so in BEEP-Ligerito the verifier samples these points in one message, as in @c:BEEP_codeswitch.

- *The batching of the queries.* For the challenge that batches the queries of a level we count the list size of the next code, as in the error $kappa'_3$ of @t:beep_codeswitch, which costs one more bit of grinding than Flock's rule.

- *Proofs of work with a threshold.* A proof of work of $g$ bits is a nonce whose hash starts with $g$ zero bits, and the prover tries $2^g$ hashes in expectation. A challenge with error $M \/ |FF|$ needs the least $g$ with $M < 2^g$, so the prover may try up to $2 dot M$ hashes. Flock's transcript also has proofs of work with a threshold: the nonce is valid if the first $64$ bits of its hash, seen as an integer, are below a threshold $T$. A nonce is then valid with probability $T \/ 2^64$, and we count such a proof of work as $log_2 (2^64 \/ T)$ bits. For a challenge with error $M \/ |FF|$ we take the largest $T$ with $M dot T < 2^64$, and the prover tries about $M$ hashes. In BEEP-Ligerito we do this for the fold challenges and for the challenges that batch claims and queries. The queries keep their #num("params:qgrind") bits.

The first two points change the size of a proof by a few bytes, and the last one does not change it. The other two variants grind as in Flock, with a whole number of bits. A threshold would not help them much: their proofs of work are mostly those of the queries, and it would save them at most #num("threshold-gain-max-pct:whole-bits")~% of the opening.

#paragraph[The first commitment.] Flock's variants also sample an out of domain point on the first commitment, i.e. on the input of the protocol. The committed word may only be close to the code, so up to $L$ codewords are candidates for the message. The answer to the sample is consistent with at most one of them, up to an error that is part of Flock's accounting. With it, the analysis of Flock's variants deals with one codeword in the fold rounds of the first level.

BEEP-Ligerito has no such sample to bind the first commitment. In @c:BEEP_codeswitch only the new commitments get one, and the errors of @t:beep_soundness already account for all the codewords of the list (these are the terms $2 dot L$ and $L$ of $kappa_2$ and $kappa_3$). This saves the prover an evaluation of the whole message.

We run the affine variant without this sample as well, so that the two variants are comparable. Its fold rounds at the first level then deal with the $L$ codewords of the list. With the sample, a fold round of the affine variant is charged the bound of @CWYZ26 plus $2\/|FF|$ for the claims that the round carries (see @tab:fold). Without it we charge $2 dot L \/ |FF|$ for the claims, by a union bound over the list, as in $kappa_2$. The fold rounds of the first level then need #num("rng-fold-grind0:anf") bits of grinding in place of #num("rng-fold-grind0:affine") at $eta = 0.02$, and #num("rng-fold-grind0:anf-small") in place of #num("rng-fold-grind0:affine-small") at the least $eta$ (see @tab:params). The later levels keep their samples. A proof is #num("rng-first-sample-bytes:affine") bytes smaller.

We stress that this accounting is ours. It is not part of the analysis of @CWYZ26, or of Flock's design note, and we did not write a proof for it.

#paragraph[The prover of the affine variant.] Flock's dense prover for the affine variant makes three passes over the table per fold round. We wrote a prover for this variant that makes one pass per round, with the techniques that we use for BEEP-Ligerito (see @s:exp_cost). It writes the same proofs as Flock's prover, bit by bit, so the verifier is Flock's.

In what follows, and in all the tables but one, "the affine variant" is Flock's affine variant with these two changes. @tab:affine_steps in @s:exp_cost has Flock's variant as it ships, and each of the two changes apart.

#figure(
  placement: auto,
  exptable(13,
    (table.cell(colspan: 8)[], table.cell(colspan: 3)[fold rounds], table.cell(colspan: 2)[batching],
     [variant], [level], [$rho$], [$blockclength$], [$eta$], [rows], [queries], [folds], [grinding], [$numsamples$], [$t - delta blockclength - 1$], [claims], [queries]),
    "params", size: 8pt),
  caption: [The parameters of the variants for #num("params:cell") words at rate $1\/2$. For each level: its rate, its block length and its slack $eta$, the number of rows that are interleaved (a query opens one column of that many elements), the number of queries, and the number of fold rounds. For the fold rounds: the bits of grinding of each fold challenge, the number of samples per round, and the threshold $t$ of the analysis. "Batching": the bits of grinding of the challenges that batch claims, and of the challenge that batches the queries of the level. For BEEP-Ligerito, whose proofs of work have a threshold, the grinding of a challenge is $log_2$ of the expected number of hashes of its proof of work. The first level of the affine variant and of BEEP-Ligerito batches no claims, since they do not sample the first commitment. Every level also has #num("params:qgrind") bits of grinding on its queries.],
) <tab:params>

#paragraph[Measurements.] We run on an #num("run:cpu") laptop (#num("run:cores")) with #num("run:memory-gb") GB of memory, on AC power and with #num("run:threads") threads. We run #num("run:instances") instances, i.e. pairs of a number of words and a rate: #num("run:shapes"). For each instance, one process opens the same commitment with all the variants, one after the other, #num("run:reps") times after a warm-up, and we report medians. For #num("run:one-process-shapes") we split the variants over #num("run:processes-per-split-shape") processes, since for the largest of these instances the provers do not fit together in memory. The commitment is the same in all the variants, so we leave it out of the prover time. It takes #num("rng-commit") ms, depending on the size and on the rate.

The number of hashes that a proof of work tries is random. Because of this we report the prover time with the proofs of work at their expected cost. We run each prover a second time with no proof of work, and we add the expected cost of each of its proofs of work. For each proof of work, this is the mean time of many searches of the same difficulty, which we time in the same process, corrected to its expected number of hashes.

The machine was not fully idle during the run: its load average was #num("run:load") before each process. No process had part of its memory compressed or swapped. We measured the instance with #num("run:added-shapes") on its own, a few hours after the others, with the same program.

As a check of these times, we compare them with the times that we measure with the proofs of work, corrected for the hashes that these runs happened to try. For Ligerito (Flock) and the affine variant the two agree within #num("run:residual-pct-max:others")~%#footnote[In #num("anomaly:runs") earlier runs of this benchmark they did not. In the processes that it shared with the other provers, Flock's prover for the affine variant took #num("anomaly:pct")~% longer with proofs of work than the time that we would report, and the other provers did not. We did not find the reason. In the #num("anomaly:later-runs") runs since then, this one included, we saw it in none of these processes, and in #num("anomaly:later-own-slow") of the #num("anomaly:later-own-processes") processes that only have affine provers (#num("anomaly:later-own-pct")~% longer; the machine was #num("anomaly:later-own-idle")~% idle when this process started, against a median of #num("anomaly:later-own-idle-rest")~% for the others). In this run, over all the affine provers of @tab:affine_steps, the two times agree within #num("run:affine-residual-pct-max:flock")~% for Flock's prover and within #num("run:affine-residual-pct-max:ours")~% for ours.].

For BEEP-Ligerito the measured times are longer in #num("run:residual-beep-positive") of the #num("run:residual-beep-rows") cases, by #num("run:residual-beep-median")~% in the median and by at most #num("run:residual-pct-max:beep")~%. So the times that we report for BEEP-Ligerito may be slightly too low.

The times of two processes also differ by a few percent. For example, without proofs of work an affine prover at $eta = 0.02$ and the same prover at the least $eta$ do the same work, up to their queries. For $2^24$ words at rate $1\/16$ the provers of the first process were #num("affine-family-diff-pct:sixteenth24")~% slower than those of the second, so in this instance the row of the affine variant at $eta = 0.02$ is slightly pessimistic. In the other instances with several processes the two agree within #num("affine-family-diff-pct-max:other-split")~%.

We stress three limitations of this comparison. First, all the provers work on a "dense" table, which is not the path that Flock uses in production. There, the first rounds of Ligerito (Flock) and of Flock's affine variant only use a few values per row of the committed table. Our prover for the affine variant does not have this path. The samples of BEEP need the folded table in every round, so it is unclear to us whether a similar optimization applies to BEEP.

Second, the fold rounds of the affine variant and of BEEP-Ligerito are our code, and we wrote both with the same techniques (see @s:exp_cost). To our knowledge they are at a comparable level of optimization, but we cannot exclude that one of them has more room left than the other. Ligerito (Flock) runs Flock's code. In particular, the affine variant that we measure is not the one that Flock ships: it has our prover, and it has no sample on its first commitment. @tab:affine_steps has the times of Flock's affine variant as it ships.

Third, each variant has $128$ bits under its own analysis, and these analyses do not have the same status. That of the affine variant has the open points of its design note, it samples the points that bind a commitment one after the other, and at its first level it uses the accounting of ours that we described above. The analysis of BEEP-Ligerito relies on @t:beep_codeswitch and on counting grinding as in @s:exp_fold.

There is one more point on which we are unsure. At the levels whose commitment has a sample, we keep Flock's rule for the affine variant, which charges the claims of a fold round for one codeword. After the sample the other codewords of the list have a false claim, but it seems to us that a fold challenge can still make such a claim true. If the list has to be counted at these levels as well, their fold rounds need #num("rng-fold-grind-list-extra:anf") more bits of grinding at $eta = 0.02$, and the prover of the affine variant takes at most #num("list-extra-pct-max:anf")~% longer.

#figure(
  placement: auto,
  exptable(8,
    ([words], [$rho$], [variant], [proof (KiB)], [prove (ms)], [no grinding (ms)], [grinding ($10^6$ hashes)], [verify (ms)]),
    "main", size: 7.5pt, group: 5, inset-y: 1pt),
  caption: [The variants on the same commitment, at $128$ bits, for a message of the given number of words and a first level of rate $rho$. The affine rows are the affine variant as we run it, i.e. with our prover and with no sample on the first commitment (see the text). "Affine, least $eta$" is this variant with the least slack that we can certify at each level, and the other rows have the same $eta$ at every level. "Prove" is the time of the opening with the proofs of work at their expected cost, "no grinding" is the same without proofs of work, and "grinding" is the expected number of hashes of all the proofs of work of one proof. In the rows marked with \*, Ligerito (Flock) runs on a configuration that Flock's code derives but that Flock does not ship (see the text). #num("run:cpu"), #num("run:threads") threads, medians of #num("run:reps") runs. The commitment, which is the same for all the variants, is not included.],
) <tab:main>

#paragraph[Results.] @tab:main has the measurements.

At the same slack $eta = 0.02$, the proofs of BEEP-Ligerito and of the affine variant have essentially the same size: they differ by at most #num("size-diff-kib-max:beep-0.02:anf") KiB. The two variants make almost the same queries, and the answers to the samples are small (see @s:exp_bytes). The affine variant makes up to #num("query-diff-max:anf:beep-0.02") more queries, since its fold loses one coordinate of agreement per round.

A smaller $eta$ gives smaller proofs. With $eta = 0.001$ the proofs of BEEP-Ligerito are #num("rng-saving:beep-0.001:anf")~% smaller than those of the affine variant at $eta = 0.02$. However, for long messages this saving is also available to the affine variant. For $2^20$ words and more, the proofs of BEEP-Ligerito at $eta = 0.001$ are #num("rng-size[long]:beep-0.001:anf-small") times as large as those of the affine variant at its least $eta$. The reason is that most of a proof comes from the first level (see @s:exp_bytes). This is the longest code, and there the affine fold also has a bound for a small $eta$.

For short messages this is no longer the case, since the affine fold needs a larger $eta$ on a shorter code (see @s:exp_fold). For $2^16$, $2^17$ and $2^18$ words the least $eta$ of the affine variant at the first level is #num("affine-small-eta0:fast16"), #num("affine-small-eta0:fast17") and #num("affine-small-eta0:fast18"). There the proofs of BEEP-Ligerito at $eta = 0.001$ are #num("saving:fast16:beep-0.001:anf-small")~%, #num("saving:fast17:beep-0.001:anf-small")~% and #num("saving:fast18:beep-0.001:anf-small")~% smaller than those of the affine variant. For $2^15$ words at rate $1\/8$ the least $eta$ of the affine variant is #num("affine-small-etas:eighth15") at its two levels, and the proofs of BEEP-Ligerito at $eta = 0.001$ are #num("saving:eighth15:beep-0.001:anf-small")~% smaller.

Both have smaller proofs than Ligerito (Flock): those of BEEP-Ligerito at $eta = 0.001$ are #num("rng-size:beep-0.001:split") times as large. For example, for $2^24$ words at rate $1\/2$ the proofs take #num("size:fast24:beep-0.001") KiB with BEEP-Ligerito, #num("size:fast24:anf-small") KiB with the affine variant and #num("size:fast24:split") KiB with Ligerito (Flock). This difference is not due to the fold alone. The ladder of Ligerito (Flock) has more levels, and at rate $1\/2$ its levels after the first one also have a higher rate, so they make more queries (see @tab:params and @s:exp_bytes).

We turn to the prover, with the proofs of work at their expected cost. The prover of BEEP-Ligerito is slower than that of the affine variant in every instance. At rate $1\/2$, BEEP-Ligerito at $eta = 0.02$ takes #num("rng-provex[half]:beep-0.02:anf") times as long as the affine variant with the same $eta$, and at $eta = 0.001$ it takes #num("rng-provex[half]:beep-0.001:anf-small") times as long as the affine variant at its least $eta$. For example, for $2^24$ words at $eta = 0.02$ the two provers take #num("provex:fast24:beep-0.02") ms and #num("provex:fast24:anf") ms.

At smaller rates the difference grows: for $2^24$ words, BEEP-Ligerito at $eta = 0.02$ takes #num("ratio-provex:slim24:beep-0.02:anf"), #num("ratio-provex:eighth24:beep-0.02:anf") and #num("ratio-provex:sixteenth24:beep-0.02:anf") times as long as the affine variant at the rates $1\/4$, $1\/8$ and $1\/16$.

There are two reasons. The first one is the samples. Without proofs of work BEEP-Ligerito takes #num("rng-nopow:beep-0.02:anf") times as long as the affine variant at $eta = 0.02$, over all the instances, since its fold rounds do more work (see @s:exp_cost).

The second one is the grinding. The proofs of work of BEEP-Ligerito try #num("rng-pow[half]:beep-0.02:anf") times as many hashes at rate $1\/2$, and #num("rng-pow[low]:beep-0.02:anf") times as many at the smaller rates. A fold challenge of BEEP needs about $log_2(delta dot blockclength)$ bits of grinding (@s:exp_fold). For a given message, a smaller rate means a longer code and a larger $delta$, and so more grinding. We come back to this in @s:exp_cost.

These results do not rest on our accounting for the first level of the affine variant. With the sample on the first commitment in both variants, BEEP-Ligerito at $eta = 0.02$ takes #num("rng-provex:beepb-0.02:afast") times as long as the affine variant with our prover, over all the instances (see @tab:steps and @tab:affine_steps).

Our two changes to the affine variant matter for this comparison. Against Flock's affine variant as it ships, BEEP-Ligerito at $eta = 0.02$ takes #num("rng-provex:beep-0.02:affine") times as long, and for $2^24$ and $2^25$ words at rate $1\/2$ it is not slower (#num("rng-provex[big]:beep-0.02:affine") times). But this compares a prover with one pass per fold round and no sample on the first commitment with one that has neither (see @tab:affine_steps).

Against Ligerito (Flock), BEEP-Ligerito takes #num("rng-provex:beep-0.02:split") times as long at $eta = 0.02$, and #num("rng-provex:beep-0.001:split") times at $eta = 0.001$. The affine variant at $eta = 0.02$ takes #num("rng-provex:anf:split") times as long as Ligerito (Flock). Recall that Ligerito (Flock) runs Flock's prover, with a sample on its first commitment, so this is not a comparison of like with like either: Flock's affine variant as it ships takes #num("rng-provex:affine:split") times as long as Ligerito (Flock).

The verifier of BEEP-Ligerito takes #num("rng-verify:beep-0.02:anf") times as long as that of the affine variant at $eta = 0.02$, and #num("rng-verify:beep-0.001:anf-small") times at the smaller slacks.

== The parts of a proof <s:exp_bytes>

We now split the proofs of @tab:main into the parts of the protocol.

#paragraph[The parts.] Each level of Ligerito commits to a table with a Merkle tree whose leaves are the columns of the table. For each query of the level, the proof has the column that the query opens, i.e. a leaf of the tree, and the authentication path of this leaf. We call the first the "leaves" and the second the "inner paths", and we count them apart.

A leaf is a column of $2^k$ elements of $"GF"(2^128)$, of $16$ bytes each, where $2^k$ is the number of rows of the level (see @tab:params). An inner path is a list of hashes of $32$ bytes. The Merkle trees of Flock are "capped": for a level with $Q$ queries the proof has, once, the nodes of the tree at depth $floor(log_2 Q)$, and the path of each query stops at that depth. So for a code with $2^d$ points a path has $d - floor(log_2 Q)$ hashes.

For example, at the first level of the instance with #num("bytes:cell") words a leaf has #num("bytes:leaf0-elements") elements, i.e. #num("bytes:leaf0-bytes") bytes, and a path has #num("bytes:path0-nodes") hashes, i.e. #num("bytes:path0-bytes") bytes.

The other parts of a proof are the caps, the messages of the fold rounds (the round polynomials or the values that the affine fold sends and, for BEEP-Ligerito, the answers to the samples), the out of domain values that bind each new commitment, the final message, and the nonces of the proofs of work.

@tab:bytes has all the parts for #num("bytes:cell") words, level by level. @tab:bytes_all has the leaves and the inner paths of all the instances.

#figure(
  placement: auto,
  exptable(7,
    (table.cell(colspan: 2)[part], [Ligerito (Flock)], [affine, $eta = 0.02$], [affine, least $eta$], [BEEP, $eta = 0.02$], [BEEP, $eta = 0.001$]),
    "bytes"),
  caption: [The parts of the proofs for #num("bytes:cell") words at rate $1\/2$, in KiB. For each level, "leaves" are the columns that its queries open and "inner paths" are the hashes of their Merkle paths. Then the caps of the Merkle trees, the round messages (round polynomials, or the values that the affine fold sends), the answers to the samples of the fold rounds of BEEP-Ligerito, the out of domain values that bind the commitments, the final message (with the overflow coefficients of the affine fold), and the nonces of the proofs of work. The levels of Ligerito (Flock) are not those of the other variants, see @tab:params.],
) <tab:bytes>

#figure(
  placement: auto,
  exptable(11,
    ([words], [$rho$], [variant], [queries], table.cell(colspan: 2)[leaves], table.cell(colspan: 2)[inner paths], table.cell(colspan: 2)[rest], [total],
     [], [], [], [], [KiB], [%], [KiB], [%], [KiB], [%], [KiB]),
    "bytes_all", size: 7.5pt, group: 5, inset-y: 1.2pt),
  caption: [The Merkle leaves and the inner paths of every proof of @tab:main, over all its levels: the number of queries, and the size of each part in KiB and as a fraction of the proof. "Rest" is everything else (the caps, the messages of the fold rounds, the binding values, the final message and the nonces).],
) <tab:bytes_all>

#paragraph[What we see.] First, almost all of a proof consists of Merkle openings. Over all the proofs of the run, the leaves, the inner paths and the caps take #num("rng-merkle-pct")~% of the proof. The leaves take #num("rng-leaves-pct")~% and the inner paths #num("rng-paths-pct")~%.

How this splits between leaves and inner paths depends on the shape of the first level, which Flock's configuration fixes: in our instances a leaf of the first level is #num("rng-leaf-over-path0") times as large as its path.

Second, the first level dominates. It takes #num("rng-level0-pct")~% of the proof. In all the variants this level is the same code, and its leaves and paths have the same size, so the variants only differ in the number of queries that they make there: for #num("bytes:cell") words, #num("bytes:queries0:anf") at $eta = 0.02$ and #num("bytes:queries0:beep-0.001") at $eta = 0.001$. This is the saving of a smaller $eta$, and it is the same in leaves and in inner paths.

Third, Ligerito (Flock) differs from the other variants in the levels after the first. For #num("bytes:cell") words, its levels $1$ to $3$ have the same block lengths and the same rows as those of the other variants (see @tab:params), but a higher rate, and so more queries. It also has #num("bytes:extra-levels:split") more levels. Its levels after the first take #num("bytes:later-kib:split") KiB in leaves and inner paths, against #num("bytes:later-kib:anf") KiB for the affine variant at $eta = 0.02$, i.e. #num("bytes:later-ratio:split:anf") times as much.

Finally, the parts that are specific to each fold are small. The answers to the samples of BEEP-Ligerito are $2 dot numsamples$ field elements per fold round. Over all our runs they take #num("rng-answers-kib") KiB, i.e. #num("rng-answers-pct")~% of the proof. In exchange, a round message of BEEP-Ligerito has two field elements, against five for the affine fold: for #num("bytes:cell") words the round messages take #num("bytes:rounds-kib:beep-0.02") KiB and #num("bytes:rounds-kib:anf") KiB, respectively.

== The cost of the samples <s:exp_cost>

We now look at what the samples of @c:BEEP cost the prover of BEEP-Ligerito, and at what we do to reduce this cost. As we saw in @s:exp_bytes, their cost in proof size is small. We also describe our prover for the affine variant, and what our two changes give this variant.

#paragraph[The fold rounds.] In a fold round the prover holds the current table and a table of weights of the same size, which encodes the claims so far. A direct implementation makes three passes over them. The first one evaluates the multilinear extensions of the two halves of the table at the $numsamples$ points, which is $numsamples$ multiplications per entry. The second one computes the message of the sumcheck round. The third one folds the two tables, and it adds the $numsamples$ new claims to the folded weights, which is $numsamples$ more multiplications per entry of the folded table.

Our prover makes one pass per round instead, and it does not add the new claims to the weights. It uses two observations. First, the challenges of the second and third rounds of @c:BEEP and the points of the next fold are sampled together (see @s:exp_fold). So the pass that folds the tables can also compute the answers at the next points and the message of the next sumcheck round.

Second, the weight of a claim at a point is a product of a factor that depends on the row and a factor that depends on the column. So for each new point the pass computes the inner product of each row of the folded table with the factor on the columns. The answers, and the part of the new claims in the messages of the later rounds of the level, are sums of these inner products over the rows. We only add these claims to the table of weights at the end of the level, when the table has one row.

In this way the samples cost $numsamples$ multiplications per entry of the folded table in each round, inside a pass that the prover makes anyway. We also wrote the inner loops of this pass with vector instructions.

#paragraph[The fold rounds of the affine variant.] A fold round of the affine variant is different. Let $f_0, f_1$ be the two halves of the table. Each row is a polynomial, written in the basis of the additive NTT of the code, and we let $T f_1$ be the table $f_1$ with each of its rows multiplied by the variable. There are six inner products of $f_0$, $f_1$ and $T f_1$ with the two halves of the weights, and the prover sends five of them, since the claim gives the sixth. Then it folds the table to $f_0 + alpha dot f_1 + beta dot T f_1$ for two challenges $alpha, beta$, and the weights with a third challenge. So the rows of the table grow by one coefficient per round. At the end of a level the prover sends the coefficients beyond the length of the next code in the clear (the "overflow" of @tab:bytes).

Flock's dense prover makes three passes per round: it computes $T f_1$, then the inner products, and then the fold. Ours makes one pass per round, as for BEEP-Ligerito: the pass that folds the tables at the challenges of a round also computes the inner products of the next round. It does not store $T f_1$, since in this basis an entry of $T f_1$ is a combination of two entries of the same row of $f_1$. The inner loops use the same vector instructions as those of BEEP-Ligerito, and the two provers share the rest of their code.

#paragraph[What the samples cost.] To isolate the cost of the samples, we also run BEEP-Ligerito with no samples at all, i.e. with the fold of a sumcheck round alone. This is not a sound protocol, and we only use it as a control. @tab:time compares the two, without proofs of work.

The samples take #num("rng-time-samples-share:0.02")~% of the opening at $eta = 0.02$, and BEEP-Ligerito takes #num("rng-time-overhead:0.02") times as long as the control (#num("rng-time-overhead:0.001") times at $eta = 0.001$). With the direct implementation the samples cost #num("rng-time-samples-speedup[long]:0.02") times as much, for $2^20$ words and more.

@tab:time also has the affine variant. Its fold rounds cost less than those of BEEP-Ligerito. For example, for $2^24$ words at rate $1\/2$ and $eta = 0.02$ they take #num("time-affine-folds:fast24:0.02") ms, against #num("time-beep-folds:fast24:0.02") ms for BEEP-Ligerito and #num("time-folds:fast24:0.02") ms for the control. Over all the instances, the fold rounds of BEEP-Ligerito take #num("rng-time-folds-vs-affine:0.02") times as long as those of the affine variant at $eta = 0.02$, and those of the affine variant take #num("rng-time-affine-folds-vs-control:0.02") times as long as those of the control.

#figure(
  placement: auto,
  exptable(12,
    (table.cell(colspan: 3)[], table.cell(colspan: 4)[BEEP], [], table.cell(colspan: 2)[affine], table.cell(colspan: 2)[grinding of BEEP],
     [words], [$rho$], [$eta$], [samples], [folds], [rest], [total], [control], [folds], [total], [folds ($10^6$ hashes)], [all (ms)]),
    "time", size: 8pt, group: 2, inset-y: 1.6pt),
  caption: [Where the time of the BEEP-Ligerito prover goes, in ms, without proofs of work. "Samples": the cost of the samples, measured as the difference with the control in the time of the fold rounds. "Folds": the fold rounds of the control, i.e. the round messages and the folds. "Rest": the commitments of the next levels, the out of domain samples that bind them, and the queries. "Total" and "control": the whole opening, with and without samples. "Affine": the fold rounds and the whole opening of the affine variant, at $eta = 0.02$ in the rows with $eta = 0.02$ and at its least $eta$ in the others. The last two columns are the expected hashes of the proofs of work of the fold challenges of BEEP-Ligerito, and the expected time of all the proofs of work of one of its proofs, in ms.],
) <tab:time>

#paragraph[The proofs of work.] The proofs of work are the other cost, and for most instances the larger one. A fold challenge of BEEP-Ligerito needs about $log_2(delta dot blockclength)$ bits of grinding (@s:exp_fold), and a level has several fold rounds. The fold challenges account for #num("rng-time-foldpow-share:0.02")~% of the expected hashes of a proof at $eta = 0.02$, and for #num("rng-time-foldpow-share:0.001")~% at $eta = 0.001$. In time, at $eta = 0.02$ the proofs of work are #num("rng-time-pow-share[half]:0.02")~% of the opening at rate $1\/2$, and #num("rng-time-pow-share[low]:0.02")~% at the smaller rates. For the affine variant they are #num("rng-time-affine-pow-share[long]:0.02")~% of the opening for $2^20$ words and more.

With a whole number of bits, the proofs of work of BEEP-Ligerito would try #num("rng-step-bits-hashes-pct:0.02")~% more hashes at $eta = 0.02$, and #num("rng-step-bits-hashes-pct:0.001")~% more at $eta = 0.001$, depending on how far the errors of its challenges are from a power of two.

#paragraph[Three choices.] Three choices of BEEP-Ligerito, as we described it in @s:exp_ligerito, only aim at the prover time: it has no sample on the first commitment, its prover makes one pass per fold round, and its proofs of work have a threshold. @tab:steps shows what each of them gives. It has the prover time of BEEP-Ligerito, and that of BEEP-Ligerito with one of the three choices undone, or with all of them.

For example, for $2^24$ words at rate $1\/2$ and $eta = 0.02$ the prover takes #num("step-ms:beep:fast24:0.02") ms. It takes #num("step-ms:beepref:fast24:0.02") ms with the direct implementation of the fold rounds, #num("step-ms:beepb:fast24:0.02") ms with the sample on the first commitment, and #num("step-ms:beepbits:fast24:0.02") ms with proofs of work of a whole number of bits. With the three choices undone it takes #num("step-ms:beepold:fast24:0.02") ms. This is #num("step-vs-shipped:beepold:fast24:0.02") times as long as Flock's affine variant as it ships (see @tab:affine_steps), which has none of the three either.

The single pass matters most for long messages at rate $1\/2$, where the proofs of work are a small part of the opening: with three passes the prover takes #num("rng-step-passes-pct[big]:0.02")~% longer for $2^24$ and $2^25$ words at $eta = 0.02$. For the short messages it still takes #num("rng-step-passes-pct[short]:0.02")~% longer.

The threshold matters for $2^22$ and $2^24$ words at the rates $1\/8$ and $1\/16$, where the proofs of work are a large part of the opening. There, with a whole number of bits the prover takes #num("rng-step-bits-pct[lowest]:0.02")~% longer at $eta = 0.02$. For example, for $2^24$ words at rate $1\/16$ the threshold saves #num("step-bits-ms:sixteenth24:0.02") ms out of #num("step-ms:beepbits:sixteenth24:0.02").

For the short messages, the sample on the first commitment and the threshold change the prover time by a few tenths of a millisecond at most, which is within the noise of these measurements.

#figure(
  placement: auto,
  exptable(9,
    ([words], [$rho$], [$eta$], [BEEP], [first sample], [three passes], [whole bits], [all three], [affine]),
    "steps", size: 8pt, group: 2, inset-y: 1.6pt),
  caption: [The prover time of BEEP-Ligerito, in ms, with the proofs of work at their expected cost, and what three of its choices give. "BEEP": BEEP-Ligerito, as in @tab:main. "First sample": with an out of domain sample on the first commitment, as in Flock's variants. "Three passes": with the direct implementation of the fold rounds. "Whole bits": with proofs of work of a whole number of bits. "All three": with the three at once. "Affine": the affine variant, at $eta = 0.02$ in the rows with $eta = 0.02$ and at its least $eta$ in the others, as in @tab:main. It has no sample on the first commitment and a prover with one pass per fold round, so it compares with the column "BEEP"; for "all three", see the column "Flock's" of @tab:affine_steps.],
) <tab:steps>

#paragraph[The two changes to the affine variant.] @tab:affine_steps does the same for the affine variant. It has the prover time of Flock's affine variant as it ships, with our prover, without the sample on the first commitment, and with both changes, which is the affine variant of the other tables.

For example, for $2^24$ words at rate $1\/2$ and $eta = 0.02$, Flock's variant takes #num("astep-ms:affine:fast24:0.02") ms as it ships. It takes #num("astep-ms:afast:fast24:0.02") ms with our prover, whose fold rounds are about #num("astep-folds-speedup:fast24:0.02") times as fast#footnote[Flock's prover does not time its fold rounds. For them we take the time of ours plus the difference between the two openings, which share the rest of their code.]. It takes #num("astep-ms:anfref:fast24:0.02") ms without the sample, and #num("astep-ms:anf:fast24:0.02") ms with both changes.

Over all the instances, at $eta = 0.02$ the opening takes #num("rng-astep-prover-pct:0.02")~% less time with our prover, and then a further #num("rng-astep-sample-pct:0.02")~% less without the sample. The first level holds most of the table, so both changes matter most for long messages at rate $1\/2$. At smaller rates the commitments of the next levels, which we did not change, take a larger part of the opening.

#figure(
  placement: auto,
  exptable(8,
    ([words], [$rho$], [$eta$], [Flock's], [our prover], [no first sample], [both], [BEEP]),
    "asteps", size: 8pt, group: 2, inset-y: 1.6pt),
  caption: [The prover time of the affine variant, in ms, with the proofs of work at their expected cost, and what our two changes give. "Flock's": Flock's affine variant as it ships, i.e. with Flock's dense prover and with an out of domain sample on the first commitment. "Our prover": the same with our prover, which writes the same proofs. "No first sample": Flock's prover, with no sample on the first commitment and with the fold rounds of the first level ground for the list of the code. "Both": the two changes, i.e. the affine variant of @tab:main. "BEEP": BEEP-Ligerito, at $eta = 0.02$ in the rows with $eta = 0.02$ and at $eta = 0.001$ in the rows with the least $eta$ of the affine variant, as in @tab:main.],
) <tab:affine_steps>

== 100 bits of security <s:exp_100>

#paragraph[Setting.] We repeat the comparison of @s:exp_ligerito at $100$ bits of security, on the same instances. The affine variant and BEEP-Ligerito have the same ladders and the same slacks as there. The field is the same, so every challenge now has $28$ bits to spare.

For the affine variant and BEEP-Ligerito, every challenge has error less than $2^(-100)$ after grinding. For Ligerito (Flock) we use the configurations that Flock ships at $100$ bits, `fast100` at rate $1\/2$ and `slim100` at rate $1\/4$, and at the rates #num("100:run:derived-rates") the configuration that Flock's code derives for `slim100` at that rate. In these configurations only the queries are set for $100$ bits. The other challenges keep the $128$ bits of the configurations of @s:exp_ligerito, and the fold challenges are still in $"GF"(2^256)$. Below rate $1\/2$ their ladders also differ from those of @s:exp_ligerito: in `slim100` the rate is halved from one level to the next, and in `slim` it is divided by four.

As at $128$ bits, the affine variant and BEEP-Ligerito take the grinding of their queries from Flock's configuration of the same instance. This is no grinding at rate $1\/2$, and #num("100:qgrind@2") bits at the other rates.

#paragraph[What changes.] At $100$ bits the fold challenge of a fold that is analyzed with MCA still needs grinding over this field with the bound of @BCHKS25: #num("100:fold:bchks-grind:0.02") bits at $eta = 0.02$ for the codes of @tab:fold, and #num("100:fold:bchks-grind:0.001") bits at $eta = 0.001$. With the bound of @DKT26 it needs #num("100:fold:dkt-grind:0.02") bits at $eta = 0.02$ and #num("100:fold:dkt-grind:0.001") bits at $eta = 0.001$.

BEEP needs none. Its fold challenge has error $(t + 3 dot L) \/ |FF|$ (see @s:exp_fold), and for the codes of our instances $t + 3 dot L$ is below $2^(#num("100:beep-fold-numerator-bits-max"))$. The rule of @s:exp_fold now selects #num("100:rng-samples") samples in every fold round, against #num("100:rng-samples-128") at $128$ bits, with the least threshold $t = delta dot blockclength + 2$ at every level.

The affine fold needs no grinding either, with or without the sample on the first commitment, and neither do the challenges that batch claims and queries. So at rate $1\/2$ the affine variant and BEEP-Ligerito have no proof of work at all, and at the other rates they only have those of their queries. @tab:params100 has the parameters for #num("100:params:cell") words.

#figure(
  placement: auto,
  exptable(13,
    (table.cell(colspan: 8)[], table.cell(colspan: 3)[fold rounds], table.cell(colspan: 2)[batching],
     [variant], [level], [$rho$], [$blockclength$], [$eta$], [rows], [queries], [folds], [grinding], [$numsamples$], [$t - delta blockclength - 1$], [claims], [queries]),
    "params100", size: 8pt),
  caption: [The parameters of the variants at $100$ bits for #num("100:params:cell") words at rate $1\/2$, as in @tab:params. At this rate no variant grinds its queries.],
) <tab:params100>

#paragraph[Measurements.] We measure as in @s:exp_ligerito, in a run of its own, with the same program up to the target. The load average of the machine was #num("100:run:load") before each process.

The machine had less unused memory than in the run of @s:exp_ligerito. In #num("100:run:limited-processes") of the #num("100:run:processes") processes a large part of the memory was compressed (the peak footprint is #num("100:run:limited-pct")~% above the resident memory): the #num("100:run:flagged-sixteenth24") processes of $2^24$ words at rate $1\/16$, and the #num("100:run:flagged-fast25") of Ligerito (Flock) for $2^25$ words at rate $1\/2$. In #num("100:run:near-limited-processes") more this is #num("100:run:near-limited-pct")~%.

This shows in single proofs. In the #num("100:run:flagged-split-processes") of those #num("100:run:limited-processes") processes that run Ligerito (Flock), its first proof takes #num("100:run:flagged-first-proof-x:split") times as long as the median of the nine, against at most #num("100:run:first-proof-x-max-128:split") times at $128$ bits. For $2^24$ words at rate $1\/16$ the affine variant and BEEP-Ligerito take #num("100:run:flagged-faults:ours") page faults per proof, against at most #num("100:run:faults-max-128:ours") at $128$ bits.

We do not see it in the medians, which are what we report. For the provers of @tab:main100 in those processes, the median without proofs of work is at most #num("100:run:flagged-median-over-min-pct-max")~% above the fastest of the nine proofs. Also, without proofs of work a prover whose ladder is the same at the two targets does no more work at $100$ bits than at $128$ bits: it makes fewer queries, and BEEP-Ligerito takes no more samples. In those processes such a prover takes #num("100:run:flagged-nopow-vs-128") times as long as in the run at $128$ bits, and over all the instances #num("100:run:nopow-vs-128") times. For Ligerito (Flock) below rate $1\/2$ we do not have this comparison, since its ladders differ.

As in @s:exp_ligerito, we compare the times that we report with the times that we measure with the proofs of work. The two agree within #num("100:run:residual-pct-max:others")~% for Ligerito (Flock) and the affine variant and within #num("100:run:residual-pct-max:beep")~% for BEEP-Ligerito. For the proofs that take $2$ ms or more this is #num("100:run:residual-pct-max[2ms]:others")~% and #num("100:run:residual-pct-max[2ms]:beep")~%.

The times of two processes differ by a few percent here as well. For $2^24$ words at rate $1\/4$, the affine provers at $eta = 0.02$ were #num("100:affine-family-diff-pct:slim24:0.02")~% slower without proofs of work than those at the least $eta$. At rate $1\/8$ those at the least $eta$ were #num("100:affine-family-diff-pct:eighth24:least")~% slower. So in each of these two instances one of the two rows of the affine variant is slightly pessimistic. In the other instances with several processes the two agree within #num("100:affine-family-diff-pct-max:other-split")~%.

#paragraph[Results.] @tab:main100 has the measurements.

The proofs are smaller than at $128$ bits, since every level makes fewer queries. At $eta = 0.02$, those of the affine variant are #num("100:rng-saving-vs-128[half]:anf")~% smaller at rate $1\/2$ and #num("100:rng-saving-vs-128[low]:anf")~% smaller at the other rates, and those of BEEP-Ligerito #num("100:rng-saving-vs-128[half]:beep-0.02")~% and #num("100:rng-saving-vs-128[low]:beep-0.02")~%. The saving is smaller at rate $1\/2$ because there the queries are ground at $128$ bits and not at $100$ bits, so their number decreases less.

Between the variants the picture is that of @s:exp_ligerito. At the same slack the proofs of BEEP-Ligerito and of the affine variant differ by at most #num("100:size-diff-kib-max:beep-0.02:anf") KiB. With $eta = 0.001$ those of BEEP-Ligerito are #num("100:rng-saving:beep-0.001:anf")~% smaller than those of the affine variant at $eta = 0.02$, and for $2^20$ words and more they are #num("100:rng-size[long]:beep-0.001:anf-small") times as large as those of the affine variant at its least $eta$.

The least $eta$ of the affine variant does not depend on the target, so for the short messages the proofs of BEEP-Ligerito are again smaller: by #num("100:saving:fast16:beep-0.001:anf-small")~%, #num("100:saving:fast17:beep-0.001:anf-small")~% and #num("100:saving:fast18:beep-0.001:anf-small")~% for $2^16$, $2^17$ and $2^18$ words at rate $1\/2$, and by #num("100:saving:eighth15:beep-0.001:anf-small")~% for $2^15$ words at rate $1\/8$.

For the prover the picture changes. At $128$ bits BEEP-Ligerito was slower than the affine variant for two reasons, its samples and the grinding of its fold challenges (see @s:exp_cost). At $100$ bits the second one is gone. BEEP-Ligerito now takes #num("100:rng-provex:beep-0.02:anf") times as long as the affine variant at $eta = 0.02$, and #num("100:rng-provex:beep-0.001:anf-small") times as long at the small slacks. This is the cost of the samples.

The ratio is largest for $2^24$ and $2^25$ words at rate $1\/2$. For example, for $2^24$ words at rate $1\/2$ and $eta = 0.02$ BEEP-Ligerito takes #num("100:provex:fast24:beep-0.02") ms and the affine variant #num("100:provex:fast24:anf") ms.

Against Ligerito (Flock), BEEP-Ligerito takes #num("100:rng-provex:beep-0.02:split") times as long at $eta = 0.02$, and the affine variant #num("100:rng-provex:anf:split") times. As in @s:exp_ligerito, this is not a comparison of like with like.

#figure(
  placement: auto,
  exptable(8,
    ([words], [$rho$], [variant], [proof (KiB)], [prove (ms)], [no grinding (ms)], [grinding ($10^6$ hashes)], [verify (ms)]),
    "main100", size: 7.5pt, group: 5, inset-y: 1pt),
  caption: [The variants on the same commitment at $100$ bits, as in @tab:main. Ligerito (Flock) runs on Flock's configurations `fast100` (rate $1\/2$) and `slim100` (rate $1\/4$), and in the rows marked with \* on the configuration that Flock's code derives for `slim100` at that rate. #num("run:cpu"), #num("run:threads") threads, medians of #num("100:run:reps") runs.],
) <tab:main100>

== A code that is not known to have MCA up to the Johnson radius <s:exp_other_code>

#todo[Placeholder (AI-drafted): experiments with a linear code that is not known to have MCA up to the Johnson radius. To decide: (1) the code, e.g. one with a linear time encoder (the expander codes of Brakedown, or the RAA codes of Blaze); (2) the baseline, i.e. the same protocol with folds analyzed with MCA, at the largest proximity parameter at which the code is known to have it (to check for the code that we pick; for a general linear code this should be the unique decoding radius); (3) the list size $L$ to use, i.e. the Johnson bound for the minimum distance of the code, and how we know that distance; (4) what to run: the fold errors as in @tab:fold, and the protocol of @c:BEEP_codeswitch as in @tab:main. Nothing below is measured yet.]

The codes of the previous experiments are Reed-Solomon codes, which are known to have MCA up to the Johnson radius @BCHKS25. So in those experiments BEEP competes with other analyses of the same fold, at the same proximity parameter.

We expect the gain of BEEP to be larger for a linear code $cal(C)$ that is not known to have MCA up to its Johnson radius. By the Johnson bound, such a code is still $(delta, L)$-list decodable with a small $L$ for every $delta$ slightly below its Johnson radius, so @t:main_thm applies there. A fold that is analyzed with MCA, instead, has to take $delta$ in the range where MCA is known for $cal(C)$, and then each level makes more queries.

@tab:other_code is meant to compare the two for such a code.

#figure(
  text(size: 9pt, table(
    columns: 8, stroke: none, align: center + horizon, inset: (x: 3.5pt, y: 2.5pt),
    table.hline(),
    [analysis of the fold], [$delta$], [$L$], [queries], [proof (KiB)], [leaves (KiB)], [inner paths (KiB)], [prove (ms)],
    table.hline(stroke: 0.4pt),
    [MCA], ..range(7).map(i => num("other:mca:" + str(i))),
    [BEEP], ..range(7).map(i => num("other:beep:" + str(i))),
    table.hline(),
  )),
  caption: [Placeholder. The protocol of @c:BEEP_codeswitch for a linear code $cal(C)$ that is not known to have MCA up to the Johnson radius, against the same protocol with folds that are analyzed with MCA, at the largest proximity parameter at which $cal(C)$ is known to have it.],
) <tab:other_code>
]


#include "batch.typ"

#bibliography("bibliography.bib", style: "ieee")

