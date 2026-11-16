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
#show: theorems-per-section

// Link color
#let linkcolor = rgb("#1c8699") 
#show link: set text(fill: linkcolor)    
#show ref:  set text(fill: linkcolor)    
#show cite: set text(fill: linkcolor)   


// Define functions:
#let show-comments = false   // set to false to hide every comment for the final version
#let comment(author, color) = body => if show-comments {
  text(fill: color)[*\[#author:* #body*\]*]
}
#let albert = comment("Albert", olive)
#let remco  = comment("Remco", blue)
#let todo   = comment("TODO", orange)
// [AI-edited (claude-fable-5-2), 2026-11-12, at the author's request] `aiedit` colors the text changed or added by AI on 2026-11-12 (the edits marked `[AI-edited ...]` in Sections 3 and 4).
#let show-ai-edits = true   // set to false to remove this color
#let aiedit(body) = if show-ai-edits { text(fill: maroon, body) } else { body }

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

  Finally, we also provide an #emph[affine] version of the DEEP technique, where folding challenges are affine polynomials instead of field elements. We show that, after the DEEP samples are done, the folding error with affine challenges is  $1\/|FF|$. 
]

// Table of contents
#show outline.entry: set text(fill: linkcolor)
#outline(depth: 2) 

// Rest of paper

= Introduction

The soundness of most modern code-based Polynomial Commitment Schemes (PCSs) and IOPPs requires using codes satisfying the #emph[$delta$-Mutual Correlated Agreement (MCA) property] @whir, for a proximity parameter $delta$ as large as possible. A code $cal(C)$ with blocklength $blockclength$ and dimension $codedim$ is said to satisfy this property if, for any two words $u_1, u_2 in FF^blockclength$, for almost all $alpha in FF$, if $u_1+ alpha dot u_2$ agrees with a codeword $c$ from $cal(C)$ on a large set $S$ (concretely $|S|≥ (1-delta) dot blockclength$), then both $u_1$ and $u_2$ agree as well with codewords from $cal(C)$ on $S$. 

A weaker property is that of list decodability. The code $cal(C)$ is #emph[$(delta, L)$-list decodable] if for any word $u in FF^blockclength$ there are at most $L$ codewords from $cal(C)$ at relative hamming distance $≤ delta$ from $u$. If the code has the $delta$-MCA property, then it is $(delta, L)$-list decodable for a polynomially sized $L$ #albert[reference?]. The converse is not true #albert[It is not right? What to cite? This new Ignacio Manzur paper?].

It is often easier to prove that a code $cal(C)$ is list decodable than that it has MCA. Indeed, it is known that all codes are $(delta, L)$-list decodable for $delta$ approaching the #emph[Johnson bound]. Concretely, for $delta = 1-sqrt(rho) - eta$ #albert[It's square root of the relative minimum distance], where $rho=codedim/blockclength$ and $eta >0$ is small, any linear code $cal(C)$ is $(delta, L)$-list decodable with $L = 1\/(2dot eta dot sqrt)$ #albert[cite]. On the other hand,  linear codes in general are only known to have MCA up to the so-called 1.5 Johnson bound #albert[cite zeilberger], and this is known to be a tight bound #albert[cite recent paper right?]. In contrast, Reed-Solomon (RS) codes are known to achieve MCA up to the Johnson bound #albert[cite papers], and, it was shown recently, in some cases (for fields of large characteristic), MCA is attained slightly above such bound #albert[cite]. The problem of whether RS codes achieve MCA (and list decodability) above Johnson bound, potentially all the way up to capacity, has recently received a great amount of attention and has undergone rapid development due to its practical and theoretical relevance #albert[cite, better codes, proximity prize, and the flurry of papers].

As we mentioned, modern code-based IOPPs rely on the MCA (or the weaker CA#footnote[The notion of MCA was introduced relatively recently in @whir. Before that, researchers and practitioners used the weaker notion of Correlated Agreement (CA).] property #albert[cite]) of their underlying codes in order to achieve soundness. Prior to that, before good enough MCA or plain CA results were known to hold, @deep proposed a technique called DEEP  (Domain Extending for Eliminating Pretenders), by which FRI #albert[cite] (the seminal code-based IOPP) achieved soundness without needing CA or MCA to hold. Instead, @deep only asked for the underlying code (an RS code), to have good list decodability bounds, which, as we mentioned, all codes satisfy up to the Johnson bound. 

#paragraph[The DEEP technique.] We explain the DEEP technique briefly. We focus on Reed-Solomon codes because they allow concretizing some otherwise slightly abstract concepts (namely, that of #emph[zero evader]). We note that the original DEEP paper @deep was taylored to RS codes, while our work applies to arbitrary linear codes. For the sake of intuition, we describe the DEEP technique as  an interactive protocol between a prover and a verifier, even though the actual relevant results establish a property of the code $cal(C)$, independently of any protocol built around it.



Similarly as above, the DEEP technique also analyses the number of elements $alpha in FF$ for which $u_1 + alpha dot u_2$ agrees with a codeword $c in cal(C)$ on a large set $S$, while $u_1, u_2$ do not. The element $alpha in FF$ is called a #emph[folding challenge], and in practice it is sent by a verifier. We say $alpha$ is MCA-bad if the previous scenario holds ($u_1+ alpha dot u_2$ agrees on a large set $S$ but $u_1, u_2$ not), and then we call $c$ an #emph[$alpha$-pretender]. Additionally, before $alpha$ is sampled, in the DEEP technique, the verifier sends a so-called   #emph[DEEP sample point] $z in FF$, to which the prover replies with $b_1, b_2 in FF$, supposedly the evaluations at $z$ of codewords $c_1, c_2$ (which we think of polynomials) that are $delta$-close to $u_1, u_2$, respectively.  

One can show (see @deep, Section @s:BEEP_fold) that in a typical IOPP including this DEEP sampling step,   soundness (more precisely, round-by-round knowledge soundness) follows by showing that, for most $z in FF$ and $alpha in FF$ there's negligibly many $alpha in FF$  such that 1) $alpha$ is MCA-bad; and 2) there is an $alpha$-pretender $c$ that, evaluated at $z$, equals $b_1 + alpha dot b_2$.  In @deep and in the present work #albert[what else should we cite], such bounds are obtained by  using only the list decodability of $cal(C)$, and not its MCA or CA (which may in any case not hold).

(Domain Extending for Eliminating Pretenders)

To the best of our understanding, the reason DEEP is not used in practice is because the soundness error bound $epsilon_(sans("DEEP"))$  obtained in @deep is too large for practical parameters. Concretely, @deep obtains 
#albert[Not clear what "the error bound" is of].    
$
epsilon_(sans("DEEP"))= max(2 dot L dot lr(( (codedim)/(|FF|) + epsilon  ))^(1/3), (4)/(epsilon^2 dot |FF|))
$
where $0<epsilon<1/3$ is a tunable parameter, and $L$ is the list size of the underlying code $cal(C)$ at radius $delta$. One can see that, for typical $codedim$ and $L$, and targeting $epsilon_(sans("DEEP")) ≤ 2^(-128)$, one needs $|FF|$ to be well above $2^800$, which for practical purposes is far from the standard $128$-$256$ bit fields. Indeed, from $4/epsilon^2 dot |FF| ≤ 2^(-128)$ we obtain $|FF| ≥ 2^130\/|L|$, and then, taking cubes, we additionally need $epsilon + codedim\/|FF| ≤ 2^(-384)/(8 dot L^3)$, which yield in particular that $epsilon ≤ 2^(-387)/(L^3)$ and so $|FF| ≥ 2^(904)/(L^3)$, while typical list sizes $L$ for $delta$ approaching the Johnson bound rarely exceeds $2^25$ (see @ex:interleaved_list) #albert[check this], and in any case the list size is also subject to the bound $codedim\/ |FF| ≤ 2^(-384)/(8 dot L^3)$. Further, in a wider protocol, $L$ appears as a linear factor in other error terms, which further limits the size $L$ one is able to tolerate.  


On the other hand, today we have practical MCA results for Reed-Solomon codes up to the Johnson bound #albert[cite], and for any linear code up to the 1.5 Johnson bound #albert[cite]. Concretely, #albert[cite] shows that for any RS code $cal(C)$ and any two words $u_1,u_2$, the fraction of MCA-bad elements $alpha in FF$ is #albert[fill in]
$
epsilon_(sans("RS-MCA")) ≤.
$

== Our contributions

#albert[mention our error is better than MCA]

In this work we provide a new soundness analysis of the DEEP technique after modifying the technique slightly. Concretely, the modification consists simply in making $numsamples$ DEEP sample evaluations, rather than only $1$, for a tunable parameter $numsamples$. We obtain the following improved error bound, for #emph[any linear code] $cal(C)$ of blockclength $blockclength$ and dimension $codedim$
$
epsilon_(sans("BEEP")) = max((|FF| dot L)^3/(delta dot blockclength +1)^2 dot (codedim/(|FF|))^numsamples , (delta dot blockclength + 1)/(|FF|) )
$
where $delta$ is an arbitrary proximity parameter (below the minimum distance of $cal(C)$) and $L$ is such that $cal(C)$ is $(delta,L)$-list decodable. 

#remark[General linear codes and zero evaders][
  For a non-RS code, "evaluation of a codeword $c$ at a point $z$" may not be well defined. For that purpose, we use the more general notion of a zero evader, see @s:zero_evaders, and then the factor $(codedim\/|FF|)^numsamples$ is replaced by the error of the evader.
]

#remark[Round-by-round knowledge soundness][
  
]

== Scratch intro notes

Additionally, @deep is taylored to $cal(C)$ a Reed-Solomon code, and the soundness results are not formulated in a way which is amenable to building a round-by-round sound protocol from them.
  
---

#albert[We also do affine folding like in the new Chiesa, Yogev and Zheng paper to get 1/q error]


  Greatly simplified analysis of affine folding (on a different setting though, i.e. the DEEP setting) 
  ---

  A consequence is that all typical code-based PCS's can be instantiated with an arbitrary linear code $cal(C)$ with proximity parameter up to the Johnson bound, after undergoing the aforementioned minor modification. 

  #albert[More consequences: we can do 128 bits of security with a 128 bit field, with any code]

  --

  "The proof basically shows that if there are many bad codewords corresponding to different folding challenges (consistent with the DEEP queries), then there’s many triples of codewords that are not colinear, and then the deep queries are zeros of some determinant-like nonzero polynomial associated to a triple"

  ---



  The fold error is about (δn + 3L)/|𝔽| instead of an MCA error with large polynomial factors or large constant or restrictive parameters #albert[From some conversation with Ulrich I think this may be a big deal (I haven't told him about this work though)]


#albert[Mention Lean]

== Related work

Affine folding, polygero, 

== Use of AI
#albert[Revise]  Most of this document was written without the use of AI, except for making small refactorings. Sections @s:BEEP_WHIR and @s:affine where initially drafted with AI and heavily edited by us afterward.

The novel results in this work were obtained through a long interactive process with an AI #albert[And the batched BEEP too?]. The Lean formalization of the results (concretely, of @?,@? and @?, see #albert[ref to repo]) was done by an AI and its statements were reviewed by us subsequently. Similarly, the experiments from Section @s:experiments were prepared with an AI and reviewed by us #albert[make sure this is the case].

== Acknowledgements

The second author was  affiliated at Nethermind during part of the preparation of this work. 

We thank Ulrich Haböck for insightful  discussions that helped improve this work. 


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


#paragraph[Interleaved codes] #albert[review (this was AI drafted)]
// [AI-added (claude-fable-5-2), 2026-11-16, at the author's request ("Add a version of Lemma 3.13 of Zook's preliminaries (about list sizes of interleaved codes) and then provide a numerical example for RS codes, for rate 1/2 and 1/8 and delta approaching Johnson. Be very brief"): the rest of this paragraph, i.e. the definition of the interleaved code, @l:interleaved_list and @ex:interleaved_list. Please review]
Given $k ≥ 1$, the #emph[$k$-interleaving] of $cal(C)$ is the code $interleavedcode(k) subset (FF^k)^blockclength$ whose codewords are the tuples $(c_1, dots, c_k)$ of codewords of $cal(C)$, seen as words of length $blockclength$ over the alphabet $FF^k$. Distances in $interleavedcode(k)$ are measured over this alphabet, so $hamming(interleavedcode(k)) = hamming(cal(C))$. If $cal(C)$ is $(delta, L)$-list decodable, then clearly $interleavedcode(k)$ is $(delta, L^k)$-list decodable. The next lemma gives a bound that does not depend on $k$.

#lemma[@GGR11, see @zook[Lemma 3.13]][
  Let $delta in [0, hamming(cal(C)))$ and assume $cal(C)$ is $(delta, L)$-list decodable. Let
  $
    b := ceil(delta / (hamming(cal(C)) - delta)), quad quad r := ceil(log_2 (hamming(cal(C))) / (hamming(cal(C)) - delta)).
  $
  Then, for every $k ≥ 1$, the code $interleavedcode(k)$ is $(delta, L_(equiv))$-list decodable with $L_(equiv) := binom(b+r, r) dot L^r$.
]<l:interleaved_list>

#example[Reed-Solomon codes close to the Johnson radius][
  Let $cal(C)$ be a Reed-Solomon code of rate $rho$, so that $hamming(cal(C)) ≥ 1 - rho$, and let $delta = 1 - sqrt(rho) - eta$ with $eta > 0$ small. By the Johnson bound we can take $L = floor(1 \/ (2 dot eta dot sqrt(rho)))$. As $eta arrow 0$ we have $delta \/ (hamming(cal(C)) - delta) arrow 1 \/ sqrt(rho)$ from below and $hamming(cal(C)) \/ (hamming(cal(C)) - delta) arrow 1 + 1 \/ sqrt(rho)$. Hence for $rho = 1\/2$ we get $b = r = 2$ (for all $eta < 0.042$) and $L_(equiv) = 6 dot L^2$, and for $rho = 1\/8$ we get $b = 3$, $r = 2$ (for all $eta < 0.063$) and $L_(equiv) = 10 dot L^2$:
  #align(center, table(
    columns: 5,
    align: center,
    stroke: none,
    table.hline(),
    table.header[$rho$][$eta$][$L$][$L_(equiv)$][$log_2 L_(equiv)$],
    table.hline(stroke: 0.5pt),
    [$1\/2$], [$0.02$], [$35$], [$7350$], [$12.8$],
    [$1\/2$], [$0.01$], [$70$], [$29400$], [$14.8$],
    [$1\/2$], [$0.001$], [$707$], [$2999094$], [$21.5$],
    [$1\/8$], [$0.02$], [$70$], [$49000$], [$15.6$],
    [$1\/8$], [$0.01$], [$141$], [$198810$], [$17.6$],
    [$1\/8$], [$0.001$], [$1414$], [$19993960$], [$24.3$],
    table.hline(),
  ))
  So @l:interleaved_list improves on $L^k$ as soon as $k ≥ 3$. We remark that below the Johnson radius one can do better: the Johnson bound only depends on $delta$ and on the relative distance of the code, hence it applies directly to $interleavedcode(k)$ and gives $L_(equiv) = L$. @l:interleaved_list is then of interest for codes and proximity parameters where the bound on $L$ does not come from the Johnson bound.
]<ex:interleaved_list>


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

== Pretender codewords and consistency

Let $FF$ be a finite field and let $cal(C) subset FF^blockclength$ be a linear code of blocklength $blockclength$ and dimension $codedim$, with $blockclength$ a power of two. Let $delta in (0,1)$ be a proximity parameter.

// [AI-edited (claude-fable-5-2), 2026-11-12, at the author's request: words are folded with two linear maps lambda_1, lambda_2 of alpha instead of the weights (1, alpha). Edited: the next paragraph; the MCA, MCA-bad, pretender and consistency definitions; the proofs of l:few_bad_points_on_line and l:colinear_zero; one sentence in the proof of t:main_thm. Please review]
#aiedit[We fix two linear maps $lambda_1, lambda_2: FF arrow FF$, so that $lambda_i (alpha) = a_i + alpha dot d_i$ for some $a_i, d_i in FF$, and we assume that $a_1 dot d_2 != a_2 dot d_1$. We use $lambda_1(alpha)$ and $lambda_2(alpha)$ as the weights when folding two words with a challenge $alpha in FF$. For example, $(lambda_1(alpha), lambda_2(alpha))$ can be $(1, alpha)$, or $(1-alpha, alpha)$ as in Section @s:BEEP_fold. The assumption $a_1 dot d_2 != a_2 dot d_1$ guarantees that the vectors $(lambda_1(alpha), lambda_2(alpha))$ and $(lambda_1(alpha'), lambda_2(alpha'))$ are linearly independent for all distinct $alpha, alpha' in FF$.]


 Let $u_1, u_2 in FF^blockclength$ be two words. Given $S subset [blockclength]$, we say $(u_1,u_2)$ has #emph[Correlated Agreement with $C$ over $S$] if there exist codewords $c_1,c_2 in cal(C)$ such that $u_1$ agrees with $c_1$ on $S$ and $u_2$ agrees with $c_2$ on $S$. 



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
    φ_z (c) = aiedit(λ_1 (α) ·) 𝐛_(1) + aiedit(λ_2 (α)) · 𝐛_(2).
  $
  When $α$ is an MCA-bad element and there exists an $α$-pretender $c in cal(C)$ such that $(α, c)$ is consistent with  $(z, vb(b)_(1), vb(b)_(2))$, then we say that $α$ is a _DEEP-MCA-bad element_ with respect to $z,vb(b)_(1), vb(b)_(2)$ and $u_1, u_2$. 

  When clear from the context, we omit referring to $z, vb(b)_(1), vb(b)_(2), u_1, u_2$ when speaking of DEEP-MCA-bad elements.
]

== Most out of domain samples admit few DEEP-MCA-bad challenges<s:main_thm>

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

#remark[Using @t:main_thm to replace the MCA error with the list decodability size in code-based PCS][Looking ahead, we will use this result as follows: before performing the fold of two words during a code-based PCS, we have the verifier sample an element $z in cal(Z)$, and the prover replies with $vb(b)_1, vb(b)_2 in FF^numsamples$, supposedly the evaluations on $evalmap_z$ of the two words (which are supposedly codewords). Now, due to @t:main_thm, with high probability over $z$, there are very few folding challenges $alpha in FF$ that result in a failure of the MCA property and which are consistent with $(z, vb(b)_1, vb(b)_2)$. Hence, at this point we can fold as usual, and obtain knowledge soundness even if  the code $cal(C)$ is not known to possess (or is known to not possess) MCA at the proximity parameter $delta$ used by the PCS. We formalize this intuition in Section @s:BEEP_fold.]<r:using_main_thm>


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
 Let $u_1,u_2 in FF^blockclength$ be two words, and let $lmap in linfuns$. Let $A_(lmap)^(sans("pret")) subset FF$ be the set of all field elements $alpha in FF$ that are MCA-bad and such that the codeword $lmap(alpha) = c_(lmap,1) + alpha dot c_(lmap, 2) in cal(C)$ is an $alpha$-pretender with respect to $u_1,u_2$.   Then
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
  
  + *Round 1 (DEEP sampling).* The verifier samples and sends uniformly at random $z ∈ 𝒵$. The prover replies with two vectors $𝐛_1, 𝐛_2 ∈ 𝔽^m$, supposedly 
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
  kappa_2 &:= (delta dot blockclength +1 + 2dot L_(interleavedcode(2)))/ (|FF|) \
  kappa_3 &:= (L)/(|FF|)
  $
]<t:beep_soundness>

We defer the proof of @t:beep_soundness to Appendix @s:proof_rbr_knowledge, and only provide a brief outline of it here. The proof follows arguments similar to those in @zook@BCFW25, with the main difference being that @c:BEEP has one initial extra round (the DEEP sampling round). For this round, it suffices to let the knowledge state function become $1$ iff $|A_z| ≥ delta dot blockclength +1$ or if the input triple $(inp,oracle, kswit)$ is valid, i.e. belongs to $cal(R)_(interleavedcode(C))^(delta)$. The main result @t:main_thm from @s:better_pretenders then shows that a flip from state $0$ to $1$ occurs with probability at most $kappa_1$. 

After the first round, if the state is $0$, we have $|A_z| < delta dot blockclength+2$. Because of this, at this point, we are in a setting where our two words $f_(1*), f_(2*)$ effectively meet an MCA-like property. In this scenario, the arguments from @zook@BCFW25 apply. In particular, the extractor uses erasure decoding, leveraging the MCA-like property that @t:main_thm provides. As with @zook@BCFW25, this means that the code $cal(C)$ does not require an efficient decoder.



== BEEP-WHIR and BEEP-Ligerito<s:BEEP_WHIR>

#albert[Add a BEEP-Basefold version too]

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


= BEEP with affine folding for Reed-Solomon codes<s:affine>

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
We now state and prove the affine version of @t:main_thm. We refer to @r:using_main_thm and to @r:affine_pairs below for explanations on how to use it inside a code-based PCS (see also Section @s:IOR).

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

  
  Let $V subset chal$ be the set of all  $alpha in chal$ such that $lmap(alpha) in Cplus$. Note that $chal$ is a linear space of dimension two over $FF$. We claim that either $V = chal$ or $|V| ≤ |FF|$. If $V$ is empty there is nothing to prove, so assume that $V$ contains some $alpha_0$. Let $W subset chal$ be the set of all $beta in chal$ such that $beta dot G_lmap in Cplus$. Since $Cplus$ is an $FF$-vector space, $W$ is an $FF$-vector subspace of $chal$. Now, since $lmap(alpha_0) in Cplus$, an element $alpha in chal$ belongs to $V$ if and only if $(alpha - alpha_0) dot G_lmap in Cplus$, i.e. if and only if $alpha - alpha_0 in W$. It follows that $V = {alpha_0 + beta | beta in W}$, and so $|V| = |W|$. Hence either $W$ has dimension at most $1$ and $|V| ≤ |FF|$, or $W = chal$ and then $V = chal$.

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
  Indeed, following the proof of @l:colinear_zero, let $vb(b)' := d_1 dot vb(b)_1 + d_2 dot vb(b)_2$. By the consistency assumption, $evalmap_z (v_i) - evalmap_z (v_1) = (evalmap_z (alpha_i) - evalmap_z (alpha_1)) emul vb(b)'$ for both $i = 2, 3$. Now the proof follows as in @l:colinear_zero, using the linearity of $evalmap_vb(z)$ and the definition of $U((alpha_i, v_i)_(i in [3]))$ #albert[check].

  Next, let $T_vb(z)$ be defined in the exact same way as in Section @s:better_pretenders, using  triples of tuples from $chal times Cplus$ instead of $FF times cal(C)$, and, of course, using the affine versions of the definitions of $alpha$-pretenders and consistency. Then the same proof as that of  @l:third_moment_bound yields
  $
    |A_vb(z)| dot (|A_vb(z)| - 1) dot (|A_vb(z)| - N) ≤ |T_vb(z)|.
  $
  It suffices to use @l:few_bad_points_on_line_0 with the bound $|A_lmap^(sans("pret"))|≤ N$ instead of the bound $|A_lmap^(sans("pret"))|≤ delta dot blockclength +1$ given by @l:few_bad_points_on_line.
  
  Finally, let $P subset chal times Cplus$ be the set of all tuples $(alpha, c)$ such that $c$ is an $alpha$-pretender. Since $Cplus$ is $(delta, L)$-list decodable, $|P| ≤ |chal| dot L = |FF|^2 dot L$. Let $(alpha_i, c_i)_(i in [3]) in P^3$ be such that $U((alpha_i, c_i)_(i in [3])) != 0$. Then by definition of $T_vb(z)$ this is a nonzero polynomial of degree at most $codedim + 1$, and hence there are at most $((codedim + 1) \/ |FF|)^numsamples dot |FF|^numsamples$ elements $vb(z) in FF^numsamples$ such that the triple belongs to $T_vb(z)$. Using an argument similar to the proof of @t:main_thm ,  and using $|chal| = FF^2$, we have
  $
    sum_(vb(z) in FF^numsamples) |T_vb(z)| ≤ (|FF|^2 dot L)^3 dot ((codedim + 1) \/ |FF|)^numsamples dot |FF|^numsamples,
  $
  Now the theorem follows as in @t:main_thm #albert[check].
]



#remark[Correlated Agreement with $interleavedcode(2)$ instead of $Cpair$][
  #albert[review] In @d:affine_pretender we ask for Correlated Agreement with $Cpair$, and not with $interleavedcode(2)$, i.e. with pairs of codewords of $cal(C)$ as in Section @s:better_pretenders. The set $Cpair$ strictly contains $interleavedcode(2)$, and so, when a codeword $c in Cplus$ agrees with the $alpha$-fold of two words $u_1, u_2$ on a subset of $[blockclength]$ of size at least $(1-delta) dot blockclength$, and $c$ is not an $alpha$-pretender, we obtain a pair from $Cpair$ that is close to $(u_1, u_2)$, and this pair need not belong to $interleavedcode(2)$. Here and below, we say that a pair of codewords $(c_1, c_2)$ is #emph[close] to a pair of words $(w_1, w_2)$ if there is a subset of $[blockclength]$ of size at least $(1-delta) dot blockclength - 1$  where $w_1$ agrees with $c_1$ and $w_2$ agrees with $c_2$.

  In a bigger protocol, for example when aiming to build an IOR from $cal(R)_(interleavedcode(2))$ to $cal(R)_cal(C)$ using affine folds, one would instead prefer to obtain a pair from $cal(R)_(interleavedcode(2))$ instead of $Cpair$. This can be ensured  using the methods described in @CWYZ26[Section 5]. To do so, one can have an initial communication round where the verifier samples an additional challenge $xi in FF$, and replaces the words $u_1$ and $u_2$ by $u'_1:=u_1$  and $u'_2:=u_2 + xi dot u_1$, and then proceeds to perform the DEEP sampling and the affine folding with these two words instead of $u_1$ and $u_2$. One also performs analogous linear changes on the witness and any linear constraints placed on the witness.

  The reason this works is the following. Let $Lambda$ be the set of all pairs of codewords of $Cplus$ that are close to the original words $(u_1, u_2)$. Note that $Lambda$ does not depend on $xi$, since $u_1, u_2$ are fixed before $xi$ is sampled. On the other hand, the pairs of codewords of $Cplus$ that are close to the new words $(u'_1, u'_2)$ do depend on $xi$: for each $xi in FF$, they are exactly the pairs $(c_1, c_2 + xi dot c_1)$ with $(c_1, c_2) in Lambda$. 

  Now let $(c_1, c_2) in Lambda$. If $(c_1, c_2)$ belongs to $interleavedcode(2)$, then so does $(c_1, c_2 + xi dot c_1)$, for all $xi in FF$. Otherwise we claim that $(c_1, c_2 + xi dot c_1)$ belongs to $Cpair$ for at most one $xi in FF$. Indeed, let $s_1, s_2 in FF$ be the leading coefficients $c_1$ and $c_2$, which are not both zero. By definition of $Cpair$, the pair $(c_1, c_2 + xi dot c_1)$ belongs to $Cpair$ if and only if $d_1 dot s_1 + d_2 dot (s_2 + xi dot s_1) = 0$. Here we assume that $d_2 != 0$ (this is the case for the folding maps $(lambda_1, lambda_2)=(1, alpha)$ and $(1-alpha, alpha)$). Then this equation has at most one solution $xi$, proving the claim. 

  Hence there are at most $|Lambda|$ elements $xi in FF$ for which some pair from $Cpair$ that is close to the new words does not belong to $interleavedcode(2)$. . For the rest of $xi in FF$, every pair $(c'_1, c'_2)$ from $Cpair$ that is close to $(u'_1, u'_2)$ belongs to $interleavedcode(2)$. From such a pair we obtain $(c'_1, c'_2 - xi dot c'_1) in interleavedcode(2)$, which is close to $(u_1, u_2)$. Note that $|Lambda|$ is bounded by the list size of  $(Cplus)^(equiv 2)$ at distance $delta + 1\/blockclength$.
]<r:affine_pairs>

= Instantiation and Experiments <s:experiments>
// [AI-drafted in the author's register (claude-fable-5-2), 2026-11-16, at the author's request ("Let's write the instantiation and experiment section. I want something minimal that fits in two pages": a comparison of runtimes and proof sizes of Ligerito and BEEP-Ligerito for 2^15 to 2^23 field elements at 100 bits over GF(2^128) and at rate 1/2; the same at 128 bits; and a table with the error bounds of the first two rounds of the BEEP IOR and the number of queries, with the fold round of Ligerito next to them, at 128 bits over a field of 2^128 elements): this whole section, up to the include of batch.typ. Every number and every table row is read from tables/minimal.json, which scripts/minimal_tables.py writes from the run beep-ligerito/bench_results/three-way-minimal-20261116-ac2 (its cells: beep-ligerito/scripts/cells_minimal.txt) and from the exact arithmetic of beep-ligerito/scripts/beep_params.py. A number that the script did not write prints as a highlighted "pending". The code is beep-ligerito/flock (Flock's branch affine-fold-f128 with crates/flock-core/src/pcs/ligerito/beep.rs added); the baseline "Ligerito over GF(2^128)" is `mca_ladder_no_first_sample_at` of that file, written for this section (BEEP-Ligerito with no samples in its fold rounds and nothing else changed; its accounting is ours, see beep-ligerito/README.md). Two readings of the request that the author should check: (1) at 128 bits BEEP-Ligerito stays over GF(2^128), with grinding on its fold challenges, and Ligerito is Flock's, with fold challenges in GF(2^256) (the request said "using a larger field for BEEP-Ligerito"; this code has no BEEP prover with challenges in GF(2^256)); (2) "n = 2^15 to 2^23" is read as the number of field elements of the message, and the block length of the first code (the n of the paper) is a column of the first table. Research, unaudited. Please review]
#aiedit[
#let expdata = json("tables/minimal.json")
#let num(key) = if key in expdata.numbers { eval(expdata.numbers.at(key), mode: "markup") } else { highlight[pending] }
#let exprows(name) = {
  let rows = expdata.tables.at(name, default: ())
  if rows.len() == 0 { (table.cell(colspan: 2, highlight[pending]),) } else {
    rows.map(r => r.map(c => eval(c, mode: "markup"))).flatten()
  }
}
#let exptable(columns, header, name, size: 7.5pt) = text(size: size, table(
  columns: columns, stroke: none, align: center + horizon, inset: (x: 3.5pt, top: 0.7pt, bottom: 1.5pt),
  table.hline(stroke: 0.6pt), ..header, table.hline(stroke: 0.4pt), ..exprows(name), table.hline(stroke: 0.6pt),
))

We instantiate @c:BEEP_codeswitch with Reed-Solomon codes over $"GF"(2^128)$, and we compare the resulting PCS, "BEEP-Ligerito", with Ligerito @ligerito. Our code (research code, not audited), the raw outputs and the scripts that write every number below are in our repository #albert[ref to repo].

#paragraph[BEEP-Ligerito.] We start from the implementation of Ligerito in Flock @flock. A message of $k dot codedim$ elements from $"GF"(2^128)$ is arranged in $k$ rows, each encoded with a Reed-Solomon code $cal(C)$ of rate $rho = 1\/2$. The rows are folded with $log k$ executions of @c:BEEP, and the folded message is committed with a code of smaller rate and queried, as in @c:BEEP_codeswitch. This is repeated until the message is short. As zero evader we take $numsamples$ independent samples of the multilinear evader, with error $epsilon_"evader" = (log_2 e \/ |FF|)^numsamples$ on messages with $e$ entries. We take $delta = 1 - sqrt(rho) - eta$ for a small "slack" $eta > 0$, so that $cal(C)$ and its interleavings are $(delta, L)$-list decodable with $L = floor(1 \/ (2 dot eta dot sqrt(rho)))$ (see @ex:interleaved_list).

#paragraph[The error of a fold.] The proof of @t:beep_soundness goes through with any integer $t >= delta dot blockclength + 2$ in place of $delta dot blockclength + 2$ (this threshold of @t:main_thm only appears in the analysis). The errors of the first two rounds of @c:BEEP are then
$
kappa_1(t) = ((|FF| dot L)^3 dot epsilon_"evader") / (t dot (t-1) dot (t - delta dot blockclength - 1)), quad quad kappa_2(t) = (t - 1 + 2 dot L) / (|FF|).
$
We count $g$ bits of proof of work ("grinding") on a challenge as $g$ bits of security, as it is usual in practice @whir @flock. For a target of $lambda$ bits we take the least $t$ with $kappa_1(t) <= 2^(-lambda)$, and the $numsamples$ for which $kappa_2(t)$ then needs the least grinding.

@tab:errors shows these errors for $lambda = 128$, next to the error of a fold round of Ligerito with the MCA bound that Flock uses @flock[Appendix C.3], i.e. that of @BCHKS25[Theorem 4.6] times $k\/2$ (a union bound over pairs of rows), plus the term $2 dot L \/ |FF|$ of $kappa_2$.

#figure(
  exptable(10,
    (table.cell(colspan: 3)[first code], table.cell(colspan: 3)[Ligerito (fold with MCA)], table.cell(colspan: 4)[BEEP-Ligerito, $eta = #num("eta:beep")$],
     [size], [$k$], [$blockclength$], [fold, $eta = #num("eta:lig")$], [fold, $eta = #num("eta:beep")$], [queries, $eta = #num("eta:lig")$], [$numsamples$], [round 1], [round 2], [queries]),
    "errors"),
  caption: [Bits of security ($-log_2$ of the error) of the first fold round before grinding, over a field with $2^128$ elements. A message of the given size has $k$ rows, encoded at rate $1\/2$ with block length $blockclength$. "Round 1", "round 2": $kappa_1(t)$, $kappa_2(t)$. "Queries": the least $Q$ with $(1-delta)^Q <= 2^(-112)$ (#num("params:qgrind") bits of grinding).],
) <tab:errors>

The second round of BEEP has #num("err:beep2") bits, so it reaches $128$ bits with #num("err:beep-grind") bits of grinding, and its small $eta$ gives #num("err:q-beep") queries in place of #num("err:q-lig"). With MCA, a fold round has #num("err:lig02") bits at $eta = #num("eta:lig")$ and #num("err:lig001") bits at $eta = #num("eta:beep")$. Reaching $128$ bits at $eta = #num("eta:lig")$ would take #num("err:lig-grind") bits of grinding per fold challenge, or a larger field: Flock's fold challenges are in $"GF"(2^256)$.

#paragraph[Measurements.] We open commitments to messages of #num("sizes:first") to #num("sizes:last") field elements, and we compare three variants. _Ligerito (Flock)_ is Flock's Ligerito as it ships, with $eta = #num("eta:lig")$. At both security levels it samples its fold challenges from $"GF"(2^256)$, and it commits to each folded message as two messages over $"GF"(2^128)$. _BEEP-Ligerito_ has all its challenges in $"GF"(2^128)$, $eta = #num("eta:beep")$, and $numsamples$ and $t$ as above. It has Flock's number of rows per level, and the rates $1\/2$, $1\/8$, $1\/32$, $1\/128$, with which its codewords are as long as Flock's at every level (its folded messages are shorter, since they stay over $"GF"(2^128)$). _Ligerito over $"GF"(2^128)$_ is ours: it is BEEP-Ligerito without the samples, analyzed as Ligerito, i.e. with $eta = #num("eta:lig")$ and with grinding on its fold challenges for the error of @tab:errors. We run it at $100$ bits only.

@tab:measured has the medians of #num("run:reps") runs on an #num("run:cpu") laptop (#num("run:memory-gb") GB, #num("run:threads") threads), with the proofs of work at their expected cost.

#figure(
  stack(dir: ttb, spacing: 3pt,
    exptable(11,
      (table.cell(colspan: 2)[$lambda = 100$], table.cell(colspan: 3)[Ligerito (Flock)], table.cell(colspan: 3)[Ligerito over $"GF"(2^128)$], table.cell(colspan: 3)[BEEP-Ligerito],
       [size], [commit], [proof], [prove], [verify], [proof], [prove], [verify], [proof], [prove], [verify]),
      "bits100"),
    exptable(8,
      (table.cell(colspan: 2)[$lambda = 128$], table.cell(colspan: 3)[Ligerito (Flock)], table.cell(colspan: 3)[BEEP-Ligerito],
       [size], [commit], [proof], [prove], [verify], [proof], [prove], [verify]),
      "bits128"),
  ),
  caption: [Proof sizes (KiB) and times (ms) at $100$ (top) and $128$ (bottom) bits of security. "Prove" is the opening, without the commitment ("commit"), which all the variants share.],
) <tab:measured>

#paragraph[Results.] At $100$ bits BEEP-Ligerito makes $numsamples = #num("params:m-100")$ samples per fold round and needs no grinding on its fold challenges, while Ligerito over $"GF"(2^128)$ needs #num("100:mca-fold-grind") bits at its first level. The proofs of BEEP-Ligerito are #num("100:size-saving-pct")~% smaller, since it makes fewer queries. Its prover takes #num("100:prove-ratio") times as long: the samples cost time (the ratio is #num("100:nopow-ratio") without proofs of work), and they save the grinding of the fold challenges. With the commitment the ratio is #num("100:total-ratio"). Its verifier takes #num("100:verify-ratio") times as long.

At $128$ bits BEEP-Ligerito stays over $"GF"(2^128)$, with $numsamples = #num("params:m-128")$ and the fold grinding of @tab:errors. Its proofs are #num("128:size-saving-pct")~% smaller than those of Ligerito (Flock): it makes fewer queries, since its $eta$ and its rates after the first level are smaller. Its prover takes #num("128:prove-ratio") times as long (#num("128:pow-share-pct")~% of its time is proofs of work), and its verifier #num("128:verify-ratio") times.

We stress that Ligerito (Flock) and BEEP-Ligerito differ in their levels and run different provers, and it is unclear to us whether these are at a comparable level of optimization.
]

#include "batch.typ"

#bibliography("bibliography.bib", style: "ieee")

#counter(heading).update(0)
#set heading(numbering: "A.1", supplement: [Appendix])


= Proof of completeness and round-by-round knowledge soundness of the BEEP-IOR  <s:proof_rbr_knowledge>
#proof[
 We prove @t:beep_soundness. Let $Pi$ denote @c:BEEP. In our formalization of IORs (Section @s:IOR), every round starts with the prover sending a message, and then the verifier replies with a challenge. Since, as described, Rounds 1 and 3 of @c:BEEP start off with a verifier challenge, we modify $Pi$ so that the prover sends  empty messages at the beginning of those rounds. 

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


