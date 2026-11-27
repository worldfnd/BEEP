#import "layout.typ": *
#import "environments.typ": *

#show: trivial.init
#show: template.with(
  title: "BEEP: IOPPs from List Decoding with Better Elimination of Pretenders",
  authors: (
    (
      name: "Remco Bloemen",
      affiliation: "World Foundation",
      email: "remco@world.org",
    ),
    (
      name: "Albert Garreta",
      affiliation: [World Foundation#footnote[The second author was affiliated with Nethermind Research during part of the preparation of this work.]],
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
#set enum(indent: 0pt) 

// Define functions:
#let submission-mode = true 

#let secretsection(body) = if submission-mode {} else {body}

#let show-comments = if submission-mode {false} else {true}
#let show-ai-edits = if submission-mode {false} else {true}   // set to false to remove this color
#let aiedit(body) = if show-ai-edits { text(fill: maroon, body) } else { body }
#let comment(author, color) = body => if show-comments {
  text(fill: color)[*\[#author:* #body*\]*]
}


#let albert = comment("Albert", purple)
#let albert-postponable = comment("Albert (postponable)", gray)
#let remco  = comment("Remco", blue)
#let todo   = comment("TODO", orange)



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

#let expdata = json("tables/tables128.json")
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

// Abstract 
#abstract[
  
  We present an improved soundness analysis of the DEEP technique for linear codes @deep (after a minor modification), which, unlike its predecessor, results in negligible error bounds for   parameters typically used in practice. 
  The modification consists simply in performing $m$ DEEP samples, instead of one. The resulting  DEEP sampling error decreases exponentially with $m$, and in practice $m=2$--$5$ makes it tiny. The subsequent folding error is of $(delta dot n +1)\/|FF|$, for $delta$ a proximity parameter and $n$ the code length.
  
  We  modify typical code-based IOPPs with this technique, such as WHIR, Ligerito, Basefold, etc. @whir @ligerito@basefold. As a result, we obtain code-based IOPPs that only require list decodability of the underlying codes, instead of Mutual Correlated Agreement (MCA), with smaller soundness errors than their counterparts. 
  
  Since it does not rely on MCA for its soundness, this improved DEEP technique allows to use #emph[arbitrary linear codes] in IOPPs with $delta$ up to the Johnson bound. Additionally, this opens the door to using  codes (e.g. perhaps Reed-Solomon codes) with $delta$ beyond the Johnson bound, assuming the code is $delta$-list decodable, even if it does not have the $delta$-MCA property. 

  Finally, we also provide an #emph[affine] version of our improved DEEP analysis, where the folding challenges are affine polynomials instead of field elements, following @polygero@CWYZ26. We provide a simple proof showing that, after the DEEP samples are done, the folding error with affine folding challenges is $2\/|FF|$,  #aiedit[which is smaller than the affine-MCA error  from @CWYZ26]. 
]

// Table of contents
#show outline.entry: set text(fill: linkcolor)
#outline(depth: 3) 

// Rest of paper


#albert[Todos: Review lean,  overall pass, review references, High arity section review,   Review last steps of affine proof
]

= Introduction

  

 Many efficient proof systems have, at their core, a  protocol for testing proximity to linear codes @whir@zook, called IOPP (or PCS). The soundness of modern such IOPPs relies on the underlying codes satisfying the so-called #emph[$delta$-Mutual Correlated Agreement (MCA) property] @whir, usually for a proximity parameter $delta$ as large as possible. It is relatively intricate to prove that a code has  MCA for  parameters $delta$ and error bounds suitable for practical purposes. 
 
  Prior to @BCIKS20@whir, before good enough MCA results were known to hold, @deep proposed a technique called DEEP  (Domain Extending for Eliminating Pretenders), by which FRI #aiedit[@fri] (the seminal  IOPP) achieved soundness without needing  MCA (or the weaker plain Correlated Agreement (CA) @BCIKS20) to hold. Instead, @deep only asked for the underlying code  to have good #emph[list decodability]  bounds.   Arguably, list decodability is 
   a property of codes that is easier to establish than MCA, and for which, in some sense, more and more attractive bounds are known to hold (see below). However, as we will see, the IOPP from @deep proves an error bound that is 
    too large for practical applications. 
    
     


 

 #paragraph[List decodability and MCA.] A code $cal(C)$ with blocklength $blockclength$ and dimension $codedim$ is  #emph[$(delta, L)$-list decodable] if for any word $u in FF^blockclength$ there are at most $L$ codewords from $cal(C)$ at relative Hamming distance $≤ delta$ from $u$. The code $cal(C)$  satisfies #emph[$delta$-MCA] if, for any two words $u_1, u_2 in FF^blockclength$, for almost all $alpha in FF$, if $u_1+ alpha dot u_2$ agrees with a codeword $c$ from $cal(C)$ on a _large_ set $S$ (concretely $|S|≥ (1-delta) dot blockclength$), then both $u_1$ and $u_2$ agree as well with codewords from $cal(C)$ on $S$.  
 


It is known that all codes are $(delta, L)$-list decodable for $delta$ approaching the #emph[Johnson bound]. Precisely, for $delta = 1-sqrt(1 - hamming(cal(C))) - eta$, where $hamming(cal(C))$ is the relative minimum distance of $cal(C)$ and $eta >0$ is small, any linear code $cal(C)$ is $(delta, L)$-list decodable with $L = 1\/(2dot eta dot sqrt(1 - hamming(cal(C))))$ #aiedit[@Joh62 (see e.g. @deep[Theorem 20]).] On the other hand,  linear codes in general are only known to have MCA up to the so-called 1.5 Johnson bound $1-(1-hamming(cal(C)))^(1\/3)$ @GKL24 @Zei26 @BCGM25, and this is known to be a tight bound #aiedit[@KTZ26 (see also @Man26 and @deep[Lemma 22])]. In contrast, Reed-Solomon (RS) codes achieve MCA up to the Johnson bound #aiedit[@BCIKS20 @Hab25 @BCHKS25]. For MCA, all errors we are aware of depend linearly on $blockclength dot sans("poly")(eta^(-1))$, where $eta$ is the additive distance to the exact Johnson bound. This is acceptable for practical purposes, but can sometimes become the "bottleneck error" (the largest error) in a proof system,  and in some occassions it forces to either use larger fields, more grinding, or a smaller proximity parameter $delta$ than one would hope for. Indeed, some deployed proof systems set $delta$ up to the Unique Decoding Radius (smaller than Johnson's), for which smaller error bounds are known. As we discuss later, recently @polygero@CWYZ26 proposed using low degree polynomials as folding challenges, so as to reduce the MCA error. 

It was shown recently that in fields of large characteristic and for adequate parameters, RS codes attain  MCA  above the Johnson  bound  #aiedit[@DKT26 @Jer26]. In fact, the problem of whether RS codes achieve MCA (and list decodability) above Johnson bound, potentially all the way up to capacity, has recently received a great amount of attention and has undergone rapid development due to its practical and theoretical relevance#aiedit[, see the Proximity Prize @proximityprize (and #link("https://better.codes")[better.codes]), the survey @ABF26, and for example @CS25 @DG25 @BCHKS25 @GG25 @BCPZZ26 @Jer26 @Gab26 @DKT26 @DKTZ26 @Jo26].  



 
// There are examples of codes having good list decodability bounds, but not good MCA bounds, see  @Man26[Theorem 3], @KTZ26,  @deep[Lemma 22]. Conversely, @Man26[Theorem 4] provides examples of codes with good MCA bounds but superpolynomially large lists #albert-postponable[wow check this].


// As we mentioned, modern code-based IOPPs rely on the MCA (or the weaker CA#footnote[The notion of MCA was introduced relatively recently in @whir. Before that, researchers and practitioners used the weaker notion of Correlated Agreement (CA).] property #aiedit[@BCIKS20]) of their underlying codes in order to achieve soundness. 

#paragraph[The DEEP technique.] We explain the DEEP technique briefly. We focus on Reed-Solomon codes because they allow concretizing some otherwise slightly abstract concepts (namely, that of #emph[zero evader]). We note that the DEEP technique also applies to arbitrary linear codes, and so does our work. For the sake of intuition, we describe the DEEP approach as  an interactive protocol between a prover and a verifier, even though the actual relevant results establish a property of the code $cal(C)$, independently of any protocol built around it.



Similarly as above, the DEEP technique also analyses the number of elements $alpha in FF$ for which, given $u_1, u_2 in FF^blockclength$, the #emph[folded word] $u_1 + alpha dot u_2 in FF^blockclength$ agrees with a codeword $c in cal(C)$ on a large set $S$, while $u_1, u_2$ do not. The element $alpha in FF$ is called a #emph[folding challenge], and in practice it is sent by a verifier. We say $alpha$ is _MCA-bad_ if the previous scenario holds (i.e. $u_1+ alpha dot u_2$ agrees on a large set $S$ but $u_1, u_2$ not), and in this case we call $c$ an #emph[$alpha$-pretender]. 

In the DEEP approach @deep, before $alpha$ is sampled, the verifier sends a so-called   #emph[DEEP sample point] $z in FF$. The  prover then replies with $b_1, b_2 in FF$, which are supposedly the evaluations at $z$ of codewords $c_1, c_2$ (which we think of as polynomials) that are $delta$-close to $u_1, u_2$, respectively.  The verifier then responds with the folding challenge $alpha$, and the  prover and verifier add the constraint (to be proved in further steps of the protocol) that a codeword  $c$ close to the folded word $u_1 + alpha dot u_2$ satisfies $c(z) = b_1 + alpha dot b_2$, where $c(z)$ is the evaluation of $c$ at $z$.  The  hope is that the number of $alpha$-pretenders $c$ such that $c(z) = b_1 + alpha dot b_2$ is much lower and easier to bound than the number of raw $alpha$-pretenders.

Recapping, one can show (see our Section @s:BEEP_fold or @deep) that in a typical IOPP including this DEEP sampling step,   (round-by-round) knowledge soundness follows from the following property: for most $z in FF$, for any prover answer $b_1, b_2 in FF$, there are negligibly many $alpha in FF$  such that: 1) $alpha$ is MCA-bad; and 2) there is an $alpha$-pretender $c in cal(C)$ that, evaluated at $z$, equals $b_1 + alpha dot b_2$.  In @deep and in the present work, such a bound on these $alpha$'s is obtained by  using only the list decodability of $cal(C)$, and not its MCA or CA (which may in any case not hold). 

We are not aware of any other results of this kind, even though plenty of prior work uses evaluations at random points (called #emph[Out Of Domain (OOD)] samples) to pin  words to a single close codeword. Even so, these works rely on CA or MCA to obtain soundness of their folding step, and use this pinning phenomena to obtain soundness not of the folding step  but of other protocol steps, e.g. code-switching in @whir, see  @stir@whir@BCFW25@zook@deepfold etc.

// #remark[DEEP evaluations and OOD evaluations][
  // Above, we deliberately distinguished between DEEP sampling and OOD sampling. As we mentioned, we understand the latter as the technique by which a word is pinned to a single close codeword by means of evaluating the word at a random point. By DEEP sampling we refer to a technique by which evaluations of the two halves $u_1, u_2$ of a word $u$ are used to obtain an MCA-like property when folding these two halves.
// ]<r:deep_ood>


To the best of our understanding, the reason the above DEEP approach  is not used in practice  is because the soundness error bound $epsilon_(sans("DEEP"))$  obtained in @deep is too large for practical parameters. Concretely, @deep[Theorem 3] shows the following. Let $0<epsilon<1/3$ be a tunable parameter. Assume that $u_1, u_2$ do not agree with two codewords of $cal(C)$ on a common set of size $(1-delta-epsilon) dot blockclength$. Then the probability, over both $z$ and $alpha$, that some codeword $c$ at relative distance less than $delta$ from $u_1 + alpha dot u_2$ satisfies $c(z) = b_1 + alpha dot b_2$, is less than
$
epsilon_(sans("DEEP"))= max(2 dot L dot lr(( (codedim)/(|FF|) + epsilon  ))^(1/3), (4)/(epsilon^2 dot |FF|))
$<e:original_deep_error>
where   $L$ is the list size of the underlying code $cal(C)$ at radius $delta$. One can see that, for typical $codedim$ and $L$, and targeting $epsilon_(sans("DEEP")) ≤ 2^(-128)$, one needs $|FF|$ to be  above $2^900$, which for practical purposes is far from the standard $128$-$256$ bit fields. Indeed, from #aiedit[$4\/(epsilon^2 dot |FF|) ≤ 2^(-128)$ we obtain $|FF| ≥ 2^130\/epsilon^2$], and then, taking cubes, we additionally need $epsilon + codedim\/|FF| ≤ 2^(-384)/(8 dot L^3)$, which yield in particular that $epsilon ≤ 2^(-387)/(L^3)$ and so #aiedit[$|FF| ≥ 2^130\/epsilon^2 ≥ 2^(904) dot L^6$]. 

In @r:original_deep_multiple_samples we discuss why increasing the number of samples and making a naive adaptation of the original DEEP proof #aiedit[@deep[Theorem 3]] still yields essentially the same impractical error (still requiring $|FF| ≥ 2^(904) dot L^6$).


#paragraph[MCA.] On the other hand, #aiedit[as we mentioned,] today we have practical MCA results for Reed-Solomon codes up to the Johnson bound, and for any linear code up to the 1.5 Johnson bound. 

#aiedit[Recently, the error bound of @BCHKS25[Theorem 4.6] for RS codes was improved in @DKT26[Theorem 4.4]. In @DKT26 it is shown that, for an RS code of rate $rho$, any $eta > 0$ and $delta <= 1 - sqrt(rho_-) - eta$, where $rho_- := rho - 1\/blockclength$, the fraction of MCA-bad elements $alpha in FF$ is less than]
#aiedit[$
epsilon'_(sans("RS-MCA")) := 1/(|FF|) dot (8 dot (r_- + 1\/2)^3)/(3 dot rho_-) dot blockclength,
$<e:mca_error>]
#aiedit[where $r_- := max(ceil(sqrt(rho_-)\/(2 dot eta)), 3)$. For practical rates (ranging from, say $1\/2$ to $1\/64$) and a small $eta$ (say $eta$ between $0.01$ and $0.001$) this is roughly $codedim\/(3 dot sqrt(rho) dot eta^3 dot |FF|)$. ] 

Equipped with these bounds, practitioners and researchers turned away from DEEP sampling, using @BCIKS20@BCHKS25@DKT26  to directly bound the number or raw MCA-bad elements.

== Contributions<s:contributions>

We describe the main results of this work.

=== Better Elimination of Pretenders (BEEP), an improvement to DEEP. 
We provide a new soundness analysis of the DEEP technique after modifying the technique slightly. Precisely, the modification consists simply in making $numsamples$ DEEP sample evaluations, rather than only $1$, for a tunable parameter $numsamples$. 

We state our main result next, but before we generalize the notion of "an evaluation of a codeword" to arbitrary linear codes $cal(C)$, and not to just RS codes. Throughout, $FF$ is an arbitrary field and $cal(C)$ a code of blocklength $blockclength$ and dimension $codedim$.


#remark[General linear codes and zero evaders][
  For a non-RS code $cal(C)$, we generalize the notion of "evaluation of a codeword $c in cal(C)$ at a point $z$". A #emph[zero evader] is a family of linear maps $evalmap_z:FF^codedim -> FF^numsamples$, indexed by $z$ in some set $cal(Z)$.  Its error is $max_(vb(w) in FF^codedim, thin vb(w) != 0)Pr_(z in cal(Z))[evalmap_z (vb(w))=vb(0)]$. We refer to  $z in cal(Z)$ as a #emph[DEEP sample point]. We extend $evalmap_z$ to codewords $c =  Enc_cal(C)(vb(w)) in cal(C)$ by letting $evalmap_z (c) = evalmap_z (vb(w))$, and this is what we call the evaluation of $c$ at $z$.  
  
  For example, if $cal(C)$ is an RS code of dimension $codedim$, we may take $cal(Z)=FF^numsamples$ and $evalmap_(vb(z))(c)$  the vector of evaluations of the polynomial corresponding to $c$, at the points from $vb(z)$. Its error is $(codedim\/|FF|)^numsamples$. For general linear codes, MLE or univariate evaluation of the message corresponding to $c in cal(C)$ lead to similar  evader errors, see Section @s:zero_evaders.
]

#theorem[@t:main_thm, informal][
  Let $cal(C)$ be a linear code of blocklength $blockclength$, dimension $codedim$, and relative minimum distance $hamming(cal(C))$. Let $u_1, u_2 in FF^blockclength$ be two words,  let $delta in (0, Delta(cal(C)))$ be a proximity parameter and let $L$ be such that $cal(C)$ is $(delta, L)$-list decodable. 
  Let $(evalmap_z)_(z in cal(Z))$ be a zero evader with error $epsilon_(sans("evader"))$. For every  DEEP sample point $z in cal(Z)$, and  $vb(b)_1, vb(b)_2 in FF^numsamples$ (supposedly  evaluations under $evalmap$ of codewords close to $u_1,u_2$, to be provided by the prover), let $A_(z, vb(b)_1, vb(b)_2) subset FF$  be the set of MCA-bad folding challenges $alpha in FF$ such that, for some $alpha$-pretender $c in cal(C)$, we have #aiedit[$evalmap_z (c)= vb(b)_1 + alpha dot vb(b)_2$].
  Then
  $
    Pr_(z in cal(Z))[ lr(( max_(vb(b)_1, vb(b)_2 in FF^numsamples) lr(|A_(z, vb(b)_1, vb(b)_2)|))) > epsilon_(sans("BEEP"),2) dot |FF| ] ≤  epsilon_(sans("BEEP"),1),
  $
  where    
  $
     epsilon_(sans("BEEP"),1)= (M dot L)^3/(delta dot blockclength +1)^2 dot epsilon_(sans("evader")), quad quad quad epsilon_(sans("BEEP"),2) := (floor(delta dot blockclength) +1)/(|FF|),
   
  $
  #aiedit[and] $M$ is either $|FF|$ or $epsilon_(sans("MCA")) dot |FF|$, for the $delta$-MCA error $epsilon_(sans("MCA"))$ of $cal(C)$, if any such nontrivial error is known.
]<t:main_thm_informal>
When $cal(C)$ is a RS code of dimension $codedim$ we have, for some $m≥1$,
$ 
cal(Z) = FF^numsamples, quad quad epsilon_(sans("evader")) = lr(((codedim)/(|FF|) ))^numsamples.
$

In @tab:mca_comparison we compare the errors $epsilon_(sans("BEEP"),1), epsilon_(sans("BEEP"),2)$ with known MCA errors. We also include the affine version of our result (@t:affine_main_0), which we discuss later.




#[
#show figure.caption: set align(left)
#figure(
  {
    set text(size: 11pt, hyphenate: false)
    set par(justify: false)
    // a result: its name, and its source on the line below, indented
    let res(name, source) = stack(spacing: 0.65em, name, pad(left: 1em, source))
    let thickrule = table.hline(stroke: 0.8pt)
    let thinrule = table.hline(stroke: 0.5pt)
    let listdecone = [any $delta in (0, hamming(cal(C)^+))$ at which $cal(C)^+$  is $(delta, L)$-list decodable#footnote[$cal(C)^+$ is  $cal(C)$ with the dimension increased by one, cf. @s:affine.]]  
    let listdectwo = [any $delta in (0, hamming(cal(C)))$ at which $cal(C)$  is $(delta, L)$-list decodable]  
    stack(spacing: 0.6em,
    table(
      columns: (auto, auto, 1fr, auto, auto),
      stroke: none,
      align: left + horizon,
      // no outer padding, so the text lines up with the caption (like @{} in LaTeX)
      inset: (x, y) => (left: if x == 0 { 0pt } else { 5pt }, right: if x == 4 { 0pt } else { 5pt }, y: 6pt),
      thickrule,
      [Result], [Code], [Range of $delta$],
      [Folding error \ (MCA, or $epsilon_(sans("BEEP"),2)$)],
      [DEEP error \ ($epsilon_(sans("BEEP"),1)$)],
      thinrule,
      // prior work
      res[MCA][@DKT26[Thm 4.4]], [RS],
      [$delta <= 1 - sqrt(rho_-) - eta$],
      [$approx display(codedim/(3 sqrt(rho) thin eta^3 thin |FF|))$, see @e:mca_error],
      [---],
      res[MCA, affine fold][@CWYZ26[Thm 1.1]], [RS],
      [$delta <= 1 - sqrt(rho) - eta$, \ if $blockclength eta^2 >= 4\/rho$],
      [$display(4/(eta thin |FF|) + (2^(14) blockclength^2)/(rho^3 eta^(10) thin |FF|^2))$],
      [---],
      res[Khatam#footnote[#aiedit[@Zei26 loses $gamma dot blockclength$ positions of agreement. Without the loss ($gamma approx 1\/blockclength$), the error is about $3 dot blockclength\/(eta dot |FF|)$.]]][@Zei26[Thm 3]], [linear],
      [$delta < 1 - root(3, 1 - hamming(cal(C)) + eta) - gamma$],
      [$display(3/(eta thin gamma thin |FF|))$],
      [---],
      thinrule,
      // this work
      table.cell(rowspan: 2, res[BEEP][This work, @t:main_thm_informal[Thm]]), [linear],
      [$delta <= 1 - sqrt(1 - hamming(cal(C))) - eta$],
      table.cell(rowspan: 2, $display((delta blockclength + 1)/(|FF|))$),
      table.cell(rowspan: 2)[$display(((M L)^3 thin epsilon_(sans("evader")))/((delta blockclength + 1)^2))$ \ #box(text(size: 8.5pt)[(e.g. $epsilon_(sans("evader")) = (codedim\/|FF|)^numsamples$)])],
      [linear], listdecone,
      res[BEEP, affine fold][This work, @t:affine_main_0[Thm]], [RS],
      listdectwo,
      [$display(2/(|FF|))$],
      [$display(((|FF| L)^3 (codedim + 1)^numsamples)/(3 |FF|^numsamples))$],
      thickrule,
    ),
    )
  },
  placement: auto,
  caption: [
    Comparison of known MCA error bounds with the errors from @t:main_thm_informal and its affine version @t:affine_main_0 (discussed below).  $blockclength$ is the code length and $codedim$ its dimension.
    As long as $L$ is relatively small (e.g. polynomial), the error $epsilon_(sans("BEEP"),1)$ can always be made arbitrarily small by taking a zero evader with $epsilon_(sans("evader"))$ small. For example, when the evader consists in evaluating on $numsamples$ points the polynomial whose coefficients are given by the message entries,  then $epsilon_(sans("evader")) = (codedim/(|FF|))^numsamples$, cf. Section @s:zero_evaders. 
    $M$ is either $|FF|$ or #aiedit[$epsilon_(sans("MCA")) dot |FF|$, for a $delta$-MCA error $epsilon_(sans("MCA"))$ of the code]. In practice $m$ is $4$--$5$ when $M=|FF|$, and $2$ when #aiedit[$epsilon_(sans("MCA"))$ is the error of] @DKT26[Thm 4.4].  In the last row we need $|FF| ≥ (delta dot blockclength +2)^2$.
  ]
) <tab:mca_comparison>
]


The statement of @t:main_thm_informal is tailored for obtaining round-by-round knowledge soundness when using DEEP sampling in an IOPP. The analogue of our statement in the formulation of @deep would be that, for any  $vb(b)_1, vb(b)_2 in FF^numsamples$,
$
  Pr_(vb(z) in FF^numsamples, alpha in FF)[ alpha in A_(vb(z), vb(b)_1, vb(b)_2) ] ≤ epsilon_(sans("BEEP"),1) + epsilon_(sans("BEEP"),2).
$
The way @t:main_thm_informal would be used inside an IOPP is as follows: the result states that for at least a $1-epsilon_(sans("BEEP"),1)$ fraction of DEEP samples $z in cal(Z)$ sent by the verifier, the following occurs: for any prover answer $vb(b)_1, vb(b)_2$, there is at most an $epsilon_(sans("BEEP"),2)$ fraction of MCA-bad folding challenges $alpha in FF$ admitting an $alpha$-pretender codeword $c$ with $evalmap_z(c) = vb(b)_(1) + alpha dot vb(b)_(2)$. The reader may find apparent that $epsilon_(sans("BEEP"),1)$ would then be the  round-by-round knowledge soundness error of the DEEP sampling round of the IOPP, and that $epsilon_(sans("BEEP"),2)$ would be  the error of the folding round (in our instantiation this latter error has additional additive terms since we simultaneously run a sumcheck round with it, see @c:BEEP and @t:beep_soundness).


\



In Section @s:high_arity we provide a generalization and alternative proof of @t:main_thm_informal which relies solely on linear algebra. 



=== BEEP-IOR: folding of constrained interleaved codes with BEEP
 We describe a BEEP variant of typical code-based IOPPs for constrained interleaved codes, such as WHIR @whir, Ligerito @ligerito, Basefold #aiedit[@basefold], etc. At its core is  an Interactive Oracle Reduction (IOR) (@c:BEEP) from $cal(R)_(interleavedcode(2))$ to $cal(R)_cal(C)$, which we call BEEP-IOR. Here $interleavedcode(2)$ is the $2$-wise interleaving of $cal(C)$, and for a code $cal(C)'$ of dimension $codedim'$ and blocklength $blockclength'$ we define
  $ cal(R)_(cal(C)') := lr({
    lr(( cases(delim: #none,
      bb(x) = (mu, vb(v)) in FF times FF^(codedim') \,,
      bb(y) = f in FF^(blockclength')\,,
      bb(w) = vb(f) in FF^(codedim'),
    ) ))
    mid(|)
    cases(delim: #none,
      f = Enc_cal(C)'(vb(f)) \,,
      lr(⟨vb(f), vb(v) ⟩) = mu,
    )
  }) . $
The BEEP-IOR (@c:BEEP) consists of three rounds: 
1. DEEP sampling: the verifier sends a DEEP sample challenge $z in cal(Z)$ and the prover replies with, supposedly, the zero evader values $vb(b)_1, vb(b)_2 in FF^numsamples$ of the two rows $vb(f)_(1*), vb(f)_(2*) in FF^codedim$ of $vb(f)$.
2. Folding: the verifier sends a folding challenge $alpha in FF$. The oracle and witness are replaced by $g:=f_(1*) + alpha dot f_(2*) in FF^blockclength$ and $vb(g):= vb(f)_(1*) + alpha dot vb(f)_(2*) in FF^codedim$, respectively (where $f_(i*)$ are the rows of $f$), and a sumcheck round is performed to reduce the claim $langle vb(f), vb(v)rangle =mu$ to a linear claim about $vb(g)$, say $langle vb(g), vb(v)'rangle =mu'$. The sumcheck challenge used is $alpha$ itself.
3. The prover and verifier batch  the linear constraints $langle vb(g), vb(v)'rangle =mu'$, #aiedit[$evalmap_z (vb(g)) = vb(b)_1 + alpha dot vb(b)_2$], and output the claim $(bb(x)'', g, vb(g)) in cal(R)_cal(C)$ for a certain new $bb(x)''$.  

We show that the BEEP-IOR is round-by-round knowledge sound with errors: 
$
  epsilon_1=(M dot L)^3/(delta dot blockclength +1)^2 dot epsilon_(sans("evader")), quad quad  epsilon_2= frac(delta dot blockclength +1,|FF|)+ frac(2dot L_(interleavedcode(2)),|FF|), quad quad epsilon_3=frac(L,|FF|)
$
where $L_(interleavedcode(2))$ is a list size bound at radius $delta$ for $interleavedcode(2)$, and as before $L$ is a list size for $cal(C)$.

This IOR can then be composed with itself several times so as to obtain an IOR from $cal(R)_(interleavedcode(k))$ to $cal(R)_cal(C)$, where the output oracle is a linear combination of $k$ oracles. One can then compose this latter IOR with a code-switching IOR (as in WHIR @whir, Ligerito @ligerito, Blaze @blaze, etc.) or a standard spot check step as in Basefold, FRI-Binius #aiedit[@basefold @fribinius], so as to replace the linear combination of oracles with a single oracle to a codeword in a new code. This can be repeated in order to obtain a "BEEP variant" of the cited IOPPs. See Section @s:BEEP_WHIR for details.

We note that, following @BCFW25, the codes used in this IOPP need not have an efficient decoding algorithm. 

//#albert[Delete?] In Section @? we compare the soundness errors of Ligerito @ligerito and our BEEP version of it, as well as their runtimes and proof sizes. We provide a highlight of the results in #aiedit[@tab:measured_0]. An implementation of BEEP-Ligerito can be found in #link("https://github.com/worldfnd/BEEP"). #albert[Make sure tables are updated]


//#figure(
//  exptable(11,
//    (table.cell(colspan: 2)[$lambda = //128$], table.cell(colspan: 3)//[Ligerito (Flock)], table.cell//(colspan: 3)[BEEP-Ligerito, $eta = //#num("eta:lig")$], table.cell//(colspan: 3)[BEEP-Ligerito, $eta = //#num("eta:beep")$],
//     [size], [commit], [proof], [prove], //[verify], [proof], [prove], //[verify], [proof], [prove], //[verify]),
//    "bits128"),
//  caption: [Proof sizes (KiB) and times //(ms) at $128$ bits of security. //"Prove" is the opening, without the //commitment ("commit"), which all the //variants share. $dagger$: a process of //this row ran short of memory.],
//) <tab:measured_0>


=== Affine folding version of BEEP
 Restricting to RS codes,  in @polygero, the authors propose to use, as folding challenges $alpha$, polynomials of small degree $s$, instead of field elements. The soundness error from @polygero is of about $1\/|FF|$, with up to $s$ positions of agreement lost after the fold. It requires however $s$ to grow linearly with the block length, e.g. in @polygero[Remark 2] $s=74$  when $blockclength = 25724$, over a $128$-bit field. In  @CWYZ26 (concurrent to @polygero), the authors show that affine challenges, i.e. $s=1$, suffice. They obtain an MCA-type error bound of #aiedit[$4\/(eta dot |FF|) + 2^(14) dot blockclength^2\/(rho^3 dot eta^(10) dot |FF|^2)$ for RS codes of rate $rho$ and $delta = 1 - sqrt(rho) - eta$, assuming $blockclength dot eta^2 ≥ 4\/rho$ @CWYZ26[Theorem 1.1]. As in @polygero, one position of agreement may be lost after the folding].

In Section @s:affine we provide a version of our results (concretely of @t:main_thm_informal) where $alpha$ is an affine polynomial, for RS codes. In this setting, the errors in @t:main_thm_informal are as follows: the DEEP sampling error $
epsilon_(sans("affine-BEEP"),1) = (|FF| dot L')^3/3 dot ((codedim+1)/(|FF|))^numsamples
$ 
#aiedit[where $L$ is a list size for the Reed-Solomon code of dimension $codedim+1$)], while the folding error $epsilon_(sans("BEEP"),2)$ becomes
$
epsilon_(sans("affine-BEEP"),2) = 2/(|FF|).
$
#aiedit[As in @CWYZ26@polygero, one position of agreement may be lost.] We require $|FF| ≥ (delta dot blockclength +2)^2$.



In contrast to @CWYZ26, our analysis in the affine setting is elementary, amounting to about five pages, with half of them being a simple rephrasing for the affine setting of definitions and arguments already used in Section @s:better_pretenders.  We note that ours is a different result than @CWYZ26@polygero though. Roughly, @CWYZ26 proves that RS codes have MCA with a smaller error when using affine folding (up to the Johnson bound, and with one position of agreement loss). Our result, on the other hand, is the affine-variant of the DEEP technique,  and requires only list-decodability of the code.  




=== Conclusions 
We list some implications of our results:\
\
*Code-agnostic IOPPs up to the Johnson bound and beyond.* Our work allows to run typical code-based IOPPs   using arbitrary codes (e.g. #aiedit[@era@bolt@blaze@qacodes]), not necessarily RS codes, and still use a proximity parameter $delta$ approaching the Johnson bound, over fields of practical size.  It suffices to add the DEEP sampling step discussed above and in Section @s:BEEP_fold.

One can also envision IOPPs using codes with good list decodability for $delta$ beyond the Johnson bound, even if the code does not have MCA at that distance. RS codes are a possible candidate.\
\
*Folding error bounds which improve upon those obtained solely with MCA.* When using DEEP sampling in an IOPP (@c:BEEP), the error $epsilon_(sans("BEEP"),2)$ (or the affine error $epsilon_(sans("affine-BEEP"),2)$ if using affine folds @CWYZ26), effectively replaces the MCA error bound from @e:mca_error. As displayed in @tab:mca_comparison, this error is smaller than known plain MCA errors. When using affine folding, our folding error is $2\/|FF|$ which again is smaller than the affine-MCA error from @CWYZ26. Smaller errors can lead to a plethora of benefits: such as being able to use smaller fields, less grinding work, or a parameter $delta$ closer to some bound (which decreases proof size).

== Use of AI and Lean formalization
This document was initially written without the use of AI, except for sections @s:BEEP_WHIR and @s:affine, which were initially drafted with AI and were substantially edited by us afterward. In the final stages, we used AI to edit and polish the text.  We chose this approach with the intention of creating a text which is as amenable to human readers as reasonably possible.

The novel results in this work were obtained through an interactive process with an AI. We had an AI formalize our main results (@t:main_thm and @t:affine_main_0) in Lean (see #link("https://github.com/worldfnd/BEEP")), and the corresponding Lean statements were reviewed by us subsequently.

== Acknowledgements


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


#paragraph[Interleaved codes] 
Given $k ≥ 1$, the #emph[$k$-interleaving] of $cal(C)$ is the code $interleavedcode(k) subset (FF^k)^blockclength$ whose codewords are  tuples $(c_1, dots, c_k)$ of codewords of $cal(C)$, seen as words of length $blockclength$ over the alphabet $FF^k$. The minimum distance of $interleavedcode(k)$ is the same as that of $cal(C)$. Moreover, for $delta < 1 - sqrt(1-Delta(cal(C)))- eta$, $interleavedcode(k)$ admits the Johnson decodability bound $
L=floor(1\/(2 dot eta dot sqrt(1-Delta(cal(C))))),
$ the same as $cal(C)$. For $delta$ at or above the Johnson bound, if  $cal(C)$ is $(delta, L)$-list decodable, then $interleavedcode(k)$ is $(delta, L^k)$-list decodable. The following lemma improves such bound  for larger values of $k$.
#lemma[@GGR11, see #aiedit[@zook[Lemma 3.18]]][
  Let $delta in [0, hamming(cal(C)))$ and assume $cal(C)$ is $(delta, L)$-list decodable. Let
  $b := ceil(delta / (hamming(cal(C)) - delta))$ and  $r := ceil(log_2 (hamming(cal(C))) / (hamming(cal(C)) - delta)).$
  Then, for every $k ≥ 1$, the code $interleavedcode(k)$ is $(delta, L_(equiv))$-list decodable with $L_(equiv) := binom(b+r, r) dot L^r$.
]<l:interleaved_list>


== Zero-evaders<s:zero_evaders>

We use the notion of a zero evader from @BCFW25, expressed as an indexed family of linear maps with vector-valued outputs.

#let evaderdim = $e$

#definition[Zero evader][
  A _zero evader_ is a family of linear maps ${φ_z : 𝔽^evaderdim → 𝔽^numsamples | z in cal(Z)}$ indexed by a finite non-empty set $𝒵$. We call $ε ∈ [0,1]$ an _error bound_ of the evader if #albert-postponable[For consistency we should write $phi_z(vb(b))$]
  $
    max_(𝐯 ∈ 𝔽^evaderdim \ 𝐯 ≠ 𝟎) thick Pr_(z ← 𝒵) thick [φ_z 𝐯 = 𝟎] ≤ ε.
  $
]

#remark[
  In a given basis $φ_z$ is an $numsamples × evaderdim$ matrix. When $numsamples=1$ we call it a _scalar zero evader_.
]

#definition[Univariate evader][
  Define the $numsamples$-sample _univariate evader_ with index family $𝒵 ≔ 𝔽^numsamples$ and $φ_𝐳$ for $𝐳 = (z_1, …, z_numsamples)$ as the map given by the $numsamples × evaderdim$ Vandermonde matrix on $𝐳$. #albert-postponable[Maybe let's now write the evader explicitly]
]

#lemma[
  The $numsamples$-sample univariate zero evader has error bound
  $ε = min(1, ((evaderdim- 1) / (|FF|))^numsamples).
  $ 
]

#proof[
  Fix a nonzero $𝐯 ∈ FF^evaderdim$. The polynomial
  $ P(X) = sum_(j∈[evaderdim]) v_j dot X^(j - 1)$
  is nonzero and has degree at most $evaderdim - 1$, so it has
  at most $evaderdim - 1$ roots in $𝔽$. By construction, $φ_𝐳 (𝐯) = (P(z_1), …, P(z_numsamples))$. Since the coordinates of $𝐳$ are independent and uniform,
  $
    Pr_(𝐳 ← 𝔽^numsamples)[φ_𝐳 (𝐯) = 𝟎]
    = product_(i ∈ [numsamples]) med Pr_(z_i ← 𝔽) med [P(z_i) = 0]
    ≤ ((evaderdim - 1) / abs(𝔽))^numsamples.
  $
]

#remark[
  We do not require the $z_i$ to be distinct. When applied to message coordinates, the univariate zero evader matches the $m$-repeated out of domain samples in WHIR @whir, and the codeword queries in the Reed-Solomon instantiation of Ligerito @ligerito, etc.
]

#definition[Multilinear evader][
  Let $e_0 := ceil(log_2 evaderdim)$ and fix a basis. We define the scalar _multilinear evader_ with index family $𝒵 ≔ 𝔽^(e_0)$ and $φ_𝐳$ for $𝐳 = (z_1, …, z_(e_0))$ as the first $evaderdim$ values of the MLE tensor product:
  $φ_𝐳 = (⨀_(i ∈ [e_0]) mat(1 - z_i; z_i))_[evaderdim].$
  #albert-postponable[As with the other one, let's write the application of $phi_z$ explicitly now]
]

#lemma[
  The _multilinear evader_ has error bound $ε = min(1, e_0\/aiedit(|𝔽|))$.
]

#proof[
  Fix a nonzero $𝐯 ∈ FF^evaderdim$ and pad its coordinates with zeros to obtain a vector of length $2^(e_0)$. Its multilinear extension $MLE[𝐯]$  has total degree at most $e_0$, and $φ_𝐳 𝐯 = MLE[𝐯](𝐳)$. The result follows from the Schwartz–Zippel bound.
]


== Interactive Oracle Reductions (IOR)<s:IOR>

An _Interactive Oracle Reduction (IOR) of proximity_ $Pi = (prover, verifier)$ from a relation $Relation$ to a relation $Relation'$ is specified as follows. The prover $prover$ receives $(inp, oracle, wit) in Relation$. The verifier $verifier$ receives $inp$ and query access to $oracle$. They interact for $k$ rounds. In round $j in [k]$, the prover sends an oracle $provermsg_j$ and the verifier sends a uniformly random message $verifiermsg_j in {0,1}^(r_j)$. After the $k$ rounds, the verifier makes queries to $oracle$ and to $provermsg_1, dots, provermsg_k$. Then:
1. $verifier$ either rejects or outputs a new pair $(inp', oracle')$, where $oracle'$ is specified implicitly in terms of the oracles $oracle$ and $provermsg_1, dots, provermsg_k$.
2. $prover$ outputs a witness $wit'$ such that $(inp', oracle', wit') in Relation'$.
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
  1. *Empty transcript.* If $tr = emptyset$ is the empty transcript, then $kstate(inp, oracle, tr, kswit) = 1$ if and only if $(inp, oracle; kswit) in tilde(Relation)$.
  2. *Prover moves.* If $tr$ is a transcript where the prover is about to move and $kstate(inp, oracle, tr, kswit) = 0$, then $kstate(inp, oracle, tr, provermsg, kswit) = 0$ for every prover message $provermsg$.
 3. *Full transcript.* If $tr = (provermsg_1, verifiermsg_1, dots, provermsg_k, verifiermsg_k)$ is a full transcript, then $kstate(inp, oracle, tr, kswit) = 1$ if and only if $verifier$ on $tr$ outputs $(inp', oracle')$ such that $(inp', oracle'; kswit) in tilde(Relation')$.
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

#lemma[Composition of IORs #aiedit[@zook[Theorem 4.7]]][
  Let $Pi_1$ be a perfectly complete $k_1$-round IOR from $Relation_1$ to $Relation_2$ with round-by-round knowledge soundness with relaxation $(tilde(Relation_1), tilde(Relation_2))$ and errors $kappa_(11), dots, kappa_(1 k_1)$, and let $Pi_2$ be a perfectly complete $k_2$-round IOR from $Relation_2$ to $Relation_3$ with round-by-round knowledge soundness with relaxation $(tilde(Relation_2), tilde(Relation_3))$ and errors $kappa_(21), dots, kappa_(2 k_2)$. Then the IOR from $Relation_1$ to $Relation_3$ that runs $Pi_1$ and then $Pi_2$ on the output of $Pi_1$ is perfectly complete, has $k_1 + k_2$ rounds, and has round-by-round knowledge soundness with relaxation $(tilde(Relation_1), tilde(Relation_3))$ and errors $kappa_(11), dots, kappa_(1 k_1), kappa_(21), dots, kappa_(2 k_2)$.
] <r:ior_compositoin>



= BEEP:  Better Elimination of Pretenders <s:better_pretenders>

In this section we prove @t:main_thm_informal. In Section @s:affine we prove an analogous version when folding challenges are affine polynomials.

== Pretender codewords and consistency

We start by establishing some concepts and terminology. Let $FF$ be a finite field and let $cal(C) subset FF^blockclength$ be a linear code of blocklength $blockclength$ and dimension $codedim$, with $blockclength$ a power of two. Let $delta in (0,1)$ be a proximity parameter.


#aiedit[We fix two linear maps $theta_1, theta_2: FF arrow FF$, so that $theta_i (alpha) = a_i + alpha dot d_i$ for some $a_i, d_i in FF$, and we assume that $a_1 dot d_2 != a_2 dot d_1$. We use $theta_1(alpha)$ and $theta_2(alpha)$ as the weights when folding two words with a challenge $alpha in FF$. For example, $(theta_1(alpha), theta_2(alpha))$ can be $(1, alpha)$, or $(1-alpha, alpha)$ as in Section @s:BEEP_fold. The assumption $a_1 dot d_2 != a_2 dot d_1$ guarantees that the vectors $(theta_1(alpha), theta_2(alpha))$ and $(theta_1(alpha'), theta_2(alpha'))$ are linearly independent for all distinct $alpha, alpha' in FF$.]


 Let $u_1, u_2 in FF^blockclength$ be two words. Given $S subset [blockclength]$, we say $(u_1,u_2)$ has #emph[Correlated Agreement with $cal(C)$ over $S$] if there exist codewords $c_1,c_2 in cal(C)$ such that $u_1$ agrees with $c_1$ on $S$ and $u_2$ agrees with $c_2$ on $S$. 



  Let  $u_1,u_2 in FF^blockclength$ be two words. We say that a field element $alpha in FF$ satisfies the #emph[$delta$-Mutual Correlated Agreement (MCA) property] with respect to $u_1,u_2$, if for every subset $S subset [blockclength]$ with $|S|≥ (1-delta) dot blockclength$ such that #aiedit[$theta_1(alpha) dot u_1 + theta_2(alpha) dot u_2$] agrees with $cal(C)$ on $S$, the pair $(u_1,u_2)$ has Correlated Agreement (CA) with $cal(C)$ over $S$.


#definition[MCA-bad element][
   We say $alpha$ is #emph[MCA-bad] if it does not satisfy the $delta$-MCA property.
]

The code $cal(C)$ is said to have #emph[$delta$-Mutual Correlated Agreement (MCA)] for the maps $theta_1, theta_2$, with error $epsilon$, if for any two words $u_1,u_2 in FF^blockclength$, there are at most $epsilon dot |FF|$ MCA-bad field elements.

#definition[Pretender codeword][
  Fix two words $u_1,u_2 in FF^blockclength$, and let $alpha in FF$ be an MCA-bad field element. We say that a codeword $c in cal(C)$ is an #emph[$alpha$-pretender] if, intuitively speaking, it is a witness to the failing of the MCA property for $alpha$. Formally, $c$ is an $alpha$-pretender if #aiedit[$theta_1(alpha) dot u_1 + theta_2(alpha) dot u_2$] and $c$ agree on a set $S subset [blockclength]$ of size $|S| ≥ (1-delta) dot blockclength$ and $(u_1,u_2)$ does not have CA with $cal(C)$ over $S$.
]

Fix a zero-evader $(φ_z)_(z ∈ 𝒵)$, i.e. a family of linear maps $phi_z : FF^codedim -> FF^numsamples$, with error bound $ε$.  Abusing the notation, we also define $phi_z$ on $cal(C)$ by letting $phi_z  (Enc_cal(C)(vb(w))) := phi_z (vb(w))$. Since $Enc_cal(C)$ is linear and injective, $phi_z$ is linear on $cal(C)$ and $Pr_(z <- Z)[phi_z (c) =0] ≤ epsilon$ for all nonzero codeword $c$.

Let $𝐛_(1), 𝐛_(2) ∈ 𝔽^numsamples$. For intuition, for an honest prover, $𝐛_1, 𝐛_2$ will be the values $φ_z (c_1), φ_z (c_2)$, where $c_1, c_2 ∈ 𝒞$ are two codewords that are $δ$-close to $u_1$  and $u_2$.

#definition[Consistency of MCA-bad elements $α ∈ 𝔽$  with $z ∈ cal(Z)_(sans("evader"))$][
  Let $α ∈ 𝔽$ and $c ∈ 𝒞$. Given $z ∈ 𝒵$ and $vb(b)_(1), vb(b)_(2) in FF^numsamples$,  we say that $(α, c)$ is _consistent_ with $(z, vb(b)_(1), vb(b)_(2))$ if 
  $
    φ_z (c) = aiedit(θ_1 (α) ·) 𝐛_(1) + aiedit(θ_2 (α)) · 𝐛_(2).
  $
  When $α$ is an MCA-bad element and there exists an $α$-pretender $c in cal(C)$ such that $(α, c)$ is consistent with  $(z, vb(b)_(1), vb(b)_(2))$, then we say that $α$ is a _DEEP-MCA-bad element_ with respect to $z,vb(b)_(1), vb(b)_(2)$ and $u_1, u_2$. 

  When clear from the context, we omit referring to $z, vb(b)_(1), vb(b)_(2), u_1, u_2$ when speaking of DEEP-MCA-bad elements.
]

== Most out of domain samples admit few DEEP-MCA-bad challenges<s:main_thm>

We are now ready to state and prove the rigorous version of @t:main_thm_informal.


#theorem[For most $z ∈ 𝒵$, there are few DEEP-MCA-bad elements $alpha in FF$][
  Let $delta in (0,1)$ and let $L$ be such that  $cal(C)$ is $(delta, L)$-list decodable.
  Let $u_1, u_2 in FF^blockclength$ be two words, and let $(φ_z)_(z ∈ 𝒵)$ be a zero evader with error $epsilon_(sans("evader"))$. 

  For each $z ∈ cal(Z)_(sans("evader"))$ and $vb(b)_1, vb(b)_2 in FF^numsamples$, let $A_(z, vb(b)_1, vb(b)_2) ⊂ 𝔽$ be the set of DEEP-MCA-bad field elements $α ∈ 𝔽$ with respect to $z, vb(b)_1, vb(b)_2, u_1, u_2$. Let $vb(b)_1^*, vb(b)_2^*$ be such that $|A_(z, vb(b)_1^*, vb(b)_2^*)|$ is maximal  for fixed $z, u_1,u_2$, and denote $A_z := A_(z, vb(b)_1^*, vb(b)_2^*)$. 
  
  Then for any $t≥ delta dot blockclength +2$,
  $
    Pr_(z ← cal(Z)_(sans("evader")))[ abs(A_(z)) ≥ t] ≤ ((|FF| dot L)^3 dot epsilon_(sans("evader"))) / (t dot (t-1) dot (t-delta dot blockclength -1))
  $<e:beep_bound>

  Moreover, if $cal(C)$ has $delta$-MCA error $epsilon_(sans("MCA"))$ then the factor $(|FF| dot L)^3$ in @e:beep_bound can be replaced by 
$
(epsilon_(sans("MCA")) dot|FF| dot L)^3
$
]<t:main_thm>

#albert-postponable[We should aim to allowsel a skimmer to understand or guess what the theorem says in a more self-contained way. Also we should provide an example of $epsilon_(sans("evader"))$.]

#remark[Using @t:main_thm to replace the MCA error with the list decodability size in code-based PCS][Looking ahead, we will use this result as follows: before performing the fold of two words during a code-based PCS, we have the verifier sample an element $z in cal(Z)$, and the prover replies with $vb(b)_1, vb(b)_2 in FF^numsamples$, supposedly the evaluations on $evalmap_z$ of the two words (which are supposedly codewords). Now, due to @t:main_thm, with high probability over $z$, there are very few folding challenges $alpha in FF$ that result in a failure of the MCA property and which are consistent with $(z, vb(b)_1, vb(b)_2)$. Hence, at this point we can fold as usual, and obtain knowledge soundness even if  the code $cal(C)$ is not known to possess (or is known to not possess) MCA at the proximity parameter $delta$ used by the PCS. We formalize this intuition in Section @s:BEEP_fold.]<r:using_main_thm>


We proceed to prove @t:main_thm. We assume the notation of its hypothesis. // We fix $vb(b)_1, vb(b)_2 in FF^numsamples$ and show that $Pr_(z <- cal(Z)) sans("Pr")[ |A_(z,vb(b)_1, vb(b)_2)|≥ t ]$ is at most the right-hand side of @e:beep_bound. This implies that $Pr_(z <- cal(Z)) sans("Pr")[ max_(vb(b)_1, vb(b)_2 in FF^numsamples) |A_(z,vb(b)_1, vb(b)_2)| ≥ t ]$ satisfies the same bound.

#let lmap = $theta$
#let linfuns = $cal(L)^(1)[FF arrow cal(C)]$
#let im = math.sans("Graph")



#definition[Parameterized lines][We let $linfuns$ be the set of all linear maps $lmap: FF arrow cal(C)$, so that $lmap(alpha) = c_(theta,1) + alpha dot c_(theta,2)$ for some codewords $c_(theta,1), c_(theta,2) in cal(C)$.  Given $lmap in linfuns$, we let $im(lmap)= {(alpha, theta(alpha)) | alpha in FF} subset FF times cal(C)$ and we call $im(lmap)$ a #emph[parameterized line in $cal(C)$].]

//Let $c_1, c_2 in cal(C)$ be two (not necessarily distinct) codewords. The  #emph[line] in $cal(C)$ spanned by  $c_1,c_2$  is the set $cal(C)_(c_1,c_2):={c_1 + alpha dot c_2 | alpha in FF}$.  // Given a MCA-bad $alpha in FF$ and an $alpha$-pretender (w.r.t. $(u_1,u_2)$) $c in cal(C)$, we say $c$ is in the  

#albert-postponable[The following result is well-known, see for example @? #albert[citation]. We include a proof for completeness. ]

The following result is folklore.
#lemma[A parameterized line contains few pretenders][
 Let $u_1,u_2 in FF^blockclength$ be two words, and let $lmap in linfuns$. Let $A_(lmap)^(sans("pret")) subset FF$ be the set of all field elements $alpha in FF$ that are MCA-bad and such that the codeword $lmap(alpha) = c_(lmap,1) + alpha dot c_(lmap, 2) in cal(C)$ is an $alpha$-pretender with respect to $u_1,u_2$.   Then
  $|A_(lmap)^(sans("pret"))| ≤ delta dot blockclength +1.
  $
]<l:few_bad_points_on_line>
#proof[
  #aiedit[Since $a_1 dot d_2 != a_2 dot d_1$, there exist codewords $c_1, c_2 in cal(C)$ such that $lmap(alpha) = theta_1(alpha) dot c_1 + theta_2(alpha) dot c_2$ for all $alpha in FF$ (they are the solution to the system $a_1 dot c_1 + a_2 dot c_2 = c_(lmap,1)$, $d_1 dot c_1 + d_2 dot c_2 = c_(lmap,2)$).] Let $D subset [blockclength]$ be the set
  $
  D := {x in [blockclength] | u_1(x) != aiedit(c_1(x)) " or " u_2(x) != aiedit(c_2(x))}.
  $
  Let $alpha in A_lmap^(sans("pret"))$. Since $theta(alpha)$ is an $alpha$-pretender, there is a set $S_alpha subset [blockclength]$  where $lmap(alpha)$ and #aiedit[$theta_1(alpha) dot u_1 + theta_2(alpha) dot u_2$] agree, with $|S_alpha|≥ (1-delta) dot blockclength$ and such that $(u_1,u_2)$ do not have correlated agreement with $cal(C)$ over $S_alpha$. Hence $S_alpha inter D != emptyset$.

  We claim that for every distinct $alpha, alpha' in A_lmap^(sans("pret"))$ we have $(S_alpha inter D) inter (S_(alpha') inter D) = emptyset$. Indeed, assume to the contrary that $x in [blockclength]$ belongs to such set. Then #aiedit[$theta_1(alpha) dot u_1(x) + theta_2(alpha) dot u_2(x)= theta_1(alpha) dot c_1(x) + theta_2(alpha) dot c_2(x)$] and #aiedit[$theta_1(alpha') dot u_1(x) + theta_2(alpha') dot u_2(x)= theta_1(alpha') dot c_1(x) + theta_2(alpha') dot c_2(x)$]. #aiedit[Since $alpha != alpha'$, the vectors $(theta_1(alpha), theta_2(alpha))$ and $(theta_1(alpha'), theta_2(alpha'))$ are linearly independent, and so] we obtain $u_1(x)=aiedit(c_1(x))$ and $u_2(x)=aiedit(c_2(x))$, contradicting the fact that $x in D$, and thus proving the claim.

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
  It follows by direct evaluation, using the linearity of $evalmap_z$ and the assumption that $evalmap_z (v_i) = aiedit(theta_1(alpha_i) dot 𝐛_1 + theta_2(alpha_i) dot 𝐛_2)$ for $i=1,2,3$. #aiedit[Writing $theta_j (alpha) = a_j + alpha dot d_j$ and $𝐛' := d_1 dot 𝐛_1 + d_2 dot 𝐛_2$, this gives $evalmap_z (v_i) - evalmap_z (v_1) = (alpha_i - alpha_1) dot 𝐛'$ for $i=2,3$, and so:] 
  $  
     evalmap_z (U((alpha_i, v_i)_(i in [3]))) &=
     (alpha_3-alpha_1) dot (evalmap_z (v_2) - evalmap_z (v_1))-(alpha_2-alpha_1) dot (evalmap_z (v_3) - evalmap_z (v_1)),\
     &= (alpha_3-alpha_1) dot (alpha_2-alpha_1) dot aiedit(𝐛') - (alpha_2-alpha_1) dot (alpha_3-alpha_1) dot aiedit(𝐛') = 𝟎,
  $
  as required.
]

Let $z ∈ 𝒵$,  and let $T_z$ be the set of triples $(alpha_i, v_i)_(i in [3]) in (FF times cal(C))^3$ such that: 1) $(alpha_i, v_i)$ is consistent with $(z, vb(b)_1^*, vb(b)_2^*)$ for all $i in [3]$; 2) $U((alpha_i, v_i)_(i in [3])) != 0$; 3) $alpha_i$ is an MCA-bad point and $v_i$ is an $alpha_i$-pretender, for all $i in [3]$; and 4) $alpha_i != alpha_j$ for all $1 ≤ i <j≤3$.

@l:few_bad_points_on_line states that a parameterized line in $cal(C)$ contains few points $(alpha, c) in FF times cal(C)$ with $c$ being an $alpha$-pretender. On the other hand, for every $alpha in A_z$,  there exists an $alpha$-pretender $c in cal(C)$. Hence, intuitively, if $|A_z|$ is large, then there are many triples $(alpha_i, c_i)_i$ that are not colinear, and so  we expect $|T_z|$ to be large too. We formalize this intuition in the next result.

#lemma[Bounding $|A_z|^3$ with $|T_z|$][
  Let $z ∈ 𝒵$ and let $T_z$ be defined as above. Then 
  $
    |A_z| dot (|A_z| -1) dot (|A_z| -delta dot blockclength -1) ≤ |T_z|.
  $
]<l:third_moment_bound>
#proof[
   For each $alpha in A_z$, fix an $alpha$-pretender $c_alpha in cal(C)$ such that $(alpha, c_alpha)$ is consistent with $(z, vb(b)_1^*, vb(b)_2^*)$. Such $c_alpha$ exists by the definition of $A_z$. Let $Y = {(alpha, c_alpha) | alpha in A_z}$ and note that $|Y|=|A_z|$.
  Every triple $(alpha_i, c_alpha_i)_(i in [3]) in Y^3$ with $alpha_i != alpha_j$ for all $i !=j$ satisfies Conditions 1, 3 and 4 in the definition of $T_z$. Hence it suffices  to lower bound the number of such triples for which $U((alpha_i, c_alpha_i)_(i in [3])) != 0$. 
  
  We claim that for every pair $(alpha, v), (alpha',v') in FF times cal(C)$ with $alpha != alpha'$, there exists a unique $lmap in linfuns$ such that $(alpha,v)$ and $(alpha',v')$ both belong to $im(lmap)$.  Indeed, let $c_2 = (v - v')/(alpha - alpha') in cal(C)$ and $c_1=v - alpha dot c_2$. Now $v = c_1 + alpha dot c_2$, and $c_1 + alpha' dot c_2 = v - alpha dot c_2 + alpha' dot c_2 = v'$, hence $(alpha,v)$ and $(alpha',v')$ both belong to $im(theta_(c_1,c_2))$. On the other hand, if $theta_(v_1,v_2)(alpha)=v$ and $theta_(v_1,v_2)(alpha')=v'$ for some $v_1,v_2 in cal(C)$, then 
  $
    v = v_1 + alpha dot v_2, quad quad 
    v'= v_1 + alpha' dot v_2
  $
  Subtracting, $(v - v')/ (alpha-alpha') = v_2 = c_2$, and then $v_1 = v - alpha dot v_2= v - alpha dot c_2 = c_1$, hence $theta_(v_1,v_2)=theta_(c_1,c_2)$, completing the proof of the claim.
  


   There are exactly  $|A_z| dot (|A_z|-1)$  pairs $(alpha_1,c_alpha_1), (alpha_2,c_alpha_2) in Y$ with $alpha_1 != alpha_2$. Fixing such $(alpha_1,c_alpha_1), (alpha_2,c_alpha_2) in Y$, let $lmap in linfuns$ be the unique map such that both tuples belong to $im(lmap)$ (see the claim above). Then, by @l:few_bad_points_on_line,  there are at most $delta dot blockclength +1$ pairs $(alpha_3, c_alpha_3) in Y$ belonging to the parameterized line $im(lmap)$. Hence there are at least $|A_z| -delta dot blockclength -1$ tuples $(alpha_3, c_alpha_3) in Y$ that do not belong to  $im(lmap)$.  Each of them satisfies $alpha_3 != alpha_1$ and $alpha_3 != alpha_2$, because otherwise, by definition of $Y$, $(alpha_3, c_alpha_3)$ would be either $(alpha_1, c_alpha_1)$ or $(alpha_2, c_alpha_2)$, and these two tuples belong to $im(lmap)$.


    Overall, there are at least $|A_z| dot (|A_z|-1) dot (|A_z| -delta dot blockclength -1)$ triples $(alpha_i, c_alpha_i)_(i in [3]) in Y^3$ with $alpha_i != alpha_j$ for all $i!= j$,  such that $(alpha_3, c_alpha_3)$ does not belong to the unique parameterized line containing $(alpha_1, c_alpha_1)$ and $(alpha_2, c_alpha_2)$. By  @l:colinear, for such triple we have $U((alpha_i, c_alpha_i)_(i in [3])) != 0$. The lemma then follows, since, as we discussed before, $T_z$ contains all the triples $(alpha_i, c_alpha_i)_(i in [3]) in Y^3$ with $alpha_i != alpha_j$ for all $i!=j$ such that $U((alpha_i, c_alpha_i)_(i in [3])) != 0$.
]


We are ready to prove @t:main_thm.

#proof[Proof of @t:main_thm][
   Let $cal(Z)_t subset cal(Z)$ be the set of all $z in cal(Z)$ such that $|A_z| ≥ t$ for all $z in cal(Z)_t$. Then by @l:third_moment_bound,
  $
  cases(delim: #none,
  sum_(z in cal(Z)_t) |T_z| &≥ sum_(z in cal(Z)_t) |A_z| dot (|A_z| -1) dot (|A_z| - delta dot blockclength -1), &≥ t dot (t -1) dot (t - delta dot blockclength -1) dot |cal(Z)_t|
  )
  $<e:proof_thm_1>
  We now claim that 
  $
  sum_(z in cal(Z)) |T_z| ≤ (|FF| dot L)^3 dot epsilon_(sans("evader")) dot |cal(Z)|,
  $<e:sum_Tz>
  and,  additionally that if $cal(C)$ has $delta$-MCA error $epsilon_(sans("MCA"))$ then the factor $(|FF| dot L)^3$ in @e:sum_Tz can be replaced by 
$(epsilon_(sans("MCA")) dot |FF| dot L)^3$.
  Indeed, let $P subset FF times cal(C)$ be the set of all tuples $(alpha, c)$ such that $c$ is an $alpha$-pretender. We  have $|P| ≤ |FF| dot L$,
  where the list size factor $L$ is due  to the fact that an $alpha$-pretender is $delta$-close to #aiedit[$theta_1(alpha) dot u_1 + theta_2(alpha) dot u_2$], and since $cal(C)$ is $(delta, L)$-list decodable, there are at most $L$ codewords in $cal(C)$ that are $delta$-close to #aiedit[$theta_1(alpha) dot u_1 + theta_2(alpha) dot u_2$]. Additionally, we also have $|P| ≤ epsilon_(sans("MCA")) dot |FF| dot L$ if $cal(C)$ has $delta$-MCA error $epsilon_(sans("MCA"))$, since for $(alpha, c)$ to belong to $P$, we need $alpha$ to be an MCA-bad element, and there are at most $epsilon_(sans("MCA")) dot |FF|$ such elements.
  
  Now,  let $(alpha_i, c_i)_(i in [3]) in P$ be such that $alpha_i != alpha_j$ for all $i!=j$ and $U((alpha_i, c_i)_(i in [3])) != 0$. Then if  $(alpha_i, c_i)_(i in [3]) in T_z$, by definition $(alpha_i, c_i)$ is consistent with $(z, vb(b)_1^*, vb(b)_2^*)$ for all $i in [3]$. By @l:colinear_zero,$evalmap_z (U((alpha_i, c_i)_(i in [3])))=0$. Then, since $0!=U((alpha_i, c_i)_(i in [3])) in cal(C)$, by the definition of zero evader there are at most $epsilon_(sans("evader")) dot |cal(Z)|$ elements $z in cal(Z)$ such that $evalmap_z (U((alpha_i, c_i)_(i in [3])))=0$. In other words, for every triple $(alpha_i, c_i)_(i in [3]) in P^3$ such that $alpha_i != alpha_j$ for all $i!=j$  and $U((alpha_i, c_i)_(i in [3])) != 0$, 
  $
  lr(|{z in cal(Z) | (alpha_i, c_i)_i in T_z}|)≤ epsilon_(sans("evader")) dot |cal(Z)|.
  $
  For  the rest of triples $(alpha_i, c_i)_(i in [3]) in P^3$ the same inequality holds, since then we actually have $lr(|{z in cal(Z) | (alpha_i, c_i)_i in T_z}|)=0$.
   Now we obtain by double counting and using $T_z subset P^3$, 
 $
&sum_(z in cal(Z)_t) |T_z| ≤ sum_(z in cal(Z)) |T_z| = lr(|{ (z,(alpha_i,c_i)_(i in [3])) in cal(Z) times P^3 mid(|) (alpha_i,c_i)_(i in [3]) in T_z}|)
\ &=sum_((alpha_i, c_i)_(i in [3]) in P^3) lr(|{z in cal(Z) mid(|) (alpha_i, c_i)_(i in [3]) in T_z}|) <= sum_((alpha_i, c_i)_(i in [3]) in P^3) epsilon dot |cal(Z)| <= (M dot L)^3 dot epsilon dot |cal(Z)|,
$<e:proof_thm_2> where $epsilon = epsilon_(sans("evader"))$ and $M$ is either $|FF|$ or $epsilon_(sans("MCA")) dot |FF|$, for $epsilon_(sans("MCA"))$ the $delta$-MCA error of $cal(C)$. The first inequality is due to $cal(Z)_t subset cal(Z)$; the two equalities are the result of double counting, using that $T_z subset P^3$ for the first one, so that ${(z,(alpha_i,c_i)_(i in [3])) in cal(Z) times (FF times cal(C))^3 | (alpha_i,c_i)_(i in [3]) in T_z}={ (z,(alpha_i,c_i)_(i in [3])) in cal(Z) times P^3 mid(|) (alpha_i,c_i)_(i in [3]) in T_z}$; the second inequality is due to our previous bound; and the last inequality is due to our prior bounds on $|P|$. This proves the claim. 

Combining @e:proof_thm_1 and @e:proof_thm_2 we now obtain 
  $
  t dot (t-1) dot (t -delta dot blockclength -1) dot |cal(Z)_t| ≤ (M dot L)^3 dot epsilon_(sans("evader")) dot |cal(Z)|
  $
  and, since $t> delta dot blockclength +1$, both sides of the inequality are positive and then the theorem follows since $Pr_(z <- cal(Z))[ |A_z| ≥ t ] = |cal(Z)_t| \/ |cal(Z)|$.
]


#remark[Multiple DEEP samples in the original DEEP work @deep][
   We consider the question of what would happen if in the original soundness analysis of @deep we increase the amount of DEEP samples, or, more generally, use an arbitrary zero evader. Upon inspecting the proofs of  #aiedit[@deep[Theorem 3 and Lemma 28]]#footnote[In the eprint version of @deep, the corresponding results are Theorem 4.1 and Lemma 4.6], it is apparent that the proof can be  word-by-word generalized so as to use an abstract evader $(evalmap_z)_(z in cal(Z))$. However, the resulting error still requires a field of size $|FF| ≥ 2^(904)dot L^6$, when targeting $128$ bits of security (see our derivation below @e:original_deep_error). Indeed,  the only spot in the proofs of  #aiedit[@deep[Theorem 3 and Lemma 28]] where the zero evader error $epsilon_(sans("evader"))$   plays a role is when concluding that, in their notation, if $(x_0, P_(x_0)(z)), (beta_0, P_(beta_0)(z)), (gamma, P_(gamma)(z))$ are colinear over $FF times FF$ for more $z$'s than $epsilon_(sans("evader")) dot |cal(Z)|$ (for @deep, this is simply $codedim$ in Theorem 3 and $sigma/N$ in Lemma 28), then $(x_0, P_(x_0)(X)), (beta_0, P_(beta_0)(X)), (gamma, P_(gamma)(X))$ are colinear over $FF times FF[X]$. With an abstract zero evader, the proofs of #aiedit[@deep[Theorem 3 and Lemma28]] would then yield an error of 
  $
  max(2 dot L dot lr(( epsilon_(sans("evader")) + epsilon  ))^(1/3), (4)/(epsilon^2 dot |FF|)).
  $
  #aiedit[The derivation below @e:original_deep_error does not use the term $codedim\/|FF|$, hence it applies as is.]
]<r:original_deep_multiple_samples>

= Folding of constrained interleaved  codes with BEEP <s:BEEP_fold>

We now discuss how to use the soundness analysis from @t:main_thm so as to modify usual code-based IOPPs. In Section @s:BEEP_IOR we discuss the DEEP sampling and folding step, and then in Section @s:BEEP_WHIR we provide a full description of BEEP-based IOPP.

== The BEEP IOR<s:BEEP_IOR>

We assume the notation from Section @s:better_pretenders. Throughout this section, we fix the linear maps $theta_1, theta_2$ as $theta_1(alpha) = 1-alpha$ and $theta_2(alpha) = alpha$, so that  two words $u_1, u_2$ are folded as $(1-alpha) dot u_1 + alpha dot u_2$. These maps satisfy the assumption $a_1 dot d_2 != a_2 dot d_1$ made in Section @s:better_pretenders (where $theta_i(X)=a_i + d_i dot X$). 

Define the following relation:
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
langle vb(f), vb(v) rangle = sum_(vb(b)in {0,1}^(1+ log(codedim))) MLE(vb(f))(vb(b)) dot MLE(vb(v))(vb(b)).
$
where here we index the entries of the $2 times codedim$ matrices $vb(f)$ and $vb(v)$ over the set ${0,1}^(1+log codedim)$, so that the first bit in the index indicates the row of the matrix. This way $MLE(vb(f))(X, vb(Y)) = (1-X) dot MLE(vb(f)_(1*))(vb(Y)) + X dot MLE(vb(f)_(2*))(vb(Y))$, and similarly for $MLE[vb(v)](X, vb(Y))$, where $vb(Y)=(Y_1, dots, Y_(log(codedim)))$.


#construction[BEEP, an IOR from $cal(R)_(interleavedcode(2))$ to $cal(R)_(cal(C))$][
  The prover and verifier receive as input  $bb(x)=(mu, vb(v)) in FF times FF^(2 dot codedim)$. The verifier also receives $bb(y)=f in aiedit((FF^2)^blockclength)$, and the prover  receives $bb(w)=vb(f)in FF^(2 dot codedim)$ such that $(bb(x), bb(y), bb(w)) in cal(R)_(interleavedcode(2))$.
  \
  *Round 1 (DEEP sampling).* The verifier samples and sends uniformly at random $z ∈ 𝒵$. The prover replies with two vectors $𝐛_1, 𝐛_2 ∈ 𝔽^m$, supposedly 
    $
      𝐛_1 &= φ_z (𝐟_(1*)), &quad quad
      𝐛_2 &= φ_z (𝐟_(2*))
    $
  *Round 2 (Fold and sumcheck round).* 
    The prover sends the quadratic univariate polynomial#footnote[Some optimizations related to sumcheck may be used in this step, see e.g. @Gru24 and @BDDT25.]
    $
      h(X):= sum_(vb(b)in {0,1}^(log codedim)) MLE(vb(f))(X,vb(b)) dot MLE(vb(v))(X,vb(b)) in FF^(<3)[X]
    $
    The verifier checks that $h(0)+h(1) = mu$, and uniformly samples and sends a #emph[folding and sumcheck challenge] $alpha in FF$. Define
    $
      g &:= (1-alpha) dot f_(1*) + alpha dot f_(2*) in FF^blockclength, quad quad quad
      vb(g) &:= (1-alpha) dot  vb(f)_(1*) + alpha dot vb(f)_(2*) in FF^codedim, \
      vb(v)_alpha &:= (1-alpha) dot  vb(v)_(1*) + alpha dot vb(v)_(2*) in FF^codedim
    $
    Note that $MLE(vb(f))(alpha,vb(X))= MLE(aiedit((1-alpha) dot) vb(f)_(1*) + alpha dot vb(f)_(2*))(vb(X))= MLE(vb(g))(vb(X))$,   and similarly $MLE(vb(v))(alpha,vb(X)) = MLE(vb(v)_alpha)(vb(X))$ #albert-postponable[Place some remark about this]. If the prover is honest, then $vb(g)$ satisfies all of the following linear claims:
    $
      h(alpha) &= sum_(vb(b)in {0,1}^(log codedim)) MLE(vb(g))(vb(b)) dot MLE(vb(v)_alpha)(vb(b)) = langle vb(g)\, vb(v)_alpha rangle,\
      φ_z (𝐠) &= φ_z ((1-alpha) dot vb(f)_(1*)+alpha dot vb(f)_(2*)) = (1-alpha) dot 𝐛_1 + alpha dot 𝐛_2 .
    $<BEEP_new_lin_claims>

    #remco[This uses $1,α$ instead of $1-α,α$ from above def of $𝐠$. But I really want to rewrite it as some $α_z upright(F)$ for interleaving matrix $upright(F)$ and some multilinear evader $α_z$.]
  *Round 3 (Batching of linear claims).* The verifier uniformly samples $vb(γ) ∈ 𝔽^(m + 1)$ to batch the linear claims from @BEEP_new_lin_claims, so that the claims are reduced to the single claim
    $
      vb(gamma) dot mat(vb(v)_alpha; φ_z) dot vb(g) =
      vb(gamma) dot mat(h(alpha); aiedit((1-alpha) dot) 𝐛_1 + alpha dot 𝐛_2)
    $
  *Output.*  The prover and verifier output
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
   Let $cal(C) subset FF^blockclength$ be a linear code of blocklength $blockclength$ and dimension $codedim$, and with minimum relative distance  $Delta(cal(C))$. Let $delta in (0,Delta(cal(C)))$ be a proximity parameter such that $delta dot blockclength$ is an integer, and let $L_(cal(C)), L_(interleavedcode(2))$ be such that $cal(C)$ is $(delta, L_(cal(C)))$-list decodable and  $interleavedcode(2)$ is $(delta, L_(interleavedcode(2)))$-list decodable, respectively,  (we do not require decodability to be efficient).  Let $(φ_z)_(z ∈ cal(Z)_(sans("evader")))$ be a zero evader with error $epsilon_(sans("evader"))$.
  
  Then @c:BEEP is a perfectly complete three-round IOR from $cal(R)_(interleavedcode(2))$ to $cal(R)_(cal(C))$ with round-by-round knowledge soundness with relaxation $(cal(R)_(interleavedcode(2))^delta, cal(R)_(cal(C))^delta)$, with errors
  $
  kappa_1 &:= ((M dot L_cal(C))^3 dot epsilon_"evader")/((delta dot blockclength + 1)^2), quad quad quad 
  kappa_2 &:= (delta dot blockclength +1 + 2dot L_(interleavedcode(2)))/ (|FF|), quad quad quad 
  kappa_3 &:= (L_cal(C))/(|FF|),
  $
  where $M$ is either $|FF|$ or $epsilon_(sans("MCA")) dot |FF|$, for the $delta$-MCA error $epsilon_(sans("MCA"))$ of $cal(C)$. 
]<t:beep_soundness>


We defer the proof of @t:beep_soundness to Appendix @s:proof_rbr_knowledge, and only provide a brief outline of it here. The proof follows arguments similar to those in @zook@BCFW25, with the main difference being that @c:BEEP has one initial extra round (the DEEP sampling round). For this round, it suffices to let the knowledge state function become $1$ iff $|A_z| ≥ delta dot blockclength + 2$ or if the input triple $(inp,oracle, kswit)$ is valid, i.e. belongs to $cal(R)_(interleavedcode(2))^(delta)$. The main result @t:main_thm from Section @s:better_pretenders then shows that a flip from state $0$ to $1$ occurs with probability at most $kappa_1$. 

After the first round, if the state is $0$, we have $|A_z| < delta dot blockclength+2$. Because of this, at this point, we are in a setting where our two words $f_(1*), f_(2*)$ effectively meet an MCA-like property. In this scenario, the arguments from @zook@BCFW25 apply. In particular, the extractor uses erasure decoding, leveraging the MCA-like property that @t:main_thm provides. As with @zook@BCFW25, this means that the code $cal(C)$ does not require an efficient decoder.



== Example PCS: BEEP-WHIR and BEEP-Ligerito<s:BEEP_WHIR>



For completeness, we now obtain an IOR from $cal(R)_(interleavedcode(k))$ to $cal(R)_(cal(C)')$, where $cal(C)'$ is a new linear code of the same dimension as $cal(C)$. The oracle part $oracle'$ output of this IOR consists of a single oracle, which is supposedly an oracle to a codeword from $cal(C)'$ (this is in contrast to @c:BEEP, where the output $oracle'$ is a linear combination of other oracles). One can then repeatedly apply this IOR in order to obtain an IOPP (or, more intuitively, a PCS) for $cal(R)_(interleavedcode(k))$. The resulting IOPP is a "BEEP variant" of Ligerito @ligerito, or of WHIR @whir when using Reed-Solomon codes of different rates. 

#remark[BEEP-Basefold and BEEP-FRI-Binius @basefold@fribinius][
  One can equally envision BEEP variants of other code-based PCSs. For example, instead of performing the codeswitch step mentioned above, we could follow a more traditional approach where the spot checks made after repeatedly folding are verified by the verifier, rather than added as new terms to an ongoing sumcheck claim .  
]



 We mostly follow the blueprint of the Zook paper #aiedit[@zook[Theorem 9.12]] (though we do not consider zk in our case). Concretely, we first compose  @c:BEEP with itself $log k$ times, so as to obtain an IOR from  $cal(R)_(interleavedcode(k))$ to $cal(R)_(cal(C))$, and then we compose this IOR with the code-switching IOR from @zook, without zero-knowledge.

 Besides the fact that our folding step uses the BEEP sampling technique, this construction is well-known @whir@ligerito@blaze@zook. Because of this we discuss it only in broad terms.

 #construction[BEEP folding and code switching: an IOR from $cal(R)_(interleavedcode(k))$ to $cal(R)_(cal(C)')$][
    *Parameters.* The code $cal(C)$; a power of two $k$; a linear code $cal(C)'$ with message space $FF^codedim$ (possibly an interleaved code); zero evaders $(phi^((j))_z)_(z in cal(Z)_j)$ on $FF^(k dot codedim \/ 2^j)$ for $j in [log k]$, and $(phi'_z)_(z in cal(Z)')$ with $phi'_z : FF^codedim -> FF^(m')$; a number of queries $Q ≥ 1$. \
  *Inputs.* The prover and verifier receive as input $inp = (mu, vb(v)) in FF times FF^(k dot codedim)$ and $oracle = f in (FF^k)^blockclength$. The prover also receives $wit = vb(f) in FF^(k dot codedim)$ such that $(inp, oracle, wit) in cal(R)_(interleavedcode(k))$.\
  \
   *Step 1: Folding.* Let $(inp_0, oracle_0, wit_0) := (inp, oracle, wit)$ and #aiedit[$cal(C)_j = interleavedcode(k\/2^j)$] for $j≥ 0$. Note that $cal(C)_(j-1) = cal(C)_j^(equiv 2)$ for all $j≥ 1$. For $j in [log k]$, the prover and verifier engage in @c:BEEP to reduce the claim that 
    $(inp_(j-1), oracle_(j-1), wit_(j-1)) in cal(R)_(cal(C)_(j)^(equiv 2))
    $
    to a claim of the form
    $(inp_(j), oracle_(j), wit_(j)) in cal(R)_(cal(C)_(j))$
    for $inp_j, oracle_j, wit_j$ output by @c:BEEP.  Write $((hat(mu), hat(vb(v))), g, vb(g)) := (inp_(log k), oracle_(log k), wit_(log k))$. If the prover is honest, we have $((hat(mu), hat(vb(v))), g, vb(g)) in cal(R)_cal(C)$. 

    An important property of $g$ is that it is a linear combination of the rows of $f in FF^(k times blockclength)$. Hence the verifier can obtain $g(x)$ for any $x in [blockclength]$ by querying $f$.\
\
  *Step 2: Code switching.* We apply the IOR from #aiedit[@zook[Construction 9.9], without zero-knowledge]. The prover and verifier start with the claim $((hat(mu), hat(vb(v))), g, vb(g)) in cal(R)_cal(C)$ and proceed as follows:\
  \ 
  *Round 1 (New oracle and out of domain samples).* The prover sends a word $g'$, supposedly $g' = Enc_(cal(C)')(vb(g))$. The verifier uniformly samples and sends  $z' in cal(Z)'$. The prover replies with $vb(b)' in FF^(m')$, supposedly $vb(b)' = phi'_(z') (vb(g))$.\
  \
    *Round 2 (Queries).* The verifier uniformly samples and sends $x_1, dots, x_Q in [blockclength]$. If the prover is honest, then $vb(g)$ satisfies the following linear claims:
      $
        langle vb(g), hat(vb(v)) rangle &= hat(mu), quad  quad phi'_(z') (vb(g)) = vb(b)', quad  quad 
        (M_cal(C))_(x_i) dot vb(g) = g(x_i) quad "for all" i in [Q],
      $<e:codeswitch_lin_claims>
      where $(M_cal(C))_x$ denotes the $x$-th row of an encoding matrix $M_cal(C)$ of $cal(C)$.
      The verifier obtains the values $g(x_1), dots, g(x_Q)$ by querying $f$, as explained previously.\
\ *Round 3 (Batching of linear claims).* The verifier uniformly samples and sends $vb(gamma)' in FF^(1 + m' + Q)$ to batch the linear claims from @e:codeswitch_lin_claims into a single claim.\    
\ 
*Output.*  The prover and verifier output $inp' := (mu', vb(v)')$, $oracle' := g'$ and $wit' := vb(g)$, where
    $
      vb(v)' := vb(gamma)' dot (hat(vb(v)), phi'_(z'), (M_cal(C))_(x_1), dots, (M_cal(C))_(x_Q))^(sans("T")), quad
      mu' := vb(gamma)' dot (hat(mu), vb(b)', g(x_1), dots, g(x_Q))^(sans("T")).
    $
    For an honest prover, it holds that $(inp', oracle', wit') in cal(R)_(cal(C)')$.
 ]<c:BEEP_codeswitch>

#theorem[Completeness and round-by-round knowledge soundness of @c:BEEP_codeswitch][
 Let $(epsilon_j)_(j in [log k])$ and $epsilon'$ be error bounds of the zero evaders used in @c:BEEP_codeswitch. Let $delta in (0, Delta(cal(C)))$, with $delta dot blockclength$ an integer, and $delta' in (0,1)$. Let $L_0, dots, L_(log k)$ and $L'$ be such that $interleavedcode(k\/2^j)$ is $(delta, L_j)$-list decodable for all $j$, and $cal(C)'$ is $(delta', L')$-list decodable.

  Then @c:BEEP_codeswitch is a perfectly complete IOR from $cal(R)_(interleavedcode(k))$ to $cal(R)_(cal(C)')$ with #box[$3 dot log k + 3$] rounds and with round-by-round knowledge soundness with relaxation $(cal(R)_(interleavedcode(k))^delta, cal(R)_(cal(C)')^(delta'))$. Its errors are $(kappa_(j,1), kappa_(j,2), kappa_(j,3))_(j in [log k])$ for the three rounds of each execution of @c:BEEP during the Folding process, and  $(kappa'_1, kappa'_2, kappa'_3)$ for the three rounds of Step 2, where
  $
    kappa_(j,1) := ((M dot L_j)^3 dot epsilon_j) / ((delta dot blockclength + 1)^2), quad
    kappa_(j,2) := (delta dot blockclength + 1 + 2 dot L_(j-1)) / (|FF|), quad
    kappa_(j,3) := L_j / (|FF|), \
    kappa'_1 := ((L')^2 dot epsilon') / 2, quad
    kappa'_2 := (1 - delta)^Q, quad
    kappa'_3 := L' / (|FF|),
  $
  #aiedit[and] $M$ is either $|FF|$ or $epsilon_(sans("MCA")) dot |FF|$, for the $delta$-MCA error $epsilon_(sans("MCA"))$ of $interleavedcode(k\/2^j)$.
]<t:beep_codeswitch>

#proof[Proof outline][Once the completeness and round-by-round knowledge of the code-switching step are established, the theorem follows from
   @t:beep_soundness and the lemma for composing IORs (@r:ior_compositoin). The code switching step is an instantiation of  #aiedit[@zook[Construction 9.9]] without zero-knowledge, for the relations $cal(R)_cal(C)$ and #aiedit[$cal(R)_(cal(C)')$]. This IOR is clearly perfectly complete, and, by #aiedit[@zook[Lemma 9.11]]#albert[review lemma], this IOR  has round-by-round knowledge soundness with  relaxation $(cal(R)^delta_cal(C), cal(R)^(delta')_(cal(C)'))$ and errors $kappa'_1, kappa'_2, kappa'_3$ #aiedit[(in @zook the queries and the batching challenge are sent in the same round, with error $kappa'_2 + kappa'_3$; its proof analyses them one after the other, as we do)]#albert-postponable[Check if I should be more explicit mapping our notation to Zook's].
]



= BEEP with affine folding for Reed-Solomon codes<s:affine>

#let Cplus = $cal(C)^+$
#let chal = $FF^(sans("lin"))[X]$
#let RS(e) = $sans("RS")_(#e)$
#let ratlines = $cal(L)^(1)[chal arrow FF(X)]$
#let emul = $dot.o$
#let Cpair = $cal(C)_theta^(equiv 2)$


As we mentioned, in the context of Reed-Solomon codes, in @polygero and @CWYZ26, the authors propose, instead of sampling challenges $alpha$ in $FF$, to sample low degree polynomials. @CWYZ26 specifically samples $alpha$ in the set of linear polynomials $chal$, so that $alpha=alpha(X)= sigma + tau dot X$ for some random $sigma, tau in FF$. We refer to  Section @s:contributions for more details on @polygero@CWYZ26.

In this section we adapt the results from Section @s:better_pretenders to the same setting as @CWYZ26, i.e. we sample folding challenges $alpha$ in $chal$ instead of in $FF$. As a result,  the fraction of folding challenges that are DEEP-MCA-bad goes from $(delta dot blockclength + 1)\/|FF|$ (@t:main_thm) to #aiedit[$2\/|FF|$] (@t:affine_main_0).These techniques apply specifically to Reed-Solomon codes, and not to any linear codes as those of Sections @s:better_pretenders and @s:BEEP_fold. 

In  @r:affine_pairs we briefly outline how an IOPP using @t:affine_main_0 would look like, following  #aiedit[@CWYZ26[Section 5]]. 
We only mention one point to keep in mind when using @t:affine_main_0. In particular, we address one technical subtlety of @CWYZ26 and our result. This is that both results consider Correlated Agreement with a set of pairs of codewords $Cpair$, which is slightly larger than the interleaved code $interleavedcode(2)$ of the Reed-Solomon code $cal(C)$ at hand.  @r:affine_pairs discusses how to obtain Correlated Agreement with $interleavedcode(2)$, which is a technique presented in @CWYZ26[Section 5].

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



 Let $chal := {sigma + tau dot X | sigma, tau in FF} subset FF[X]$ be the set of linear polynomials on $FF$. As in Section @s:better_pretenders, fix two linear maps $theta_i (Y):= a_i + d_i dot Y$, $i=1,2$, with[Section] @s:better_pretenders, $a_1 dot d_2 != a_2 dot d_1$. Given two words $u_1, u_2in FF^blockclength$ and a folding challenge $alpha in chal$, we define the $alpha$-fold of $u_1, u_2$ as the word (recall our notation convention from @e:poly_times_word)
$
theta_1(alpha) dot u_1 + theta_2(alpha) dot u_2 in FF^blockclength.
$
Note that  if $c_1, c_2 in cal(C)$, then the folded word $theta_1(alpha) dot c_1 + theta_2(alpha) dot c_2$ belongs to $Cplus$ for all $alpha in chal$. 

For technical reasons, we will need to work with pairs of codewords $c_1, c_2 in Cplus$ whose fold belongs to $Cplus$ for all $alpha in chal$ #albert-postponable[Explain why. Overall, I need a good intutive explanation of the role of the degree differences in the affine fold]. These are precisely those in
$
Cpair := {(c_1, c_2) in Cplus times Cplus | d_1 dot c_1 + d_2 dot c_2 in cal(C)}.
$
In @CWYZ26, $Cpair$ is the set $Cplus times cal(C)$, which corresponds to the specific setting $lmap_1(alpha)=1$, $lmap_2(alpha)=alpha$, which is the one considered in @CWYZ26.

\
Let $u_1, u_2 in FF^blockclength$ be two words and let $delta in (0,1)$. Given $S subset [blockclength]$, we say that $(u_1, u_2)$ has #emph[Correlated Agreement with $Cpair$ over $S$ up to one position] if there exist a pair $(c_1, c_2) in Cpair$ and a set $S' subset S$ with $|S'| ≥ |S| - 1$ such that $u_1$ agrees with $c_1$ on $S'$ and $u_2$ agrees with $c_2$ on $S'$.

#definition[Pretender codeword][
  Let $u_1, u_2 in FF^blockclength$ be two words and let $alpha in chal$. We say that a codeword $c in Cplus$ is an #emph[$alpha$-pretender] (with respect to $u_1, u_2$) if $theta_1(alpha) dot u_1 + theta_2(alpha) dot u_2$ and $c$ agree on a set $S subset [blockclength]$ of size $|S| ≥ (1-delta) dot blockclength$ such that $(u_1, u_2)$ does not have Correlated Agreement with $Cpair$ over $S$ up to one position. We say that $alpha$ is #emph[MCA-bad] (with respect to $u_1, u_2$) if there exists an $alpha$-pretender.
]<d:affine_pretender>



#let evalmap = $vb(phi)$
#let samples = $vb(z)$


Let $numsamples≥ 1$ be a parameter. Given $samples=(z_1, dots, z_numsamples) in FF^numsamples$, let $evalmap_vb(z): FF[X] -> FF^numsamples$ consist of evaluating a polynomial at the entries of $samples$, i.e.
$
evalmap_samples (p) := (p(z_1), dots, p(z_numsamples)) in FF^numsamples.
$
This will be our zero evader, and is precisely the univariate evader from Section @s:zero_evaders  applied to the coefficients of $p$. 

Given $vb(b), vb(b)' in FF^numsamples$ we write $vb(b) emul vb(b)' in FF^numsamples$ for the  entrywise product of $vb(b)$ and $vb(b)'$. For any two $p,p' in FF[X]$ we have $evalmap_samples (p dot p') = evalmap_vb(z) (p) emul evalmap_vb(z) (p')$.

#definition[Consistency of MCA-bad elements $alpha in chal$ with $samples in FF^numsamples$][
  Let $alpha in chal$ and $c in Cplus$. Given $vb(z) in FF^numsamples$ and $vb(b)_1, vb(b)_2 in FF^numsamples$, we say that $(alpha, c)$ is _consistent_ with $(vb(z), vb(b)_1, vb(b)_2)$ if
  $
    evalmap_vb(z) (c) = evalmap_vb(z) (theta_1(alpha)) emul vb(b)_1 + evalmap_vb(z) (theta_2(alpha)) emul vb(b)_2.
  $
  When $alpha$ is MCA-bad and there exists an $alpha$-pretender $c in Cplus$ such that $(alpha, c)$ is consistent with $(vb(z), vb(b)_1, vb(b)_2)$, we say that $alpha$ is a _DEEP-MCA-bad challenge_ with respect to $vb(z), vb(b)_1, vb(b)_2$ and $u_1, u_2$.
]<d:affine_consistency>

For intuition, for an honest prover $vb(b)_1, vb(b)_2$ will be  values $evalmap_vb(z) (c_1), evalmap_vb(z) (c_2)$, where $(c_1, c_2) in interleavedcode(2)$  are $delta$-close to $u_1$ and $u_2$. 


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
We proceed to prove @t:affine_main_0. The proof is almost a word-by-word adaptation of that of @t:main_thm to the new definitions introduced above. The main difference is in @l:few_bad_points_on_line, which states that a parameterized line contains few pretenders. In its affine version, this is a generalization of @CWYZ26[Lemma 4.4] with a slightly better bound, and arbitrary folding weights $lmap_1(alpha), lmap_2(alpha)$ and proximity parameter $delta$. We include a proof for completeness. 

 We start with a new definition of parameterized lines. Below, $FF(X)$ denotes the set of all rational functions over $FF$, on the variable $X$.

#definition[Parameterized lines for the affine fold][
  We let $ratlines$ be the set of all maps $lmap: chal arrow FF(X)$ of the form $lmap(alpha) = F_lmap + alpha dot G_lmap$ for some $F_lmap, G_lmap in FF(X)$. Given $lmap in ratlines$, we let $im(lmap) = {(alpha, lmap(alpha)) | alpha in chal} subset chal times FF(X)$, and we call $im(lmap)$ a #emph[parameterized line].
]

   


#lemma[A parameterized line contains few pretenders, for the affine fold; analogue of @l:few_bad_points_on_line; slight generalization of @CWYZ26[Lemma 4.4]][
  Let $u_1,u_2 in FF^blockclength$ be two words, and let $lmap in ratlines$. Let $A_(lmap)^(sans("pret")) subset chal$ be the set of all  $alpha in chal$ such that $lmap(alpha) in Cplus$ and $lmap(alpha)$ is an $alpha$-pretender with respect to $u_1,u_2$. Then
  $
    |A_(lmap)^(sans("pret"))| ≤ max lr(( |FF|, thick ((delta dot blockclength + 2) dot (delta dot blockclength + 1)) / 2 )) = N.
  $ 
]<l:few_bad_points_on_line_0>
#proof[
  Fix $lmap = F_lmap + G_lmap dot Y in ratlines$. Recall that $theta_i (Y):= a_i + d_i dot Y$, $i=1,2$, with $a_1 dot d_2 != a_2 dot d_1$. As in the proof of @l:few_bad_points_on_line, since $a_1 dot d_2 != a_2 dot d_1$ there exist $F_1, F_2 in FF(X)$ such that $lmap(Y) = theta_1(Y) dot F_1 + theta_2(Y) dot F_2$ as polynomials on $Y$ (it suffices to solve the system of equations over the field $KK:=FF(X)$ obtained by equating the coefficients of the linear polynomials on $Y$ on both sides).

  
  Let $V subset chal$ be the set of all  $alpha in chal$ such that $lmap(alpha) in Cplus$. Note that $chal$ is a linear space of dimension two over $FF$. We claim that either $V = chal$ or $|V| ≤ |FF|$. If $V$ is empty there is nothing to prove, so assume that $V$ contains some $alpha_0$. Let $W subset chal$ be the set of all $beta in chal$ such that $beta dot G_lmap in Cplus$. Since $Cplus$ is an $FF$-vector space, $W$ is an $FF$-vector subspace of $chal$. Now, since $lmap(alpha_0) in Cplus$, an element $alpha in chal$ belongs to $V$ if and only if $(alpha - alpha_0) dot G_lmap in Cplus$, i.e. if and only if $alpha - alpha_0 in W$. It follows that $V = {alpha_0 + beta | beta in W}$, and so $|V| = |W|$. But  $W$ is an $FF$-vector space of dimension $≤2$, hence either $|V| ≤ |FF|$ or , or  $V = chal$.

  By definition $A_lmap^(sans("pret")) subset V$. Hence if $V != chal$, we have $|A_lmap^(sans("pret"))| ≤ |FF|$ and we are done. Hence assume $V=chal$. We claim that  $(F_1, F_2) in Cpair$. Indeed, since $V=chal$, we have $(theta(0), theta(1) - theta(0), theta(X) - theta(0)) = (F_lmap, G_lmap, X dot G_lmap) in Cplus^3$, meaning $F_lmap in Cplus$ and $G_lmap in cal(C)$.  We know that the following equality of polynomials holds
  $
  lmap(Y) = theta_1(Y) dot F_1 + theta_2(Y) dot F_2 = (a_1 dot F_1+ a_2 dot F_2) +  (d_1 dot F_1 + d_2 dot F_2) dot Y
  = F_lmap + Y dot G_lmap 
  $
  and so $a_1 dot F_1 + a_2 dot F_2 = F_lmap in Cplus$ and $d_1 dot F_1 + d_2 dot F_2 = G_lmap in cal(C)$. Since $a_1 dot d_2 != a_2 dot d_1$, solving this system we obtain that $F_1$ and $F_2$ are linear combinations of $F_lmap$ and $G_lmap$ with coefficients in $FF$, and so $F_1, F_2 in Cplus$. Hence  $(F_1, F_2) in Cpair$, as claimed.
  
  Similarly as in @l:few_bad_points_on_line, define $
    D := {i in [blockclength] | u_1(i) != F_1(x_i) " or " u_2(i) != F_2(x_i)} subset [blockclength].
  $

  Looking ahead, from here on the proof is analogous to that of @l:few_bad_points_on_line, except that the sets $S_alpha inter D$ (for $alpha in A_lmap^(sans("pret"))$) contain at least $2$ elements instead of $1$, and, for $alpha != alpha'$, these sets pairwise intersect on at most one element, instead of being pairwise disjoint.
  
   Let $alpha in A_lmap^(sans("pret"))$. Since $lmap(alpha)$ is an $alpha$-pretender, there is a set $S_alpha subset [blockclength]$ where $lmap(alpha)$ and $theta_1(alpha) dot u_1 + theta_2(alpha) dot u_2$ agree, with $|S_alpha| ≥ (1-delta) dot blockclength$ and such that $(u_1, u_2)$ does not have Correlated Agreement with $Cpair$ over $S_alpha$ up to one position. We argue that $|S_alpha inter D| ≥ 2$. Indeed, assume towards contradiction that $|S_alpha inter D| ≤ 1$, and let $S_alpha ' := S_alpha \\ D$. Then $S_alpha ' subset S_alpha$ is a set of size $≥ |S_alpha| -1$ over which $u_1,u_2$ agree with $F_1, F_2$, respectively (by definition of $D$). Since $(F_1, F_2) in Cpair$, this means that $(u_1, u_2)$ has Correlated Agreement with $Cpair$ over $S_alpha$ up to one position, a contradiction. Hence $|S_alpha inter D| ≥ 2$ for all $alpha in A_lmap^(sans("pret"))$.

 We now claim that for every two distinct  $alpha, alpha' in A_lmap^(sans("pret"))$ the set $(S_alpha inter D) inter (S_(alpha') inter D)$ has at most one element. Indeed, let $i in [blockclength]$ be an element of such set. Then #albert-postponable[Isn't it weird how $u_i$'s are indexed with $[blockclength]$?]
  $
    theta_1(alpha(x_i)) dot u_1(i) + theta_2(alpha(x_i)) dot u_2(i) =   theta_1(alpha(x_i)) dot F_1(x_i) + theta_2(alpha(x_i)) dot F_2(x_i),
  $
  and similarly for $alpha'$. Since $i in D$, the vector $(u_1(i) - F_1(x_i), u_2(i) - F_2(x_i))$ is nonzero, and so the vectors $(theta_1(alpha(x_i)), theta_2(alpha(x_i)))$ and $(theta_1(alpha'(x_i)), theta_2(alpha'(x_i)))$ are linearly dependent. Hence the determinant of $((a_1 + alpha(X) dot d_1, a_2 + alpha(X) dot d_2), (a_1 + alpha'(X) dot d_1, a_2 + alpha'(X) dot d_2))$ vanishes at $x_i$.  This determinant equals $(alpha(X)-alpha'(X)) dot (a_2 dot d_1 - d_2 dot a_1)$. Since we assumed $a_2 dot d_1 != d_2 dot a_1$, we have $alpha(x_i) = alpha'(x_i)$. Since $alpha!= alpha'$ are polynomials of degree at most one, there is at most one $i in D$ satisfying  $alpha(x_i) = alpha'(x_i)$.  This proves the claim.

  
  Because of the claim, every subset of $D$ with two elements is contained in $S_alpha$ for at most one $alpha in A_lmap^(sans("pret"))$. By the same argument as in the proof of @l:few_bad_points_on_line we have $|S_alpha inter D| ≥ |D| - delta dot blockclength$. Let $s := max(2, |D| - delta dot blockclength)$ so that $|S_alpha inter D|≥ s$ for all $alpha in A_lmap^(sans("pret"))$. Now,  double counting the set $E= {(alpha, {i,j}) | alpha in A_lmap^(sans("pret")),  {i,j} subset S_alpha inter D, thick i!=j}$,
  $
   |A_lmap^(sans("pret"))| dot (s dot (s-1)) / 2 ≤ |E| ≤  (|D| dot (|D| - 1)) / 2
  $
  where the second inequality uses that every subset of $D$ with two elements is contained in at most one $S_alpha$. Now
  if $|D| ≤ delta dot blockclength + 2$ then $s = 2$ and we are done. Otherwise $s = |D| - delta dot blockclength$ and
  $
    |A_lmap^(sans("pret"))| ≤ frac(|D|, |D| - delta dot blockclength) dot frac(|D| - 1, |D| - delta dot blockclength - 1) < frac(delta dot blockclength + 2, 2) dot (delta dot blockclength + 1),
  $
  completing the proof.
]
Equipped with @l:few_bad_points_on_line_0, we now prove @t:affine_main_0 by adapting word by word the proof of @t:main_thm to the affine folding setting.

\
#proof[Proof of @t:affine_main_0][
  We follow the proof of @t:main_thm, instantiated with $cal(C)$ a Reed-Solomon code, taking challenges $alpha in chal$ instead of in $FF$, and using the parameterized lines $ratlines$ instead of $linfuns$. We go through the proof and explain in what ways it is the same as that of @t:main_thm and, when it is not, we explain how to modify the proof to our setting. 
  
  First, let $(alpha_i, v_i)_(i in [3]) in (chal times Cplus)^3$ with $alpha_1, alpha_2, alpha_3$ pairwise distinct, and let
  $
    U((alpha_i, v_i)_(i in [3])) := (alpha_3 - alpha_1) dot (v_2 - v_1) - (alpha_2 - alpha_1) dot (v_3 - v_1).
  $
   $U((alpha_i, v_i)_(i in [3]))$ is a polynomial of degree at most $codedim + 1$ (unlike in @t:main_thm where it has degree $≤ codedim$). The analogue of @l:colinear holds: $(alpha_i, v_i)_(i in [3])$ belongs to the same parameterized line from $ratlines$ if and only if $U((alpha_i, v_i)_(i in [3])) = 0$ as a polynomial. The proof goes through exactly as in @l:colinear #albert[Double check],  where now operations take place in $FF(X)$ rather than in $FF$.

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
  
  Finally, let $P subset chal times Cplus$ be the set of all tuples $(alpha, c)$ such that $c$ is an $alpha$-pretender. Since $Cplus$ is $(delta, L)$-list decodable, $|P| ≤ |chal| dot L = |FF|^2 dot L$. Let $(alpha_i, c_i)_(i in [3]) in P^3$ be such that $U((alpha_i, c_i)_(i in [3])) != 0$. Then since $U((alpha_i, c_i)_(i in [3]))$ is a polynomial of degree at most $codedim+1$ (note that in @t:main_thm it would be of degree at most $codedim$), there are at most $(codedim + 1)^numsamples$ elements $vb(z) in FF^numsamples$ such that the triple belongs to $T_vb(z)$. Using now the same double counting arugment as in the proof of @t:main_thm,
  $
   t dot (t-1) dot (t -N) dot |cal(Z)_t| ≤ sum_(vb(z) in cal(Z)_t) |T_(vb(z))|  ≤ sum_(vb(z) in FF^numsamples) |T_vb(z)| ≤ (|FF|^2 dot L)^3 dot (codedim + 1)^numsamples,
  $
  where $cal(Z)_t$ is the set of tuples $vb(z) in FF^numsamples$ such that $|A_vb(z)| ≥ t$. Again, this completes the proof since $Pr_(vb(z) <- FF^numsamples)[ |A_vb(z)| ≥ t| ] = |cal(Z)_t|\/|FF|^numsamples$.
]



#remark[Correlated Agreement with $interleavedcode(2)$ instead of $Cpair$][
  #albert[review] In @d:affine_pretender we ask for Correlated Agreement with $Cpair$, and not with $interleavedcode(2)$, i.e. with pairs of codewords of $cal(C)$ as in Section @s:better_pretenders. The set $Cpair$ strictly contains $interleavedcode(2)$, and so, when a codeword $c in Cplus$ agrees with the $alpha$-fold of two words $u_1, u_2$ on a subset of $[blockclength]$ of size at least $(1-delta) dot blockclength$, and $c$ is not an $alpha$-pretender, we obtain a pair from $Cpair$ that is close to $(u_1, u_2)$, and this pair need not belong to $interleavedcode(2)$. Here and below, we say that a pair of codewords $(c_1, c_2)$ is #emph[close] to a pair of words $(w_1, w_2)$ if there is a subset of $[blockclength]$ of size at least $(1-delta) dot blockclength - 1$  where $w_1$ agrees with $c_1$ and $w_2$ agrees with $c_2$.

  In a bigger protocol, for example when aiming to build an IOR from $cal(R)_(interleavedcode(2))$ to $cal(R)_cal(C)$ using affine folds, one would instead prefer to obtain a pair from #aiedit[$interleavedcode(2)$] instead of $Cpair$. This can be ensured  using the methods described in @CWYZ26[Section 5]. To do so, one can have an initial communication round where the verifier samples an additional challenge $xi in FF$, and replaces the words $u_1$ and $u_2$ by $u'_1:=u_1$  and $u'_2:=u_2 + xi dot u_1$, and then proceeds to perform the DEEP sampling and the affine folding with these two words instead of $u_1$ and $u_2$. One also performs analogous linear changes on the witness and any linear constraints placed on the witness.

  The reason this works is the following. Let $Lambda$ be the set of all pairs of codewords of $Cplus$ that are close to the original words $(u_1, u_2)$. Note that $Lambda$ does not depend on $xi$, since $u_1, u_2$ are fixed before $xi$ is sampled. On the other hand, the pairs of codewords of $Cplus$ that are close to the new words $(u'_1, u'_2)$ are the pairs $(c_1, c_2 + xi dot c_1)$ with $(c_1, c_2) in Lambda$. 

  Now let $(c_1, c_2) in Lambda$. If $(c_1, c_2)$ belongs to $interleavedcode(2)$, then so does $(c_1, c_2 + xi dot c_1)$, for all $xi in FF$. Otherwise we claim that $(c_1, c_2 + xi dot c_1)$ belongs to $Cpair$ for at most one $xi in FF$. Indeed, let $s_1, s_2 in FF$ be the  coefficients of the monomial $X^codedim$ of $c_1$ and $c_2$, which are not both zero. By definition of $Cpair$, the pair $(c_1, c_2 + xi dot c_1)$ belongs to $Cpair$ if and only if $d_1 dot s_1 + d_2 dot (s_2 + xi dot s_1) = 0$. Here we assume that $d_2 != 0$ (this is the case for the folding maps $(theta_1, theta_2)=(1, alpha)$ and $(1-alpha, alpha)$). Then this equation has at most one solution $xi$, proving the claim. 

  Hence there are at most $|Lambda|$ elements $xi in FF$ for which some pair from $Cpair$ that is close to the new words does not belong to $interleavedcode(2)$. . For the rest of $xi in FF$, every pair $(c'_1, c'_2)$ from $Cpair$ that is close to $(u'_1, u'_2)$ belongs to $interleavedcode(2)$. From such a pair we obtain $(c'_1, c'_2 - xi dot c'_1) in interleavedcode(2)$, which is close to $(u_1, u_2)$. Note that $|Lambda|$ is bounded by the list size of  $(Cplus)^(equiv 2)$ at distance $delta + 1\/blockclength$.
]<r:affine_pairs>



= An alternative and more general proof of @t:main_thm via linear algebra<s:high_arity>


In this section we present the  proof of @t:main_thm in an alternative way where folding is an arbitrary random linear map, structured as a zero-evader.

//We emphasize that the higher arity instantiation of this result  is  not used in the IOR and IOPP  constructions from Section @s:BEEP_fold. This is because, as it stands, applying the BEEP IOR (@c:BEEP) at every sumcheck round requires less DEEP samples than having one big DEEP sampling step before every full sumcheck. 


== Zero-evaders

We use the notion of a zero evader from @BCFW25, expressed as an indexed family of linear maps with vector-valued outputs and error bounds for subspaces. This allows stronger bounds when testing several vectors to be zero simultaneously as they all map to zero exactly when their span does. We bound the probability of this event for any fixed subspace in a given family.

#definition[Zero evader][
  A _zero evader_ is a family of linear maps $φ_z : 𝔽^n → 𝔽^m$ indexed by a finite non-empty set $𝒵$, called the _seeds_. For a nonempty family $𝒲$ of linear subspaces of $𝔽^n$, we call $ε_𝒲 ∈ [0,1]$ an _error bound_ if
  $
    max_(W ∈ 𝒲) thick Pr_(z ← 𝒵) thick [W ⊆ ker φ_z] ≤ ε_𝒲.
  $
]

#albert-postponable[it would be good to add an example of how a zero evader would look like for a nontrivial family of subspaces. i think some readers will replace the subspace by a tuple of codewords after staring at the definition]

#remark[
  In a given basis $φ_z$ is a $m × n$ matrix such that $φ_z (𝐯) = φ_z · 𝐯$. When $m=1$ we call it a _scalar zero evader_.
]

#remark[
  For $1 ≤ d ≤ n$ we write $ε_d$ for an error bound where $𝒲$ consists of all $d$-dimensional subspaces. By subspace containment, these bounds may be chosen so that $ε_d ≥ ε_(d+1)$ for $1 ≤ d < n$, which we require.

  In particular $ε_1$ recovers the error bound from @BCFW25.
  Intuitively, $ε_d$ bounds the probability of annihilating any fixed collection of $d$ linearly independent vectors simultaneously.

]

#lemma[Few folding vectors lie in a subspace][  #albert-postponable[Are Lemma 31, 33, 34 needed here? If not they could be placed after the statement of the main thm]
  Let $(ψ_z)_(z ∈ 𝒵)$ be a scalar zero evader on $𝔽^n$ with error bounds $ε_d$. 
  For every $j$-dimensional subspace $H ⊂ 𝔽^n$ with $0 ≤ j < n$, we have
  $abs({z | ψ_z ∈ H}) &≤ abs(𝒵) ε_(n - j).
  $
]
#proof[
 #albert-postponable[it was not clear to me what $psi in H$ means] The condition $ψ_s ∈ H$ is equivalent to $H^⟂ ⊆ ker ψ_s$ and $dim H^⟂ = n - j$. The result follows from the definition of $ε_(n - j)$.
]
#secretsection[
  #corollary[
  Given $S ⊆ 𝒵$ such that $abs(S) > abs(𝒵) ε_1$, the family $(ψ_z)_(z ∈ S)$ contains a basis for $𝔽^n$.
] <thm:ze-basis>
#proof[
  If their span had dimension $j < n$ we would have a contradiction $abs(S) ≤ abs(𝒵) ε_(n - j) ≤ abs(𝒵) ε_1$.
]
]

#secretsection[
#definition[Univariate evader][
  Define the $m$-sample _univariate evader_ with index family $𝒵 ≔ 𝔽^m$ and $φ_𝐳$ for $𝐳 = (z_1, …, z_m)$ as the map given by the $m × n$ Vandermonde matrix on $𝐳$.
]
#secretsection[
  #lemma[
    The $m$-sample univariate zero evader has error bounds
    $
      ε_d = min(1, ((n - d) / q)^m).
    $ 
  ]
  #proof[To do.]
  #albert-postponable[Prove]
]

#remark[
  We do not require the $z_i$ to be distinct. When applied to message coordinates, the univariate zero evader matches the $m$-repeated out of domain samples in WHIR @whir, and the codeword queries in the Reed-Solomon instantiation of Ligerito @ligerito, etc.

#definition[Multilinear evader][
  Let $k = ceil(log_2 n)$ and fix a basis. We define the scalar _multilinear evader_ with index family $𝒵 ≔ 𝔽^k$ and $φ_𝐳$ for $𝐳 = (z_1, …, z_k)$ as the first $n$ values of the MLE tensor product
  $φ_𝐳 = (⨀_(i ∈ [k]) mat(1 - z_i; z_i))_[n] .
  $
]
]
#secretsection[
  #lemma[
    For $1 ≤ d ≤ n$ let $r = ceil(log_2 n) - floor(log_2 d)$. The multilinear evader
    has error bounds
    $
      ε_d = 1-(1-1/q)^r ≤ min(1, r/ q).
    $
  ]
  #proof[To do.]
  #albert[prove]
]

#definition[Product zero evader][
  For $j ∈ [k]$, let $ψ^j_(z_j) : 𝔽^(b_j) → 𝔽$
  be scalar zero evaders indexed by $𝒵_j$, with
  error bounds $ε^(j)_d$.
  Their _product zero evader_ has domain $𝔽^b$,
  where $b = product_(j ∈ [k]) b_j$, index set  and maps
  $𝒵 &= 𝒵_1 × ⋯ × 𝒵_k, &quad
    ψ_𝐬 &= ψ^(k)_(s_k) ⊗ ⋯ ⊗ ψ^(1)_(s_1).
  $
]
]
== Few bad seeds via linear algebra 

We start by fixing notation. Let $𝔽$ be a finite field of size $q = abs(𝔽)$. We denote with $(q)_(n+1)$ the falling factorial $q(q-1)⋯(q-n)$. We let $ℓ$ be the message length, $n$ the code length, $b$ the folding size and $m$ the check size. Let $𝒞 ⊆ 𝔽^n$ be a code of dimension $ℓ$ that is $(δ, L)$-list decodable and has MCA bound $E$.

We use two zero evaders, one for folding and one for checking. For folding we use a scalar zero evader $ψ_s ∈ 𝔽^(1 × b)$ with seeds $s ∈ 𝒵_fold$ and error bounds $ε^fold_d$. We abbreviate $N = abs(𝒵_fold)$. For checking we use a zero evader $φ_z ∈ 𝔽^(m × ℓ)$ with seeds $z ∈ cal(Z)_check$ and error bounds $ε^check_d$. We define $hat(φ)_z ∈ 𝔽^(m × n)$ as $φ_z Enc_𝒞^(-1)$, where $Enc_𝒞^(-1)$ is a left inverse of $Enc_𝒞$.

#albert-postponable[seed sounds strange to me, but i think we havent established any name for z yet. we should do that when defining zero evaders. maybe "sample seeds"?]

#albert-postponable[I think having a zero evader for folding may not be worth the generality. The problem I see is that it introduces several symbols that replaces commonly recognized symbols. For example $N=|cal(Z)_(sans("fold"))|$ being an abstraction of $|FF|$ has a relatively high cognitive tax when combined with the rest of the new things happening in this section (at least for me). Maybe keeping $|cal(Z)_(sans("fold"))|$ instead of $N$ would already help]\
*Setup.* Abstractly, the protocol we are interested in is as follows:

#[
#set enum(indent: 0pt) // this list starts at the left margin
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
]

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
  Let $β = ceil(δ n) N ε^fold_1$ then $abs(A_z) ≤ E$ and for any $β < t ≤ E$, #albert-postponable[I would only use falling factorial notation inside the proof. Also I'd define $beta$ only inside the proof, no reason to have it in the statement IMO] 

  
  #albert-postponable[We should make very clear that we don't necessarily need E to be small, i.e. we can set it to $N$ so we don't need MCA at all]
  $
    Pr_(z ← 𝒵_check)[ abs(A_z) ≥ t] ≤ 
        ((E)_(b+1) L^(b+1) ε^check_1) /
    ((t - β) product_(d ∈ [b]) (t - N ε^fold_d)).
  $
] <thm:main_batch>

In particular, for sumcheck folding we obtain a bound cubic in the list size.

#corollary[Sumcheck folds][
  Sumcheck rounds fold using a multilinear evader $ψ_α = (1-α, α)$, so we have $b = 2$, $N = q$, $ε^fold_1 = 1/q$ and $ε^fold_2 = 0$ and hence for $t > ceil(δ n)$,
  
  $
    Pr_(z ← 𝒵_check)[ abs(A_z) ≥ t] ≤ 
        ((E)_3 L^3 ε^check_1) /
    (t (t - 1) (t - ceil(δ n))).
  $
]

#[
  #set heading(outlined: false)
  === Proof of @thm:main_batch
]
We will show that $b$ linearly independent folding vectors#albert[folding zero evaders?], together with their codewords, determine a unique explanation $D$#albert[not defined?]. An additional codeword can contradict that explanation; any fixed such collection #albert[not sure what such refers to here :)] passes checking with probability at most $ε^check_1$.

#lemma[Explanation][
  Let $ψ_s_1, …, ψ_s_b$ form a basis #albert[why does the set of evader have dimension b?] and let $𝐜_1, …, 𝐜_b ∈ 𝒞$. They determine a unique $D ∈ 𝒞^b$ satisfying $ψ_s_i D = 𝐜_i$. If these pairs each satisfy the checking equation @eq:consistency, then $D hat(φ)_z^⊤ = B(z)$. #albert[I think $psi_s$ and $phi_z$ may look to similar. I'd use $psi^(sans("fold"))_s$ and $psi^(sans("sample"))_z$ or something of the likes]
]<thm:explanation>
#proof[
  Since $ψ_s_i$ form a basis, the system $ψ_s_i D = 𝐜_i$ for $i ∈ [b]$ has a unique solution $D$. Its rows are linear combinations of $𝐜_i$ so $D ∈ 𝒞^b$. For $i ∈ [b]$ we have $ψ_s_i (D hat(φ)_z^⊤ - B(z)) = 𝟎$ and since $ψ_s_i$ form a basis it follows $D hat(φ)_z^⊤ - B(z) = 𝟎$.
]

#lemma[Contradiction][
  Fix the $b$ pairs #albert[it would be good to explicitly refer to the pairs or to say instead "assuming the notation of Lemma 44"] from @thm:explanation and their explanation $D$, independently of $z$. Fix an additional pair $(s, 𝐜)$ with $𝐜 ∈ 𝒞$ and $𝐜 ≠ ψ_s D$. If all $b+1$ pairs satisfy @eq:consistency, then $(𝐜 - ψ_s D) hat(φ)_z^⊤ = 𝟎$. The probability over $z ← 𝒵_check$ of this event is at most $ε^check_1$.
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

  At an intersecting column $i$ we have $ψ_s (U_(*i) - D_(*i)) =  𝟎$. Each discrepancy is fixed and nonzero. A union bound then gives
  $abs({s ∈ 𝒵_fold | ψ_s D ∈ 𝒫_s}) ≤ abs(J) N ε^fold_1 ≤ ceil(δ n) N ε^fold_1.
  $
]

We now count collections that contradict their explanation while passing all checks. Each fixed collection passes rarely, but many bad seeds produce many such collections.

#definition[
  Let $M(z)$ count ordered collections of $b+1$ pairs $(s_i, 𝐜_i)$ with distinct folding seeds $s_i$ and pretender codewords $𝐜_i ∈ 𝒫_(s_i)$ that all satisfy consistency check @eq:consistency such that $(ψ_(s_i))_(i∈ [b])$ is a basis and $𝐜_(b+1) ≠ ψ_(s_(b+1)) D$, where $D$ is the explanation from @thm:explanation.
]

#lemma[Upper bound][
  $limits(𝔼)_(z ← cal(Z)_check) [M(z)] ≤ (E)_(b+1) L^(b+1) ε^check_1.
  $
]
#proof[
  The lists $𝒫_s$ are fixed independently of $z$. By @eq:proximity and $(δ, L)$-list decodability of $𝒞$, each satisfies $abs(𝒫_s) ≤ L$ and is nonempty for at most $E$ folding seeds. There are therefore at most $(E)_(b+1) L^(b+1)$ possible ordered collections with distinct seeds. Each fixed collection whose final pair contradicts the explanation of its first $b$ pairs passes all checks with probability at most $ε^check_1$, by @thm:contradiction-check. Summing these probabilities gives the bound.
]

#lemma[Lower bound][
  Let $a = abs(A_z)$, if $a > β$ then
  $M(z) ≥ (a - β) product_(d ∈ [b]) (a - N ε^fold_d).
  $
]
#proof[
  For each $s ∈ A_z$, fix a pretender $𝐜_s$ such that $𝐜_s hat(φ)_z^⊤ = ψ_s B(z)$. Membership in $A_z$ guarantees such a choice.
  
  After choosing $j < b$ independent folding vectors, their span contains at most $N ε^fold_(b -j)$ seeds. Thus there are at least
  $product_(d ∈ [b]) (a - N ε^fold_d)
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
    Pr_(z ← 𝒵_check)[abs(A_z) ≥ t] (t - β) product_(d ∈ [b]) (t - N ε^fold_d) ≤ (E)_(b+1) L^(b+1) ε^check_1.
  $
  The result follows from dividing by the positive left hand factors.
]

#secretsection[
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
    Pr_(z ∈ 𝒵_check)[
      abs(A_z)/(product_(j ∈ [k]) N_j) ≥ sum_(j ∈ [k]) t_j / N_j
    ] ≤ sum_(j ∈ [k]) p_j (t_j)
  $
]

If all the $b_j$, $N_j$, $ε^((d))_j$ and $t_j$ are the same (but not necessarily the list bounds $L_j$), we have the stronger conjecture

#theorem[Homogenous composition conjecture][
  For $t > β$, we have
  $
    Pr_(z ∈ 𝒵_check)[
      abs(A_z)/N^k ≥ (k t) / N
    ] ≤ 1/k sum_(j ∈ [k]) p_j (t)
  $
]
]

#bibliography("bibliography.bib", style: "ieee-alpha.csl")

#counter(heading).update(0)
#set heading(numbering: "A.1", supplement: [Appendix])


= Proof of completeness and round-by-round knowledge soundness of the BEEP-IOR  <s:proof_rbr_knowledge>

#proof[
 We prove @t:beep_soundness. Let $Pi$ denote @c:BEEP. In our formalization of IORs (Section @s:IOR), every round starts with the prover sending a message, and then the verifier replies with a challenge. Since, as described, Rounds 1 and 3 of @c:BEEP start off with a verifier challenge, we modify $Pi$ so that the prover sends  empty messages at the beginning of those rounds. 

It is clear that $Pi$ is perfectly complete#albert-postponable[review?]. We prove soundness of $Pi$.  Let $inp=(mu,vb(v))in FF times FF^(2 times codedim)$ and  $oracle=f in FF^(2 times blockclength)$, with $f=(f_(1*), f_(2*))$. Let $tr$ be a partial interaction transcript for $Pi$.

We progressively describe a knowledge state function $kstate$ for $Pi$. For all $kswit$, if  $tr = emptyset$ is the empty transcript, then we set $kstate(inp, oracle, tr, kswit) = 1$ if and only if $(inp, oracle; kswit) in cal(R)_(interleavedcode(2))^delta$. If $tr$ is a transcript where the prover is about to move, then we define $kstate(inp, oracle, tr, provermsg, kswit) = kstate(inp, oracle, tr, kswit)$ for every prover message $provermsg$. If $tr = (provermsg_1, verifiermsg_1, provermsg_2, verifiermsg_2, provermsg_3, verifiermsg_3)$ is a full transcript, then we define $kstate(inp, oracle, tr, kswit) = 1$ if and only if $verifier$ on $tr$ outputs $(inp', oracle')$ such that $(inp', oracle'; kswit) in cal(R)_(cal(C))^delta$.

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
We show that @e:beep_soundness_prob_1 is at most $kappa_1$ as defined in the statement of the present @t:beep_soundness. Indeed, assume $kstate(inp, oracle, m_1,  kswit) = 0$. Then by definition we have $(inp,oracle, kswit) in.not cal(R)_(interleavedcode(2))^delta$.  The only way we can have  $kstate(inp, oracle, m_1, z, kswit) = 1$ then is if $ abs(A_z) ≥ delta dot blockclength +2$. By @t:main_thm taking $t= delta dot blockclength+2$,  we have $Pr_(z <- cal(Z))[ abs(A_z) ≥ delta dot blockclength+2] ≤ (M dot L_cal(C))^3 dot epsilon_(sans("evader")) \/ ((delta dot blockclength + 2) dot (delta dot blockclength + 1)) ≤ kappa_1$, where $M$ is as in the statement of @t:beep_soundness. It follows that $s_1 ≤ kappa_1$.

//Indeed, assume $kstate(inp,oracle, m_1, kswit) = 0$. Then either $langle kswit, vb(v) rangle != mu$ or $hamming(f, Enc_cal(interleavedcode(2))(wit)) > delta$. Assume first that $langle kswit, vb(v) rangle != mu$. Then by definition $kstate(inp,oracle, m_1 || z, kswit)=0$ as well, hence $S_1=0$. Otherwise  

#paragraph[Round 2.] Let $m_1=emptyset$ be an empty first prover message; $z in cal(Z)$ a verifier first challenge; and $m_2=(vb(b)_1, vb(b)_2 , h(X))  in FF^numsamples times FF^numsamples times FF^(<3)[X]$ a second prover message. Let $tr=(m_1, z, m_2)$. For every second verifier challenge $alpha in FF$, we let 
$
kstate(inp, oracle, tr, alpha, kswit) = 1 " " <==>  " " |A_z|≥ delta dot blockclength + 2 " or "
lr((cases(delim:#none,
& kswit  in FF^(codedim),
and & h(0)+h(1) = mu,
and & langle kswit\, (1-alpha) dot vb(v)_(1*) + alpha dot vb(v)_(2*)  rangle = h(alpha),
and &  φ_z kswit =  aiedit((1-alpha) dot) 𝐛_(1) + alpha dot 𝐛_(2),
and & hamming(aiedit((1-alpha) dot) f_(1*) + alpha dot f_(2*), Enc_cal(C)(kswit)) ≤ delta 
))) //" or " langle kswit, vb(v)  rangle != mu,
$ 
We define an extractor $rbrextractor$ for transcripts of the form $(tr, alpha)$ as follows. #albert-postponable[Mention somewhere this is similar to the techniques from "linear time accumulation schemes"] The extractor proceeds under the assumption that $Delta(aiedit((1-alpha) dot) f_(1*) + alpha dot f_(2*), Enc_cal(C)(kswit))≤delta$. If that is not the case, the extractor may fail and output $bot$.  The extractor computes $Enc_cal(C)(kswit)$ and finds the maximal set $S_alpha subset [blockclength]$ where $Enc_cal(C)(kswit)$ and $aiedit((1-alpha) dot) f_(1*) + alpha dot f_(2*)$ agree. If $|S_alpha| < (1-delta) dot blockclength$, the extractor outputs $bot$.

Next, the extractor computes $kswit_(1*), kswit_(2*) in FF^codedim$ such that  $Enc_cal(C)(kswit_(i*))$ agrees with $f_(i*)$ on $S_alpha$ for both $i=1,2$, with the following procedure: let $M_cal(C) in FF^(blockclength times codedim)$ be an encoding matrix for $cal(C)$. The extractor sets up the following system of linear equations  on variables $(kswit_(1*), kswit_(2*))$: 
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

We further define a subset of challenges  $B_2 subset FF$ as follows. Let $W subset FF^(2 times codedim)$ be the set of messages $kswit'$ such that $hamming_(interleavedcode(2))(Enc_(interleavedcode(2))(kswit'), f) ≤ delta$. Since $interleavedcode(2)$ is $(delta, L_(interleavedcode(2)))$-list decodable, $|W|≤ L_(interleavedcode(2))$. Then we let $B_2 subset FF$ be the set of all $alpha in FF$ such that for some $kswit'=(kswit_(1*), kswit_(2*)) in W$, we have
$
h_(kswit')(X) != h(X) quad " and " quad h_(kswit')(alpha) = h(alpha)
$
where $h_(kswit')(X)$ is the quadratic polynomial $h_(kswit')(X) := langle aiedit((1-X) dot) kswit_(1*) + X dot kswit_(2*), aiedit((1-X) dot) vb(v)_(1*) + X dot vb(v)_(2*) rangle$. If $h_(kswit')(X) != h(X)$, then there are at most $2$ field elements $alpha$ such that  $h_(kswit')(alpha) = h(alpha)$, and so $|B_2| ≤ 2 dot |W|≤ 2 dot L_(interleavedcode(2))$.

We show that if $alpha in.not B_1 union B_2$, then $kstate(inp,oracle, tr, alpha, kswit)=1$ implies that $kstate(inp,oracle, tr, rbrextractor(inp,oracle,tr, alpha,kswit))=1$. Once this claim is proved, it follows that
$
s_2 ≤ (|B_1| + |B_2|)/(|FF|) ≤ (delta dot blockclength + 1 + 2 dot L_(interleavedcode(2)))/(|FF|) = kappa_2 
$

To prove the claim, assume $kstate(inp,oracle, tr, alpha, kswit)=1$. Then $aiedit((1-alpha) dot) f_(1*) + alpha dot f_(2*)$ and  $Enc_cal(C)(kswit)$ agree on the set $S_alpha subset [blockclength]$ computed by the extractor, with $|S_alpha| ≥ (1-delta) dot blockclength$. Since $alpha in.not B_1$, $alpha$ is not DEEP-MCA-bad with respect to $(z, vb(b)_1, vb(b)_2, f_(1*), f_(2*))$. Now, $(alpha, Enc_cal(C)(kswit))$ must be consistent with $(z, vb(b)_1, vb(b)_2)$ because $phi_z (Enc_cal(C)(kswit)) = phi_z (kswit) = aiedit((1-alpha) dot) vb(b)_(1) + alpha dot vb(b)_(2)$ and $hamming(aiedit((1-alpha) dot) f_(1*)+alpha dot f_(2*), Enc_cal(C)(kswit))≤ delta$ due to  $kstate(inp,oracle, tr, alpha, kswit)=1$. Hence, $Enc_cal(C)(kswit)$ is not an $alpha$-pretender. This means that $f_(1*), f_(2*)$ have correlated agreement with $cal(C)$ over $S_alpha$. By our previous claim, the system of equations @e:system_beep_soundness has a solution $kswit'=(kswit_(1*), kswit_(2*))in FF^(2 times codedim)$, which is output by the extractor. Now, $kstate(inp,oracle, tr, kswit')=1$ if and only if $|A_z|≥ delta dot blockclength +2$ or $(inp, oracle, kswit') in cal(R)_(interleavedcode(2))^delta$.  We assumed the former does not occur, and so we now have to show that $(inp, oracle, kswit') in cal(R)_(interleavedcode(2))^delta$, i.e. we must prove that $langle kswit', vb(v) rangle = mu$ and $hamming_(interleavedcode(2))(f, Enc_(interleavedcode(2))(kswit')) ≤ delta$ . The second holds because $f_(1*), f_(2*)$ agree with $Enc_cal(C)(kswit_(1*)), Enc_cal(C)(kswit_(2*))$ on $S_alpha$. We now prove the first. We know that $langle kswit, aiedit((1-alpha) dot vb(v)_(1*) + alpha dot vb(v)_(2*))  rangle= h(alpha)$ and that $kswit=(1-alpha) dot kswit_(1*) + alpha dot kswit_(2*)$, and so $h_(kswit')(alpha) = h(alpha)$. Since $kswit' in W$ and  $alpha in.not B_2$, we must have that $h_(kswit')(X) = h(X)$. Since $h(0) + h(1)= mu$, we obtain 
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
We show that $s_3 ≤ kappa_3 = L_cal(C) \/ |FF|$. Indeed, assume $kstate(inp, oracle, tr, kswit) = 0$  and $kstate(inp, oracle, tr, vb(gamma), kswit) = 1$ for some $kswit$. Since $verifier(inp, oracle, tr, vb(gamma))=1$, we have $h(0)+h(1)=mu$. Moreover since $(inp',oracle',kswit)in cal(R)_cal(C)^delta$, we have $kswit in FF^codedim$ and $hamming(g, Enc_cal(C)(kswit)) = hamming(aiedit((1-alpha) dot) f_(1*) + alpha dot f_(2*), Enc_cal(C)(kswit)) ≤ delta$. Hence, to have $kstate(inp, oracle, tr, kswit) = 0$ either $phi_z kswit != (1-alpha) dot vb(b)_1 + alpha dot vb(b)_2$, or $langle kswit, vb(v)_alpha rangle != h(alpha)$. On the other hand, since $(inp',oracle',kswit)in cal(R)_cal(C)^delta$, we have $langle kswit, vb(v)' rangle = mu'$, i.e.
$
 vb(gamma) dot (vb(v)_alpha, phi_z)^(sans("T")) dot kswit = vb(gamma) dot (h(alpha),(1-alpha) dot vb(b)_1 + alpha dot vb(b)_2)^(sans("T")).
$
By Schwartz-Zippel lemma the probability over $vb(gamma)$ that the above equality holds, for fixed $kswit$ for which one of these claims fails, is  $≤ (1)/(|FF|)$.  Finally, there are at most $L_cal(C)$ tuples $kswit in FF^codedim$ such that $(inp',oracle', kswit) in cal(R)_(cal(C))^(delta)$, and so, by a union bound, $s_3 ≤ aiedit(L_cal(C)) \/ |FF|$. 
]


