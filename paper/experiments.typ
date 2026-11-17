
#secretsection[
  = Instantiation and Experiments <s:experiments>
#aiedit[
We instantiate @c:BEEP_codeswitch with Reed-Solomon codes over $"GF"(2^128)$, and we compare the resulting PCS, "BEEP-Ligerito", with Ligerito @ligerito at $128$ bits of security. Our code (research code, not audited), the raw outputs and the scripts that write every number below are in our repository #albert[ref to repo].

#paragraph[BEEP-Ligerito.] We start from the implementation of Ligerito in Flock @flock. A message of $k dot codedim$ elements from $"GF"(2^128)$ is arranged in $k$ rows, each encoded with a Reed-Solomon code $cal(C)$ of rate $rho = 1\/2$. The rows are folded with $log k$ executions of @c:BEEP, and the folded message is committed with a code of smaller rate and queried, as in @c:BEEP_codeswitch, until the message is short. As zero evader we take $numsamples$ independent samples of the multilinear evader, with error $epsilon_"evader" = (log_2 e \/ |FF|)^numsamples$ on messages with $e$ entries. We take $delta = 1 - sqrt(rho) - eta$ for a small "slack" $eta > 0$, so that $cal(C)$ and its interleavings are $(delta, L)$-list decodable with $L = floor(1 \/ (2 dot eta dot sqrt(rho)))$ (see #albert[fill in]).

#paragraph[The error of a fold.] The proof of @t:beep_soundness goes through with any integer $t >= floor(delta dot blockclength) + 2$ in place of $delta dot blockclength + 2$ (this threshold of @t:main_thm only appears in the analysis, and agreement is counted in positions). The first two rounds of @c:BEEP have errors
$
kappa_1(t) = ((|FF| dot L)^3 dot epsilon_"evader") / (t dot (t-1) dot (t - floor(delta dot blockclength) - 1)), quad quad kappa_2(t) = (t - 1 + 2 dot L) / (|FF|).
$
We count $g$ bits of proof of work ("grinding") on a challenge as $g$ bits of security, as it is usual in practice @whir @flock. For a target of $lambda$ bits we take, for each $numsamples$, the least $t$ with $kappa_1(t) <= 2^(-lambda)$, and then the least $numsamples$ for which $kappa_2(t)$ needs the fewest whole bits of grinding.

@tab:errors shows these errors for $lambda = 128$, next to the error of a fold round of Ligerito under MCA. For the latter we take the bound of @DKT26[Theorem 4.4] on the number of MCA-bad challenges, which improves that of @BCHKS25[Theorem 4.6] and holds as well for interleaved codes @DKT26[Corollary 6.6], plus the term $2 dot L \/ |FF|$ of $kappa_2$.

#figure(
  exptable(10,
    (table.cell(colspan: 3)[first code], table.cell(colspan: 3)[Ligerito (fold with MCA)], table.cell(colspan: 4)[BEEP-Ligerito, $eta = #num("eta:beep")$],
     [size], [$k$], [$blockclength$], [fold, $eta = #num("eta:lig")$], [fold, $eta = #num("eta:beep")$], [queries, $eta = #num("eta:lig")$], [$numsamples$], [round 1], [round 2], [queries]),
    "errors"),
  caption: [Bits of security ($-log_2$ of the error) of the first fold round before grinding, over a field with $2^128$ elements. A message of the given size has $k$ rows, encoded at rate $1\/2$ with block length $blockclength$. "Round 1", "round 2": $kappa_1(t)$, $kappa_2(t)$. "Queries": the least $Q$ with $(1-delta)^Q <= 2^(-112)$ (#num("params:qgrind") bits of grinding).],
) <tab:errors>

The second round of BEEP has #num("err:beep2") bits, so it reaches $128$ bits with #num("err:beep-grind-1") bits of grinding, and its small $eta$ gives #num("err:q-beep") queries in place of #num("err:q-lig"). With MCA, a fold round has #num("err:lig02") bits at $eta = #num("eta:lig")$ and #num("err:lig001") bits at $eta = #num("eta:beep")$. Reaching $128$ bits at $eta = #num("eta:lig")$ would take #num("err:lig-grind-1") bits of grinding in that round, or a larger field: Flock uses $"GF"(2^256)$. (Flock's own analysis @flock[Appendix C.3] uses the bound of @BCHKS25[Theorem 4.6] times $k\/2$, a union bound over pairs of rows, which gives #num("err:flock-less") bits less at $eta = #num("eta:lig")$.)

#paragraph[Measurements.] We open commitments to messages of #num("sizes:first") to #num("sizes:last") field elements. _Ligerito (Flock)_ is Flock's Ligerito as it ships, with $eta = #num("eta:lig")$ (for #num("sizes:first") elements Flock ships no parameters, and we take the ones that its derivation gives). Its fold challenges are in $"GF"(2^256)$, and it commits to each folded message as two messages over $"GF"(2^128)$. _BEEP-Ligerito_ has all its challenges in $"GF"(2^128)$, and $numsamples$ and $t$ as above. It has Flock's number of rows per level, and #num("ladder:levels") levels of rates $1\/2$, $1\/8$, $1\/32$, etc., so that its codewords are as long as Flock's at every level. We run it with $eta = #num("eta:beep")$, and also with Flock's $eta = #num("eta:lig")$.

@tab:measured has medians of #num("run:reps") repetitions on an #num("run:cpu") laptop (#num("run:memory-gb") GB, #num("run:threads") threads), with proofs of work at their expected cost. Measured again, the prover times moved by up to #num("run:noise-pct")~% and the verifier times by up to #num("run:verify-noise-pct")~%.

#figure(
  exptable(11,
    (table.cell(colspan: 2)[$lambda = 128$], table.cell(colspan: 3)[Ligerito (Flock)], table.cell(colspan: 3)[BEEP-Ligerito, $eta = #num("eta:lig")$], table.cell(colspan: 3)[BEEP-Ligerito, $eta = #num("eta:beep")$],
     [size], [commit], [proof], [prove], [verify], [proof], [prove], [verify], [proof], [prove], [verify]),
    "bits128"),
  caption: [Proof sizes (KiB) and times (ms) at $128$ bits of security. "Prove" is the opening, without the commitment ("commit"), which all the variants share. $dagger$: a process of this row ran short of memory.],
) <tab:measured>

#paragraph[Results.] BEEP-Ligerito stays over $"GF"(2^128)$. With Flock's $eta = #num("eta:lig")$, its proofs are #num("128e:size-saving-pct")~% smaller than those of Ligerito (Flock): it makes fewer queries after the first level (smaller rates), and at #num("128:fewer-levels") of the #num("sizes:count") sizes it has fewer levels. Its prover takes #num("128e:prove-ratio") times as long, and its verifier #num("128e:verify-ratio") times (the ratios of times leave out the row with a $dagger$).

With $eta = #num("eta:beep")$ it makes $numsamples = #num("params:m-128")$ samples per fold round, with #num("128:fold-grind-log2") bits of grinding per fold challenge ($kappa_3$ of @t:beep_soundness included). It also makes fewer queries at the first level, and its proofs are #num("128:size-saving-pct")~% smaller. Its prover takes #num("128:prove-ratio") times as long, with #num("128:fold-pow-share-pct")~% of its time in the grinding of its fold challenges, and its verifier #num("128:verify-ratio") times.

#paragraph[Ligerito over $"GF"(2^128)$.] Ligerito can also keep its fold challenges in $"GF"(2^128)$, with a proof of work on each of them for the MCA error of @tab:errors (we implemented it as BEEP-Ligerito without the samples). At $eta = #num("eta:lig")$ this takes $2^x$ hashes per proof, with $x$ from #num("mca128:0.02:fold-hashes-log2"), against #num("128:fold-hashes-log2") for BEEP-Ligerito. Its prover then takes #num("mca128:0.02:expected-ms:14") ms for $2^(14)$ elements and #num("mca128:0.02:expected-ms:16") ms for $2^(16)$, against #num("128:prove-ms:14") and #num("128:prove-ms:16") ms, and for #num("sizes:last") elements the searches alone would take about #num("mca128:0.02:search-min-last") minutes on our machine. A larger $eta$ needs fewer hashes and more queries: at $eta = 0.1$, $x$ is #num("mca128:0.1:fold-hashes-log2") and the proofs are #num("mca128:0.1:size-more-pct")~% larger than those of BEEP-Ligerito.

#paragraph[Lower security levels.] The situation is different when the field has bits to spare. At $lambda = #num("low:bits")$, Ligerito over $"GF"(2^128)$ with $eta = #num("low:eta")$ needs at most #num("low:fold-hashes-max") hashes per proof on its fold challenges. Its proofs are then as large as those of BEEP-Ligerito (within #num("low:size-diff-pct")~%), and the prover of BEEP-Ligerito takes #num("low:prove-ratio") times as long, because of the samples.

We stress that Ligerito (Flock) differs from BEEP-Ligerito in its levels, in an out of domain sample on its first commitment and in its prover, and it is unclear to us whether the two provers are at a comparable level of optimization. We also do not include in this comparison the affine fold of @CWYZ26, which keeps the fold challenges in $"GF"(2^128)$ as well, for Reed-Solomon codes.
]
]