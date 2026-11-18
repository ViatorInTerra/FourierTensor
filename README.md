# Exact DFTs at every length

This repository contains the Lean proofs for *Exact DFTs at Every Length with a Lean-Verified 142,420-Fold Increase in the Published Logarithmic Exponent Saving*. [Paper (PDF)](paper/paper.pdf) · [TeX source and figures (ZIP)](paper/tex-source.zip)

For every positive integer $N$ and every $x\in\mathbb C^N$, one fixed pair of programs computes all $N$ coefficients of the positive-sign, unnormalized discrete Fourier transform. The first program chooses an order $1\le D(N)<8N^3$. One charged operation supplies $\exp(2\pi i/D(N))$, and the second program uses it to compute the transform. The work includes root selection, coefficient preparation and moving data. Integer words and addresses stay polynomially bounded in $N$.

The total work in the exact scalar/word RAM model is

$$
T(N)=O\!\left(N(\log N)^\beta(\log\log N)^{2-\beta}\right),
\qquad \beta=1-3\cdot10^{-8}.
$$

The saving $1-\beta$ in the exponent of $\log N$ is between 142,420.49 and 142,420.50 times the saving in OpenAI's published all-length bound. The saving is 1,500 times the one in the accompanying upstream Lean implementation. Lean also proves $T(N)=o(T_{\mathrm{published}}(N))$. [Published bound, Theorem 1.1 and Eq. (1.1)](https://github.com/openai/math/blob/main/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/build/sections/introduction.tex) · [Lean statements](FourierTensor/AllLengthDFT.lean)

## Center sharing and the all-length transform

The tensor subroutine applies $C^{\otimes n}$ to a vector of length $2^n$, where $C$ has diagonal entries $(1+i)/2$ and off-diagonal entries $(1-i)/2$. The earlier program applied a change of basis to each of 33 independent auxiliary arrays at three crossings, giving 99 rank-32 calls per invocation. The correction generated from the main inputs factors through 30 sums. Transforming those sums once and taking the original 33 arrays directly to their final frame takes 63 calls in either direction and preserves every output. Counting the resulting recursive calls, including their copies on independent arrays, gives work $O(2^n(n+1)^\beta)$. [Tensor certificate](FourierTensor/CachedExecutor.lean) · [Finite word and cost proofs](FourierTensor/Tensor/CenterCache)

The DFT compiler uses a chirp reduction to reach a cyclic transform whose length has small, coprime factors. It aligns the local transforms into $O((\log\log N)^2)$ layers across $O(\log N/\log\log N)$ axes. Each pair layer splits into blocks on which the tensor subroutine acts. The layer count and the tensor work bound give the two logarithmic powers above. The compiler evaluates the DFT directly at small lengths, including $N=1$. [DFT compiler and work bounds](FourierTensor/DFT)

Every input of length $N$ incurs exactly the same charge. Branches and tape indices depend on integer data, so the work counter can replace complex arithmetic with unit-cost dummy writes and compute the same integer from $N$ alone. [Exact work proof](FourierTensor/DFT/ExactWork.lean)

## Build and verify

Install [elan](https://github.com/leanprover/elan) and run these commands from the repository root. The project pins Lean 4.29.1 and mathlib commit `5e932f97dd25535344f80f9dd8da3aab83df0fe6`.

```sh
lake exe cache get
lake build
lake env lean FourierTensor/Check.lean
```

The checker prints the main statements and audits their kernel dependencies. The public import exposes the all-length guarantee, the exact work statements and the tensor certificate. [Checker](FourierTensor/Check.lean)

```lean
import FourierTensor

#check FourierTensor.AllLengthDFT.guarantee
#check FourierTensor.AllLengthDFT.running_time
#check FourierTensor.AllLengthDFT.count_from_length
#check FourierTensor.AllLengthDFT.below_published_bound
#check FourierTensor.CachedExecutor.guarantee
```

## Source provenance

The [support sources](support) contain the earlier executor, the compiler dependencies and the compatibility bundle from [OpenAI's pinned source revision](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). They retain their original bytes and Lean import names. The [source manifest](provenance/local_source_manifest.json) records their paths, imports and SHA-256 hashes. The [verification record](provenance/validation.json) describes the proof checks for the original layout. Attribution and licensing are in [NOTICE](NOTICE) and [LICENSE](LICENSE).

```sh
python tools/check_sources.py
lake script run checkTargets
```

Evolving Programs sponsored the use of GPT 6.2 Astra in this work.
