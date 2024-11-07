# ZUCCMAP: Lean4 and the Curry-Howard Isomorphism (Luis Wirth)

This repository contains the [typst](https://typst.app) source files for the slides of the ZUCCMAP talk of Luis Wirth from the fall semester 2024.\
A PDF version of the slides is available under the [GitHub releases page](https://github.com/luiswirth/zuccmap2024fs/releases).

A [recording](https://www.youtube.com/watch?v=Sy_4z751YWI) of the talk is available on the offical ZUCCMAP Youtube channel.

## Lean4 and the Curry-Howard Isomorphism: The Deep Connection Between Logic and Programming Through Type Theory

In this talk, we will explore the inner workings of interactive proof assistants
such as Lean4 and discover a profound connection between mathematical logic and
computer programs known as the Curry-Howard Isomorphism.

At the heart of this correspondence lies type theory, the formal study of type
systems---the same kind you know from strongly-type programming languages like
C++. Lean4 is a functional programming language that is also strongly typed. But
it's special in sense that it's equipped with a type system so powerful, that
it is capable of expressing any mathematical statement (as a type) and formally
verifying their proofs (by constructing the type). In this way it's possible to
construct the entirety of mathematics within Lean4.

People are actually doing this by creating a library called Mathlib!
There's even a project that tries to rewrite every theorem and proof of the
undergraduate math curriculum of Imperial College London in Lean. Famous
mathematicians like Terrance Tao are also using Lean to formalize their complex
conjectures.

The most impressive real-life application of Lean4 to me is the use of it in
AI-driven mathematics. For instance, Google DeepMind's AlphaProof, built with
Lean4, recently solved an International Math Olympiad problem at the level
of a Silver Medalist! This breakthrough shows how proof assistants have the
potential to transform mathematics, paving the way for automated mathematical
superintelligence.

