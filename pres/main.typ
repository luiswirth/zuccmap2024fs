#import "@preview/polylux:0.3.1": *

#set page(paper: "presentation-16-9", margin: 1cm)

#set text(size: 16pt)
#set text(font: "New Computer Modern Sans")

#set par(justify: true)

#let contentcolor = white
#let bgcolor = black
#set text(fill: contentcolor)
#set page(fill: bgcolor)

#let weblink(a) = text(fill: blue, link(a))

#page(fill: white, margin: 0pt)[
  #align(center)[#image("res/talk-logo.jpg", height: 100%)]
]

#page(fill: white)[
  #set text(black)
  #set align(center + horizon)
  #box(baseline: 35%)[#image("res/lean-codeine.jpg", width: 20%)]#text(80pt)[-] #text(80pt)[4] \
  #box(baseline: 35%)[#image("res/curry-food.jpg", width: 20%)] #text(80pt)[-]
  #box(baseline: 40%)[#image("res/howard-bcs.png", width: 20%)] #h(1.0cm) #text(40pt)[Isomorphism]
]

#polylux-slide[
  = Introduction

  == The strongly-typed functional programming language Lean4
  == Type Theory
  == Foundations of math

  This is a talk on logic and type theory and how they related to programming
  languages and computation.
]

#polylux-slide[
  = Motivation

  Terrance Tao formalizes his proofs
]

#polylux-slide[
  AI in Math powered by Lean.

  International Math Olympiad
]

#polylux-slide[
  Reasoner
  RL
  Mathematical Superintelligence
  Millenium Problems
]

#polylux-slide[
  = Lean Basics

  Define some variables, by specifing name, type and value as expression.
  ```lean
  def m : Nat := 1
  def n : Nat := 0
  def b1 : Bool := true
  def b2 : Bool := false
  ```
  #v(1cm)
  #uncover("2-")[
  Use `#check` command to deduce type of expression.
  ```lean
  #check m            -- Nat
  #check b1           -- Bool
  #check m * (n + 0)  -- Nat
  #check b1 && b2     -- Bool
  ```
  ]

  #v(1cm)
  #uncover(3)[
  Use `#eval` command to evaluate expression to value.
  ```lean
  #eval 5 * 4         -- 20
  #eval m + 2         -- 3
  #eval b1 && b2      -- false
  ```
  ]
]

#polylux-slide[
  = Example: Commutativity of $and$
  #v(1cm)

  The commutivity of the logical and operator $and$
  can be expressed as the following proposition: \
  For any two propositions $p$ and $q$, we have
  $
    p and q -> q and p
  $
  In the calculus of constructions this means that we need to construct
  the type
  #align(center)[`p ∧ q → q ∧ p`]

  ```lean
  theorem and_commutative (p q : Prop) : p ∧ q -> q ∧ p :=
    fun hpq : p ∧ q =>
    have hp : p := And.left hpq
    have hq : q := And.right hpq
    show q ∧ p from And.intro hq hp
  ```
]
