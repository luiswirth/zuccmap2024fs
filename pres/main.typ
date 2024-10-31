#set page(paper: "presentation-16-9", margin: 1cm)
#set text(size: 16pt)

#set text(font: "New Computer Modern Sans")
//#show math.equation: set text(font: "Fira Math Ultra")

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
  #box(baseline: 35%)[#image("res/lean-codeine.jpg", width: 20%)]#text(80pt)[-4] \
  #box(baseline: 35%)[#image("res/curry-food.jpg", width: 20%)] #text(80pt)[-]
  #box(baseline: 40%)[#image("res/howard-bcs.png", width: 20%)] #h(1.0cm) #text(40pt)[Isomorphism].
]

Foundations of math

This is a talk on logic and type theory and how they related to programming
languages and computation.


#pagebreak()
= Motivational Stuff
#v(1cm)

Harmonic
Math AI and the most general reasoner
Mathematical superintelligence
Solving Millenia problems such as Riemann Hypothesis and Navier-Stockes.

#pagebreak()
= Introduction to Lean

```lean
def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
```

#pagebreak()
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
