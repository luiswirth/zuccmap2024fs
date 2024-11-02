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

  - Lean4 as a functional programming language.
  - Type Theory and Type Systems
  - Logic
  - Foundations of Math
]

#polylux-slide[
  = Motivation

  Terrance Tao formalizes his proofs

  International Math Olympiad
]


#polylux-slide[
  = Lean Basics
  #v(1cm)
  #pause

  Lean is just a programming language.

  #alternatives-match((
    "3": [
      Let's define some objects.
    ],
    "4-": [
      Let's define some objects (constants), by specifing name, type and term.
    ]
  ))

  #pause
  #pause
  ```lean
  def n : Nat   := 69
  def z : Int   := -420
  def f : Float := 8.0085
  def b : Bool  := true
  ```
  #pause

  #v(1cm)
  Use `#check` command to deduce type of expression.
  ```lean
  #check n           -- Nat
  #check z           -- Int
  #check 5 * (n + 0) -- Nat
  ```
  #pause

  #v(1cm)
  Use `#eval` command to evaluate expression to value.
  ```lean
  #eval 5 * 4 -- 20
  #eval n + 2 -- 3
  ```
]

#polylux-slide[
  = Type Constructors
  Build new types from existing types.
  #pause

  *Product Types*
  #pause
  ```lean
  def p : Int × Bool := (2, true)
  #check p -- Int × Bool
  ```
  It's two terms existing side by side.
  Is like a tuple in a cartesian product.
  #pause

  There's a `C++` equivalent.
  #pause
  
  A struct with two fields.
  ```cpp
  struct Prod {
    int l;
    bool r;
  } p = {2, true};
  ```
]

#polylux-slide[
  = Type Constructors
  Build new types from existing types.
  #pause

  *Sum Types*
  #pause
  ```lean
  def s0 : Int ⊕ Bool := Sum.inl 5
  def s1 : Int ⊕ Bool := Sum.inr true
  #check s -- Int ⊕ Bool
  ```
  It's either the left or the right term.
  #pause

  There's a `C++` equivalent.
  #pause

  #alternatives-match(position: left + top, (
    "5": [
      A union with two variants.
      ```cpp
      union Sum {
        int l;
        bool r;
      };
      Sum s0 = {5};
      Sum s1 = {true};
      ```
    ],
    "6": [
      A tagged(!) union with two variants.
      ```cpp
      struct Sum {
        enum Variant { Left, Right } variant;
        union { int l; bool r; } data;

        Sum(int l) : data{l}, variant(Left) {}
        Sum(bool r) : data{r}, variant(Right) {}
      };
      Sum s0 = {5};
      Sum s1 = {true};
      ```
    ]
  ))
]

#polylux-slide[
  = Functions in Lean
  #v(1cm)
  #pause

  Define a simple function.
  #pause
  ```lean
  def plus_one (x : Nat) : Nat := x + 1
  ```
  #pause
  Argument-dependent constant.\
  *Lambda Abstraction* / *Function Introduction*

  #pause
  #v(1cm)

  Apply the function to an argument.
  ```lean
  #eval plus_one 5 -- 6
  ```
  No paranthesis needed.\
  *Lambda Application* / *Function Elimination*
]

#polylux-slide[
  = Lean as functional programming language
  Functions are first class citizens, meaning they are objects themselves.
  #v(0.5cm)
  ```lean
  def plus_one (x : Nat) : Nat := x + 1
  ```
  #pause
  #v(0.5cm)
  
  What is the type of our function?
  ```lean
  #check f -- Nat → Nat
  ```
  #pause
  #v(0.5cm)

  The function arrow `→` is another type constructor. \
  Given two types `A` and `B`, we get the new type `A → B`, consisting of all functions from `A` to `B`.
  #pause
  #v(0.5cm)

  There is another way to define a function using a lambda term of type `Nat → Nat`.
  ```lean
  def plus_one : Nat → Nat := λ x ↦ x + 1
  #check (λ x ↦ x + 1) -- Nat → Nat
  ```
]

#polylux-slide[
  = Higher-Order functions
  Functions with another function as argument.

  We can write this function for instance.
  ```lean
  def twice (f : Nat -> Nat) (x : Nat) : Nat := f (f x)
  #eval plus_one 5 -- 7
  ```

  ```lean
  def compose (g : Nat → Nat) (f : Nat → Nat) (x : Nat) : Nat :=
    g (f x)
  ```
]

#polylux-slide[
  = Multiple function arguments and Currying

  In non-functional languages multiple arguments are passed using tuples.
  ```lean
  def sum_tuple : Nat × Nat → Nat := λ (x, y) ↦ x + y
  ```

  But in functional programming, one instead does *Currying*.
  ```lean
  def sum_curry : Nat → (Nat → Nat) := λ x ↦ λ y ↦ x + y
  #check sum_curry      -- Nat -> Nat -> Nat
  #check sum_curry 5    -- Nat -> Nat
  #check sum_curry 5 6  -- Nat
  #eval  sum_curry 5 6  -- 11
  ```
  We fix the first argument and return a function which accepts the second argument.\
  We do so called *partial function application*.
]


#polylux-slide[
  = First Class Types
  Types are objects themselves!
  #pause

  Declare new constants for types.
  ```lean
  def α := Nat
  def β := Bool
  ```
  #pause

  We can use it to specify the type of a "normal" constant.
  ```lean
  def n : α := 5
  ```

  #pause

  Nothing too crazy.
  It's like template parameters in `C++`:
  #pause
  ```cpp
  template <typename T>
  struct { T n; };
  ```
  #pause

  But in Lean it's more streamlined.\
  It's treated like any other variable.
]

#polylux-slide[
  = Types as Objects
  #v(1cm)

  ```lean
  def α := Nat
  ```

  But what is the type of `α`?

  #alternatives-match((
    "1": [
    ```lean
    #check α
    ```
    ],
    "2-": [
    ```lean
    #check α -- Type
    ```
    ]
  ))

  #pause
  #pause

  So we have now discovered a type that is called `Type`.

  We can write fill in our definition as:
  ```lean
  def α : Type := Nat
  ```
]

#polylux-slide[
  = Generic Functions using `Type`
  We can take a `Type` argument to make a function generic.
  #pause

  ```lean
  def twice (α : Type) (f : α → α) (x : α) : α :=
    f (f x)
  ```
  #pause

  This is like `C++` generics but more powerful:

  ```cpp
  template <typename T>
  T twice(std::function<T(T)> f, T x) {
    return f(f(x));
  }
  ```
]

#polylux-slide[
  = Generic Functions using `Type`
  Another example.

  ```lean
  def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
    g (f x)
  ```

  #pause

  ```cpp
  template <typename A, typename B, typename C>
  C compose(std::function<C(B)> g, std::function<B(A)> f, A x) {
    return g(f(x));
  }
  ```
  

]

#polylux-slide[
  = Type Constructors on `Type`
  Since `Type` is a type, we can use the type constructors we have seen so far on it.
  #pause

  A product type on `Type`:
  ```lean
  def t1 : Type × Type    := (Nat, Bool)
  def t2 : Prod Type Type := (String, Char)
  ```
  #pause

  Function arrow can also be used.
  ```lean
  def f : Type → Type := λ _ => Nat
  ```
  The constant function returning `Nat`.
]

#polylux-slide[
  Now we can understand what `Prod` is.
  ```lean
  #check Prod               -- Type -> Type -> Type
  #check Prod Int           -- Type -> Type
  #check Prod Int Bool      -- Type
  ```
  #pause

  C++ Struct
  ```cpp
  template <typename L, typename R>
  struct Prod {
    L l;
    R r;
  }

  Prod<int, bool> p;
  ```
]

#polylux-slide[
  = What's the Type of `Type`?
  `Type` must be an object too, since it's a type.
  #pause

  We must be able to define such a constant.
  ```lean
  def t := Type
  ```
  #pause

  What is the type of this constant?
  ```lean
  #check t -- Type 1
  ```

  #pause
  So there's a new type, called `Type 1`. It once again must be an object.
  ```lean
  def t1 := Type 1
  #check t1 -- Type 2
  ```
  
  #pause
  Keep on doing this:
  ```lean
  #check Nat      -- Type
  #check Type     -- Type 1
  #check Type 1   -- Type 2
  #check Type 2   -- Type 3
  #check Type 3   -- Type 4
  -- ...
  ```
  We've stumbled upon the infintely many, but countable type univeres.
]

#polylux-slide[
  The universes form a hierarchy.
  Because each lower type universe is a term in it's next higher type universe.
  ```lean
  def t0 : Type 0 := Nat
  def t1 : Type 1 := Type 0
  def t2 : Type 2 := Type 1
  def t3 : Type 3 := Type 2
  -- ...
  ```
  In general `Type n : Type (n+1)`.

  Brainfuck?

  Useful for having higher abstraction levels.
  We can define more and more abstract functions.
]

#polylux-slide[
  = Girard's Paradox

  This hierarchy is strict and doesn't allow for type universes to contain themselves.
  ```lean
  def t0 : Type 0 := Type 0 -- ERROR: type mismatch: `Type` actually has type `Type 1`
  ```

  This avoids *Girard's paradox*, which is a type-theoretic version of the
  set-theoretic *Russell's paradox*.
]

#polylux-slide[
  = Hierarchy of Type Universes

  #table(
    columns: 5,
    //rows: 3,
    inset: 6pt,
    align: horizon,
    stroke: contentcolor,
    [*Sort*], [Type 0], [Type 1], [Type 2], [Type 3],
    [*Type*], [Nat], [Type 0], [Type 1], [Type 2],
    [*Term*], [1], [Nat], [Type 0], [Type 1],
  )

  In this sense type objects in Lean can both be a type or a term depending on the context.
  
]

#polylux-slide[
  Now after looking at some basic type theory and lambda calculus in Lean.
  We want to figure out, how to do math with this!

  We want to leverage the powerful type system to do the proof verification for us.
  In order for this to work, we first to express mathematical statements using types.

  We will start with basic propositional logic.
  The first step is to define a new type that represents all possible propositions.
  We will call this type `Prop`.

  Now we can introduce variables called `p` and `q` which are of type `Prop`.
  In propositional logic one can use two propositional statements and use
  logical connectices to build new ones.

  $p and q$ $p or q$ $p -> q$
]

#polylux-slide[
  = Implication

  
  Modus Ponens
  Implication Elimination
  Function Application

  "From a proof of Implies p q and a proof of p, we obtain a proof of q."

  Implication Introduction
  Function Abstraction
  "Suppose that, assuming p as a hypothesis, we have a proof of q. Then we can "cancel" the hypothesis and obtain a proof of Implies p q."
]

#polylux-slide[
  And, Or

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

#polylux-slide[
  True, False
]


#polylux-slide[
  = Curry-Howard Isomorphism
  #v(1cm)

  #table(
    columns: 4,
    inset: 6pt,
    align: horizon,
    stroke: contentcolor,
    table.header(
      [*Logic Name*], [*Logic Notation*], [*Type Notation*], [*Type Name*]
    ),
    [Proposition], $P$, $T$, [Type],
    [Proof], $p$, $t$, [Term],
    [True], $top$, $top$, [Unit Type],
    [False] ,$tack.t$, $tack.t$, [Empty Type],
    [Implication] ,$->$, $->$, [Function],
    [Not], $not A$, $A -> tack.t$, [Function to Empty Type],
    [And / Conjunction], $A and B$, $A times B$, [Product Type],
    [Or / Disjunction], $A or B$, $A + B$, [Sum Type],
    [For All / Universal Quantification], $forall a in A, P(a)$, $Pi a : A. space P(a)$, [Dependent Product Type],
    [Exists / Existential Quantification], $exists a in A, P(a)$, $Sigma a : A. space P(a)$, [Dependent Sum Type],
  )
]

#table(
  columns: 2,
  inset: 5pt,
  align: horizon,
  stroke: contentcolor,
  table.header(
    [*Logic*], [*Programming*]
  ),
  [hypotheses], [free variables],
  [implication elimination (modus ponens)], [function application],
  [implication introduction], [function abstraction],
)

#polylux-slide[
  = Predicate Logic

  ```lean
  def is_even (n : Nat) : Prop := n % 2 = 0
  ```
]

#polylux-slide[
  = Universal Quantification "Forall"
]

#polylux-slide[
  = Existential Quantification "Exists"
]

#polylux-slide[
  = Constructive Math
  Law of Excluded Middle
]



#polylux-slide[
  = Tactic Mode

  In tactic mode:
  ```lean
  theorem and_comm (p q : Prop) : p ∧ q → q ∧ p := by
    intro h            -- assume p ∧ q with proof h, the goal is q ∧ p
    apply And.intro    -- goal is split into two subgoals, one is q and the other is p
    · exact h.right    -- first subgoal is exactly the right part of h : p ∧ q
    · exact h.left     -- second subgoal is exactly the left part of h : p ∧ q
  ```
]

#polylux-slide[
  = Inductive types

  The natural numbers can be defined as an inductive type. This definition is
  based on the Peano axioms and states that every natural number is either zero or
  the successor of some other natural number.

  ```lean
  inductive Nat : Type
  | zero : Nat
  | succ : Nat → Nat
  ```

  Addition of natural numbers can be defined recursively, using pattern matching.

  ```lean
  def Nat.add : Nat → Nat → Nat
  | n, Nat.zero   => n                      -- n + 0 = n  
  | n, Nat.succ m => Nat.succ (Nat.add n m) -- n + succ(m) = succ(n + m)
  ```
]


#polylux-slide[
  AI in Math powered by Lean.

  Reasoner
  RL
  Mathematical Superintelligence
  Millenium Problems
]

#polylux-slide[
  = References
  - https://leanprover-community.github.io/logic_and_proof
  - https://leanprover.github.io/theorem_proving_in_lean4/
  - https://www.youtube.com/watch?v=NvAxuCIBb-c
    Why Vlad Tenev and Tudor Achim of Harmonic Think AI Is About to Change Math—and Why It Matters
]
