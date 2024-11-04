#import "@preview/polylux:0.3.1": *

#set page(paper: "presentation-16-9", margin: 1cm)

#set text(font: "New Computer Modern Sans")
#set text(size: 16pt)
#set par(justify: true)

//#show math.equation: set text(font: "Noto Sans Math")

#let contentcolor = white
#let bgcolor = black
#set text(fill: contentcolor)
#set page(fill: bgcolor)

#let weblink(a) = text(fill: blue, link(a))

#set raw(lang: "lean")

//#show raw.where(block: false): box.with(
//  //fill: black.lighten(10%),
//  //stroke: black.lighten(10%),
//  inset: (x: 3pt, y: 0pt),
//  outset: (y: 5pt),
//  radius: 4pt,
//)
//#show raw.where(block: true): block.with(
//  fill: black.lighten(5%),
//  inset: (x: 3pt, y: 0pt),
//  outset: 5pt,
//  radius: 4pt,
//)


#let True = $top$
#let False = $tack.t$

#page(fill: white, margin: 0pt)[
  #align(center)[#image("res/talk-logo.jpg", height: 100%)]
]

#polylux-slide[
  = Why Lean matters

  #align(center + horizon)[#grid(
    columns: 2,
    gutter: 10%,
    align: center + horizon,
    image("res/lieben-sie-lean.png", height: 60%),
    image("res/lean-codeine.jpg", height: 60%),
  )]
]

#polylux-slide[
  = Why Lean matters
  #v(1cm)

  #text(20pt)[
    $ "Lean" = "Programming Language" + "Interactive Proof Assistant" $
  ]
  #pause
  #v(1cm)
  
  Allows us to do some groundbreaking things:
  - _Express_ Mathematical Ideas using code.
  - _Express_ Mathematical Proofs using code.
  - _Verify_ the Proofs formally.
  - Write in a cool ass programming language

  #pause
  #v(1cm)

  #text(20pt)[
    $ "Lean" = "Type Theory" + "Lambda-Calculus" $
  ]
  #pause
  #v(0.5cm)

  #text(20pt)[
    $
      "Type Theory" &#sym.arrow.squiggly "Type System/Checker" \
      "Lambda-Calculus" &#sym.arrow.squiggly "Functional Programming"
    $
  ]
]

#polylux-slide[
  = Why Type Theory matters
  #pause
  #v(1cm)

  New *Foundation for Mathematics* beyond traditional set theory.\
  Set Theory is actually not so nice...
  #pause
  #v(1cm)
  // Set theory has become the standard foundation for mathematics, as
  // every mathematical object can be viewed as a set, and every theorem of mathematics can be
  // logically deduced in the Predicate Calculus from the axioms of set theory.
  
  *Curry-Howard Isomorphism* (CH) tells us that logic can be done in a type system!

  
  #only(3)[
    #align(center + horizon)[
      #box(baseline: 35%)[#image("res/curry-food.jpg", width: 20%)] #text(80pt)[-]
      #box(baseline: 40%)[#image("res/howard-bcs.png", width: 20%)] #h(1.0cm) #text(40pt)[Isomorphism.]
    ]
  ]
  #only("4-")[
    #align(center)[#text(25pt)[
      Propositions-as-Types\
      Proofs-as-Programs\
    ]]

    #pause
    #pause
    #v(1cm)

    Let's us write mathematical proofs as if we’re writing functions!\
    Verifying Proof is just Typechecking! #emoji.face.explode
  ]
]

#polylux-slide[
  = Mathematicians use Lean
  #v(1cm)

  #quote(block: true, attribution: [Terence Tao, Fields Medalist and Professor of Mathematics, UCLA])[
    *Lean enables large-scale collaboration* by allowing mathematicians to *break
    down complex proofs* into smaller, verifiable components. This formalization
    process *ensures the correctness of proofs* and facilitates contributions from
    a broader community. With Lean, we are beginning to see *how AI can accelerate
    the formalization of mathematics*, opening up new possibilities for research.
  ]

]

#polylux-slide[
  = AI Breakthrough in Math, July 2024
  #v(0.5cm)

  #align(center)[#text(25pt)[
    #quote[AI achieves silver-medal standard\
    solving International Mathematical Olympiad problems]
  ]]
  #pause

  // AlphaProof is a system that trains itself to prove mathematical statements
  // in the formal language Lean. It couples a pre-trained language model with the
  // AlphaZero reinforcement learning algorithm, which previously taught itself how
  // to master the games of chess, shogi and Go.
  // When presented with a problem, AlphaProof generates solution candidates and then
  // proves or disproves them by searching over possible proof steps in Lean. Each
  // proof that was found and verified is used to reinforce AlphaProof’s language
  // model, enhancing its ability to solve subsequent, more challenging problems.

  #grid(
    columns: 2,
    rows: 1,
    gutter: 3pt,
    align: center + horizon,
    image("res/alphaproof-score.png", height: 50%),
    [
      #text(20pt)[*Google DeepMind*'s *AlphaProof*]
      #quote(block: true, attribution:
        [Prof Sir Timothy Gowers, *IMO gold medalist* and *Fields Medal winner*]
      )[
        The fact that the program can come up with a non-obvious construction like
        this is very impressive, and well *beyond what I thought was state of the art*.
      ]
    ]
  )

  Soon (this or next year) Gold Medal probably.\
  #pause

  Maybe someday Millenium Problem?
]

#polylux-slide[
  = The Typing Judgment

  // we have terms and we have types
  // terms are just expressions
  #v(3cm)
  #align(center)[#text(60pt)[
    $t : T$
  ]]
  #v(2cm)
  // there is one important judgment in type theory:
  #align(center)[#text(60pt)[
    "$t$ is a term of type $T$"
  ]]

]

#polylux-slide[
  = Lean is just a Programming Language!
  #v(1cm)
  #pause

  #alternatives-match(position: top, (
    "2": [
      Let's define some objects.
    ],
    "3": [
      Let's define some objects: constants!\
      Specify *name*, *type* and *term*.
      ```lean
      def n : Nat   := 69
      def z : Int   := -420
      def f : Float := 8.0085
      def b : Bool  := true
      ```
    ],
    "4-": [
      Let's define some objects: constants!\
      Specify *name*, *type* (optional) and *term*.
      ```lean
      def n         := 69
      def z         := -420
      def f         := 8.0085
      def b         := true
      ```
    ]
  ))

  #pause
  #pause
  #pause
  #v(0.5cm)

  Use `#check` command to deduce type of expression.
  ```lean
  #check n           -- Nat
  #check z           -- Int
  #check 5 * (n + 0) -- Nat
  ```
  #pause
  #v(0.5cm)

  Use `#eval` command to evaluate expression to value.
  ```lean
  #eval 5 * 4 -- 20
  #eval n + 2 -- 71
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
  #pause
  The two terms exist side by side.
  #pause
  #v(0.5cm)

  The `C++` equivalent:\
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
  Another one, built different.

  *Sum Types*
  #pause
  ```lean
  def s0 : Int ⊕ Bool := Sum.inl 5
  def s1 : Int ⊕ Bool := Sum.inr true
  #check s1 -- Int ⊕ Bool
  ```
  #pause
  It's either the left or the right term.
  #pause
  #v(0.5cm)

  The `C++` equivalent:\
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
      A _tagged_ union with two variants.
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
  #v(0.5cm)
  #pause

  Define a simple function (*Lambda Abstraction*):
  #pause
  ```lean
  def plus_one (x : Nat) : Nat := x + 1
  ```
  Looks like argument-dependent constant.
  #pause
  #v(0.5cm)

  Apply the function to an argument (*Lambda Application*):
  #pause
  ```lean
  #eval plus_one 5 -- 6
  ```
  No paranthesis needed.
]

#polylux-slide[
  = Lean is a _functional_ programming language!
  Functions are first class objects.
  #v(0.5cm)

  Consider our function:
  ```lean
  def plus_one (x : Nat) : Nat := x + 1
  ```
  #pause
  #v(0.5cm)
  
  It's an object! What is it's type?\
  #pause
  #alternatives-match((
    "3": [
    ```lean
    #check plus_one
    ```
    ],
    "4-": [
    ```lean
    #check plus_one -- Nat → Nat
    ```
    ]
  ))
  #pause
  #pause
  #v(0.5cm)

  New type constructor just dropped: `→`\
  #pause
  Given two types `A` and `B`, we get the new type `A → B`, consisting of all functions from `A` to `B`.
  #v(0.5cm)

  Different way to define a function:
  #pause
  ```lean
  def plus_one : Nat → Nat := λ x ↦ x + 1
  #check (λ x ↦ x + 1) -- Nat → Nat
  ```
  Directly using a lambda term of type `Nat → Nat`.

  #pause
  We sort of moved the "`:`" from right to left.

]

#polylux-slide[
  = Higher-Order functions
  Functions with another function as argument.
  #pause
  #v(0.5cm)

  We can write this function for instance:\
  #alternatives-match(position: top, (
    "2": [
      ```lean
      def do_twice (f : Nat → Nat) (x : Nat) : Nat :=
        f (f x)
      ```
    ],
    "3-": [
      ```lean
      def do_twice (f : Nat → Nat) (x : Nat) : Nat :=
        f (f x)
      #eval do_twice plus_one 5 -- 7
      ```
    ]
  ))
  #pause
  #pause
  #v(0.5cm)

  In `C++`:
  ```cpp
  int do_twice(std::function<int(int)> f, int x) {
    return f(f(x));
  }
  ```
]

#polylux-slide[
  = Multiple Arguments
  Functional Programmers like Curry #emoji.face.lick.
  #pause
  #v(0.5cm)


  In non-functional languages:
  #pause
  With tuples!\
  ```lean
  def sum_tuple : Nat × Nat → Nat := λ (x, y) ↦ x + y
  ```
  #pause
  #v(1.0cm)

  Instead in functional languages:
  Function Chain (*Currying*).\
  #alternatives-match(position: top, (
    "3": [
      ```lean
      def sum_curry : Nat → (Nat → Nat) := λ x ↦ λ y ↦ x + y
      ```
    ],
    "4": [
      ```lean
      def sum_curry : Nat → (Nat → Nat) := λ x ↦ λ y ↦ x + y
      #check sum_curry      -- Nat -> Nat -> Nat
      ```
    ],
    "5": [
      ```lean
      def sum_curry : Nat → (Nat → Nat) := λ x ↦ λ y ↦ x + y
      #check sum_curry      -- Nat -> Nat -> Nat
      #check sum_curry 5    -- Nat -> Nat
      ```
    ],
    "6": [
      ```lean
      def sum_curry : Nat → (Nat → Nat) := λ x ↦ λ y ↦ x + y
      #check sum_curry      -- Nat -> Nat -> Nat
      #check sum_curry 5    -- Nat -> Nat
      #check sum_curry 5 6  -- Nat
      ```
    ],
    "7-": [
      ```lean
      def sum_curry : Nat → (Nat → Nat) := λ x ↦ λ y ↦ x + y
      #check sum_curry      -- Nat -> Nat -> Nat
      #check sum_curry 5    -- Nat -> Nat
      #check sum_curry 5 6  -- Nat
      #eval  sum_curry 5 6  -- 11
      ```
    ]
  ))

  #pause
  #pause
  #pause
  #pause
  Allows for *partial function application*.
]


#polylux-slide[
  = Types as Objects!
  We can declare new constants for types.
  #pause

  ```lean
  def α := Nat
  def β := Bool
  ```
  #pause

  We can use it to specify the type of a "data" constant.
  ```lean
  def n : α := 5
  ```
  #pause
  #v(0.5cm)

  Actually not so crazy. In `C++` one can also define type constants.
  #pause

  ```cpp
  using T = int;
  T n;
  ```
  #pause

  But this is not really an object. Not as flexible.\
  In Lean this is like any other object.
]

#polylux-slide[
  = But every object must have a type...
  #v(1cm)

  Given that this is an object.
  ```lean
  def α := Nat
  ```
  #pause

  What is it's type?

  #alternatives-match((
    "2": [
    ```lean
    #check α
    ```
    ],
    "3-": [
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

  
  #alternatives-match(position: top, (
    "2": [
      ```lean
      def do_twice (f : Nat → Nat) (x : Nat) : Nat :=
        f (f x)
      ```
    ],
    "3-": [
      ```lean
      def do_twice (α : Type) (f : α → α) (x : α) : α :=
        f (f x)
      ```
    ],
  ))

  #pause
  #pause
  #v(0.5cm)

  In `C++` we can do generics using templates:
  ```cpp
  template <typename T>
  T do_twice(std::function<T(T)> f, T x) {
    return f(f(x));
  }
  ```
  #pause

  But here `C++` makes a big distinction between type variables
  and normal variables.\
  Lean doesn't. It's like any other object.
]

#polylux-slide[
  = Type Constructors on `Type`
  Since `Type` is a type, we can use the type constructors we have seen so far on it.
  #pause

  A product type on `Type`:
  ```lean
  def t : Type × Type    := (Nat, Bool)
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
  #check Int × Bool         -- Type
  #check Prod Int Bool      -- Type
  #check Prod Int           -- Type -> Type
  #check Prod               -- Type -> Type -> Type
  ```
  #pause

  Actually `Prod` is generic even over all type univeres.
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
  We've stumbled upon the infintely many, but countable *type universes*.
]

#polylux-slide[
  = Hierarchy of Type Universes
  Each lower type universe is a term in it's next higher type universe.
  ```lean
  def t0 : Type 0 := Nat
  def t1 : Type 1 := Type 0
  def t2 : Type 2 := Type 1
  def t3 : Type 3 := Type 2
  -- ...
  ```
  In general `Type n : Type (n+1)`.
  #pause
  #v(0.5cm)

  The distinction between universe, type and term becomes blurry.\
  It depends on the context.

  #table(
    columns: 6,
    //rows: 3,
    inset: 6pt,
    align: horizon,
    stroke: contentcolor,
    [*Universe*], [Type 0], [Type 1], [Type 2], [Type 3], $dots.c$,
    [*Type*], [Nat], [Type 0], [Type 1], [Type 2], $dots.c$,
    [*Term*], [1], [Nat], [Type 0], [Type 1], $dots.c$,
  )
]

#polylux-slide[
  = What's the use of Higher Order Types?
  It's all about abstraction.
  #pause
  #v(0.5cm)

  Standard Type Universe `Type 0`.\
  Data types: `Nat : Type 0`, `Float : Type 0`, ...\
  Function Types on Data also `Nat -> Nat : Type 0`.
  #pause
  #v(0.5cm)

  One abstraction level higher: `Type 1`.\
  `Type 0` itself: `Type 0 : Type 1`.\
  Type constructors: `Type -> Type -> Type : Type 1`
  #pause
  #v(0.5cm)

  Abstracting over all type constructors?\
  `Type 2`!
  #pause
  #v(0.5cm)

  Arbitrary levels of abstraction are possible!\
  `Type n`
]

#polylux-slide[
  = Does the typed Barber shave itself?
  #v(0.5cm)

  Why not just have one universe.\
  One type to rule them all: The type of ALL types.
  #pause
  #v(0.5cm)

  Oh oh. Russell is knocking on the door. And he has a Paradox for you.
  #pause

  #align(center)[$R = {x | x in.not x} $ then $R in R <==> R in.not R$ #emoji.lightning]
  #pause
  #v(0.5cm)

  Russell invented simple type theory!
  #pause
  #v(0.5cm)
  // after the discovery russell invented simple type theory.
  // with one type to rule them all, but this then lead
  // to a type-theoretic version of the paradox.

  *Girard's Paradox* is type-theoretic version of it.

  Solution: _Strict_ hierarchy of type universes.\
  No universe may contain itself.
  ```lean
  def t : Type 0 := Type 0 -- ERROR: type mismatch: `Type 0` actually has type `Type 1`
  ```
]

#polylux-slide[
  = How to do Math in Lean?
  Spill the tea!
  #pause

  Logical Interpretation of Type Theory .

  Leverage the Type System!\
  #sym.arrow.squiggly *Mathematical Statements need to be types!*
  #pause
  #v(1cm)

  Start by expressing *Propositional Logic* using types.
  #table(
    columns: 2,
    align: (left, center),
    inset: 7pt,
    stroke: contentcolor,
    [Conjunction], $p and q$,
    [Disjunction], $p or q$,
    [Implication], $p -> q$,
    [Negation], $not p$,
    [True], $True$,
    [False], $False$,
  )
]

#polylux-slide[
  = Propositions in Lean
  New Type Universe just dropped: `Prop`\
  Universe of all logical propositions.
  #pause

  *Types in `Prop` are propositions.*\
  For example: `p : Prop` and `q : Prop`.
  #pause
  #v(1cm)

  What's the meaning of terms in this universe?\
  For example: `hp : p` and `hq : q`?
  #pause

  Herein lies the magic! *A term is a proof*!
  #pause
  #v(1cm)

  Types are propositions.
  Terms are proofs/witnesses.

  $t : T$ means $t$ is a witness to the truth of $T$.

  There can be multiple distinct proofs/witnesses/terms of the same proposition.
  But we don't care. *Proof-Irrellevance*. We only care about inhabitedness.

  The prove a proposition is to construct it's term!\
  And validating the proof is just typechecking the expression!

  "$T$ is inhabited" $<=>$ there are terms of type $T$.
  "$T$ is uninhabited" $<=>$ there are _no_ terms of type $T$.
]

#polylux-slide[
  = Functions between Propositions
  We have our two propositions
  ```lean
  variable (p q : Prop)
  ```
  What is the meaning of a function `f : p → q`?
  #pause

  Syntactically looks like implication...
  #pause

  Also semantically the same! How?
  #pause
  #v(1cm)

  Given proof `hp : p` and function `f : p → q`,
  we can get `hq : q := f hp`!\
  Known as *modus ponens* or *implication elimination*.
  #pause

  How to do *implication introduction*?\
  Create a function `f : p → q` by assuming `hp : p`
  and deriving `hq : q`.
  #pause
  #v(1cm)

  First instance of *Curry-Howard Isomorphism* (CH)!\
  Functions are Implications.
]

#polylux-slide[
  = Logical Conjunction $p and q$
  What is the corresponding type?
  #pause
  
  Type combining to terms of type `p` and `q`?
  #pause

  Product Type `p × q` by CH!
  #pause

  Illustrate at example!
  ```lean
  theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
    λ hpq : p ∧ q ↦ And.intro hpq.right hpq.left
  ```
]

#polylux-slide[
  = Logical Disjunction $p or q$
  What is the corresponding type?
  #pause

  Sum Type `p ⊕ q` by CH!
  #pause
  
  ```lean
  theorem or_commutative (p q : Prop) : p ∨ q → q ∨ p :=
    λ hpq : p ∨ q ↦ 
      hpq.elim
        (λ hp ↦ Or.inr hp)
        (λ hq ↦ Or.inl hq)
  ```
]

#polylux-slide[
  = Logical Constant `True`
  
  `True` is simply true.\
  Get Proof for free:
  ```lean
  def t : True := True.intro
  ```

  But introduction-only. No Elemination. It just exists.

  It's the unit type by CH. It is _uniquely_ inhabited by
  the 0-tuple `()`.
]

#polylux-slide[
  = Logical Constant `False`

  Represents a contradiction. You shouldn't be able to obtain.
  ```lean
  def f : False := -- impossible
  ```

  Opposite of `True`:\
  No introduction. Elemination-Only.

  Most powerful elimination. Anything follows from a contradiction / `False`.
  ```lean
  false.elim : ∀ (q : Prop), False → q
  ```

  If we include `False` as axiom in our type system, it becomes *unsound*.
  ```lean
  axiom false : False
  variable (q : Prop)
  theorem hq : q := false.elim
  ```

  Is empty type by CH. The uninhabitated type, that has no terms.

  Even though no introduction, still appears in formula.
  
  ```lean
  example : p ∨ False ↔ p := Iff.intro
    (λ h ↦ h.elim
      (λ hp ↦ hp)
      (λ hf ↦ False.elim hf)
    )
    (λ hp ↦ Or.inl hp)

  example : p ∧ False ↔ False := Iff.intro
    (λ hpf ↦ hpf.right)
    (λ hf ↦ hf.elim)

  ```
]

#polylux-slide[
  = Logical Negation

  Negation $not p$ in Lean is defined as `p -> False`.

  How introduction and how elemination?

  If you got a `hp : p` and a `hnp : p -> False` you would obtain a contradiction.

  ```lean
  example : (p → q) → (¬q → ¬p) :=
    λ hpq ↦ λ hnq ↦ λ hp ↦ hnq (hpq hp)
  ```
]

#polylux-slide[
  = Curry-Howard Isomorphism for Propositional Logic
  #v(1cm)

  // should be like summary slide!

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
    //[For All / Universal Quantification], $forall a in A, P(a)$, $Pi a : A. space P(a)$, [Dependent Product Type],
    //[Exists / Existential Quantification], $exists a in A, P(a)$, $Sigma a : A. space P(a)$, [Dependent Sum Type],
  )
]

#polylux-slide[
  = Predicate Logic in Lean

  Unary Predicate can be represented as
  ```lean
  variable (α : Type) (p : α → Prop)
  ```

  Given `x : α`, then `p x` denotes the assertion that `p` holds of `x`.

  `r : α → α → Prop` denotes a binary relation on `α`: given `x y : α` then,
  `r x y` denotes the assertion that `x` is related to `y`.

  ```lean
  variable (men : Type) (barber : men)
  variable (shaves : men → men → Prop)
  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
    Classical.byCases
      (λ hsbb ↦ absurd hsbb ((h barber).mp hsbb))
      (λ hnsbb ↦ absurd ((h barber).mpr hnsbb) hnsbb)
  ```
]

#polylux-slide[
  = Universal Quantification $forall$
  Called "Universal" because it's a big *conjunction over the whole type universe*!

  The forall quantifier `∀ x : Nat, p x` is really just a function `Nat -> Prop`
]

#polylux-slide[
  = Existential Quantification $exists$

  Existance Quantifier "Existance" => Big disjunction over the whole universe.

  `∃ x, p x` is defined as `¬(∀ x, p x)`
  Existance is just $not forall$.
]

#polylux-slide[
  = Constructive vs. Nonconstructive Math

  Two types of logical arguments / proofs.

  Example:

  Is there an $x > 2$ such that $2^x = x^2$?

  - Constructive: Yes, 4.
  - Nonconstructive: Yes, because Intermediate Value theorem.

  //A non-constructive proof of $"P" = "NP"$, would be very disappointing.
  // As it wouldn't give a recipe for constructing such algorithms.

  The computational logic we looked at so far is completly constructive.
  Meaning that every existance proof made like this,
  would result in a construction of the postulated object.
  
  This is in contrast to Classical Logic, which is usally used
  in university courses.

  The only difference between the two is one axiom!
  The *Law of Excluded Middle* (EM).
  It assumes that $p or not p$ is true.
  So it creates a term of type `p or not p` out of thin air.

  Using it we can prove double negation, as well as the proof pattern
  of proof by contradiction. (only possible in classical logic!).

  Proofs involving EM might not construct the mathematical object at hand.
  But only proof that such an object exists.

  
Explained Lean's constructive mathematics—each proof explicitly constructs what it claims exists.

Constructive/Intuistionic vs Classical Logic.

There is a single axiom that governs this:
*Law of Excluded Middle* (EM)
Double Negation
Binary Logic and Philosphical Implications
Non-constructive Existence Proofs
Proof by contradiction.
Proof by case distinction
De Morgan's law



Because the law of excluded middle does not hold, there is no term of type
$Pi a. space A + (A -> tack.t)$. Likewise, double
negation does not hold, so there is no term of type 
$Pi A. space ((A -> tack.t) -> tack.t) -> A$.

It is possible to include the law of excluded middle and double negation into
a type theory, by rule or assumption. However, terms may not compute down to
canonical terms and it will interfere with the ability to determine if two terms
are judgementally equal to each other.
WHAT DOES THIS MEAN?

Constructive Mathematics is powerful in the sense that there is always a computational recipe for
creating the stipulated mathematical object.
But it's also less powerful in the sense, that fewer mathematical statements can be proven this way.

An example of a non-constructive proof is proof by contradiction. The first
step is assuming that $x$ does not exist and refuting it by contradiction.
The conclusion from that step is "it is not the case that $x$ does not exist".
The last step is, by double negation, concluding that $x$ exists. Constructive
mathematics does not allow the last step of removing the double negation to
conclude that $x$ exists.

Lean supports both and does a seperation of concerns.
Lean supports classical reasoning through the `Classical` namespace. `open Classical`
]

#polylux-slide[
Relation known from set theory. But relations are more fundamental and can be formulated directly
in logic/type theory.
Define relation as`alpha -> alpha -> Prop`


Define Aequivalence Relation in Lean Code:
- Reflexiv
- Symmetric
- Transitive

]

#polylux-slide[
  = Tactic Mode

  
So far we've only seen Lean in *term-mode*. But actually for writing more complicated proofs,
this is used only very rarely. Instead there is *tactic-mode*.
Here the *automated proof writing* of lean comes into play.


The Lean Theorem Prover aims to bridge the gap between interactive and automated
theorem proving, by situating automated tools and methods in a framework that
supports user interaction and the construction of fully specified axiomatic
proofs. The goal is to support both mathematical reasoning and reasoning about
complex systems, and to verify claims in both domains.

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
  = Mathlib Showcase
]

#polylux-slide[
  = VScode Extension
]

#polylux-slide[
  = Further Reading
  
  "Theorem Proving in Lean4"
  - https://leanprover-community.github.io/logic_and_proof

  Some other resources:
  - https://leanprover.github.io/theorem_proving_in_lean4/

  Youtube:
  - https://youtu.be/NvAxuCIBb-c?si=Nhs6o-79xwwMKA2Z
    Why Vlad Tenev and Tudor Achim of Harmonic Think AI Is About to Change Math—and Why It Matters

  - https://youtu.be/BdXWlQsd7RI?si=7ZhTNCOl6e3P12ds
    Type Theory for the Working Rustacean - Dan Pittman

  = Beyond "just" Type Theory: Homotopy Type Theory (HoTT) #emoji.face.explode
  - https://youtube.com/playlist?list=PL245PKGUDdcN9-El9D7DRefwX4c9feiYq&si=RnAo2CUVPXfPNqkf
]

#polylux-slide[
  = References
]
