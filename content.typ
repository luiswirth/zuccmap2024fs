#set text(font: "New Computer Modern Sans")
//#show math.equation: set text(font: "Fira Math Ultra")

#set par(justify: true)

#let contentcolor = white
#let bgcolor = black
#set text(fill: contentcolor)
#set page(fill: bgcolor)


= ZUCCMAP Talk

== Type theory

Type theories serve as alternatives to set theory as a foundation of mathematics.
Two influential type theories that have been proposed as foundations are:
- Typed λ-calculus of Alonzo Church
- Intuitionistic type theory of Per Martin-Löf

Type theory was created to avoid a paradox in a mathematical equation based on
naive set theory and formal logic.
Russell's paradox is that, without proper axioms, it is possible to define
the set of all sets that are not members of themselves; this set both contains
itself and does not contain itself.
Russell arrived at a ramified theory of types together with an axiom of reducibility
This system avoided contradictions suggested in Russell's paradox by creating
a hierarchy of types and then assigning each concrete mathematical entity to a
specific type. Entities of a given type were built exclusively of subtypes of
that type, thus preventing an entity from being defined using itself.
This resolution of Russell's paradox is similar to approaches taken in other
formal systems, such as Zermelo-Fraenkel set theory.

Type theory is particularly popular in conjunction with Alonzo Church's lambda calculus.
Church demonstrated that it could serve as a foundation of mathematics and it
was referred to as a higher-order logic.

Any static program analysis, such as the type checking algorithms in the
semantic analysis phase of compiler, has a connection to type theory.

In the modern literature, "type theory" refers to a typed system based around
lambda calculus. One influential system is Per Martin-Löf's intuitionistic type
theory, which was proposed as a foundation for constructive mathematics. Another
is Thierry Coquand's calculus of constructions, which is used as the foundation
by Coq, Lean, and other computer proof assistants. Type theory is an active area
of research, one direction being the development of homotopy type theory.

Much of the current research into type theory is driven by proof checkers, interactive proof assistants, and automated theorem provers.

A type theory is a mathematical logic, which is to say it is a collection
of rules of inference that result in judgments.
Most logics have judgments asserting "The proposition $phi$ is true", or
"The formula $phi$ is a well-formed formula".
A type theory has judgments that define types and assign them to a collection of
formal objects, known as terms.
A term and its type are often written together as
$"term" : sans("type")$

A term in logic is recursively defined as a constant symbol, variable, or a
function application, where a term is applied to another term.

*Judgements*
Judgments may follow from assumptions.
Such judgments are formally written with the turnstile symbol $tack.r$ with assumptions on the left.
$x : "bool", y : "nat" tack.r ("if" x y y) : "nat"$ // TODO: format types as bold
The list of assumptions on the left is the context of the judgment.
Capital greek letters, such as $Gamma$ and $Delta$, are common choices to represent some or all of the assumptions.

Most type theories have 4 judgments:
#table(
  columns: (auto, auto),
  inset: 5pt,
  align: horizon,
  stroke: contentcolor,
  table.header(
    [*Formal notation*], [*Description*]
  ),
  $Gamma tack.r T "Type"$, [$T$ is a type (under assumptions $Gamma$)],
  $Gamma tack.r t : T$, [$t$ is a term of type $T$ (under assumptions $Gamma$)],
  $Gamma tack.r T_1 = T_2$, [Type $T_1$ is equal to type $T_2$ (under assumptions $Gamma$)],
  $Gamma tack.r t_1 = t_2 : T$, [Terms $t_1$ and $t_2$ both of type $T$ are equal (under assumptions $Gamma$)],
)

The judgments enforce that every term has a type. The type will restrict which rules can be applied to a term. 

*Rules of Inference*
A type theory's inference rules say what judgments can be made, based on the
existence of other judgments.
Rules are expressed as a Gentzen-style deduction using a horizontal line, with
the required input judgments above the line and the resulting judgment below the
line.

For example, the following inference rule states a substitution rule for
judgmental equality.
$
  mat(
    delim: #none,
    augment: #(hline: 1),
    Gamma tack.r t : T_1 quad quad Delta tack.r T_1 = T_2;
    Gamma\, Delta tack.r t : T_2
  )
$
The rules are syntactic and work by rewriting. The metavariables
$Gamma, Delta, t, T_1, T_2$ may actually consist of complex terms and types that
contain many function applications, not just single symbols.

To generate a particular judgment in type theory, there must be a rule to
generate it, as well as rules to generate all of that rule's required inputs,
and so on.
The applied rules form a proof tree, where the top-most rules need no
assumptions.
One example of a rule that does not require any inputs is one that
states the type of a constant term.
For example, to assert that there is a term 0 of type $"nat"$ one would write
the following
$
  mat(
    delim: #none,
    augment: #(hline: 1),
    ;
    tack.r 0 : "nat"
  )
$

Generally, the desired conclusion of a proof in type theory is one of type
inhabitation.
The decision problem of type inhabitation is

Given a context $Gamma$ and a type $tau$ decide whether there exists a term $t$
that can be assigned the type $τ$ in the type environment $Gamma$.

$exists t. space Gamma tack.r t : tau ?$


Girard's paradox shows that type inhabitation is strongly related to the
consistency of a type system with Curry–Howard correspondence. To be sound, such
a system must have uninhabited types.
Girard's paradox is the type-theoretic analogue of Russell's paradox in set theory.

*Connections to logical foundations*
The logical framework of a type theory bears a resemblance to intuitionistic, or
constructive, logic.
Formally, type theory is often cited as an implementation of the Brouwer–
Heyting–Kolmogorov interpretation of intuitionistic logic.
Additionally, connections can be made to category theory and computer programs.

*Intuitionistic logic*
When used as a foundation, certain types are interpreted to be propositions
(statements that can be proven), and terms inhabiting the type are interpreted
to be proofs of that proposition.
When some types are interpreted as propositions, there is a set of common types
that can be used to connect them to make a Boolean algebra out of types.
However, the logic is not classical logic but intuitionistic logic, which is to
say it does not have the law of excluded middle nor double negation.

#table(
  columns: (auto, auto, auto, auto),
  inset: 5pt,
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

Because the law of excluded middle does not hold, there is no term of type
$Pi a. space A + (A -> tack.t)$. Likewise, double
negation does not hold, so there is no term of type 
$Pi A. space ((A -> tack.t) -> tack.t) -> A$.

It is possible to include the law of excluded middle and double negation into
a type theory, by rule or assumption. However, terms may not compute down to
canonical terms and it will interfere with the ability to determine if two terms
are judgementally equal to each other.
WHAT DOES THIS MEAN?

*Constructive mathematics*\
Per Martin-Löf proposed his intuitionistic type theory as a foundation for
constructive mathematics.
Constructive mathematics requires when proving "there exists an $x$ with
property $P(x)$.", one must construct a particular $x$ and a proof that it has
property $P$.
In type theory, existence is accomplished using the dependent product type, and
its proof requires a term of that type.

An example of a non-constructive proof is proof by contradiction. The first
step is assuming that $x$ does not exist and refuting it by contradiction.
The conclusion from that step is "it is not the case that $x$ does not exist".
The last step is, by double negation, concluding that $x$ exists. Constructive
mathematics does not allow the last step of removing the double negation to
conclude that $x$ exists.

Most of the type theories proposed as foundations are constructive, and
this includes most of the ones used by proof assistants.
It is possible to add non-constructive features to a type theory, by rule or
assumption.

*Curry-Howard correspondence*\
The Curry–Howard correspondence is the observed similarity between logics and
programming languages. The implication in logic, "A → {\displaystyle \to }
B" resembles a function from type "A" to type "B". For a variety of logics,
the rules are similar to expressions in a programming language's types. The
similarity goes farther, as applications of the rules resemble programs in the
programming languages. Thus, the correspondence is often summarized as "proofs
as programs".

The opposition of terms and types can also be viewed as one of implementation
and specification. By program synthesis, (the computational counterpart of)
type inhabitation can be used to construct (all or parts of) programs from the
specification given in the form of type information.

#table(
  columns: (auto, auto),
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


== Curry-Howard Isomorphism

Curry-Howard connects logic and computation, essentially showing that proofs are
programs, and propositions are types.

Logical propositions are types and instances of it are proofs.
The instantiation of a proposition (type) is the proof of it.
Implications are functions.

Not only is there a syntactic correspondance between logic and programming languages
but there is also a semantic one.

== Calculus of constructions

The CoC has been developed alongside the Coq proof assistant. As features were
added (or possible liabilities removed) to the theory, they became available
in Coq.
Variants of the CoC are used in other proof assistants, such as Matita and Lean. 

The calculus of constructions can be considered an *extension of the Curry–
Howard isomorphism*.
The Curry–Howard isomorphism associates a term in the simply typed lambda
calculus with each natural-deduction proof in intuitionistic propositional
logic.
The calculus of constructions extends this isomorphism to proofs in the
full intuitionistic predicate calculus, which includes proofs of quantified
statements (which we will also call "propositions").

Computational interpretation of intuitionistic logic.
Constructive foundation for mathematics.
Intuitionistic logic: No law of excluded middle. Not binary logic. No double negation
Constructive vs Existential

Inductive constructions
The CoC is a higher-order typed lambda calculus, initially developed by Thierry Coquand.
It is well known for being at the top of Barendregt's lambda cube. It is
possible within CoC to define functions from terms to terms, as well as terms to
types, types to types, and types to terms.

== Lean4

Leo de Moura (former Microsoft Research, now AWS) is not a mathematician, but a software engineer.
He wrote Lean as a software verification tool. He believed that in the future software
will be formally verified and thought that existing software verification tools such
as Coq and Isabelle were bad and unusable. So he wanted to create something better
to have better software through verification.
Software Verification, all it is, is proving that software has certain properites
(does it adher to the specification). So it's all about proving statements. So it's math!
And so this thing became very popular in the math community. So they built mathlib.
[From Vlad Tenev]

Lean was intitially developed as a software verification tool.
But software verification is just proving that a software adhers to a specification.
So since Lean was able to prove this, this could as well be used to prove
mathematical statements.


Dependend type theory.
Eine mächtige Sprache, in der mathematische Annahmen und Folgerungen formuliert
werden können. Es werden Propositions (Aussagen) definiert, bei denen es sich
um spezielle Typen handelt, und Proofs (Beweise), die einfach Elemente von
Propositions sind.

Funktionen sind lambda abstractions.

Lean is an interactive theorem prover (neither fully automatice nor fully manual).
Lean is also a general-purpose functional programming language.

It is an open-source project hosted on GitHub. It was developed primarily
by Leonardo de Moura while employed by Microsoft Research and now Amazon Web
Services

Lean was launched by Leonardo de Moura at Microsoft Research in 2013.[
In 2021, Lean 4 was released, which was a reimplementation of the Lean theorem
prover capable of producing C code which is then compiled
The frontend and other key parts of the core system, are all implemented in Lean itself.

*Online* under https://live.lean-lang.org/

Lean integrates with:
- Visual Studio Code
- Neovim
- Emacs
via a client-extension and Language Server Protocol server.

Lean4 is based on calculus of constructions with inductive types

Calculus of Constructions, with a countable hierarchy of non-cumulative
universes and inductive types.

Lean 4 naturally embodies this isomorphism through its type theory, turning
logical proofs into executable programs.

Lean can not only define mathematical objects and express mathematical
assertions in dependent type theory, but it also can be used as a language for
writing proofs.

Term-mode vs Tactic-mode

Small kernel -> probably no bugs


=== What people are saying about Lean
"Lean has become a key enabler in scaling automated reasoning at Amazon. Its
capacity to verify complex systems involving advanced mathematical concepts has
transformed how we tackle problems once thought too complex or impractical. Lean
is an indispensable tool in modern, large-scale software engineering, helping
ensure soundness, correctness, and verified AI across our systems."
— Byron Cook, Vice President and Distinguished Scientist, AWS

"Lean enables large-scale collaboration by allowing mathematicians to break
down complex proofs into smaller, verifiable components. This formalization
process ensures the correctness of proofs and facilitates contributions from
a broader community. With Lean, we are beginning to see how AI can accelerate
the formalization of mathematics, opening up new possibilities for research."
— Terence Tao, Fields Medalist and Professor of Mathematics, UCLA

"At Google DeepMind, we used Lean to build AlphaProof, a new
reinforcement-learning based system for formal math reasoning. Lean’s
extensibility and verification capabilities were key in enabling the development
of AlphaProof."
— Pushmeet Kohli, Vice President, Research Google DeepMind

"Mathematical Superintelligence (MSI) with Lean will play a critical role in any
industry where safety is paramount, including aerospace, automotive, and medical
technology. In addition, we look forward to providing early access to our
technology to students and researchers to accelerate advancement in mathematics,
science, and engineering."
— Tudor Achim, Co-Founder and CEO of Harmonic

"Lean is the core verification technology behind Cedar, the open-source
authorization language that powers cloud services like Amazon Verified
Permissions and AWS Verified Access. Our team rigorously formalizes and verifies
core components of Cedar using Lean’s proof assistant, and we leverage Lean’s
lightning-fast runtime to continuously test our production Rust code against
the Lean formalization. Lean’s efficiency, extensive libraries, and vibrant
community enable us to develop and maintain Cedar at scale, while ensuring
the key correctness and security properties that our users depend on."
— Emina Torlak, Senior Principal Applied Scientist, AWS

=== Functional programming

Functional programming is a programming paradigm where programs are constructed
by applying and composing functions
It is a declarative programming paradigm in which function definitions are
trees of expressions that map values to other values, rather than a sequence of
imperative statements which update the running state of the program.


== Applications

*Terance Tao* and *Peter Scholze* formalize their big theorems.

*Kevin Buzzard* uses it for the *Xena project*.
Rewrite every theorem and proof in the *undergraduate math curriculum* of Imperial
College London in Lean.

In 2017, a community-maintained project to develop a Lean library *mathlib* began,
with the goal to digitize as much of pure mathematics as possible in one large
cohesive library, up to research level mathematics. As of September 2024,
mathlib had formalised over 165,000 theorems and 85,000 definitions in Lean.

*AI/LLM*:
In 2024 Google DeepMind created *AlphaProof*, an AI model for generating proofs for
mathematical statements at the skill level of a silver medalist at the International Mathematical Olympiad (IMO).
This achievement is thanks to the ability of a proof assistant called Lean4, which
is able to check the validity of any arbitrary formal proof of any statement.

*Thomas Hales*
A *formal abstract*, or *fabstract* for short, is a formalization of the main
results (constructions, definitions, proofs, conjectures) of a piece of informal
mathematics, such as a research paper. There is no requirement that the entire
text be formalized.
FAbstracts enables machine learning in math.

*Harmonic* AI Research Lab trying to develop mathematical superintelligence.
Exploring the frontiers of human knowledge.
A lot about correctness.
Core believe: Math is reasoning.
The best way to train a model to be good in math is to directly train it in math,
instead of letting math emerge when being trained on another task.
If you make system that is really good at math, it will excell in all scientic domains,
because it's all about reasoning. And math embodies this best.
Other companies 
We are forging the world's most advanced mathematical reasoning engine.
When learning math understanding of general reasoning is a side product.
For this reason harmonic believes that training an AI on math, will give
the best and most general reasoner possible.

We will win the IMO soon. In 2024 or 2025.
When will you win a Millenium price? I would guess 2029.

Vlad Tenev believes that the next Millenium problem will be solved by an AI.
They believe the Riemann Hypothesis and the Existence Problem of solutions to Navier-Stockes
could be solved in 2029 using AI.

All future software could be verified by AI.

Reinformcement Learning with Lean. Playing against itself.
There is no upper ceiling to how good it can get, compared to other games,
where there eventually will be an optimal strategy.

Other companies run into a data wall with training their general purpose foundation models.
This isn't the case for math AI, because it can generate it's own data through playing proof games.
This is thanks to self-reinforcement / self-play.
Also for normal foundation models the quality of the internet content puts a ceiling on the intelligence of the system.
This is not the case for RL.
Same path as AlphaGo to AlphaZero.

Lean code length can be used as a measure for mathematical complexity.

== Computers and Theorem proving

Formal verification involves the use of logical and computational methods
to establish claims that are expressed in precise mathematical terms. These
can include ordinary mathematical theorems, as well as claims that pieces of
hardware or software, network protocols, and mechanical and hybrid systems meet
their specifications. In practice, there is not a sharp distinction between
verifying a piece of mathematics and verifying the correctness of a system:
formal verification requires describing hardware and software systems in
mathematical terms, at which point establishing claims as to their correctness
becomes a form of theorem proving. Conversely, the proof of a mathematical
theorem may require a lengthy computation, in which case verifying the truth
of the theorem requires verifying that the computation does what it is supposed
to do.

proof methods can be reduced to a small set of axioms and rules in any of a
number of foundational systems.

Automated theorem proving focuses on the "finding" aspect. Resolution theorem
provers, tableau theorem provers, fast satisfiability solvers, and so on provide
means of establishing the validity of formulas in propositional and first-order
logic.

Automated reasoning systems strive for power and efficiency, often at the
expense of guaranteed soundness.

In contrast, interactive theorem proving focuses on the "verification" aspect
of theorem proving, requiring that every claim is supported by a proof in a
suitable axiomatic foundation. This sets a very high standard: every rule of
inference and every step of a calculation has to be justified by appealing to
prior definitions and theorems, all the way down to basic axioms and rules.
In fact, most such systems provide fully elaborated "proof objects" that can
be communicated to other systems and checked independently. Constructing such
proofs typically requires much more input and interaction from users, but it
allows you to obtain deeper and more complex proofs.

The Lean Theorem Prover aims to bridge the gap between interactive and automated
theorem proving, by situating automated tools and methods in a framework that
supports user interaction and the construction of fully specified axiomatic
proofs. The goal is to support both mathematical reasoning and reasoning about
complex systems, and to verify claims in both domains.

Lean is based on, a version of dependent type theory.
Lean is based on a version of a system known as the Calculus of Constructions
with inductive types. Lean can not only define mathematical objects and express
mathematical assertions in dependent type theory, but it also can be used as a
language for writing proofs.
Calculus of Constructions, with a countable hierarchy of non-cumulative universes and inductive types

== Lean4 Coding

*Introduction to Simple Type Theory*

you can declare objects in Lean and check their types
```lean
def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false

```

What makes simple type theory powerful is that you can build new types out of
others. For example, if a and b are types, a -> b denotes the type of functions
from a to b, and a × b denotes the type of pairs consisting of an element of a
paired with an element of b, also known as the Cartesian product.

```lean
#check Nat → Nat      -- type the arrow as "\to" or "\r"
#check Nat -> Nat     -- alternative ASCII notation

#check Nat × Nat      -- type the product as "\times"
#check Prod Nat Nat   -- alternative notation

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  same type as above

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- a "functional"

#check Nat.succ     -- Nat → Nat
#check (0, 1)       -- Nat × Nat
#check Nat.add      -- Nat → Nat → Nat

#check Nat.succ 2   -- Nat
#check Nat.add 3    -- Nat → Nat
#check Nat.add 5 2  -- Nat
#check (5, 9).1     -- Nat
#check (5, 9).2     -- Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9

```
First, the application of a function f to a value x is denoted f x (e.g., Nat.succ 2).
Second, when writing type expressions, arrows associate to the right; for
example, the type of Nat.add is Nat → Nat → Nat which is equivalent to Nat
→ (Nat → Nat). Thus you can view Nat.add as a function that takes a natural
number and returns another function that takes a natural number and returns a
natural number. In type theory, this is generally more convenient than writing
Nat.add as a function that takes a pair of natural numbers as input and returns
a natural number as output. For example, it allows you to "partially apply" the
function Nat.add. Classic functional programming.

*Types as objects*

In type theory, a universe is a type whose elements are types. 

Type vs Term
types themselves can be regarded as terms
countably infinite hierarchy of such universes, with each universe being a term of the next one. 

One way in which Lean's dependent type theory extends simple type theory is that
types themselves --- entities like Nat and Bool --- are first-class citizens,
which is to say that they themselves are objects. For that to be the case, each
of them also has to have a type.

```lean
#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat
```

You can see that each one of the expressions above is an object of type Type. You can also declare new constants for types:
```lean
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α        -- Type
#check F α      -- Type
#check F Nat    -- Type
#check G α      -- Type → Type
#check G α β    -- Type
#check G α Nat  -- Type
```

you have already seen an example of a function of type Type → Type → Type,
namely, the Cartesian product Prod:
```lean
def α : Type := Nat
def β : Type := Bool

#check Prod α β       -- Type
#check α × β          -- Type

#check Prod Nat Nat   -- Type
#check Nat × Nat      -- Type
```

another example: given any type α, the type List α denotes the type of lists of elements of type α.
```lean
def α : Type := Nat

#check List α    -- Type
#check List Nat  -- Type
```

Given that every expression in Lean has a type, it is natural to ask: what type does Type itself have?
```lean
#check Type      -- Type 1
```

You have actually come up against one of the most subtle aspects of Lean's typing system. Lean's underlying foundation has an infinite hierarchy of types:
```lean
#check Type     -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5
```

Think of Type 0 as a universe of "small" or "ordinary" types. Type 1 is then a
larger universe of types, which contains Type 0 as an element, and Type 2 is an
even larger universe of types, which contains Type 1 as an element. The list is
infinite: there is a Type n for every natural number n. Type is an abbreviation
for Type 0:

*Function Abstraction and Evaluation*

Lean provides a fun (or λ) keyword to create a function from an expression as follows:
```lean
#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- λ and fun mean the same thing
#check fun x => x + 5     -- Nat inferred
#check λ x => x + 5       -- Nat inferred
```

You can evaluate a lambda function by passing the required parameters:
```lean
#eval (λ x : Nat => x + 5) 10    -- 15
```

Creating a function from another expression is a process known as lambda abstraction. Suppose you have the variable x : α and you can construct an expression t : β, then the expression fun (x : α) => t, or, equivalently, λ (x : α) => t, is an object of type α → β. Think of this as the function from α to β which maps any value x to the value t.

Here are some more examples
```lean
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat
```

You can also define a function that takes another function as input. The following calls a given function twice passing the output of the first invocation to the second:
```lean
def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2   -- 8
```

Now to get a bit more abstract, you can also specify arguments that are like type parameters:
```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```


*What makes dependent type theory dependent?*

The short explanation is that types can depend on parameters. You have already
seen a nice example of this: the type List α depends on the argument α, and this
dependence is what distinguishes List Nat and List Bool. For another example,
consider the type Vector α n, the type of vectors of elements of α of length n.
This type depends on two parameters: the type of the elements in the vector (α :
Type) and the length of the vector n : Nat.
(Think generics but more powerful.)

Suppose you wish to write a function cons which inserts a new element at the
head of a list. What type should cons have? Such a function is polymorphic: you
expect the cons function for Nat, Bool, or an arbitrary type α to behave the
same way. So it makes sense to take the type to be the first argument to cons,
so that for any type, α, cons α is the insertion function for lists of type α.
In other words, for every α, cons α is the function that takes an element a : α
and a list as : List α, and returns a new list, so you have cons α a as : List
α.

It is clear that cons α should have type α → List α → List α. But what type
should cons have? A first guess might be Type → α → List α → List α, but, on
reflection, this does not make sense: the α in this expression does not refer to
anything, whereas it should refer to the argument of type Type. In other words,
assuming α : Type is the first argument to the function, the type of the next
two elements are α and List α. These types vary depending on the first argument,
α.
```lean
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat        -- Nat → List Nat → List Nat
#check cons Bool       -- Bool → List Bool → List Bool
#check cons            -- (α : Type) → α → List α → List α
```

This is an instance of a dependent function type, or dependent arrow type. Given
α : Type and β : α → Type, think of β as a family of types over α, that is, a
type β a for each a : α. In that case, the type (a : α) → β a denotes the type
of functions f with the property that, for each a : α, f a is an element of β a.
In other words, the type of the value returned by f depends on its input.

Notice that (a : α) → β makes sense for any expression β : Type. When the value
of β depends on a (as does, for example, the expression β a in the previous
paragraph), (a : α) → β denotes a dependent function type. When β doesn't depend
on a, (a : α) → β is no different from the type α → β. Indeed, in dependent type
theory (and in Lean), α → β is just notation for (a : α) → β when β does not
depend on a.

*Implicit Arguments*:
But this information is redundant: one can infer the argument

*Propositions as Types*

In this chapter, we will begin to explain how to write mathematical assertions
and proofs in the language of dependent type theory as well.

One strategy for proving assertions about objects defined in the language of
dependent type theory is to layer an assertion language and a proof language
on top of the definition language. But there is no reason to multiply languages
in this way: dependent type theory is flexible and expressive, and there is no
reason we cannot represent assertions and proofs in the same general framework.

For example, we could introduce a new type, Prop, to represent propositions, and
introduce constructors to build new propositions from others.
```lean
#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop
```

We could then introduce, for each element p : Prop, another type Proof p, for the type of proofs of p. An "axiom" would be a constant of such a type.
```lean
#check Proof   -- Proof : Prop → Type

axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)
#check and_comm p q     -- Proof (Implies (And p q) (And q p))
```

ule of modus ponens:

"From a proof of Implies p q and a proof of p, we obtain a proof of q."

We could represent this as follows:
```lean
axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q
```

Systems of natural deduction for propositional logic also typically rely on the following rule:

"Suppose that, assuming p as a hypothesis, we have a proof of q. Then we can "cancel" the hypothesis and obtain a proof of Implies p q."

We could render this as follows:
```lean
axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)
```

*Inductive types*

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

This is a simple proof of $(P and Q) -> (Q and P)$ for two propositions
$P$ and $Q$ (where $and$ is the conjunction and $->$ the implication) in Lean using *tactic mode*:

```lean
theorem and_comm (p q : Prop) : p ∧ q → q ∧ p := by
  intro h            -- assume p ∧ q with proof h, the goal is q ∧ p
  apply And.intro    -- goal is split into two subgoals, one is q and the other is p
  · exact h.right    -- first subgoal is exactly the right part of h : p ∧ q
  · exact h.left     -- second subgoal is exactly the left part of h : p ∧ q
```

This same proof in *term mode*:

```lean
theorem and_swap (p q : Prop) : p ∧ q → q ∧ p :=
  fun ⟨hp, hq⟩ => ⟨hq, hp⟩
```


Sources:

Why Vlad Tenev and Tudor Achim of Harmonic Think AI Is About to Change Math—and Why It Matters
https://www.youtube.com/watch?v=NvAxuCIBb-c
