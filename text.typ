#set text(font: "New Computer Modern Sans")
//#show math.equation: set text(font: "Fira Math Ultra")

#set par(justify: true)

#let contentcolor = white
#let bgcolor = black
#set text(fill: contentcolor)
#set page(fill: bgcolor)

#let False = $tack.t$
#let True = $top$


// TODO: at least once quickly show the definition of the natural numbers

// TODO: emphasize the idea that type theory includes logic.
// in contrast: set theory is built on top of logic.
// for type theory: you have both in one.

// think about word use:
// instance is inhabitant

= Beginning

Greeting and Welcome
Lighten the mood
Introduction: What is this talk about?

Lean is a programming language with a type system so powerful it's able to not only express
any mathematical statement but even check the validity any proof of the statement.

This is enabled by the ideas of type theory.
Type theory can be used to build a new *Foundation of Mathematics* by introducing a type-theoretic logic
and in this way type-theory is an alternative to set theory for constructing the whole of mathematics.
It's more fundamental then set theory.
It's a very computational formulation of mathematics, which will lead to a constructive version of mathematics.
Type theories serve as alternatives to set theory as a foundation of mathematics.
Two influential type theories that have been proposed as foundations are:
- Typed λ-calculus of Alonzo Church
- Intuitionistic type theory of Per Martin-Löf

Type theory was created to avoid a paradox in a mathematical equation based on
naive set theory and formal logic, called Russell's Paradox. You probably already heard of it.
We will soon see, how type theory avoids this.

Type theory is particularly popular in conjunction with Alonzo Church's lambda calculus.
Church demonstrated that it could serve as a foundation of mathematics and it
was referred to as a higher-order logic.

In the modern literature, "type theory" refers to a typed system based around
lambda calculus.

Thierry Coquand's calculus of constructions, which is used as the foundation
by Coq, Lean, and other computer proof assistants.

Any static program analysis, such as the type checking algorithms in the
semantic analysis phase of compiler, has a connection to type theory.

= Motivation, Relevance and Applications

Not so suprising: Mathematicians such as Terrance Tao use Lean to formalize their complicated 100 page conjectures

// Considering moving down the more comprehensive explanation of Math in AI / Lean in AI...
// Especially the indepth RL part. Maybe at the end?
More interesting: AI Math powered by Lean
How does this work? LLM produces lean code.
Not only is this a language/syntax for expressing math (already extremly important)
but lean is also a proof checker, so it provides feedback to the LLM wheter the proof is valid or not!
LLM can learn through Self-Reinforcement Learning by doing self-play.
Recent breakthrough 2024: Silver Medalist at International Math Olympiad (IMO)
Speculative Future: Harmonic
They believe that AI in math will change the way we do math.
Next Millenium Problem will be solved by AI or by a human with heavy AI support.
Maybe someday Riemann Hypothesis or Navier-Stockes will be resolved by AI. Undecidable?
Current LLMs and Foundation models are trained on texts.
AI has word predication as terminal goal. The emergent instrumental goals are producing coherent texts
with meaningful content. It needs to understand the content. Learns various topics and get good at reasoning.
But here reasoning is just a sideproduct.
What if reasoning is terminal goal. Most powerful form of reasoning: Math!
So built an AI that knows how to do math. Will be the most powerful reasoner and will be good at reasoning in other fields too! E.g. economics
Also RL! Typical LLMs are limited by the quality of data they are trained on. The quality of the data sets an upper bounds on the intelligence of the LLM.
But with AI + Lean there is no such upper bound, since we can do RL.
The AI can do self-play where it plays against the lean compiler and tries to come up with proofs that are accepted by lean.
It generates "perfect" data on the fly by asking the lean type-checker for validity.
The data is perfect since the compiler gives always correct labels of correct or wrong proofs.
So no upper bound on intelligence!
So Harmonic talks about Math Superintelligence and wants to explore the frontiers of human knowledge.

= Simple Type Theory in the programming language Lean

Basic definitions of objects of a type
Types and terms.
Compare to C++

= Building Types from existing types

Type constructors: Function Arrow, Product Type, Sum Type

What makes simple type theory powerful is that you can build new types out of
others. For example, if a and b are types, a -> b denotes the type of functions
from a to b, and a × b denotes the type of pairs consisting of an element of a
paired with an element of b, also known as the Cartesian product.

Quick elaboration on functions in lean:


First, the application of a function f to a value x is denoted f x (e.g., Nat.succ 2).
Second, when writing type expressions, arrows associate to the right; for
example, the type of Nat.add is Nat → Nat → Nat which is equivalent to Nat
→ (Nat → Nat). Thus you can view Nat.add as a function that takes a natural
number and returns another function that takes a natural number and returns a
natural number. In type theory, this is generally more convenient than writing
Nat.add as a function that takes a pair of natural numbers as input and returns
a natural number as output. For example, it allows you to "partially apply" the
function Nat.add. Classic functional programming.

= What is special about Lean's type system?

Types as first class citizens.
Types themselves can be objects.
Nat is an object.


One way in which Lean's dependent type theory extends simple type theory is that
types themselves --- entities like Nat and Bool --- are first-class citizens,
which is to say that they themselves are objects. For that to be the case, each
of them also has to have a type.


What is it's type? It's `Type`!
Can have variables of type `Type`.
Compare to C++ templates and `typename T`.
Also exists in C++ but in lean it's first class.
No differentiation between normal variables and type variables. Same syntax, same semantics.

We can now use the type `Type` to construct new types.
There is for instance the `List` type constructor, which takes as argument the type of the elements of the list
and gives back the type of the list of this element type.
This is the same as templating a `std::vector` in C++. But it's just more streamlined.

But now we have a new type, called `Type`... It must also be treatet as first class citizen!
What is it's type? It's `Type 1`.
Oh. New type! It must also be an object... What is the type of `Type 1`? It's `Type 2`!
Keep on doing this giving you `Type 3`, `Type 4` and so on...

If u have never seen this before then this is probably some Major Brainfuck to you.

This creates an infinte but countable hierarchy of so called *type universes*.
These form a hierarchy, because in every higher type universe contains all the lower type universes as *objects*!
This is the first characterization of Lean's type system.
It features a countably infinte hierarchy of cumulative type universes.
`Type n` is strictly contained in the higher universe `Type (n+1)`.
`Type n : Type (n+1)`
In other words:
In type theory, a universe is a type whose elements are types. 
Types themselves can be regarded as terms.
Each universe being a term of the next one.

This is probably very unused for you. Because in conventional programming languages
you pretty much only work with the `Type 0` universe, also just called `Type`, which contains the Integers, Floats, Booleans and so on.

Think of Type 0 as a universe of "small" or "ordinary" types. Type 1 is then a
larger universe of types, which contains Type 0 as an element, and Type 2 is an
even larger universe of types, which contains Type 1 as an element. The list is
infinite: there is a Type n for every natural number n. Type is an abbreviation
for Type 0:

But it allows for talking about higher-order types, such as `Nat -> Type`.
This allows for further abstraction into infinity.

But in lean this is necessary for this first class support of types.
Because if it wouldn't be for this hierarchy. Then we would run into contradictions, such as *Girard's paradox*,
which is a type-theoretic version of the set-theoretic *Russell's paradox*.

Russell's paradox is that, without proper axioms, it is possible to define
the set of all sets that are not members of themselves; this set both contains
itself and does not contain itself.

This system avoided contradictions suggested in Russell's paradox by creating
a hierarchy of types and then assigning each concrete mathematical entity to a
specific type. Entities of a given type were built exclusively of subtypes of
that type, thus preventing an entity from being defined using itself.

The hierarchy disallows for any type universe to contain itself as an object. Only higher up universes contain the lower down universes.
Lean avoids impredicative types at higher levels and prevents self-reference.
It's a strict containment without self-reference and this avoid logical paradoxes similar to Russell's.
This is like the resolution of Russell's paradox, where one forbids the existance of sets that contain themselves.
So this is the solution in type theory.

= Functional Programming in Lean

Functional programming is a programming paradigm where programs are constructed
by applying and composing functions
It is a declarative programming paradigm in which function definitions are
trees of expressions that map values to other values, rather than a sequence of
imperative statements which update the running state of the program.

Now let's do a little switch and look at the nature of functional programming.
Lean is a functional programming language.
This means that functions themselves are first-class citizens, meaning they are just normals objects.
In C++ lambda functions are the closest thing to this, but in lean it's must more powerful.


The introduction (creation) of a function is called *lambda abstraction*.
Syntax for lambda abstraction involves `fun` keyword or `lambda` unicode symbol.
The elimination (use) of a function is called *lambda application*.
The syntax for function application is `f x` only using a space, no paranthesis.


Creating a function from another expression is a process known as lambda
abstraction. Suppose you have the variable x : α and you can construct an
expression t : β, then the expression fun (x : α) => t, or, equivalently, λ (x :
α) => t, is an object of type α → β. Think of this as the function from α to β
which maps any value x to the value t.


In functional programming multiple arguments through cartesian product / tuples are discouraged.
The more idiomatic way is creating function chains by a precedure known as currying.
The benefit is that partial function application is more natural.
Code Examples!

The fact that functions are first-class they allow for higher order functions.
Functions can be normal arguments of functions. In contrast: In C++ templates are necessary.

As example we can write a composition function, taking two functions, whose argument and return types align, as in this example, and it also takes a input argument.
Now this is for some specific types for the argument and return type. Instead we can generalize this and have it take
arbitrary types. This is something very normal in lean.

= What are dependent types?

Do we have time explain this and how relevant is it?

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

But this information is redundant: one can infer the argument.
-> Implicit function arguments.

= Propositional Logic through Type Theory

Now after this quick intro to lean as programming language, we know
want to learn how to do some actual math with it and it is related to math.

!!! The story of how lean came to be? Actually software verifier, but the same as math proofs!

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


For this we will try to somehow find a way of formulating propositions as known from propositional logic using lean.

!!!!!!! AVOID `Proof p` for explaining !!!!!

Defined a type `Prop` for propositions (statements) and dependent type `Proof p` for proofs.
Type constructors for usual logical connectors: `And, Or, Not, Implies`.

*Modus Ponens* example
Modus Ponens is implication elimination.
It's a rule of inference.

Simplifications:
Don't differentiate between proposition itself and it's proof. Combine them.
We can leverage the type system, by the proof being an object of the propositional type!
This scheme is known as *propositions-as-types* and *proofs-as-programs*, but maybe better *proofs-as-terms*.

In order to prove a proposition, all we need to do is, to construct a term of this type!
So proving something in lean is just playing the game of constructing terms of a type.

Thanks to this idea further simplifications are possible.
The Implication arrow now becomes the same as the function arrow.
Not only are they syntacticly the same, they are event semanticly the same in type theory.
This is the first example of the *Curry-Howard Isomorphism*!
Explain what it means!

Now understand the whole hierarchy of type universes.
`Prop` is type universe at the bottom of the hierarchy!
`Prop` is the type of all logical propositions. It's different from `Type`, where all conventional data types like `Nat` live.
`Prop` is below `Type 0`. It's `Sort 0`. While `Type n` is `Sort (n+1)`
`Prop` is contained in `Type 0`.
Show big universe table.
First row: Universe, Second row: Example Type in Universe, Third row: Example Term of Type in Universe

`Prop` is special because of *proof-irrelevance*. The actual terms don't matter
in `Prop`. Lean doesn't care what the term looks like once it's existance it's established.
It's only a question of *type inhabitation*.
So all terms of a proposition are considered completely equivalent.

= Some more logic constructs


Logical connectives are generally characterized by their introduction and
elimination rules. An introduction rule shows how to establish a claim involving
the connective, while an elimination rule shows how to use such a statement that
contains the connective to derive others.

True: Easiest introduction but no elimination.
Introduction-only

False: Impossible introduction but most powerful elimination.
Elimination-only
False is a contradiction.
False is the Empty type. It's by definition a uninhabitated type. That's why it doesn't have a intro rule.
This is a powerful construct.
Once again CH.

False can be used to define negation as
$not p$ as $p -> False$.
Show negation of implication as an example of how normal it is to work with False, even though it's a contradiciton.
$p -> False$ means that `p` itself is uninhabitated. So there is cannot be a proof of `p`.
Even though False doesn't have an intro rule, we can still work with terms of it! How?
By hypothetically assuming it's existance and deriving something else.
Give some code examples.
For example, if we have a proof `h : False`, we can derive any proposition `q` from it, known as ex falso quodlibet.
```lean
false.elim : ∀ (q : Prop), False → q
```
The introduction rule for negation, is show that by assuming `p` that this leads to a contradiction.
The elimination rule for negation is dual to this and shows that if we have `p` and `not p` then we have a contradiction.

As an axiom or assumption: If we assume False directly or as an axiom, we can use it to derive any result.
This makes the axiomatic system unsound.

And is like a product type. Once again CH. Show `intro` and `elem`.
Or is Sum type (CH). Show `intro` and `elem`.
elimination is case-based hypothetical reasoning

= Full Curry-Howard

The whole table.

The calculus of constructions can be considered an *extension of the Curry–
Howard isomorphism*.
The Curry–Howard isomorphism associates a term in the simply typed lambda
calculus with each natural-deduction proof in intuitionistic propositional
logic.
The calculus of constructions extends this isomorphism to proofs in the
full intuitionistic predicate calculus, which includes proofs of quantified
statements (which we will also call "propositions").

The CoC is a higher-order typed lambda calculus, initially developed by Thierry Coquand.
The CoC has been developed alongside the Coq proof assistant.

The CoC is a higher-order typed lambda calculus, initially developed by Thierry Coquand.
It is well known for being at the top of Barendregt's lambda cube. It is
possible within CoC to define functions from terms to terms, as well as terms to
types, types to types, and types to terms.



= Predicate logic

Predicates as functions on various arguments to determine the truth for this argument.
e.g. `is_even : Nat -> Prop`

Universal Quantifier "Forall" => "Universal" because a big conjunction over the whole type universe!!!
Really is just a function with arguments of the type into Prop.

Existance Quantifier "Existance" => Big disjunction over the whole universe.
Existance is just $not forall$.

= Constructive Math

Explained Lean's constructive mathematics—each proof explicitly constructs what it claims exists.

Constructive/Intuistionic vs Classical Logic.

There is a single axiom that governs this:
*Law of Excluded Middle* (EM)
Double Negation
Binary Logic and Philosphical Implications
Non-constructive Existence Proofs
Proof by contradiction.

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

= Some proofs about (Aquivalence and Partial Order) Relations

Relation known from set theory. But relations are more fundamental and can be formulated directly
in logic/type theory.
Define relation as`alpha -> alpha -> Prop`


Define Aequivalence Relation in Lean Code:
- Reflexiv
- Symmetric
- Transitive

Some elementary proofs about them.

So far we've only seen Lean in *term-mode*. But actually for writing more complicated proofs,
this is used only very rarely. Instead there is *tactic-mode*.
Here the *automated proof writing* of lean comes into play.


The Lean Theorem Prover aims to bridge the gap between interactive and automated
theorem proving, by situating automated tools and methods in a framework that
supports user interaction and the construction of fully specified axiomatic
proofs. The goal is to support both mathematical reasoning and reasoning about
complex systems, and to verify claims in both domains.


Lean is an interactive theorem prover (neither fully automatice nor fully manual).
In contrast to automated proof theorem proving, interactive theorem proving focuses on the "verification" aspect
of theorem proving, requiring that every claim is supported by a proof in a
suitable axiomatic foundation. This sets a very high standard: every rule of
inference and every step of a calculation has to be justified by appealing to
prior definitions and theorems, all the way down to basic axioms and rules.
In fact, most such systems provide fully elaborated "proof objects" that can
be communicated to other systems and checked independently. Constructing such
proofs typically requires much more input and interaction from users, but it
allows you to obtain deeper and more complex proofs.


= Lean in Mathematics

Quick showcase of *mathlib* and some code.

= Lean as a project

It is an open-source project hosted on GitHub. It was developed primarily
by Leonardo de Moura while employed by Microsoft Research and now Amazon Web
Services (AWS).

In 2021, Lean 4 was released, which was a reimplementation of the Lean theorem
prover capable of producing C code which is then compiled
The frontend and other key parts of the core system, are all implemented in Lean itself.

*Online* under https://live.lean-lang.org/

Lean integrates with:
- Visual Studio Code
- Neovim
- Emacs
via a client-extension and Language Server Protocol server.

Lean4 is based on the Calculus of Constructions, with a countable hierarchy of non-cumulative
universes and inductive types.

Small kernel -> probably no bugs

= Final words

Lean and Type Theory is Great!!!
I encourage you to investigate it further!

I'm sorry if the talk was very complicated or if I did a bad job at explaining.
If you got any questions let me know! Either right now or after the talk at the Apero or at any other time :).

Getting into Lean and trying it out on your own computer is a joy.
Lean is GOOD software. The software engineers that created lean, know how to create good software.
Great LSP, Great VScode extension, web version. Elan package manager written in Rust.
A good official book on theorem proving in Lean.
And especially the language and it's compiler. The smartest compiler i've ever seen.
Can deduce incredible things and you can be extremly concise.
Big metaprogramming is contained.

Point to Further resources:
- Theorem Proving in Lean4 Book
- Lean Zulip
- For AI in Math: Harmonic Podcast

