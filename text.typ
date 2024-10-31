#set text(font: "New Computer Modern Sans")
//#show math.equation: set text(font: "Fira Math Ultra")

#set par(justify: true)

#let contentcolor = white
#let bgcolor = black
#set text(fill: contentcolor)
#set page(fill: bgcolor)

#let False = $tack.t$
#let True = $top$

= Beginning

Greeting and Welcome
Lighten the mood
Introduction: What is this talk about?

Lean is a programming langauge with a type system so powerful it's able to not only express
any mathematical statement but even check the validity any proof of the statement.

This is enabled by the ideas of type theory.
Type theory can be used to build a new *Foundation of Mathematics* by introducing a type-theoretic logic
and in this way type-theory is an alternative to set theory for constructing the whole of mathematics.
It's more fundamental then set theory.
It's a very computational formulation of mathematics, which will lead to a constructive version of mathematics.

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

= What is special about Lean's type system?

Types as first class citizens.
Types themselves can be objects.
Nat is an object.
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
This creates an infinte but countable hierarchy of so called *type universes*.
These form a hierarchy, because in every higher type universe contains all the lower type universes as *objects*!
This is the first characterization of Lean's type system.
It features a countably infinte hierarchy of cumulative type universes.
`Type n` is strictly contained in the higher universe `Type (n+1)`.
`Type n : Type (n+1)`

This is probably very unused for you. Because in conventional programming languages
you pretty much only work with the `Type 0` universe, also just called `Type`, which contains the Integers, Floats, Booleans and so on.

But it allows for talking about higher-order types, such as `Nat -> Type`.
This allows for further abstraction into infinity.

But in lean this is necessary for this first class support of types.
Because if it wouldn't be for this hierarchy. Then we would run into contradictions, such as *Girard's paradox*,
which is a type-theoretic version of the set-theoretic *Russell's paradox*.
The hierarchy disallows for any type universe to contain itself as an object. Only higher up universes contain the lower down universes.
Lean avoids impredicative types at higher levels and prevents self-reference.
It's a strict containment without self-reference and this avoid logical paradoxes similar to Russell's.
This is like the resolution of Russell's paradox, where one forbids the existance of sets that contain themselves.
So this is the solution in type theory.

= Functional Programming in Lean

Now let's do a little switch and look at the nature of functional programming.
Lean is a functional programming language.
This means that functions themselves are first-class citizens, meaning they are just normals objects.
In C++ lambda functions are the closest thing to this, but in lean it's must more powerful.


The introduction (creation) of a function is called *lambda abstraction*.
Syntax for lambda abstraction involves `fun` keyword or `lambda` unicode symbol.
The elimination (use) of a function is called *lambda application*.
The syntax for function application is `f x` only using a space, no paranthesis.

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

= Propositional Logic through Type Theory

Now after this quick intro to lean as programming language, we know
want to learn how to do some actual math with it and it is related to math.

!!! The story of how lean came to be? Actually software verifier, but the same as math proofs!

For this we will try to somehow find a way of formulating propositions as known from propositional logic using lean.

!!!!!!! AVOID `Proof p` for explaining !!!!!

Defined a type `Prop` for propositions (statements) and dependent type `Proof p` for proofs.
Type constructors for usual logical connectors: `And, Or, Not, Implies`.

*Modus Ponens* example

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

As an axiom or assumption: If we assume False directly or as an axiom, we can use it to derive any result.
This makes the axiomatic system unsound.

And is like a product type. Once again CH. Show `intro` and `elem`.
Or is Sum type (CH). Show `intro` and `elem`.

= Full Curry-Howard

The whole table!

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

Constructive Mathematics is powerful in the sense that there is always a computational recipe for
creating the stipulated mathematical object.
But it's also less powerful in the sense, that fewer mathematical statements can be proven this way.

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

= Lean in Mathematics

Quick showcase of *mathlib* and some code.

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
