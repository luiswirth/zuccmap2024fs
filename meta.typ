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

More interesting: AI Math powered by Lean
How does this work? LLM produces lean code.
Not only is this a language for expressing math (already extremly important)
but lean is also a proof checker, so it provides feedback to the LLM wheter the proof is valid or not!
LLM can learn through Self-Reinforcement Learning.
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
It kind of generates the data on the fly and this data is of best quality since the compiler gives always correct labels of sound or unsound proofs.
So no upper bound on intelligence!
So Harmonic talks about Math Superintelligence and wants to explore the frontiers of human knowledge.

= Simple Type Theory in the programming language Lean

Basic definitions of objects of a type
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
It features a countably infinte hierarchy of commulative type universes.

This is probably very unused for you. Because in conventional programming languages
you pretty much only work with the `Type 0` universe, also just called `Type`, which contains the Integers, Floats, Booleans and so on.

But in lean this is necessary for this first class support of types.
Because if it wouldn't be for this hierarchy. Then we would run into contradictions, such as *Girard's paradox*,
which is a type-theoretic version of the set-theoretic *Russell's paradox*.
The hierarchy disallows for any type universe to contain itself as an object. Only higher up universes contain the lower down universes.
This is like the resolution of Russell's paradox, where one forbids the existance of sets that contain themselves.
So this is the solution in type theory.

= Functional Programming in Lean

Now let's do a little switch and look at the nature of functional programming.
Lean is a functional programming language.
This means that functions themselves are first-class citizens, meaning they are just normals objects.
In C++ lambda functions are the closest thing to this, but in lean it's must more powerful.

Functions can be normal arguments of functions.

Multiple arguments through currying.

We can write a composition function, taking two functions, whose argument and return types align, as in this example, and it also takes a input argument.
Now this is for some specific types for the argument and return type. Instead we can generalize this and have it take
arbitrary types. This is something very normal in lean.

= What are dependent types?

Do we have time explain this and how relevant is it?

= Propositional Logic through Type Theory

!!! The story of how lean came to be? Actually software verifier, but the same as math proofs!

Now after this quick intro to lean as programming language, we know
want to learn how to do some actual math with it and it is related to math.

For this we will try to somehow find a way of formulating propositions as known from propositional logic using lean.


propositions-as-types
proofs-as-programs

playing the game of constructing an instance of a type
exactly this game one must play in order to come up with a proof of a statement in lean

= Predicate logic


= Some proofs about (Aquivalence and Partial Order) Relations

Define a relation.

Some elementary proofs about them.

= Lean in Mathematics

So far we've only seen Lean in *term-mode*. But actually for writing more complicated proofs,
this is used only very rarely. Instead there is *tactic-mode*.
Here the *automated proof writing* of lean comes into play.

Quick showcase of *mathlib* and some code.

= Final words

Getting into Lean and trying it out on your own computer is a joy.
Lean is GOOD software. The software engineers that created lean, know how to create good software.
Great LSP, Great VScode extension, web version. Elan package manager written in Rust.
A good official book on theorem proving in Lean.
And especially the language and it's compiler. The smartest compiler i've ever seen.
Can deduce incredible things and you can be extremly concise.
Big metaprogramming is contained.
