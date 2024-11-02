#set text(font: "New Computer Modern Sans")
//#show math.equation: set text(font: "Fira Math Ultra")

#set par(justify: true)

#let contentcolor = white
#let bgcolor = black
#set text(fill: contentcolor)
#set page(fill: bgcolor)

= Lean4 Coding

== Type theory as a mathematical logic

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

Given a context $Gamma$ and a type $tau$ decide whether there exists a term $t$
that can be assigned the type $τ$ in the type environment $Gamma$.

$exists t. space Gamma tack.r t : tau ?$


Girard's paradox shows that type inhabitation is strongly related to the
consistency of a type system with Curry–Howard correspondence. To be sound, such
a system must have uninhabited types.
Girard's paradox is the type-theoretic analogue of Russell's paradox in set theory.



== Software Verification vs Math Proofs

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


=== Quotes: What people are saying about Lean

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

