# potato
being an experiment with potato power


## what's the plan, dead man?

The purpose of the **potato** project is to develop a toolkit for implementing typecheckers for *predicative* dependent type theories which are proven

  * **sound** in that only well typed terms typecheck
  * **complete** in that all well typed terms typecheck
  
There are lots of components to such constructions, but the key challenge is to build the evaluator which allows types to be reduced to normal form in order to be compared for equality. That's where predicativity and potatoes both come in: the method is to build a type of large enough ordinals such that every type maps to an ordinal, transfinite induction on which is sufficient to ensure that computation at that type terminates. But it's delightfully unsubtle! The evaluator just runs, like an Irish pacman (Dr Brady's gag about pacman-completeness takes on another dimension), on whatever ordinal carbohydrates it can gobble up as it bobbles along. It computes with terms in a raw syntax which need not make sense for the evaluator to function. The evaluator checks types *dynamically* as it goes, doing only what is needed to ensure that the rules are being superficially respected.


## the bidirectional setup

The bidirection syntax cleaves the world in two:

  * **chk** (checkable) terms require a type proposed in advance if they are to be typechecked or evaluated. They include all the canonical forms, but they also embed...
  * **syn** (synthesizable) terms, from which types may be computed, either precisely (by a type synthesis algorithm) or approximately (by the evaluator). They include variables (which get types from the context) and all the elimination forms (which compute using any potato supply available). The synthesized type corresponds to the spare potatoes after the elimination step. A chk term, t, may embed into a syn term only if it is *radicalised*, i.e., given a type annotation, becoming t : T, where T serves both as the clue to t's type, as well as the hearty meal needed before one attempts to compute t's value.
  

## how does the evaluator work?

The evaluator works in fairly standard *normalisation-by-evaluation* style. Terms are evaluated to higher-order values in a Kripke model, which may then be reified back to terms.

Types themselves are chk terms, which are finite first-order data structures (i.e., made of potatoes). In order to power computation, we must map them to transfinite ordinals made of sugar, in a type defined by *induction-recursion*. The computational analogue of the amylase enzyme replaces first-order abstractions (which admit substitution) by the corresponding higher-order functions (replacing substitution by application). In the world of syntactic starch, T with (s : S) for x is not syntactically smaller than Pi S x.T, but once converted to semantic sugar, the limit ordinal Pi S T has inductive substructures S and T s for any s : S.

This transfinite notion of semantic type allows us to define the Kripke model we need, with respect to context inclusion. A value is either a *stopped* term or a *going* radical&emdash;powered up by its type with all it needs for whatever eliminations may lie ahead and by Kripke semantics for any binders under which it must go.

The evaluators for both syntactic categories require an *environment* mapping free variables to *cells*. A *cell* is the dependent pair of a semantic type and a value of that type. The evaluator for chk terms takes a semantic type as its input, which is used to empower the semantic value which it yields. The evaluator for syn terms expects to find all the power it needs therein, and emits a cell. When the latter encounters a radical, t : T, it computes the semantic counterpart (i.e., the ordinal) of T, which it then feeds to the evaluator for t.

The embedding from syn to chk requires the corresponding conversion of values from one type to another, which can happen if the source ordinal is at least as powerful as the target. If not, the source ordinal is certainly powerful enough to reify the value, so computation stops. Likewise, anytime we run out of ordinal power to actually compute with values, we reify them. That is, the consequence of having the *wrong* ordinal is just that we give up evaluating before we reach normal form. Bear in mind that some terms do not have a normal form.

