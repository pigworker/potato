# potato
being an experiment with potato power


## what's the plan, dead man?

The purpose of the **potato** project is to develop a toolkit for implementing typecheckers for *predicative* dependent type theories which are proven

  * **sound** in that only well typed terms typecheck
  * **complete** in that all well typed terms typecheck
  
There are lots of components to such constructions, but the key challenge is to build the evaluator which allows types to be reduced to normal form in order to be compared for equality. That's where predicativity and potatoes both come in: the method is to build a type of large enough ordinals such that every type maps to an ordinal, transfinite induction on which is sufficient to ensure that computation at that type terminates. But it's delightfully unsubtle! The evaluator just runs, like an Irish pacman (Dr Brady's gag about pacman-completeness takes on another dimension), on whatever ordinal carbohydrates it can gobble up as it bobbles along. It computes with terms in a raw syntax which need not make sense for the evaluator to function. The evaluator checks types *dynamically* as it goes, doing only what is needed to ensure that the rules are being superficially respected.


## the bidirectional setup

The bidirection syntax cleaves the world in two:

  * **chk** (checkable) terms, `s` `t` `S` `T`, require a type proposed in advance if they are to be typechecked or evaluated. They include all the canonical forms, but they also embed `(e)`...
  * **syn** (synthesizable) terms, `e` `f`, from which types may be computed, either precisely (by a type synthesis algorithm) or approximately (by the evaluator). They include variables `x` (which get types from the context) and all the elimination forms `e s` (which compute using any potato supply available). The synthesized type corresponds to the spare potatoes after the elimination step. A chk term, `t`, may embed into a syn term only if it is *radicalised*, i.e., given a type annotation, becoming `(t : T)`, where `T` serves both as the clue to `t`'s type, as well as the hearty meal needed before one attempts to compute `t`'s value.
  

## how does the evaluator work?

The evaluator works in fairly standard *normalisation-by-evaluation* style. Terms are evaluated to higher-order values in a Kripke model, which may then be reified back to terms.

Types themselves are chk terms, which are finite first-order data structures (i.e., made of potatoes). In order to power computation, we must map them to transfinite ordinals made of sugar, in a type defined by *induction-recursion*. The computational analogue of the amylase enzyme replaces first-order abstractions (which admit substitution) by the corresponding higher-order functions (replacing substitution by application). In the world of syntactic starch, `T` with `(s : S)` for `x` is not syntactically smaller than `Pi S x.T`, but once converted to semantic sugar, the limit ordinal *Pi S T* has inductive substructures *S* and *T s* for any *s : S*.

This transfinite notion of semantic type allows us to define the Kripke model we need, with respect to context inclusion. A value is either a *stopped* term or a *going* radical---powered up by its type with all it needs for whatever eliminations may lie ahead and by Kripke semantics for any binders under which it must go.

The evaluators for both syntactic categories require an *environment* mapping free variables to *cells*. A *cell* is the dependent pair of a semantic type and a value of that type. The evaluator for chk terms takes a semantic type as its input, which is used to empower the semantic value which it yields. The evaluator for syn terms expects to find all the power it needs therein, and emits a cell. When the latter encounters a radical, `t : T`, it computes the semantic counterpart (i.e., the ordinal) of `T`, which it then feeds to the evaluator for `t`.

The embedding from syn to chk requires the corresponding conversion of values from one type to another, which can happen if the source ordinal is at least as powerful as the target. If not, the source ordinal is certainly powerful enough to reify the value, so computation stops. Likewise, anytime we run out of ordinal power to actually compute with values, we reify them. That is, the consequence of having the *wrong* ordinal is just that we give up evaluating before we reach normal form. Bear in mind that some terms do not have a normal form.


## how to define the type theory

  1. Say how to check canonical constructions given a canonical type.
  2. Say how to check an eliminator given the type of its target and synthesize the type of the elimination given an abstract value of its target.
  3. Say how to compute the one-step reduct of such an elimination, given a canonical replacement for the abstract target.
  
Crucially, all three of the above must be achieved by inspecting only the canonical outer layers of chk terms. The remaining rules (a.k.a., the *sine qua non*) are fixed *in saecula saeculorum*.

```
           T ~> T'    T' :> t
pre      ----------------------
           T :> t

           e  <:  S    S = T
embed    ---------------------
           T  :>  (e)

           e  <:  S    S ~> S'
post     -----------------------
           e  <:  S' 

           * :> T    T :> t
radical  --------------------
           (t : T)  <:  T
           
           -| x : S
var      ------------
           x  <:  S
```

where `~>` is one-step reduction, `:>` is checking, `<:` is synthesis, and `-|` is context lookup. The only fixed reduction rule is

```
upsilon  --------------------
           ((t : T))  ~>  t
```

which discards potatoes not required to feed us for honest toil.

In more conventional logical terms, the beta rules show how to simplify a cut `(t : T) s` to a radical `(t' : T')` where `T'` corresponds to a structurally smaller ordinal than the ordinal for `T`, as do the types of any other radicals introduced within `t'` or `T'`. The upsilon rule marks the end of cut elimination by discarding the now inactive type.


## what (not) to prove about the type theory

  1. **beta-upsilon-reduction is confluent**: that's true because beta-contraction for `(t : T) s` inspects only the *canonical* outer layers of `t`, `T` and `s`, thus *cannot* discover and disrupt any other beta- or upsilon-redex therein. I prove this so you don't have to. Takahashi's method works unproblematically: I define *parallel reduction* `=>` which lets you fire none, some or all of the redexes you can see in a term; I define the *development* of a term, `develop(-)`, which fires all its redexes; I show that if `t => t'` then `t' => develop(t)` (because beta-contraction is stable with respect to both substitution and `=>`)
  2. **computation preserves type**: that's true if beta-contraction is well typed. I will get around to proving this so you don't have to. Specifically, I prove that
  
    * if `Ga |- T :> t` and `Ga =>* Ga'`, `T =>* T` and `t => t'`, then `Ga' |- T' :> t'`
    * if `Ga |- e <: S` and `Ga =>* Ga'` and `e => e'`, then there exists an `S'` such that `S =>* S' and `Ga' |- e' <: S'`
    
    The essence of the proof is that, er, your typing rules only inspect the *canonical* outer layers of introduction forms and eliminators and are thus stable with respect to both substitution and `=>`.
    
    
## what to prove about the evaluator

I write `u` and `v` for the semantics of chk-terms and `w` for the semantics of syn-terms. I write `U` `V` `W` for semantic types and `De` for contexts comprised thereof. The latter are computed from syntacic contexts by `cx-eval(-)`, invoking `ty-eval(De,S)` for types in subcontexts. We then have `chk-eval(De,V,t)` yielding `v` and `syn-eval(De,e)` yielding `(S,w)`. We can return to syntax with `ty-reify(V)`, `chk-reify(V,v)` and `syn-reify(W,w)`.

  3. `T ~>* ty-reify(ty-eval(De,T))`; `t ~>* chk-reify(V,chk-eval(De,V,t))`; `e ~> syn-reify(syn-eval(De,e))`
  4. if `Ga |- valid` and `Ga |- * :> T` and `Ga |- T :> t`, then, letting `De = cx-eval(Ga)` and `V = ty-eval(De,T)`, we get that both `ty-reify(V)` and `chk-reify(V,chk-eval(De,V,t))` are in beta-upsilon normal form; if `Ga |- valid` and `Ga |- e <: S`, then, letting `De = cx-eval(Ga)` and `(W,w) = syn-eval(De, e)`, we get that `S ~>* ty-reify(W)`, and that both `ty-reify(W)` and `syn-reify(W,w)` are in beta-upsilon normal form
  
That is, feed in any old spuds and you'll get honest computation: that gets you soundness of typechecking via the `pre` and `post` rules. Feed in the *correct* spuds for *well typed* terms and you'll make it to normal form. Normal forms are unique because of confluence. So typechecking is also complete.

The proofs of the above are, of course, achieved by defining suitable logical relations, recursive over the ordinal interpretation of types.
