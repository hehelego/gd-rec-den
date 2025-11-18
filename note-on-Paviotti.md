[Publications | Marco Paviotti](https://mpaviotti.github.io/pubs/)

- A Model of PCF in Guarded Type Theory  
  by _Marco Paviotti, Rasmus Ejlers Møgelberg, and Lars Birkedal_
  in _The 31st Conference on the Mathematical Foundations of Programming Semantics, MFPS, 2015, Elsevier._
- Denotational semantics of recursive types in synthetic guarded domain theory  
  by _Rasmus Ejlers Møgelberg, and Marco Paviotti_  
  in _Mathematical Structures in Computer Science, MSCS, 2019, Cambridge University Press._
- Denotational semantics in Synthetic Guarded Domain Theory  
  by _Marco Paviotti_
  as _Ph.D. Thesis, ISBN 978-87-7949-345-2, 2016, IT-Universitetet i KØbenhavn._

## chapter 1

Two approaches for giving semantics to programs

- Operational semantics is about *how* will the computation described by the program executed.
- Denotational semantics is about *what* is the program computing.

For example, consider the operational semantics of IMP/GCL. `(cmd, store) -> (skip, store')`

- small-step: how is each step executed
- big-step: how to chain intermediate states.

One possible denotational semantics of the programming language can be defined as `[[program]] : store -> P(store)`, where `[[program]] s = {t in state | (program, s) -> (skip, t)}`.
That is, a program dictates a function from initial state to all possible terminal states (can be empty).

Opertional semantics are intensional by their nature, while denotational semantics are extensional.

Lambda calculus:

```
data Term : Set where
    var : id -> Term
    abs : Term -> Term
    app : Term -> Term -> Term
data Type : Set where
    base : id -> Type
    fun : Type -> Type -> Type
```

The interpretation of types

```
[[base T]] some domain
[[fun A B]] mappings from [[A]] to [[B]]
```

Simply-typed ones: easy set-theoretic models (sound, complete, and adequate)

Untyped ones and PCF: no set-theoretic model is possible.
Intuition behind it is that the fixed point combinator is not expressible in set-theoretic language.

```
fix : forall a, (a -> a) -> a
[[fix]] : ([[a]] -> [[a]]) -> [[a]]
```

However, many endofunctions do not admit a fixed point.

---------------------

Denotational semantics:

- Domain theory based models (e.g. complete partial orders and continuous functions).
    + construct specific objects called domains in set theory
    + give semantics of programs in a way that ensures monotonicity and continuity
    + the existence and uniqueness of the (least) fixed point is guaranteed by Knaster-Tarski fixed point theorem.
    + **problem** hard to encode the notion of computation
    + **problem** hard to accommodate recursive types and general references.
    + **problem** burden of proving that every language construct is a Scott-continuous function.
- Axiomatic/Synthetic domain theory (SDT)  
    + types as domains, programs as continuous functions
    + essentially, bake semantical justifiable reasoning into programming in a type theory.
    + postulate/assume the operators and properties
    + **problem** introducing unrestricted fixed point combinator breaks consistency. For any type `X`, take the fixed point of the identity function `id : X -> X` will give an inhabitant of `X`, making the theory inconsistent.
    + **takeaway** we need a proper theoretical framework under which domain theory reasoning can be done consitently.
- Capretta's lifting monad or delayed monad: the GFP of `L A ~ A + L A` (directly a value, or steps to X1, where X is a value or steps to X2, where X2 is a value or steps to X3 ...)
    + previously, in type theory, we will ended up being able to decide termination. A function `A -> Maybe B` is always total in type theory.
    + using the lifting monad, we use an infinite element to represent a non-terminating computation.
    + **takeaway** it is hard to encode domain theory in type theory
    + **takeaway** domain theoretical constructions and reasoning principles are not the only feasible approach to denotational semantics.
- Step-indexing in metric spaces
    + break circularity by enforcing some well-founded structure
    + **problem** step-index makes the model intensional. Two computations ended up in the same result in different steps are considered different.
- Synthetic guarded domain theory (guarded dependent type theory)
- Synthetic guarded type theory (SGDT)

## guarded recursion

A applicative functor structure: `later : Type -> Type` where

- pure `next : A -> later A`
- later application `(*) : later (A -> B) -> later A -> later B`
- functor map `fmap f = (x : later x) => next f (*) x`
- identity `next id (*) v = v`
- composition `(next (.) (*) f (*) g) (*) a = f (*) (g (*) a)`
- homomorphism `next f (*) next x = next (f x)`
- interchange `u (*) next y = next (f => f y) (*) u`
- fixed point combinator: `gfix f = f (next (gfix f))` shape `gfix : (later A -> A) -> A`

It is generally not possible to inhabit `later (later A) -> later A`

Models of Guarded type theory (GTT) : **topos of trees**  

- The model of a closed type is `X(1) <- X(2) ... X(n) <- X(n+1) ...`
- `later X(1) = 1` the initial, which is `True`
- `later X(n+1) = X(n)`
- If `X(n+1)` is inhibited, then so is `X(n)`. Specifically, `x : X(n+1)` then `later x : later X(n+1) = X(n)`.
- Intuition: if a proposition cannot be falsified within `n` steps of computation, it is impossible to falsify it with fewer steps of computation.
- Important example: let `0 ~ False`, then `later^n False` is a proposition that appears to be true in the first `n` steps and only falsified after `n+1` steps.
- Important example: `bot = gfix next = next (next (gfix next)) = next (next (next (gfix next))) ...`. This is a computation that never gives a value. Under the CH correspondence, this is a proposition that cannot be falsified with arbitrary number steps of computation.

**Question** Is this kind of program guarded? Does it admit a guarded fixed point?

```
gfix (x => if true then x else x)
```

## clocked type theory

## side notes

### Tarski's fixed point theorem

Infimum (least upper bound) and supremum (greatest lower bound).

Consider a monotone `f`, i.e, `x <= y` implies `f x <= f y`.
Then `y = inf {x | f x <= x}` is the least fixed point of `f`.

To show `f y = y`, we show that `f y <= y` and `y <= f y`

For `f y <= y`. The statement can be easily justified.
For every `x` such that `f x <= x`, we have `f x <= x`.
Take the infimum on both side:

```
f y = inf {f x | f x <= x} <= inf {x | f x <= x} = y
```

For `y <= f y`, note that `{f x | f x <= x}` is a subset of `{x | f x <= x}` because `f x <= x` implies `f (f x) <= f x`.
Thus

```
inf {f x | x <= f x} <= inf {x | x <= f x}
```

The statement being proved is exactly `f y <= y`.

### where does the domain equation surfaces

For untyped lambda calculus.

Suppose that `D` is the domain of denotational interpretations.

- For lambda abstractions, the denotation has shape `D -> D`. Therefore, we need an operator `(D -> D) -> D` that injects a lambda abstraction into `D`.
- For every two terms `f` and `g`, the term `f g` is a valid term. The compositional denotation will be `[[f g]] = [[f]] [[g]]`. Therefore, we need to turn `[[f]] : D` into `D -> D`.
- This gives an isomorphism between `D` and `D -> D`.

### we are familiar with denotational semantics

> denotation: direct reference of a term or expression to the actual object (what is the thing, litereally)
> connotation: concerns associated ideas or attributes (what do you actually mean)

Denotational semantics is all about "what does this syntactic object mean".

The slogan: a denotational semantics for a programming language is comparable to a model theory of a logic.

For example, we usually think of propositional logic in their model.
We talks about satisfiability and equi-satisfiability but don't usually reosrt to provability and provably euivalence.

- Proof theory: operational semantics of the logic.
- Model theory: denotational semantics of the logic

```
p : Prop    q : Prop
--------------------
p /\ q : Prop
```

When defining the interpretation and model of propositional logic and predicate logic, we have already seen the denotational semantics approach.

- `[Prop] = {True, False}` for type propositional variable
- `[p1, p2, p3 ...] = [Prop] * [Prop] * [Prop] ... = {True, False}^n`
- `[p1, p2, p3 ... |- q : Prop] = {True, False}^n -> {True, False}`

For example, `/\ : {True, False} * {True, False} -> {True, False}` is given the following semantics

```
(T,T) -> T
(T,F) -> F
(F,T) -> F
(F,F) -> F
```

The semantics relate with syntactic by the following properties:

- soundness: `Gamma |- phi <-> psi` implies `[Gamma |- phi] = [Gamma |- psi]`.
- completeness: `[Gamma |- phi] = [Gamma |- psi]` implies `Gamma |- phi <-> psi`
- adequacy coincide with completeness

Another example. Context free grammar as a programming language.

- operational semantics: derivation trees
- denotational semantics: each rule `A -> XYZ` is interpreted as `[[A]] = {x . y . z | x in [[X]], y in [[Y]], z in [[Z]]}`

As a special case: regular expressions

- operational semantics:
    + `empty`: no rule for empty set
    + `epsilon`: `match epsilon []`
    + `{c}`: `forall c, match {c} [c]`
    + `r1 . r2`: `forall s1 s2, match r1 s1 -> match r2 s2 -> match (r1 . r2) (s1 ++ s2)`
    + `r1 | r2`: `forall s1, match r1 s1 -> match (r1 | r2) s1` and `forall s2, match r2 s2 -> match (r1 | r2) s2`
    + `r*`: `match (r*) []` and `forall s0 s, match r s0 -> match (r*) s -> match (r*) (s0 ++ s)`
- denotational semantics:
    + `[[empty]] = {}`
    + `[[epsilon]] = {[]}`
    + `[[{c}]] = {[c]}`
    + `[[r1 . r2]] = {s ++ t | s in [[r1]], t in [[r2]]}`
    + `[[r1 | r2]] = [[r1]] union [[r2]]`
    + `[[r *]] = least-fixed-point (S => {} union {s0 ++ s | s0 in [[r]], s in S})`

Denotational semantics is good for proving/refuting equality.

### why guarded recursion

> Finally, we construct a relation between syntax and semantics and show how to prove contextual equivalence between programs. It is difficult to reason about languages with recursion and computational effects such as probabilistic choice, because these features have no obvious counterpart in type theory. By using the later modality of guarded type theory and a special guarded fixpoint combinator, it is possible to define semantic domains that interpret these effects.
>
> Programming language semantics in modal type theories
> PhD Dissertation by Philipp Stassen

There is a fundamental tension between the semantics of object language and the metalanguage.

- the metalanguage is well-founded and terminating.
- the object language is often non-terminating and may allow non well-founded constructions.
- we cannot embed the object language programs into the metalanguage in a straight-forward approach.

### why relational

Logical predicate (unary) and logical relation (binary).

Contextual refinement.

- hard: need to quantify over all possible context that the open term can be embedded into.
- easier approach: Computational adequacy i.e. denotational equality implies contextual equality.

### cubical and HoTT

This series of work demonstrate why advanced type theories are needed for reasoning about advanced programming language features.

Specifically, we will see why _higher inductive types_ (HITs) are helpful in modeling PLs.

Finite/coutable powerset construction:

- empty subset `P A`
- singleton `(a : A) -> P A`
- union `P A -> P A -> P A`
- countable union `(Nat -> P A) -> P A`
- commutative `forall x y, x union y == y union x`
- associative `forall x y z, x union (y union z) == (x union y) union z`
- idempotent `forall x, x union x == x`
- neutral element `forall x, x union empty == x`
- inclusion `forall s n, (s n) union (sup s) == sup s`
- distribution `forall s x, (sup s) union x == sup (n => (s n) union x)`
- **TODO** propositional truncation

Allow baking the intended equalities into the data defintion.
Otherwise, you would need a canonical map for canonicalization and congruence.


Remark on HIT:

- point constructors: data/shape
- path constructors: equality/equivalence/quotient
- usefulness: univalence (extensional equality)
- previous quotient solutions:
    + Setoids: give equivalence relation and prove equivalence explictly.
    + Canonical representation
    + Add quotient types as axioms/postulates


### why GStream is definable in the first place.

Recall that we have a equation `GStream A = A * later (GStream A)`, which itself is a guarded recursion.
Suppose that it is defined by `gfix GA`, then `gfix GA = GA (next (gfix GA))` and `GA(X) = A * X`

What we actually do is:

- `later Type` is somehow also a `Type` and can be composed with other types using the familiar constructs
- `gfix : (later A -> A) -> A` instantiate with `gfix : (later Type -> Type) -> Type`
- for any functor `F : later Type -> Type`, `G = gfix F` satisfies the guarded recursion `G = G (next G)`
- the guarded recursive stream `F X = A * X` equation `S = A * (next S)`
- unfolding
    1. starting point `gfix (X => A * X)`
    2. unfold once `(X => A * X) (next (gfix (X => A * X))) = A * next (gfix (X => A * X))`
    3. unfold twice `A * next (A * next (gfix (X => A * X)))`
    3. unfold three times `A * next (A * next (A * next (gfix (X => A * X))))`

### example finite/countable branching process

```
-- deterministic
Process [iso] Action -> later Process
-- non-deterministic
Process [iso] Powerset (Action * later Process)
```

```
Stream A [iso] A * Stream A

F(X) = A * X

F(X) = (A -> X)

F A [iso] A -> F A
```

More examples: Coinductive formulation of reactive systems.

**TODO** bisimilarity proof

### decidable type checking and canonicity computation with guarded recursion unfold equality

In [Guarded Cubical Type Theory | Journal of Automated Reasoning](https://link.springer.com/article/10.1007/s10817-018-9471-7)
> we want decidable type checking, including decidable judgemental equality, and so we cannot admit such an unrestricted unfolding rule. Our solution is that fixed points should not be judgementally equal to their unfoldings, but merely path equal.

The will also need recover _canonicity_ i.e. things compute to introduction form.



### lifting monad

The lifting monad is the solution to

```
LA [isomorphic] A + later LA
```

Note that the solution is 

This means: for every `A`

- there is a map `injection-left  : A        -> LA` (eta $\eta$)
- there is a map `injection-right : later LA -> LA` (theta $\theta$)

The map `later LA -> LA` is particularly interest since it is suitable for feeding into the guarded fixed point combinator.

For every `B` such that a morphism `theta{B} : later B -> B` exists, we can elimination `LA` to `B`.
This can be defined as a functor `F` that transforms `f : A -> B` into `F f : LA -> B`, where

- for eta (now): `injection-left x` where `x : A`, get mapped to `f x`
- for theta (avilable later): `injection-right y` where `y : later LA`.
    + first compute `next (F f) <*> y : later B`
    + embed into `B` by `theta{B} : later B -> B`.

The morphism `theta{B} : later B -> B` gives a _later algebra_

Recall that `next : B -> later B` is always defined.
To add one step to a computation use `delta{B} x = theta (next x)` which has type `LB -> LB`

Understanding the `delta` $\delta$:

- start with a computation `x : LB`
- make it available in the next step: `next x : later LB`
- return a computation such that
    + inspect now: not done yet
    + inspect after one step: exactly `next x`

So delta is really adding one step to the computation

- if $x=\eta(v)$, the $\delta(x) = \theta(\mathrm{next}(\eta(v)))$
- if $x=\theta(c)$, the $\delta(x) = \theta(\mathrm{next}(\theta(c)))$

Intuition: come back to my when you have an extra step.

### examples of guarded recursive datatype

- Functor `G(X) = A * X`, let `T = gfix G`, then `T [iso] A * later T`
    + an infinite stream of `A`
    + constructor: `A * later T -> T`
    + destructor: `T -> A * later T`
    + recursion `T -> S [iso] A * later T -> S [iso] A * later S -> S` for every `S`
- Functor `G(X) = A + X`, let `T = gfix G`, then `T [iso] A + later T`
    + a computation that potentially halt with `A`
    + constructor 1: `A -> T` now
    + constructor 2: `later T -> T` next
    + recursion `T -> S [iso] A + later T -> S [iso] A + later S -> S` for every `S`
- Functor `G(X) = X`, let `T = gfix G`, then `T [iso] later T`
    + constructor `later T -> T`
    + recursion `T -> S [iso] later T -> S [iso] later S -> S` for every `S`.
- Functor `G(X) = later (A * X)`, let `T = gfix G`, then `T [iso] later (A * later T)`
- Functor `G(X) = later (A + X)`, let `T = gfix G`, then `T [iso] later (A + later T)`
- Functor `G(X) = A -> X`, let `T = gfix G`, then `T [iso] A -> later T`
    + constructor `(A -> later T) -> T`
    + destructor `T -> (A -> later T)`
    + recursion `T -> S [iso] (A -> later T) -> S [iso] (A -> later S) -> S` for every `S`.
- Functor `G(X) = list X`
- Functor `G(X) = gstream X`

## tracking the number of unfolds in operational semantics

Note, we are using call-by-names (CBN): How the application case is defined.

- Type `bigstep : Term * Nat * (Value -> Nat -> Type) -> Type`
- Meaning `M bigstep^k Q` means:
    + there exists a value `v`.
    + there exists a natural number `l` such that `l <= k`.
    + `M` evaluates to a value `v` in `l` steps.
    + `Q(v, k-l)` holds (`Q` examines the _remaining steps_ and test the _return value_)
- rules (inductive definition)
    + values (nat/bool literal) `v bigstep^k Q` is `Q(v,k)`
    + `pred M bigstep^k Q` is `M bigstep^k (x l => match (n:nat, x = n => Q(n-1,l)))`
    + `succ M bigstep^k Q` is `M bigstep^k (x l => match (n:nat, x = n => Q(n+1,l)))`
    + `M N bigstep^k Q` is `M bigstep^k (v l => match (v = lam x . L => L[N/x] bigstep^l Q))`
    + `is-zero L M N bigstep^k Q` is `L bigstep^k (v l => match (v = 0 => M bigstep^l Q) (n: nat, v = S n => N bigstep^l Q))`
    + `Y M bigstep^k Q` is `exists l, k = S l /\ later (M (Y M) bigstep^l Q)`
- convenient notation
    + `M bistep^k Q` means `M bigstep^k (v l => l = 0 /\ Q(v))` if `Q` does not care about the step-counter.
    + `M bigstep^k u` means `M bigstep^k (v l => l = 0 /\ u = v)` if we only want to talk about the value and the step.
    + `M bigstep u` means `exists k, M bigstep^k (v l => l = 0 /\ u = v)`

Similarly, we should have a small-step operational semantics that tracks the number of unfoldings.
Type `step : Term -> {0,1} -> Term`. Notation `M ->0 N` or `M ->1 N`.

A transitive closure that synchronize unfold in the object language (the `nat` parameter) and unfold in the metatheory (clock ticks) using the later modality.

- Type: `multistep : Term -> Nat -> (Term -> Type)`. Notation `M =>k Q`.
- no unfold: `M =>0 Q` is `exists N, M ->0* N /\ Q(N)`
- at least one unfold: `M =>(k+1) Q` is `exists M1 M2, M ->0* M1 /\ M1 ->1 M2 /\ later (M2 =>k Q)`
- convient notation `M =>k u` is `M =>k (N => v = N)`

## denotational semantics of PCF in guarded type theory

The problem of non-termination: what should be the denotation of a base type (`nat`, `bool`, or `unit`).

Some attempts:

- `[[nat]] = N` i.e. map the type `[[nat]]` to natural numbers in the semantics domain. Problem: in a constructive type theory, for such definition to be valid, we have to compute the canonical form of any closed term of type `nat`.
- `[[nat]] = exists feul, is_some (compute fuel e)` same problem, to inhabit such type is to find the number of steps for a program to halt
- `[[nat]] = N + step1 N + step2 N ...` or `[[nat]] = N + later [[nat]]` a lifting monad. Use the lifting monad to model potentially non-terminating program. The definition is coinductive and we lifted the requirement of finding the normal form for any program of type `nat`.

Back to the denotational semantics framework

- interpreation of types
    + `[[nat]] = L N` where `L` is the lifting monad (the free later algebra) and `N` is the natural number in the metalanguage. Intuition: a computation that may halt with a natural number
    + `[[unit]] = L Unit`
    + `[[bool]] = L Bool`
    + `[[A -> B]] = [[A]] -> [[B]]`
- denotational of every type is a later algebra (by induction on types)
    + Base type `[[base A]] = L A [iso] A + later (L A)`. The map `theta : later [[base A]] -> [[base A]]` is just injection left.
    + Function type `[[A -> B]] = [[A]] -> [[B]]`. Suppose that `theta{A} : later [[A]] -> [[A]]` and `theta{B} : later [[B]] -> [[B]]`.  
      Construct `theta{A->B} : (f : later [[A -> B]]) -> (x : [[A]]) -> theta{B} (f <*> next x)`
- interpretation of type judgement `Gamma |- M : tau` where `Gamma = x1:sigma1, x2:sigma2 ...`
    + a function from the interpretation of context to the interpretation of the assigned type of a term
    + domain: `[[Gamma]] = [[sigma1]] * [[sigma2]] * [[sigma3]] ...`
    + codomain: `[[tau]]`
- interpretation rules
    + a variable is a projection: `[[x1:S1, x2:S2 ... |- xi : Si]] = env => proj{i} env`
    + a constant literal is a constant function `[[E |- const n : nat]] = env => injection-left n`
    + a lambda abstraction is a currying `[[E |- lambda x:S . M : S -> T]] = env => (x => [[E , x:S |- M : T]] (env,x))`
    + an application is an application (S combinator) `[[E |- M N : T]] = env => [[E |- M : S -> T]] env ([[E |- N : S]] env)`
    + operations: summation/difference/product/quotient of two `nat`s, lift the operator `nat -> nat` into `L nat -> L nat`.
    + a recursion is a guarded recursion: `[[E |- Y M : S]] = env => gfix (lx => theta{S} (next ([[E |- M : S -> S]] env) <*> lx))`
        1. to construct `[[S]]` from `env : [[E]]`
        2. invert the typing judgement to get `[[E |- M : S -> S]]` which gives `[[E]] -> [[S]] -> [[S]]`
        3. use Loeb's induction `(later [[S]] -> [[S]]) -> [[S]]` to introduce `lx : later [[S]]`
        4. lift `next ([[E |- M : S -> S]] env) : later ([[S]] -> [[S]])` and apply to `lx` get `later [[S]]`
        5. use `theta{S}` constructor to turn `later [[S]]` into `[[S]]`.
        6. Note that `later [[S]] -> [[S]]` can be directly instantiated by `theta{S}`.
           This gives a term `gfix (_ => theta{S})` this is the bottom element of `L[[S]]`. Note that `bot [iso] theta (next bot)`
           But doing so makes `[[E |- Y M : S]]` totally unrelated with `M`.
- The denotation of a (syntactic) fixed point is indeed a (semantic) fixed point. That is, our definition validates the fixed point unfolding equation.

Let's zoon in on the `Y` case and prove (MFPS15 lemma 4.1):
If `E |- M : S -> S` then `[[E |- Y M : S]] = delta{S} . [[E |- M (Y M)]] = theta{S} . next . [[E |- M (Y M) : S]]` where `(.)` is the function composition.

```
LHS env
= gfix (lx => theta $ next $ [[E |- M]] env) <*> lx
= theta $ next ([[E |- M]] env) <*> (next (LHS env))
= theta $ next $ [[E |- M]] env (LHS env)

RHS enV
= theta $ next $ [[E |- M]] env $ [[E |- Y M]] env
= theta $ next $ [[E |- M]] env $ LHS env
= theta $ next $ [[E |- M]] env (LHS env)
```


## the framework of a logical relation proof

- goal: to relate a syntactic property with a semantic property
- approach: come up with an inductive relation that can imply the "connection"

Actual work:

1. preserved by substitution
2. subject reduction:
3. subject expansion:
4. compatible with typing rules for constructs
5. all well-typed judgements are in the relation and thus syntax and semantics are connected.

## delayed substitution

To define abstraction and instantiation, we need a well-defined substitution.

- dependent function `Gamma |- f : later (Pi (x:A). B)`
- argument `Gamma |- t : later A`
- application is substitution `Gamma |- f <*> t : later [x <- t] . B`
- a new definitional equality `later [x <- next u] B` is `later B[u/x]`
- if `t` eventually reduces to `next u`, then we have `Gamma |- f <*> t : later B[u/x]`

We use the greek letter $\xi$ for delayed substitution.

Some useful laws:

- `next xi . t = next xi . u` is `later xi . (t = u)`
- `El(universe-later (next xi. A))` is `later xi. El(A)`

For more information, look into paper:

- Guarded dependent type theory with coinductive types.
- Aleš Bizjak, Hans Bugge Grathwohl, Ranald Clouston, Rasmus Ejlers Møgelberg, and Lars Birkedal.
- In Foundations of Software Science and Computation Structures. 19th International Conference, FoSSaCS 2016.

## the logical relation proof of denotational adequacy

Before we start, delayed substitution allow lifting an `A * B` relation to a `later A * later B` relation.

Suppose that `R : A -> B -> Type`, then `later R : later A -> later B -> Type`.
The delayed relation `t (later R) u` is defined as a delayed substitution `later [x <- t, y <- u] . (x R y)`.
Intuitively, when `next t` and `next u` are delayed-related now if `t` and `u` are related in the next step.

A typed-index logical relation: `R : (t : PCF-type) -> [[t]] -> PCF-term -> universe`.

- `eta(v) R[nat] M` is defined as `M bigstep^0 v`.  
  A `nat` term `M` is related to a now available value `v` if `M` reduces to `v` without unfolding `Y`.
- `theta(r) R[nat] M` is defined as `exists M' M'', M ->0* M' /\ M' ->1 M'' /\ r (later R[nat]) next M''`  
  A `nat` term `M` is related to a later available computation `r` if `M` reduces to `M''` with one unfold and `next M''` is delayed related with `r`
- `f R[T -> S] M` is defined as `forall (alpha : [[T]]) (N : Term), alpha R[S] N [implies] f(alpha) R[S] (M N)`

The standard logical relation development

### lemma 2.25 the logical relation is carried on by application

Premises

- `f (later R[T -> S]) next M`
- `r (later R[T]) next N`

Conclusion

- `f <*> r (later R[S]) next (M N)`

Proof sketch: If `f ~> next f0` and `r ~> next r0`, then we have

- `later (f0 R[T->S] M)`
- `later (r0 R[T] N)`
- note that `R[T->S]` is a function
- applying `<*>` to combine things under `later`
- application results `later (f0 r0 R[S] M N)`
- definitionally equal to `next (f0 r0) (later R[S]) next (M N)`
- definitionally equal to `f <*> r (later R[S]) next (M N)`

### lemma 2.26 a subject expansion lemma

Premises

- `alpha : later [[S]]`
- `alpha (later R[S]) next N`
- `M ->1 N` (`M` reduces to `N` by one unfold somewhere)

Conclusion

- `theta[S] alpha R[S] M`

Proof sketch: (TODO)

<!-- TODO: proof sktech: induction on `s` -->

### lemma 2.27 subject reduction and subject expansion of no-unfolding steps

Premise

- `M ->0 N` reduction without unfolding `Y`

Conclusion

- `alpha R[S] M` is logically equivalent to `alpha R[S] N`

<!-- TODO: proof sktech: induction on `s` -->

### lemma 2.28 fundamental lemma, substitution lemma

Premise

- `Gamma |- u : T` where `Gamma = x1:T1, x2:T2, ...`
- for each `x_i : T_i`, assign `t_i` and `alpha_i` such that `alpha_i R[T_i] t_i`

Conclusion

- `[[Gamma |- u : T]](alpha_1, alpha_2, ...) R[T] u [t1/x1, t2/x2, ...]`

Intuitive understanding: given a some related pairs of semantic objects and syntactic terms,
if we use them to instantiate an open term,
we will ended up with a pair of related semantic object and syntactic term.

<!-- TODO: proof sktech: typing judgement `Gamma |- u : T` -->

### theorem 2.29 Computational Adequacy

For a closed PCF term of type `nat` `M : nat`,
and a semantic domain natural number `v : [[nat]]`,
the following two statements are logically equivalent.

- `M bigstep^k v` that is, `M` can reduce to value `v` during which exactly `k` unfolds occurred.
- `[[|- M : nat]](*) = delta[nat]^k v` that is the denotation of `M` is `v` but `k` time step is added.

Proof:

- reduction to denotation: the soudness proof
- denotation to reduction:
    + the fundamental lemma
    + with the empty closing-substitution (instantiated by empty semantic vector).
    + `[[|- M : nat]](*) R[nat] M`
    + `delta[nat]^k v R[nat] M`
    + induction on `k`
    + `k=0`, now: `eta(v) R[nat] M` is `M bigstep^0 v` by definition
    + `k=1+k'`, later `theta (next (delta[nat]^k' v)) R[nat] M` by definition this is
    + `Sigma (M' M'' : Term), M ->0* M' /\ M' ->1 M'' /\ (next (delta[nat]^k' v)) (later R[nat]) next M''`
    + strip off `next` with delayed substitution
    + `Sigma (M' M'' : Term), M ->0* M' /\ M' ->1 M'' /\ later ((delta[nat]^k' v) R[nat] M'')`
    + combine with IH, which states `delta[nat]^k' v R[nat] M''` implies `M'' bigstep^k' v`, to complete the proof

## closing remark

the notion of abstract time in guarded type theory:

- Is different from the concept of time in temporal logic.
  In temporal logic, time is the property of the object or the structure of the object. When we say `next phi`, we don't prove `phi` in the next time step, we prove "for the current state, phi will hold after a step of evolution".
  We prove things by talking about "after one step, the system will be in state X Y Z, and thus ..."
- In guarded type theory, time is the property of the metalanguage i.e. the logic itself.
  When we say `later P`, we have access to `P` when we have a time step recourse.
- can be used to synchronize reasoning and computation of recursion.

remarks

- more things in the metatheory
- less trash in the formalization
- the efforts we paid in developing better type theories will be paid out
