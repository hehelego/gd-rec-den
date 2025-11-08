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

## part 1

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

Denotational semantics is all about "what does this syntactic object mean".

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


### lifting monad

The lifting monad is the solution to

```
LA [isomorphic] A + later LA
```

Note that the solution is 

This means: for every `A`

- there is a map `injection-left  : A        -> LA`
- there is a map `injection-right : later LA -> LA`

The map `later LA -> LA` is particularly interest since it is suitable for feeding into the guarded fixed point combinator.

For every `B` such that a morphism `theta{B} : later B -> B` exists, we elimination `LA` to `B`.
This can be defined as a functor `F` that transforms `f : A -> B` into `F f : LA -> B`, where

- `injection-left x` where `x : A`, get mapped to `f x`
- `injection-right y` where `y : later LA`.
    + first compute `next (F f) <*> y`, which is in `later B`
    + embed into `B` by `theta{B} : later B -> B`.

The morphism `theta{B} : later B -> B` gives a _later algebra_

Recall that `next : B -> later B` is always defined.
To add one step to a computation use `delta{B} x = theta (next x)` which has type `LB -> LB`


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

### decidability problem with guarded recursion unfold equality

In [Guarded Cubical Type Theory | Journal of Automated Reasoning](https://link.springer.com/article/10.1007/s10817-018-9471-7)
> we want decidable type checking, including decidable judgemental equality, and so we cannot admit such an unrestricted unfolding rule. Our solution is that fixed points should not be judgementally equal to their unfoldings, but merely path equal.

The will also need recover _canonicity_ i.e. things compute to introduction form.

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
    + `M bistep^k Q` means `M bigstep^k (v l => l = 0 /\ Q(v))`
    + `M bigstep^k u` means `M bigstep^k (v l => l = 0 /\ u = v)`
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
    + a variable is a projection: `[[x1:s1, x2:s2 ... |- xi]] = env => proj{i} env`
    + a constant literal is a constant function `[[E |- const n : nat]] = env => injection-left n`
    + a lambda abstraction is a currying `[[E |- lam x:s . M : s -> t]] = env => (x => [[E , x:s |- M : t]] (env,x))`
    + an application is an application (S combinator) `[[E |- M N : t]] = env => [[E |- M : s -> t]] env ([[E |- N : s]] env)`
    + operations: summation/difference/product/quotient of two `nat`s, lift the operator `nat -> nat` into `L nat -> L nat`.
    + a recursion is a guarded recursion: `[[E |- Y M : s]] = env => gfix (lx => theta{s} (next ([[E |- Y : s-> s]] env) <*> x))`
        1. to construct `[[s]]` from `[[E]]`
        2. invert the typing judgement to get `[[E |- M : s -> s]]` which gives `[[E]] -> [[s]] -> [[s]]` and thus `[[s]] -> [[s]]`
        3. use Loeb's induction `(later [[s]] -> [[s]]) -> [[s]]` to introduce `later [[s]]`
        4. lift and apply `[[E |- M : s -> s]] : [[s]] -> [[s]]` to get `later [[s]]`
        5. use `theta{s}` to turn `later [[s]]` into `[[s]]`.
        6. note that `later [[s]] -> [[s]]` can be directly instantiated by `theta{s}`, but doing so makes `[[E |- Y M : s]]` totally unrelated with `M`.
- The denotation of a (syntactic) fixed point is indeed a (semantic) fixed point. That is, our definition validates the fixed point unfolding equation.


## the framework of a logical relation proof

- goal: to relate a syntactic property with a semantic property
- approach: come up with an inductive relation that can imply the "connection"

Actual work:

1. preserved by substitution
2. subject reduction:
3. subject expansion:
4. compatible with typing rules for constructs
5. all well-typed judgements are in the relation and thus syntax and semantics are connected.
