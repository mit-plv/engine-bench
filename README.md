# Systematic evaluation of proof engine performance
[![CI (Coq)](https://github.com/mit-plv/engine-bench/workflows/CI%20(Coq)/badge.svg?branch=master)](https://github.com/mit-plv/engine-bench/actions?query=workflow%3A%22CI+%28Coq%29%22+branch%3Amaster) [![CI (LaTeX)](https://github.com/mit-plv/engine-bench/workflows/CI%20(LaTeX)/badge.svg?branch=master)](https://github.com/mit-plv/engine-bench/actions?query=workflow%3A%22CI+%28LaTeX%29%22+branch%3Amaster)

The *proof engine* is the component of a proof assistant that maintains the state of a *partial* proof or construction and provides an interface with fine-grained but individually meaningful (and checkable!) steps.
For orientation: the state of the proof engine usually features a list of remaining goals and a proof step might consist of specializing a function to a variable (beta reduction) or creating one new expression node.
Our goal is threefold:
First, identify a minimal interface in terms of which higher-level operations (for example, rewriting all occurrences of a pattern using an equality lemma) can be expressed.
Then benchmark the implementation of these operations in existing proof engines to highlight asymptotic performance trends.
Finally, we will try to specify the amortized complexity each proof engine operation would need to have to implement representative high-level tactics without asymptotic slowdown.

Currently, this repository contains contains benchmarks and quick demonstrations for Coq 8.11.

# Interface requirements

Our choice of primitive operations to be benchmarked as the canonical interface of a proof assistant is based on several criteria.
We require each operation to be individually checkable and that after an erroneous step the proof engine can immediately return an error that can be explained from first principles, as opposed to failing long arbitrarily thereafter with a generic error message like "bad proof" or "ill-typed term".
For this reason, we consider expressions as a part of some particular context in the proof engine rather than as "free-floating" objects which the user can attempt to use in any context.
We treat expression construction as a part of the proof engine API, even if internally the proof engine is further decomposed into an expression language implementation and proof state code that uses it.
Based on our experience that (performance-) engineering on top of heuristic procedures is a bad time, we further require the proof engine operations to be deterministic and have fully specified behavior and running time.
In particular, conversion- or type-checking with dependent types is not a primitive operation, each rule individually is.
The same desire for predictability leads us to specify primitive operations with explicit sharing in their input and output and measure their performance in the presence of explicit `let` binders.

We treat tactic language features such as exceptions, backtracking, multiple resumption, non-proof state, and debug prints as orthogonal to the core challenge of representation and manipulation of the proof state (it seems reasonable to expect that non-trivial interactions and synergies do exist, but they are outside the scope of this work).
Still, we require that the proof engine supports operations on any open goal so that multi-goal support can be implemented in the tactic language.
We similarly do not investigate features whose sole purpose is to present the proof state to the user, for example generating human-readable names for binders and converting the internal representation to nicely formatted strings.

## Operations

- creating a proof goal given context and statement / creating a new expression hole given context and type
- creating an application node given function and arguments (using only syntactic conversion for type checking)
- creating a let binder given bound expression (new hole/subproof for continuation)
- creating a lambda/quantifier given bound type (new hole/subproof for continuation)
- creating a type annotation given term (using only syntactic conversion for type checking)
- one-step reductions: lambda application, constructor elimination, definition unfolding 
- using a expression/subproof from a smaller context to fill a hole in a larger context
- replacing an expression with a reference to an alpha-equivalent variant
- extracting subterms of a given term<a name="text_*">[\*](#*)</a>
- optional: reducing an expression to normal form (with performance expectations with reference to a non-proof-assistant interpreter)

As the job of the proof engine is to maintain *partial* proofs, we consider all of these operations with terms and contexts which may contain holes and unfinished subproofs.
We do not specify a particular representation of partial proofs and constructions, anything that can be worked with using the operations described above is fair game; when matching existing operations to our specifications we will interpret the operation descriptions more loosely than the overarching requirements discussed earlier.
Ideally, the amortized overhead due to operating in a rich context would be asymptotically polylogarithmic (or at least otherwise sublinear) and fast in practice. Needless to say, we are not aware of any proof engine that comes close to achieving this.

<a name="*">[\*](#text_*)</a> This operation may seem obvious, and, indeed, we expect it to be trivial in any proof engine in which it is valid.
However, in extensional type theories, just because `λ _ : False, f` is well-typed doesn't mean that `f` is well-typed in the empty context, even if it doesn't mention the binder.
Furthermore, it's possible for `f x` to be well-typed without `f` and/or `x` being individually well-typed in some proof assistants such as Nuprl.
(For example, `(λ _, true) (0 = ℕ)` may be well-typed because it reduces to `true`, even though `0 = ℕ` is not well-typed when `=` is heterogenous.
TODO: Is this example actually correct?)

# Performance Graphs

A compilation of autogenerated performance graphs for Coq is available at [here](https://mit-plv.github.io/engine-bench/coq.pdf).

Adding a new let binder underneath n lets
- Coq: See [`coq/PerformanceDemos/do_n_let_binder.v`](./coq/PerformanceDemos/do_n_let_binder.v), [`coq/PerformanceExperiments/intros_n_let.v`](./coq/PerformanceExperiments/intros_n_let.v), [`coq/PerformanceExperiments/do_n_pose.v`](./coq/PerformanceExperiments/do_n_pose.v), [`coq/PerformanceExperiments/let_n_uconstr.v`](./coq/PerformanceExperiments/let_n_uconstr.v), and [`coq/PerformanceExperiments/let_n_ltac2.v`](./coq/PerformanceExperiments/let_n_ltac2.v)

  intros_n_let | do_n_pose | let_n_uconstr | let_n_ltac2
  --|--|--|--
  <img src="https://mit-plv.github.io/engine-bench/coq/intros-n-let.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/do-n-pose.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/let-n-uconstr.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/let-n-ltac2.svg" height=100px />


Adding a new binder underneath n binders
- Coq: See [`coq/PerformanceDemos/do_n_binder.v`](./coq/PerformanceDemos/do_n_binder.v), [`coq/PerformanceExperiments/intros_n_fun.v`](./coq/PerformanceExperiments/intros_n_fun.v), [`coq/PerformanceExperiments/fun_n_uconstr.v`](./coq/PerformanceExperiments/fun_n_uconstr.v), and [`coq/PerformanceExperiments/fun_n_ltac2.v`](./coq/PerformanceExperiments/fun_n_ltac2.v)

  intros_n_fun | fun_n_uconstr | fun_n_ltac2
  --|--|--
  <img src="https://mit-plv.github.io/engine-bench/coq/intros-n-fun.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/fun-n-uconstr.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/fun-n-ltac2.svg" height=100px />

- Needed for: good performance of rewrite/rewrite_strat under binders
  + Coq: See [`coq/PerformanceDemos/rewrite_strat_under_binders.v`](./coq/PerformanceDemos/rewrite_strat_under_binders.v), [`coq/PerformanceExperiments/repeat_setoid_rewrite_under_binders.v`](./coq/PerformanceExperiments/repeat_setoid_rewrite_under_binders.v), and [`coq/PerformanceExperiments/rewrite_strat_under_binders.v`](./coq/PerformanceExperiments/rewrite_strat_under_binders.v)

    repeat_setoid_rewrite_under_binders | rewrite_strat_under_binders
    --|--
    <img src="https://mit-plv.github.io/engine-bench/coq/repeat-setoid-rewrite-under-binders.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/rewrite-strat-under-binders.svg" height=100px />

- Needed for: good performance of proving large conjunctions (structural types could be an alternative)
  + Coq: See [`coq/PerformanceDemos/repeated_conj.v`](./coq/PerformanceDemos/repeated_conj.v), [`coq/PerformanceExperiments/conj_True_repeat_constructor.v`](./coq/PerformanceExperiments/conj_True_repeat_constructor.v), and [`coq/PerformanceExperiments/conj_True_fast_conj.v`](./coq/PerformanceExperiments/conj_True_fast_conj.v)

    conj_True_repeat_constructor | conj_True_fast_conj
    --|--
    <img src="https://mit-plv.github.io/engine-bench/coq/conj-True-repeat-constructor.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/conj-True-fast-conj.svg" height=100px />

- Needed for: good performance of turning `f (f (... (f x))) = g (g (... (g x)))` given `f x = g x` (or `x = y -> f x = g y`) w/ `rewrite_strat`
  + Coq: See [`coq/PerformanceDemos/rewrite_strat_repeated_app.v`](./coq/PerformanceDemos/rewrite_strat_repeated_app.v), [`coq/PerformanceExperiments/rewrite_repeated_app_autorewrite.v`](./coq/PerformanceExperiments/rewrite_repeated_app_autorewrite.v), [`coq/PerformanceExperiments/rewrite_repeated_app_ssrrewrite.v`](./coq/PerformanceExperiments/rewrite_repeated_app_ssrrewrite.v), [`coq/PerformanceExperiments/rewrite_repeated_app_rewrite_strat.v`](./coq/PerformanceExperiments/rewrite_repeated_app_rewrite_strat.v), and [`coq/PerformanceExperiments/rewrite_repeated_app_fast_rewrite.v`](./coq/PerformanceExperiments/rewrite_repeated_app_fast_rewrite.v)

    rewrite_repeated_app_autorewrite | rewrite_repeated_app_ssrrewrite | rewrite_repeated_app_rewrite_strat | rewrite_repeated_app_fast_rewrite
    --|--|--|--
    <img src="https://mit-plv.github.io/engine-bench/coq/rewrite-repeated-app-autorewrite.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/rewrite-repeated-app-ssrrewrite.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/rewrite-repeated-app-rewrite-strat.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/rewrite-repeated-app-fast-rewrite.svg" height=100px />

Typechecking an application of a function to n arguments (very convenient if this is Õ(n))
- Can be constructed if you can prove conjunction/pairing without quadratic overhead
- Coq: See [`coq/PerformanceDemos/app_n.v`](./coq/PerformanceDemos/app_n.v), [`coq/PerformanceExperiments/app_n_uconstr.v`](./coq/PerformanceExperiments/app_n_uconstr.v), and [`coq/PerformanceExperiments/app_n_ltac2.v`](./coq/PerformanceExperiments/app_n_ltac2.v)

  app_n_uconstr | app_n_ltac2
  --|--
  <img src="https://mit-plv.github.io/engine-bench/coq/app-n-uconstr.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/app-n-ltac2.svg" height=100px />

Fast alpha-equivalence check
- Coq: See [`coq/PerformanceDemos/constr_eq.v`](./coq/PerformanceDemos/constr_eq.v) and [`coq/PerformanceExperiments/constr_eq_alpha.v`](./coq/PerformanceExperiments/constr_eq_alpha.v)

  constr_eq_alpha |
  --|
  <img src="https://mit-plv.github.io/engine-bench/coq/constr-eq-alpha.svg" height=100px /> |

 One-step reductions:
 - Coq: See [`coq/PerformanceDemos/one_step_reduction.v`](./coq/PerformanceDemos/one_step_reduction.v), [`coq/PerformanceExperiments/one_step_reduction.v`](./coq/PerformanceExperiments/one_step_reduction.v), [`coq/PerformanceExperiments/one_step_reduction_with_abstract.v`](./coq/PerformanceExperiments/one_step_reduction_with_abstract.v), [`coq/PerformanceExperiments/iota_reduction_fact8.v`](./coq/PerformanceExperiments/iota_reduction_fact8.v), [`coq/PerformanceExperiments/iota_reduction_fact9.v`](./coq/PerformanceExperiments/iota_reduction_fact9.v), [`coq/PerformanceExperiments/iota_reduction_with_abstract_fact8.v`](./coq/PerformanceExperiments/iota_reduction_with_abstract_fact8.v), and [`coq/PerformanceExperiments/iota_reduction_with_abstract_fact9.v`](./coq/PerformanceExperiments/iota_reduction_with_abstract_fact9.v)

  one_step_reduction | one_step_reduction_with_abstract | iota_reduction_fact8 | iota_reduction_fact9 | iota_reduction_with_abstract_fact8 | iota_reduction_with_abstract_fact9
  --|--|--|--|--|--
  <img src="https://mit-plv.github.io/engine-bench/coq/one-step-reduction.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/one-step-reduction-with-abstract.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/iota-reduction-fact8.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/iota-reduction-fact9.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/iota-reduction-with-abstract-fact8.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/iota-reduction-with-abstract-fact9.svg" height=100px />

Inserting a cast node should not have overhead over type checking

Evar creation should be Õ(1)
- Coq: See [`coq/PerformanceExperiments/do_n_open_constr_True.v`](./coq/PerformanceExperiments/do_n_open_constr_True.v)

  do_n_open_constr_True |
  --|
  <img src="https://mit-plv.github.io/engine-bench/coq/do-n-open-constr-True.svg" height=100px /> |

## Evar context management in Coq

Sample unification problem (context-changing):
- `eq_refl : (fun y => y) = ((fun e y => e y) ?e)`
- `eq_refl : (fun y => y) = (fun y => ?e@{no y} y)`
- User: inside ?e, do intro, i.e., `?e@{no y} := fun z => ?e2@{z}`
- `eq_refl : (fun y => y) = (fun y => (fun z => ?e2@{z, no y}) y)`

Lifting identity evar substitution should really be Õ(1)
- Coq: See [`coq/PerformanceDemos/lift_identity_evar_subst.v`](./coq/PerformanceDemos/lift_identity_evar_subst.v), [`coq/PerformanceExperiments/lift_identity_evar_subst_nevars.v`](./coq/PerformanceExperiments/lift_identity_evar_subst_nevars.v), [`coq/PerformanceExperiments/lift_identity_evar_subst_ctx.v`](./coq/PerformanceExperiments/lift_identity_evar_subst_ctx.v), and [`coq/PerformanceExperiments/lift_identity_evar_subst_binders.v`](./coq/PerformanceExperiments/lift_identity_evar_subst_binders.v)

  lift_identity_evar_subst_nevars | lift_identity_evar_subst_ctx | lift_identity_evar_subst_binders
  --|--|--
  <img src="https://mit-plv.github.io/engine-bench/coq/lift-identity-evar-subst-nevars.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/lift-identity-evar-subst-ctx.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/lift-identity-evar-subst-binders.svg" height=100px />


Composing identity evar substitution should also be Õ(1)

Lifting non-identity evar substitutions:
- Coq: See [`coq/PerformanceDemos/lift_non_identity_evar_subst.v`](./coq/PerformanceDemos/lift_non_identity_evar_subst.v), [`coq/PerformanceExperiments/lift_non_identity_evar_subst_nevars.v`](./coq/PerformanceExperiments/lift_non_identity_evar_subst_nevars.v), [`coq/PerformanceExperiments/lift_non_identity_evar_subst_ctx.v`](./coq/PerformanceExperiments/lift_non_identity_evar_subst_ctx.v), and [`coq/PerformanceExperiments/lift_non_identity_evar_subst_binders.v`](./coq/PerformanceExperiments/lift_non_identity_evar_subst_binders.v)

  lift_non_identity_evar_subst_nevars | lift_non_identity_evar_subst_ctx | lift_non_identity_evar_subst_binders
  --|--|--
  <img src="https://mit-plv.github.io/engine-bench/coq/lift-non-identity-evar-subst-nevars.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/lift-non-identity-evar-subst-ctx.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/lift-non-identity-evar-subst-binders.svg" height=100px />


## Optional operations:

Full reduction on a function of complexity O(f) should be Õ(f + input term size + output term size)
- See [`coq/PerformanceDemos/quadratic_reduction.v`](./coq/PerformanceDemos/quadratic_reduction.v), [`coq/PerformanceExperiments/quadratic_cbv_lazy_PHOAS.v`](./coq/PerformanceExperiments/quadratic_cbv_lazy_PHOAS.v), [`coq/PerformanceExperiments/quadratic_native_PHOAS.v`](./coq/PerformanceExperiments/quadratic_native_PHOAS.v), and [`coq/PerformanceExperiments/quadratic_vm_PHOAS.v`](./coq/PerformanceExperiments/quadratic_vm_PHOAS.v)

  quadratic_cbv_lazy_PHOAS | quadratic_native_PHOAS | quadratic_vm_PHOAS
  --|--|--
  <img src="https://mit-plv.github.io/engine-bench/coq/quadratic-cbv-lazy-PHOAS.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/quadratic-native-PHOAS.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/quadratic-vm-PHOAS.svg" height=100px />


Performance Criterion: pattern on k variables should be Õ(term size + k + cost of retypechecking the output term (only if input term is not simply typed))
- Coq: See [`coq/PerformanceDemos/pattern.v`](./coq/PerformanceDemos/pattern.v) and [`coq/PerformanceExperiments/pattern.v`](./coq/PerformanceExperiments/pattern.v)

  pattern |
  --|
  <img src="https://mit-plv.github.io/engine-bench/coq/pattern.svg" height=100px /> |


Performance Criterion: pattern should be Õ(term size * size of thing being patterned + cost of retypechecking the output term (only if input term is not simply typed))
- Note: Andres is not confident in this
- Coq: See [`coq/PerformanceDemos/pattern.v`](./coq/PerformanceDemos/pattern.v) and [`coq/PerformanceExperiments/pattern.v`](./coq/PerformanceExperiments/pattern.v)

  pattern |
  --|
  <img src="https://mit-plv.github.io/engine-bench/coq/pattern.svg" height=100px /> |


# Tactics to consider implementing on this API

- `pattern`
    + pattern-without-conversion should be fast
    + pattern-with-conversion should be as slow as needed (because of conversion during typechecking) but not gratuitously slow
    + neither needs to be a primitive operation.
- `destruct` / `induction`
- `assert`
- `rewrite`
- `setoid_rewrite` (rewrite with binders)
- `autorewrite`
- `rewrite_strat` / `autosetoid_rewrite`
- `intro` / `intros` / `revert` / `generalize` / `set` / `clear` / `clearbody`
- `refine` / `exact` / `assumption`
- `change` / `refine` + unification
- `unify`, roughly how an unuification algorithm can do its job by calling intantiate / refine-in-evar / reduction-step-with/in-evar
- `constr:(⋯)` / `open_constr:(⋯)`
- `match goal` / `match` constr (readback problem)
- moving constrs / out-of-band-things across contexts?
- multi-step-reduction / `cbv` / `lazy` / `vm_compute` / ⋯ (probably not much detail, either use the steps above or use a skyhook vm)
- `pose` / `pose proof`
- `congruence` or some arithmetic tactic?
- non-reflective `ring` tactic? try to estaiblish correspondance between time spent in a reflective and in a non-reflective implementation, to show that our proof engine can do okay on things previously pushed to reflection
- `apply` (`rapply`!) / `apply ⋯ in ⋯` / `auto`

# Miscellaneous notes

Jason (Sun 6:03pm): [benchmarking one-step reductions in Coq] is heard because Coq doesn't expose a satisfactory one-step reduction.  (But maybe you claim the thing to do is to just bench the version that we can hack up in Coq, even when we know most of the time isn't spent in the single step of reduction?)  I think it's hard to construct them in a way where you're actually benching the single step.  If we do it via Ltac match + constr hacks, I expect we incur overhead in retypechecking and Ltac matching (I suppose I might be wrong, but we'd have to be dealing with truly enormous terms before we expect one-step reduction to take more than 0.0004 seconds (Coq can only measure down to 0.001).  Alternatively, we could do a non-one-step reduction when there's only one step to do, but it's not clear to me to what extent this is benching what we want to bench.  Alternatively we could try to bench a conversion problem where there's just one step of reduction to do, but again I think we'll end up just measuring the conversation overhead

Backtracking???? maybe discuss that this is really about functional interface / persistence, and the cost of providing that

Discuss how proof by reflection is like replacing the proof engine with a special-purpose reflective implementation

We might also want alpha-variation as a fast primitive (even if the original term took arbitraily long to typecheck)
