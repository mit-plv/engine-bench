# engine-bench
Benchmarks for various proof engines

# Performance Graphs
## Coq
Some autogenerated performance graphs for Coq are available at [here](https://mit-plv.github.io/engine-bench/coq.pdf).

# Some Information About Benchmarks:
Assumption: Proof engine API has partial (proof) terms, and is modular
- Tactics should reference quantified assumptions in the same way they reference global constants

Performance Criterion: Adding a new let binder underneath n lets should be Õ(1)
- See [`coq/PerformanceDemos/do_n_pose.v`](./coq/PerformanceDemos/do_n_pose.v), [`coq/PerformanceDemos/do_n_intro.v`](./coq/PerformanceDemos/do_n_intro.v)

Performance Criterion: Adding a new binder underneath n binders should be Õ(1)
- See [`coq/PerformanceDemos/do_n_intro.v`](./coq/PerformanceDemos/do_n_intro.v)
- Needed for: good performance of rewrite/rewrite_strat under binders
  + See [`coq/PerformanceDemos/rewrite_strat_under_binders.v`](./coq/PerformanceDemos/rewrite_strat_under_binders.v)
- Needed for: good performance of proving large conjunctions without structural types
  + See [`coq/PerformanceDemos/repeated_conj.v`](./coq/PerformanceDemos/repeated_conj.v)
- Needed for: good performance of turning f (f (... (f x))) = g (g (... (g x))) given f x = g x (or x = y -> f x = g y) w/ rewrite_strat
  + See [`coq/PerformanceDemos/rewrite_strat_repeated_app.v`](./coq/PerformanceDemos/rewrite_strat_repeated_app.v)

Performance criterion (convenient, not limiting): Typechecking an application of a function to n arguments with no conversion should be Õ(n)
- Can be constructed if you can prove conjunction/pairing without quadratic overhead
- Coq: See [`coq/PerformanceDemos/app_n.v`](./coq/PerformanceDemos/app_n.v), [`coq/PerformanceExperiments/app_n_uconstr.v`](./coq/PerformanceExperiments/app_n_uconstr.v), and [`coq/PerformanceExperiments/app_n_ltac2.v`](./coq/PerformanceExperiments/app_n_ltac2.v)

  app_n_uconstr | app_n_ltac2
  --|--
  <img src="https://mit-plv.github.io/engine-bench/coq/app-n-uconstr.svg" height=100px /> | <img src="https://mit-plv.github.io/engine-bench/coq/app-n-ltac2.svg" height=100px />

Note: not talk about display names at all; if you want to have them, all operations need to be basically Õ(1)

Performance Criterion: fast alpha-equivalence check (Õ(term size))
- we might also want alpha-variation as a fast primitive (even if the original term took arbitraily long to typecheck)
- See [`coq/PerformanceDemos/constr_eq.v`](./coq/PerformanceDemos/constr_eq.v)

Unification problem (context changing):
- `eq_refl : (fun y => y) = ((fun e y => e y) ?e)`
- `eq_refl : (fun y => y) = (fun y => ?e@{no y} y)`
- User: inside ?e, do intro, i.e., `?e@{no y} := fun z => ?e2@{z}`
- `eq_refl : (fun y => y) = (fun y => (fun z => ?e2@{z, no y}) y)`

Performance Criterion: lifting identity evar substitution should Õ(1)
- See [`coq/PerformanceDemos/lift_identity_evar_subst.v`](./coq/PerformanceDemos/lift_identity_evar_subst.v)

Performance Criterion: composing identity evar substitution should Õ(1)
- Needed for: modular performance behavior

Performance Criterion: lifting non-identity evar substitution should Õ(size of subst)
- See [`coq/PerformanceDemos/lift_non_identity_evar_subst.v`](./coq/PerformanceDemos/lift_non_identity_evar_subst.v)

Performance Criterion: composing non-identity evar substitution should Õ(size of subst)


Performance Criterion: Evar creation should be Õ(1)
- Coq: See [`coq/PerformanceExperiments/do_n_open_constr_True.v`](./coq/PerformanceExperiments/do_n_open_constr_True.v)

  do_n_open_constr_True |
  --|
  <img src="https://mit-plv.github.io/engine-bench/coq/do-n-open-constr-True.svg" height=100px /> |

Performance Criterion: 1-step delta on k constants should Õ(output term size)

Performance Criterion: 1-step iota should be Õ(output term size)

Performance Criterion: 1-step beta on k arguments of the same application node where each argument is mentioned multiple times should be Õ(input term size + output term size)


Performance Criterion: Inserting a cast node should be Õ(conversion checking the types)


Performance Criterion: Full reduction on a function of complexity O(f) should be Õ(f + input term size + output term size)
- See [`coq/PerformanceDemos/quadratic_reduction.v`](./coq/PerformanceDemos/quadratic_reduction.v)

Performance Criterion: lifting term across n consecutive binders should be Õ(term size)
- maybe we should require this to be O(1) so we don't have to batch lifting?

Performance Criterion: substitution-of-variables-for-variables should be Õ(term size)
- TODO: This can maybe be subsumed into beta?

Performance Criterion: pattern on k variables should be Õ(term size + k + cost of retypechecking the output term (only if input term is not simply typed))
- See [`coq/PerformanceDemos/pattern.v`](./coq/PerformanceDemos/pattern.v)

Performance Criterion: pattern should be Õ(term size * size of thing being patterned + cost of retypechecking the output term (only if input term is not simply typed))
- Note: Andres is not confident in this
- See [`coq/PerformanceDemos/pattern.v`](./coq/PerformanceDemos/pattern.v)

```
x, y := x |- pattern x in (eq_refl x : x = y)

x, z, pf : x = z, y := x |- subst x in (eq_refl x : x = y)
eq_rect ?P pf (?goal : eq_refl z : z = y <-- ill typed) : (eq_refl x : x = y)
```
What's `?P`?

Andres: let's postpone pattern discussion
- in particular perhaps pattern shouldn't be a primitive because it does too much?

later:
- pattern-without-conversion should be fast
- pattern-with-conversion should be as slow as needed (because of conversion during typechecking) but not gratuitously slow
- neither needs to be a primitive operation.

Backtracking???? maybe discuss that this is really about functional interface / persistence, and the cost of providing that
- (How do you implement progress without backtracking)

----------

Tactics for the paper:

- `pattern`
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
- 1-step-reduction / multi-step-reduction / `cbv` / `lazy` / `vm_compute` / ⋯ (probably not much detail, either use the steps above or use a skyhook vm)
- `pose` / `pose proof`
- run tactic under binders (i.e., readback under binders)
- `lia` by simplex by `pose`? or perhaps `congruence`? (analyze performance overhead over just doing the computation)
- non-reflective `ring` tactic? try to estaiblish correspondance between time spent in a reflective and in a non-reflective implementation, to show that our proof engine can do okay on things previously pushed to reflection
- `apply` (`rapply`!) / `apply ⋯ in ⋯` / `auto`


there are "goal management" tactics like `clear` / `cycle` / `shelve` that seem totally orthogonoal to everything here

also let's pretend multisuccess doesn't exist



only multi-goal thing: yes you can do things in any evar.

how do we transfer `constr`-s between evars?
