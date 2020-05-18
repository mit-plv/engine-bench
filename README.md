# engine-bench
Benchmarks for various proof engines

# Some Information About Benchmarks:
Assumption: Proof engine API has partial (proof) terms, and is modular
- Tactics should reference quantified assumptions in the same way they reference global constants

Performance Criterion: Adding a new let binder underneath n lets should be Õ(1)
Performance Criterion: Adding a new binder underneath n binders should be Õ(1)
Needed for: good performance of rewrite/rewrite_strat under binders
Needed for: good performance of proving large conjunctions without structural types
Needed for: good performance of turning f (f (... (f x))) = g (g (... (g x))) given f x = g x (or x = y -> f x = g y) w/ rewrite_strat

Performance criterion (convenient, not limiting): Typechecking an application of a function to n arguments with no conversion should be Õ(n)
- Can be constructed if you can prove conjunction/pairing without quadratic overhead

Note: not talk about display names at all; if you want to have them, all operations need to be basically Õ(1)

Performance Criterion: fast alpha-equivalence check (Õ(term size))
we might also want alpha-variation as a fast primitive (even if the original term took arbitraily long to typecheck)

Unification problem (context changing):
eq_refl : (fun y => y) = ((fun e y => e y) ?e)
eq_refl : (fun y => y) = (fun y => ?e@{no y} y)
User: inside ?e, do intro, i.e., ?e@{no y} := fun z => ?e2@{z}
eq_refl : (fun y => y) = (fun y => (fun z => ?e2@{z, no y}) y)

Performance Criterion: lifting identity evar substitution should Õ(1)
Performance Criterion: composing identity evar substitution should Õ(1)
Needed for: modular performance behavior
Performance Criterion: lifting non-identity evar substitution should Õ(size of subst)
Performance Criterion: composing non-identity evar substitution should Õ(size of subst)

Performance Criterion: Evar creation should be Õ(1)

Performance Criterion: 1-step delta on k constants should Õ(output term size)
Performance Criterion: 1-step iota should be Õ(output term size)
Performance Criterion: 1-step beta on k arguments of the same application node where each argument is mentioned multiple times should be Õ(input term size + output term size)

Performance Criterion: Inserting a cast node should be Õ(conversion checking the types)

Performance Criterion: Full reduction on a function of complexity O(f) should be Õ(f + input term size + output term size)

Performance Criterion: lifting term across n consecutive binders should be Õ(term size)
maybe we should require this to be O(1) so we don't have to batch lifting?
Performance Criterion: substitution-of-variables-for-variables should be Õ(term size)
TODO: This can maybe be subsumed into beta?

Performance Criterion: pattern on k variables should be Õ(term size + k + cost of retypechecking the output term (only if input term is not simply typed))
Performance Criterion: pattern should be Õ(term size * size of thing being patterned + cost of retypechecking the output term (only if input term is not simply typed))
Note: Andres is not confident in this

x, y := x |- pattern x in (eq_refl x : x = y)

x, z, pf : x = z, y := x |- subst x in (eq_refl x : x = y)
eq_rect ?P pf (?goal : eq_refl z : z = y <-- ill typed) : (eq_refl x : x = y)
What's ?P?

Andres: let's postpone pattern discussion
in particular perhaps pattern shouldn't be a primitive because it does too much?
later:
pattern-without-conversion should be fast
pattern-with-conversion should be as slow as needed (because of conversion during typechecking) but not gratuitously slow
neither needs to be a primitive operation.

Backtracking???? maybe discuss that this is really about functional interface / persistence, and the cost of providing that
(How do you implement progress without backtracking)

----------

Tactics for the paper:
    - pattern
    - destruct / induction
    - assert
    - rewrite
    - setoid_rewrite (rewrite with binders)
    - autorewrite
    - rewrite_strat / autosetoid_rewrite
    - intro / intros / revert / generalize / set / clear / clearbody
    - refine / exact / assumption
    - change / refine + unification
    - unify, roughly how an unuification algorithm can do its job by calling intantiate / refine-in-evar / reduction-step-with/in-evar
    - constr:(...) / open_constr:(...)
    - match goal / match constr (readback problem)
    - moving constrs / out-of-band-things across contexts?
    - 1-step-reduction / multi-step-reduction / cbv / lazy / vm_compute / ... (probably not much detail, either use the steps above or use a skyhook vm)
    - pose / pose proof
    - run tactic under binders (i.e., readback under binders)
    - lia by simplex by pose? or perhaps congruence? (analyze performance overhead over just doing the computation)
    - non-reflective ring tactic? try to estaiblish correspondance between time spent in a reflective and in a non-reflective implementation, to show that our proof engine can do okay on things previously pushed to reflection
    - apply (rapply!) / apply in / auto


there are "goal management" tactics like clear / cycle / shelve that seem totally orthogonoal to everything here
also let's pretend multisuccess doesn't exist

only multi-goal thing: yes you can do things in any evar.
how do we transfer constr-s between evars?
