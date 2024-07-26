(** * Performance Criterion: lifting identity evar substitution should Õ(1) *)
From Coq Require Import List.
(** For this test, we construct [x] evars each with context size [y]
    and then we β-reduce to move them under a context with an
    additional [z] elements.  We also check to see how long it takes
    to β reduce the evars when β-reduction is the identity.  We
    contrast this to doing the same thing except using [x] copies of
    [tt] instead. *)
Axiom P : list unit -> Prop.

Ltac make_uconstr_under_forall y bottom :=
  lazymatch y with
  | 0 => bottom
  | S ?y => let H := fresh "arr1X" in
            let __ := match goal with _ => pose proof I as H end in (* save the name [H] *)
            let bottom := make_uconstr_under_forall y bottom in
            let __ := match goal with _ => clear H end in
            uconstr:(forall H : unit, bottom)
  end.

Ltac make_uconstr_under_forall2 y bottom :=
  lazymatch y with
  | 0 => bottom
  | S ?y => let H := fresh "arr2X" in
            let __ := match goal with _ => pose proof I as H end in (* save the name [H] *)
            let bottom := make_uconstr_under_forall2 y bottom in
            let __ := match goal with _ => clear H end in
            uconstr:(forall H : unit, bottom)
  end.

Ltac replicate T x term :=
  lazymatch x with
  | 0 => uconstr:(@nil T)
  | S ?x => let tl := replicate T x term in
            uconstr:(@cons T term tl)
  end.

Ltac make_first_arg_under_binders T z :=
  (** pull a hack to get an open uconstr *)
  let x := fresh "x" in
  let bottom := lazymatch constr:(fun x : unit => x) with
                | fun x => ?body => uconstr:(body)
                end in
  let rest := make_uconstr_under_forall2 z bottom in
  uconstr:(fun x : T => rest).

Ltac make_arg F ev x y :=
  let bottom := replicate unit x ev in
  make_uconstr_under_forall y uconstr:(F (P bottom)).
Ltac make_evars F x y := make_arg F uconstr:(_) x y.
Ltac make_tts F x y := make_arg F uconstr:(tt) x y.
Ltac make_fun z := make_first_arg_under_binders Prop z.

(** TODO: rework this using [@id Prop] to bring it in line with
     [lift_non_identity_evar_subst.v] *)
Ltac time_evars' do_idtac x y z :=
  restart_timer;
  let F := make_fun z in
  finish_timing ("Tactic call make_fun");
  restart_timer;
  let X := make_evars uconstr:(fun v : Prop => v) x y in
  finish_timing ("Tactic call make_evars-id");
  restart_timer;
  let FX := make_evars F x y in
  finish_timing ("Tactic call make_evars-F");
  restart_timer;
  let F := open_constr:(F) in
  finish_timing ("Tactic call open_constr_F");
  restart_timer;
  let FX := open_constr:(FX) in
  finish_timing ("Tactic call open_constr_FX");
  restart_timer;
  let X := open_constr:(X) in
  finish_timing ("Tactic call open_constr_X");
  restart_timer;
  let F := (eval cbv beta in F) in
  finish_timing ("Tactic call beta-F");
  restart_timer;
  let X := (eval cbv beta in X) in
  finish_timing ("Tactic call beta-X");
  restart_timer;
  let FX := (eval cbv beta in FX) in
  finish_timing ("Tactic call beta-FX");
  lazymatch do_idtac with
  | true => idtac F X FX
  | false => idtac
  end.
Ltac time_evars x y z := time_evars' false x y z.
Ltac time_evars_do_idtac x y z := time_evars' true x y z.

Ltac time_tts' do_idtac x y z :=
  restart_timer;
  let F := make_fun z in
  finish_timing ("Tactic call make_fun");
  restart_timer;
  let X := make_tts uconstr:(fun v : Prop => v) x y in
  finish_timing ("Tactic call make_tts-id");
  restart_timer;
  let FX := make_tts F x y in
  finish_timing ("Tactic call make_tts-F");
  restart_timer;
  let F := open_constr:(F) in
  finish_timing ("Tactic call open_constr_F");
  restart_timer;
  let FX := open_constr:(FX) in
  finish_timing ("Tactic call open_constr_FX");
  restart_timer;
  let X := open_constr:(X) in
  finish_timing ("Tactic call open_constr_X");
  restart_timer;
  let F := (eval cbv beta in F) in
  finish_timing ("Tactic call beta-F");
  restart_timer;
  let X := (eval cbv beta in X) in
  finish_timing ("Tactic call beta-X");
  restart_timer;
  let FX := (eval cbv beta in FX) in
  finish_timing ("Tactic call beta-FX");
  lazymatch do_idtac with
  | true => idtac F X FX
  | false => idtac
  end.
Ltac time_tts x y z := time_tts' false x y z.
Ltac time_tts_do_idtac x y z := time_tts' true x y z.

Goal True. Time time_evars_do_idtac 5 6 7. Abort.
(* (fun x : Prop => unit -> unit -> unit -> unit -> unit -> unit -> unit -> x)
(forall arr1X arr1X0 arr1X1 arr1X2 arr1X3 arr1X4 : unit,
 P (?a4 :: ?a5 :: ?a6 :: ?a7 :: ?a8 :: nil))
(forall arr1X arr1X0 arr1X1 arr1X2 arr1X3 arr1X4 : unit,
 unit ->
 unit ->
 unit -> unit -> unit -> unit -> unit -> P (?a :: ?a0 :: ?a1 :: ?a2 :: ?a3 :: nil))
Finished transaction in 0.004 secs (0.004u,0.s) (successful)
*)
Goal True. Time time_tts_do_idtac 5 6 7. Abort.
(* (fun x : Prop => unit -> unit -> unit -> unit -> unit -> unit -> unit -> x)
(unit ->
 unit -> unit -> unit -> unit -> unit -> P (tt :: tt :: tt :: tt :: tt :: nil))
(unit ->
 unit ->
 unit ->
 unit ->
 unit ->
 unit ->
 unit ->
 unit ->
 unit -> unit -> unit -> unit -> unit -> P (tt :: tt :: tt :: tt :: tt :: nil))
Finished transaction in 0.004 secs (0.004u,0.s) (successful)
*)
Goal True. Time time_evars 100 100 100. Abort.
(* Tactic call make_fun ran for 0.016 secs (0.016u,0.s)
Tactic call make_evars-id ran for 0.017 secs (0.017u,0.s)
Tactic call make_evars-F ran for 0.033 secs (0.033u,0.s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.004 secs (0.004u,0.s)
Tactic call open_constr_X ran for 0.004 secs (0.004u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Finished transaction in 0.079 secs (0.079u,0.s) (successful)
*)
Goal True. Time time_tts 100 100 100. Abort.
(* Tactic call make_fun ran for 0.013 secs (0.013u,0.s)
Tactic call make_tts-id ran for 0.036 secs (0.036u,0.s)
Tactic call make_tts-F ran for 0.014 secs (0.014u,0.s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.001 secs (0.001u,0.s)
Tactic call open_constr_X ran for 0.001 secs (0.001u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Finished transaction in 0.068 secs (0.068u,0.s) (successful)
*)
Goal True. Time time_evars 1000 100 100. Abort.
(* Tactic call make_fun ran for 0.016 secs (0.016u,0.s)
Tactic call make_evars-id ran for 0.071 secs (0.071u,0.s)
Tactic call make_evars-F ran for 0.059 secs (0.059u,0.s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.054 secs (0.054u,0.s)
Tactic call open_constr_X ran for 0.158 secs (0.158u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0.002 secs (0.002u,0.s)
Tactic call beta-FX ran for 0.004 secs (0.004u,0.s)
Finished transaction in 0.374 secs (0.374u,0.s) (successful)
*)
Goal True. Time time_tts 1000 100 100. Abort.
(* Tactic call make_fun ran for 0.012 secs (0.012u,0.s)
Tactic call make_tts-id ran for 0.074 secs (0.066u,0.008s)
Tactic call make_tts-F ran for 0.133 secs (0.133u,0.s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.011 secs (0.011u,0.s)
Tactic call open_constr_X ran for 0.01 secs (0.01u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Finished transaction in 0.247 secs (0.238u,0.008s) (successful)
*)
Goal True. Time time_evars 100 1000 100. Abort.
(* Tactic call make_fun ran for 0.081 secs (0.081u,0.s)
Tactic call make_evars-id ran for 1.301 secs (1.268u,0.031s)
Tactic call make_evars-F ran for 1.319 secs (1.29u,0.027s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.176 secs (0.172u,0.004s)
Tactic call open_constr_X ran for 0.239 secs (0.227u,0.011s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0.004 secs (0.004u,0.s)
Tactic call beta-FX ran for 0.006 secs (0.006u,0.s)
Finished transaction in 3.134 secs (3.056u,0.075s) (successful)
*)
Goal True. Time time_tts 100 1000 100. Abort.
(* Tactic call make_fun ran for 0.012 secs (0.012u,0.s)
Tactic call make_tts-id ran for 1.803 secs (1.747u,0.055s)
Tactic call make_tts-F ran for 1.434 secs (1.354u,0.079s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.03 secs (0.03u,0.s)
Tactic call open_constr_X ran for 0.026 secs (0.026u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Finished transaction in 3.313 secs (3.177u,0.136s) (successful)
*)
Goal True. Time time_evars 100 100 1000. Abort.
(* Tactic call make_fun ran for 1.392 secs (1.363u,0.027s)
Tactic call make_evars-id ran for 0.014 secs (0.014u,0.s)
Tactic call make_evars-F ran for 0.014 secs (0.014u,0.s)
Tactic call open_constr_F ran for 0.014 secs (0.014u,0.s)
Tactic call open_constr_FX ran for 0.021 secs (0.021u,0.s)
Tactic call open_constr_X ran for 0.004 secs (0.004u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Finished transaction in 1.468 secs (1.438u,0.028s) (successful)
*)
Goal True. Time time_tts 100 100 1000. Abort.
(* Tactic call make_fun ran for 1.074 secs (1.026u,0.048s)
Tactic call make_tts-id ran for 0.014 secs (0.014u,0.s)
Tactic call make_tts-F ran for 0.015 secs (0.015u,0.s)
Tactic call open_constr_F ran for 0.014 secs (0.014u,0.s)
Tactic call open_constr_FX ran for 0.019 secs (0.019u,0.s)
Tactic call open_constr_X ran for 0.001 secs (0.001u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Finished transaction in 1.144 secs (1.096u,0.048s) (successful)
 *)
(* Fatal error: out of memory. *)
(*
Goal True. Time time_evars 2000 100 100. Abort.
(* Tactic call make_fun ran for 0.015 secs (0.015u,0.s)
Tactic call make_evars-id ran for 0.092 secs (0.088u,0.003s)
Tactic call make_evars-F ran for 0.072 secs (0.068u,0.004s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.165 secs (0.165u,0.s)
Tactic call open_constr_X ran for 0.313 secs (0.305u,0.007s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0.006 secs (0.006u,0.s)
Tactic call beta-FX ran for 0.01 secs (0.01u,0.s)
Finished transaction in 0.688 secs (0.672u,0.016s) (successful)
*)
Goal True. Time time_tts 2000 100 100. Abort.
(* Tactic call make_fun ran for 0.012 secs (0.012u,0.s)
Tactic call make_tts-id ran for 0.109 secs (0.105u,0.003s)
Tactic call make_tts-F ran for 0.074 secs (0.074u,0.s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.034 secs (0.034u,0.s)
Tactic call open_constr_X ran for 0.019 secs (0.019u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0.001 secs (0.001u,0.s)
Finished transaction in 0.259 secs (0.255u,0.003s) (successful)
*)
Goal True. Time time_evars 100 2000 100. Abort.
(* Tactic call make_fun ran for 0.07 secs (0.054u,0.015s)
Tactic call make_evars-id ran for 5.17 secs (5.094u,0.075s)
Tactic call make_evars-F ran for 5.183 secs (5.067u,0.115s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.449 secs (0.445u,0.004s)
Tactic call open_constr_X ran for 0.431 secs (0.419u,0.011s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0.009 secs (0.009u,0.s)
Tactic call beta-FX ran for 0.013 secs (0.013u,0.s)
Finished transaction in 11.336 secs (11.113u,0.223s) (successful)
*)
Goal True. Time time_tts 100 2000 100. Abort.
(* Tactic call make_fun ran for 0.012 secs (0.012u,0.s)
Tactic call make_tts-id ran for 4.075 secs (3.919u,0.155s)
Tactic call make_tts-F ran for 5.604 secs (5.456u,0.148s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.108 secs (0.108u,0.s)
Tactic call open_constr_X ran for 0.1 secs (0.1u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0.001 secs (0.001u,0.s)
Finished transaction in 9.908 secs (9.604u,0.304s) (successful)
*)
Goal True. Time time_evars 100 100 2000. Abort.
(* Tactic call make_fun ran for 4.851 secs (4.739u,0.111s)
Tactic call make_evars-id ran for 0.014 secs (0.014u,0.s)
Tactic call make_evars-F ran for 0.015 secs (0.015u,0.s)
Tactic call open_constr_F ran for 0.074 secs (0.074u,0.s)
Tactic call open_constr_FX ran for 0.084 secs (0.084u,0.s)
Tactic call open_constr_X ran for 0.004 secs (0.004u,0.s)
Tactic call beta-F ran for 0.001 secs (0.001u,0.s)
Tactic call beta-X ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0.001 secs (0.001u,0.s)
Finished transaction in 5.055 secs (4.943u,0.112s) (successful)
*)
Goal True. Time time_tts 100 100 2000. Abort.
(* Tactic call make_fun ran for 7.413 secs (7.277u,0.135s)
Tactic call make_tts-id ran for 0.014 secs (0.014u,0.s)
Tactic call make_tts-F ran for 0.014 secs (0.014u,0.s)
Tactic call open_constr_F ran for 0.075 secs (0.075u,0.s)
Tactic call open_constr_FX ran for 0.082 secs (0.082u,0.s)
Tactic call open_constr_X ran for 0.001 secs (0.001u,0.s)
Tactic call beta-F ran for 0.001 secs (0.001u,0.s)
Tactic call beta-X ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0.001 secs (0.001u,0.s)
Finished transaction in 7.609 secs (7.473u,0.135s) (successful)
*)
Goal True. Time time_evars 1000 1000 1000. Abort.
(* Tactic call make_fun ran for 1.213 secs (1.172u,0.04s)
Tactic call make_evars-id ran for 1.09 secs (1.037u,0.052s)
Tactic call make_evars-F ran for 1.094 secs (1.07u,0.023s)
Tactic call open_constr_F ran for 0.015 secs (0.015u,0.s)
Tactic call open_constr_FX ran for 1.174 secs (1.158u,0.016s)
Tactic call open_constr_X ran for 1.597 secs (1.573u,0.023s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0.046 secs (0.046u,0.s)
Tactic call beta-FX ran for 0.062 secs (0.05u,0.011s)
Finished transaction in 6.313 secs (6.141u,0.171s) (successful)
*)
Goal True. Time time_tts 1000 1000 1000. Abort.
(* Tactic call make_fun ran for 1.213 secs (1.165u,0.048s)
Tactic call make_tts-id ran for 1.095 secs (1.051u,0.043s)
Tactic call make_tts-F ran for 1.099 secs (1.047u,0.051s)
Tactic call open_constr_F ran for 0.014 secs (0.014u,0.s)
Tactic call open_constr_FX ran for 0.189 secs (0.189u,0.s)
Tactic call open_constr_X ran for 0.131 secs (0.131u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0.001 secs (0.001u,0.s)
Finished transaction in 3.754 secs (3.61u,0.144s) (successful)
 *)
(*
Goal True. Time time_evars 2000 1000 1000. Abort.
(* Tactic call make_fun ran for 1.221 secs (1.181u,0.04s)
Tactic call make_evars-id ran for 1.117 secs (1.105u,0.011s)
Tactic call make_evars-F ran for 1.469 secs (1.425u,0.044s)
Tactic call open_constr_F ran for 0.015 secs (0.015u,0.s)
Tactic call open_constr_FX ran for 4.309 secs (4.201u,0.108s)
Tactic call open_constr_X ran for 3.665 secs (3.601u,0.063s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0.093 secs (0.085u,0.008s)
Tactic call beta-FX ran for 0.212 secs (0.188u,0.024s)
Finished transaction in 12.122 secs (11.822u,0.3s) (successful)
 *)
Goal True. Time time_tts 2000 1000 1000. Abort.
(* Tactic call make_fun ran for 1.256 secs (1.256u,0.s)
Tactic call make_tts-id ran for 1.225 secs (1.225u,0.s)
Tactic call make_tts-F ran for 1.385 secs (1.384u,0.s)
Tactic call open_constr_F ran for 0.015 secs (0.015u,0.s)
Tactic call open_constr_FX ran for 0.312 secs (0.312u,0.s)
Tactic call open_constr_X ran for 0.229 secs (0.229u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0.001 secs (0.001u,0.s)
Tactic call beta-FX ran for 0.001 secs (0.001u,0.s)
Finished transaction in 4.436 secs (4.436u,0.s) (successful)
*)
Goal True. Time time_evars 1000 2000 1000. Abort.
(* Tactic call make_fun ran for 2.655 secs (2.595u,0.059s)
Tactic call make_evars-id ran for 5.508 secs (5.36u,0.148s)
Tactic call make_evars-F ran for 4.072 secs (3.936u,0.136s)
Tactic call open_constr_F ran for 0.014 secs (0.014u,0.s)
Tactic call open_constr_FX ran for 2.172 secs (2.068u,0.103s)
Tactic call open_constr_X ran for 2.873 secs (2.857u,0.016s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0.083 secs (0.083u,0.s)
Tactic call beta-FX ran for 0.233 secs (0.209u,0.023s)
Finished transaction in 17.63 secs (17.142u,0.488s) (successful)
*)
Goal True. Time time_tts 1000 2000 1000. Abort.
(* Tactic call make_fun ran for 1.959 secs (1.895u,0.063s)
Tactic call make_tts-id ran for 8.208 secs (8.072u,0.135s)
Tactic call make_tts-F ran for 9.546 secs (9.35u,0.196s)
Tactic call open_constr_F ran for 0.015 secs (0.015u,0.s)
Tactic call open_constr_FX ran for 0.427 secs (0.427u,0.s)
Tactic call open_constr_X ran for 0.319 secs (0.319u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0.001 secs (0.001u,0.s)
Tactic call beta-FX ran for 0.001 secs (0.001u,0.s)
Finished transaction in 20.492 secs (20.096u,0.396s) (successful)
*)
Goal True. Time time_evars 1000 1000 2000. Abort.
(* Tactic call make_fun ran for 6.252 secs (6.12u,0.131s)
Tactic call make_evars-id ran for 1.645 secs (1.601u,0.044s)
Tactic call make_evars-F ran for 1.69 secs (1.658u,0.031s)
Tactic call open_constr_F ran for 0.075 secs (0.075u,0.s)
Tactic call open_constr_FX ran for 1.955 secs (1.939u,0.015s)
Tactic call open_constr_X ran for 2.568 secs (2.568u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0.055 secs (0.055u,0.s)
Tactic call beta-FX ran for 0.065 secs (0.061u,0.004s)
Finished transaction in 14.323 secs (14.095u,0.227s) (successful)
*)
Goal True. Time time_tts 1000 1000 2000. Abort.
(* Tactic call make_fun ran for 7.156 secs (7.008u,0.147s)
Tactic call make_tts-id ran for 1.747 secs (1.702u,0.044s)
Tactic call make_tts-F ran for 1.76 secs (1.72u,0.04s)
Tactic call open_constr_F ran for 0.074 secs (0.074u,0.s)
Tactic call open_constr_FX ran for 0.287 secs (0.287u,0.s)
Tactic call open_constr_X ran for 0.112 secs (0.112u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-X ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0.001 secs (0.001u,0.s)
Finished transaction in 11.151 secs (10.919u,0.231s) (successful)
*)
*)
*)
