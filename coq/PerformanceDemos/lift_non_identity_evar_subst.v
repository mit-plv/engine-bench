(** * Performance Criterion: lifting identity evar substitution should Õ(1) *)
Require Import Coq.Lists.List.
(** For this test, we construct [x] evars each with context size [y],
    then we β-reduce to make the substitution non-identity.  Then we
    β-reduce again to move them under a context with an additional [z]
    elements.  We also check to see how long it takes to β reduce the
    evars when β-reduction is the identity.  We contrast this to doing
    the same thing except using [x] copies of [tt] instead. *)
Axiom P : list unit -> Prop.

Ltac make_uconstr_under_forall y bottom :=
  lazymatch y with
  | 0 => bottom
  | S ?y => let H := fresh "arrX" in
            let __ := match goal with _ => pose proof I as H end in (* save the name [H] *)
            let bottom := make_uconstr_under_forall y bottom in
            let __ := match goal with _ => clear H end in
            uconstr:(forall H : unit, bottom)
  end.

Ltac make_uconstr_under_fun y bottom :=
  lazymatch y with
  | 0 => bottom
  | S ?y => let H := fresh "funX" in
            let __ := match goal with _ => pose proof I as H end in (* save the name [H] *)
            let bottom := make_uconstr_under_fun y bottom in
            let __ := match goal with _ => clear H end in
            uconstr:(fun H : unit => bottom)
  end.

Ltac make_uconstr_app y f :=
  lazymatch y with
  | 0 => f
  | S ?y => make_uconstr_app y uconstr:(f tt)
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
  let rest := make_uconstr_under_forall z bottom in
  uconstr:(fun x : T => rest).

Ltac make_arg F ev x y :=
  let bottom := replicate unit x ev in
  let f := make_uconstr_under_fun y uconstr:(F (P bottom)) in
  make_uconstr_app y f.
Ltac make_evars F x y := make_arg F uconstr:(_) x y.
Ltac make_tts F x y := make_arg F uconstr:(tt) x y.
Ltac make_fun z := make_first_arg_under_binders Prop z.

Ltac time_evars' do_idtac x y z :=
  restart_timer;
  let F := make_fun z in
  finish_timing ("Tactic call make_fun");
  restart_timer;
  let FX := make_evars uconstr:(fun v : Prop => F (@id Prop v)) x y in
  finish_timing ("Tactic call make_evars");
  restart_timer;
  let F := open_constr:(F) in
  finish_timing ("Tactic call open_constr_F");
  restart_timer;
  let FX := open_constr:(FX) in
  finish_timing ("Tactic call open_constr_FX");
  restart_timer;
  let F := (eval cbv beta in F) in
  finish_timing ("Tactic call beta-F");
  restart_timer;
  let FX := (eval cbv beta in FX) in
  finish_timing ("Tactic call beta-FX");
  restart_timer;
  let FX := (eval cbv delta [id] in FX) in
  finish_timing ("Tactic call deta-id-FX");
  restart_timer;
  let FX := (eval cbv beta in FX) in
  finish_timing ("Tactic call beta-FX");
  lazymatch do_idtac with
  | true => idtac F FX
  | false => idtac
  end.
Ltac time_evars x y z := time_evars' false x y z.
Ltac time_evars_do_idtac x y z := time_evars' true x y z.

Ltac time_tts' do_idtac x y z :=
  restart_timer;
  let F := make_fun z in
  finish_timing ("Tactic call make_fun");
  restart_timer;
  let FX := make_tts uconstr:(fun v : Prop => F (@id Prop v)) x y in
  finish_timing ("Tactic call make_tts");
  restart_timer;
  let F := open_constr:(F) in
  finish_timing ("Tactic call open_constr_F");
  restart_timer;
  let FX := open_constr:(FX) in
  finish_timing ("Tactic call open_constr_FX");
  restart_timer;
  let F := (eval cbv beta in F) in
  finish_timing ("Tactic call beta-F");
  restart_timer;
  let FX := (eval cbv beta in FX) in
  finish_timing ("Tactic call beta-FX");
  restart_timer;
  let FX := (eval cbv delta [id] in FX) in
  finish_timing ("Tactic call deta-id-FX");
  restart_timer;
  let FX := (eval cbv beta in FX) in
  finish_timing ("Tactic call beta-FX");
  lazymatch do_idtac with
  | true => idtac F FX
  | false => idtac
  end.
Ltac time_tts x y z := time_tts' false x y z.
Ltac time_tts_do_idtac x y z := time_tts' true x y z.

Goal True. Time time_evars_do_idtac 5 6 7. Abort.
(* (fun x : Prop => unit -> unit -> unit -> unit -> unit -> unit -> unit -> x)
(unit ->
 unit ->
 unit ->
 unit ->
 unit ->
 unit ->
 unit ->
 P
   (?a@{funX:=tt; funX0:=tt; funX1:=tt; funX2:=tt; funX3:=tt; funX4:=tt}
    :: ?a0@{funX:=tt; funX0:=tt; funX1:=tt; funX2:=tt; funX3:=tt; funX4:=tt}
       :: ?a1@{funX:=tt; funX0:=tt; funX1:=tt; funX2:=tt; funX3:=tt; funX4:=tt}
          :: ?a2@{funX:=tt; funX0:=tt; funX1:=tt; funX2:=tt; funX3:=tt; funX4:=tt}
             :: ?a3@{funX:=tt; funX0:=tt; funX1:=tt; funX2:=tt; funX3:=tt;
                     funX4:=tt} :: nil))

Finished transaction in 0.003 secs (0.003u,0.s) (successful)
*)
Goal True. Time time_tts_do_idtac 5 6 7. Abort.
(* (fun x : Prop => unit -> unit -> unit -> unit -> unit -> unit -> unit -> x)
(unit ->
 unit ->
 unit -> unit -> unit -> unit -> unit -> P (tt :: tt :: tt :: tt :: tt :: nil))

Finished transaction in 0.003 secs (0.002u,0.s) (successful)
*)
Goal True. Time time_evars 100 100 100. Abort.
(* Tactic call make_fun ran for 0.014 secs (0.014u,0.s)
Tactic call make_evars ran for 0.015 secs (0.015u,0.s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.004 secs (0.001u,0.003s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Tactic call deta-id-FX ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Finished transaction in 0.038 secs (0.034u,0.003s) (successful)
*)
Goal True. Time time_tts 100 100 100. Abort.
(* Tactic call make_fun ran for 0.013 secs (0.013u,0.s)
Tactic call make_tts ran for 0.031 secs (0.027u,0.003s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.001 secs (0.001u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Tactic call deta-id-FX ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Finished transaction in 0.048 secs (0.044u,0.004s) (successful)
*)
Goal True. Time time_evars 1000 100 100. Abort.
(* Tactic call make_fun ran for 0.013 secs (0.013u,0.s)
Tactic call make_evars ran for 0.052 secs (0.051u,0.s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.091 secs (0.091u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0.003 secs (0.003u,0.s)
Tactic call deta-id-FX ran for 0.003 secs (0.003u,0.s)
Tactic call beta-FX ran for 0.003 secs (0.003u,0.s)
Finished transaction in 0.172 secs (0.171u,0.s) (successful)
*)
Goal True. Time time_tts 1000 100 100. Abort.
(* Tactic call make_fun ran for 0.016 secs (0.016u,0.s)
Tactic call make_tts ran for 0.057 secs (0.057u,0.s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.01 secs (0.01u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Tactic call deta-id-FX ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Finished transaction in 0.091 secs (0.091u,0.s) (successful)
*)
Goal True. Time time_evars 100 1000 100. Abort.
(* Tactic call make_fun ran for 0.025 secs (0.025u,0.s)
Tactic call make_evars ran for 1.181 secs (1.149u,0.032s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.182 secs (0.178u,0.003s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0.037 secs (0.037u,0.s)
Tactic call deta-id-FX ran for 0.004 secs (0.004u,0.s)
Tactic call beta-FX ran for 0.004 secs (0.004u,0.s)
Finished transaction in 1.44 secs (1.403u,0.036s) (successful)
*)
Goal True. Time time_tts 100 1000 100. Abort.
(* Tactic call make_fun ran for 0.016 secs (0.016u,0.s)
Tactic call make_tts ran for 1.332 secs (1.298u,0.032s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.046 secs (0.046u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0.015 secs (0.015u,0.s)
Tactic call deta-id-FX ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Finished transaction in 1.415 secs (1.382u,0.032s) (successful)
*)
Goal True. Time time_evars 100 100 1000. Abort.
(* Tactic call make_fun ran for 1.27 secs (1.222u,0.047s)
Tactic call make_evars ran for 0.015 secs (0.015u,0.s)
Tactic call open_constr_F ran for 0.016 secs (0.012u,0.003s)
Tactic call open_constr_FX ran for 0.022 secs (0.022u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Tactic call deta-id-FX ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Finished transaction in 1.331 secs (1.279u,0.051s) (successful)
*)
Goal True. Time time_tts 100 100 1000. Abort.
(* Tactic call make_fun ran for 1.248 secs (1.208u,0.04s)
Tactic call make_tts ran for 0.015 secs (0.015u,0.s)
Tactic call open_constr_F ran for 0.016 secs (0.016u,0.s)
Tactic call open_constr_FX ran for 0.02 secs (0.02u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Tactic call deta-id-FX ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Finished transaction in 1.306 secs (1.266u,0.04s) (successful)
*)
(* Fatal error: out of memory. *)
(*
Goal True. Time time_evars 2000 100 100. Abort.
(* Tactic call make_fun ran for 0.015 secs (0.015u,0.s)
Tactic call make_evars ran for 0.085 secs (0.085u,0.s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.286 secs (0.274u,0.011s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0.009 secs (0.009u,0.s)
Tactic call deta-id-FX ran for 0.009 secs (0.009u,0.s)
Tactic call beta-FX ran for 0.008 secs (0.008u,0.s)
Finished transaction in 0.424 secs (0.412u,0.012s) (successful)
*)
Goal True. Time time_tts 2000 100 100. Abort.
(* Tactic call make_fun ran for 0.015 secs (0.015u,0.s)
Tactic call make_tts ran for 0.099 secs (0.099u,0.s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.019 secs (0.019u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Tactic call deta-id-FX ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Finished transaction in 0.145 secs (0.145u,0.s) (successful)
*)
Goal True. Time time_evars 100 2000 100. Abort.
(* Tactic call make_fun ran for 0.02 secs (0.02u,0.s)
Tactic call make_evars ran for 5.254 secs (5.107u,0.135s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.478 secs (0.478u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0.082 secs (0.082u,0.s)
Tactic call deta-id-FX ran for 0.007 secs (0.007u,0.s)
Tactic call beta-FX ran for 0.006 secs (0.002u,0.003s)
Finished transaction in 5.859 secs (5.707u,0.139s) (successful)
*)
Goal True. Time time_tts 100 2000 100. Abort.
(* Tactic call make_fun ran for 0.015 secs (0.015u,0.s)
Tactic call make_tts ran for 5.261 secs (5.149u,0.111s)
Tactic call open_constr_F ran for 0. secs (0.u,0.s)
Tactic call open_constr_FX ran for 0.169 secs (0.161u,0.008s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0.065 secs (0.065u,0.s)
Tactic call deta-id-FX ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Finished transaction in 5.52 secs (5.4u,0.12s) (successful)
*)
Goal True. Time time_evars 100 100 2000. Abort.
(* Tactic call make_fun ran for 5.482 secs (5.373u,0.108s)
Tactic call make_evars ran for 0.016 secs (0.016u,0.s)
Tactic call open_constr_F ran for 0.075 secs (0.075u,0.s)
Tactic call open_constr_FX ran for 0.086 secs (0.086u,0.s)
Tactic call beta-F ran for 0.001 secs (0.001u,0.s)
Tactic call beta-FX ran for 0.001 secs (0.001u,0.s)
Tactic call deta-id-FX ran for 0.001 secs (0.001u,0.s)
Tactic call beta-FX ran for 0.001 secs (0.001u,0.s)
Finished transaction in 5.673 secs (5.565u,0.108s) (successful)
*)
Goal True. Time time_tts 100 100 2000. Abort.
(* Tactic call make_fun ran for 4.582 secs (4.442u,0.14s)
Tactic call make_tts ran for 0.016 secs (0.016u,0.s)
Tactic call open_constr_F ran for 0.076 secs (0.076u,0.s)
Tactic call open_constr_FX ran for 0.083 secs (0.083u,0.s)
Tactic call beta-F ran for 0.001 secs (0.001u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Tactic call deta-id-FX ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Finished transaction in 4.768 secs (4.628u,0.14s) (successful)
*)
Goal True. Time time_evars 1000 1000 1000. Abort.
(* Tactic call make_fun ran for 1.486 secs (1.466u,0.02s)
Tactic call make_evars ran for 1.607 secs (1.567u,0.039s)
Tactic call open_constr_F ran for 0.014 secs (0.014u,0.s)
Tactic call open_constr_FX ran for 1.801 secs (1.745u,0.056s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0.318 secs (0.314u,0.003s)
Tactic call deta-id-FX ran for 0.046 secs (0.046u,0.s)
Tactic call beta-FX ran for 0.045 secs (0.045u,0.s)
Finished transaction in 5.33 secs (5.21u,0.12s) (successful)
*)
Goal True. Time time_tts 1000 1000 1000. Abort.
(* Tactic call make_fun ran for 2.095 secs (2.059u,0.035s)
Tactic call make_tts ran for 1.184 secs (1.132u,0.051s)
Tactic call open_constr_F ran for 0.014 secs (0.014u,0.s)
Tactic call open_constr_FX ran for 0.21 secs (0.21u,0.s)
Tactic call beta-F ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0.017 secs (0.017u,0.s)
Tactic call deta-id-FX ran for 0. secs (0.u,0.s)
Tactic call beta-FX ran for 0. secs (0.u,0.s)
Finished transaction in 3.535 secs (3.447u,0.088s) (successful)
 *)
(*
Goal True. Time time_evars 2000 1000 1000. Abort.
(* *)
Goal True. Time time_tts 2000 1000 1000. Abort.
(* *)
Goal True. Time time_evars 1000 2000 1000. Abort.
(* *)
Goal True. Time time_tts 1000 2000 1000. Abort.
(* *)
Goal True. Time time_evars 1000 1000 2000. Abort.
(* *)
Goal True. Time time_tts 1000 1000 2000. Abort.
(* *)
*)
*)
