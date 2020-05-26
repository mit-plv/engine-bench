Require Import PerformanceExperiments.Harness.

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
  finish_timing ("Tactic call make_fun-ev");
  restart_timer;
  let FX := make_evars uconstr:(fun v : Prop => F (@id Prop v)) x y in
  finish_timing ("Tactic call make_evars");
  restart_timer;
  let F := open_constr:(F) in
  finish_timing ("Tactic call open_constr_F-ev");
  restart_timer;
  let FX := open_constr:(FX) in
  finish_timing ("Tactic call open_constr_FX-ev");
  restart_timer;
  let F := (eval cbv beta in F) in
  finish_timing ("Tactic call beta-F-ev");
  restart_timer;
  let FX := (eval cbv beta in FX) in
  finish_timing ("Tactic call prebeta-FX-ev");
  restart_timer;
  let FX := (eval cbv delta [id] in FX) in
  finish_timing ("Tactic call deta-id-FX-ev");
  restart_timer;
  let FX := (eval cbv beta in FX) in
  finish_timing ("Tactic call beta-FX-ev");
  lazymatch do_idtac with
  | true => idtac F FX
  | false => idtac
  end.
Ltac time_evars x y z := time_evars' false x y z.
Ltac time_evars_do_idtac x y z := time_evars' true x y z.

Ltac time_tts' do_idtac x y z :=
  restart_timer;
  let F := make_fun z in
  finish_timing ("Tactic call make_fun-tt");
  restart_timer;
  let FX := make_tts uconstr:(fun v : Prop => F (@id Prop v)) x y in
  finish_timing ("Tactic call make_tts");
  restart_timer;
  let F := open_constr:(F) in
  finish_timing ("Tactic call open_constr_F-tt");
  restart_timer;
  let FX := open_constr:(FX) in
  finish_timing ("Tactic call open_constr_FX-tt");
  restart_timer;
  let F := (eval cbv beta in F) in
  finish_timing ("Tactic call beta-F-tt");
  restart_timer;
  let FX := (eval cbv beta in FX) in
  finish_timing ("Tactic call prebeta-FX-tt");
  restart_timer;
  let FX := (eval cbv delta [id] in FX) in
  finish_timing ("Tactic call deta-id-FX-tt");
  restart_timer;
  let FX := (eval cbv beta in FX) in
  finish_timing ("Tactic call beta-FX-tt");
  lazymatch do_idtac with
  | true => idtac F FX
  | false => idtac
  end.
Ltac time_tts x y z := time_tts' false x y z.
Ltac time_tts_do_idtac x y z := time_tts' true x y z.

Ltac time_both x y z :=
  optimize_heap;
  time_evars x y z;
  optimize_heap;
  time_tts x y z.

Ltac mkgoal n := constr:(True).
Ltac redgoal _ := idtac.
Local Notation default_x := 1000 (only parsing).
Local Notation default_y := 100 (only parsing).
Local Notation default_z := 100 (only parsing).
Ltac describe_goal_x x :=
  let y := constr:(default_y) in
  let z := constr:(default_z) in
  idtac "Params: nevars=" x ", ctx-size=" y ", extra-binders=" z.
Ltac time_solve_goal_x x := time_both x constr:(default_y) constr:(default_z).
Ltac describe_goal_y y :=
  let x := constr:(default_x) in
  let z := constr:(default_z) in
  idtac "Params: ctx-size=" y ", nevars=" x ", extra-binders=" z.
Ltac time_solve_goal_y y := time_both constr:(default_x) y constr:(default_z).
Ltac describe_goal_z z :=
  let x := constr:(default_x) in
  let y := constr:(default_y) in
  idtac "Params: extra-binders=" z ", nevars=" x ", ctx-size=" y.
Ltac time_solve_goal_z z := time_both constr:(default_x) constr:(default_y) z.

Definition args_of_size_x (s : size) : list nat
  := match s with
     | Sanity => seq 1 3
     | SuperFast => List.map (fun x => x * 100) (seq 1 10)
     | Fast => List.map (fun x => x * 100) (seq 1 20)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Definition args_of_size_y (s : size) : list nat
  := match s with
     | Sanity => seq 1 3
     | SuperFast => List.map (fun x => x * 100) (seq 1 10)
     | Fast => List.map (fun x => x * 100) (seq 1 20)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Definition args_of_size_z (s : size) : list nat
  := match s with
     | Sanity => seq 1 3
     | SuperFast => List.map (fun x => x * 100) (seq 1 10)
     | Fast => List.map (fun x => x * 100) (seq 1 20)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.
