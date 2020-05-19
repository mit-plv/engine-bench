(** * Performance Criterion: Evar creation should be Õ(1) *)
(** See also COQBUG(https://github.com/coq/coq/issues/8245), COQBUG(https://github.com/coq/coq/issues/8237), COQBUG(https://github.com/coq/coq/issues/9582) *)
(** See also [../PerformanceExperiments/do_n_open_constr_True.v], [../PerformanceExperiments/open_constr_n_lambda_no_types_no_names.v], [../PerformanceExperiments/open_constr_n_lambda_no_types_same_names.v], and [../PerformanceExperiments/open_constr_n_lambda_no_types_different_names.v] *)

(* TODO: Make these line up with those in experiments *)
(*
Goal True. Time do 250 let x := open_constr:(_:unit) in idtac. Time Optimize Proof. Abort. Optimize Heap.
(* Finished transaction in 0.005 secs (0.u,0.005s) (successful) *)
Goal True. Time do 500 let x := open_constr:(_:unit) in idtac. Time Optimize Proof. Abort. Optimize Heap.
(* Finished transaction in 0.007 secs (0.007u,0.s) (successful) *)
Goal True. Time do 1000 let x := open_constr:(_:unit) in idtac. Time Optimize Proof. Abort. Optimize Heap.
(* Finished transaction in 0.025 secs (0.017u,0.006s) (successful) *)
Goal True. Time do 2000 let x := open_constr:(_:unit) in idtac. Time Optimize Proof. Abort. Optimize Heap.
(* Finished transaction in 0.083 secs (0.07u,0.012s) (successful) *)
Goal True. Time do 4000 let x := open_constr:(_:unit) in idtac. Time Optimize Proof. Abort. Optimize Heap.
(* Finished transaction in 0.302 secs (0.284u,0.017s) (successful) *)
Goal True. Time do 8000 let x := open_constr:(_:unit) in idtac. Time Optimize Proof. Abort. Optimize Heap.
(* Finished transaction in 1.341 secs (1.294u,0.043s) (successful) *)
Goal True. Time do 16000 let x := open_constr:(_:unit) in idtac. Time Optimize Proof. Abort. Optimize Heap.
(* Finished transaction in 6.187 secs (6.165u,0.003s) (successful) *)

Goal True. Time do 250 let x := open_constr:(_:unit) in pose x. Time Optimize Proof. Abort. Optimize Heap.
(* Finished transaction in 0.085 secs (0.062u,0.022s) (successful) *)
(* Evars: 751 -> 251 Finished transaction in 0.098 secs (0.067u,0.03s) (successful) *)
Goal True. Time do 500 let x := open_constr:(_:unit) in pose x. Time Optimize Proof. Abort. Optimize Heap.
(* Finished transaction in 0.3 secs (0.286u,0.013s) (successful) *)
(* Evars: 1501 -> 501 Finished transaction in 0.509 secs (0.505u,0.003s) (successful) *)
Goal True. Time do 1000 let x := open_constr:(_:unit) in pose x. Time Optimize Proof. Abort. Optimize Heap.
(* Finished transaction in 1.36 secs (1.327u,0.029s) (successful) *)
(* Evars: 3001 -> 1001 Finished transaction in 4.191 secs (4.172u,0.01s) (successful) *)
Goal True. Time do 2000 let x := open_constr:(_:unit) in pose x. Time Optimize Proof. Abort. Optimize Heap.
(* Finished transaction in 7.053 secs (6.866u,0.139s) (successful) *)
(* Evars: 6001 -> 2001 Finished transaction in 38.897 secs (38.714u,0.029s) (successful) *)
Goal True. Time do 4000 let x := open_constr:(_:unit) in pose x. Time Optimize Proof. Abort. Optimize Heap.
(* Finished transaction in 33.937 secs (33.338u,0.451s) (successful) *)
(* Evars: 12001 -> 4001 Finished transaction in 380.494 secs (379.115u,0.26s) (successful) *)
*)
