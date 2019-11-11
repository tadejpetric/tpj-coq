(* izjave ... tipi *)
(* dokazi ... izrazi *)
(*    T   ... unit *)
(* P => Q ... 'p -> 'q *)
(* P /\ Q ... 'p * 'q *)
(* P \/ Q ... 'p + 'q *)
type ('p, 'q) sum =
  | Inl of 'p (* : ('p, 'q) sum *)
  | Inr of 'q (* : ('p, 'q) sum *)

let f : string = "bla bla"
let f (x : int) : bool = x > 10
let f : int -> bool = fun x -> x > 10

(* ((P => Q) /\ P) => Q *)
let modus_ponens : ('p -> 'q) * 'p -> 'q =
  fun (h_p_sledi_q, h_p) -> h_p_sledi_q h_p

(* P /\ Q => Q /\ P *)
let and_comm : 'p * 'q -> 'q * 'p =
  fun (h_p, h_q) -> (h_q, h_p)

(* P \/ Q => Q \/ P *)
let or_comm : ('p, 'q) sum -> ('q, 'p) sum =
  fun h_p_ali_q -> 
    match h_p_ali_q with
    | Inl h_p -> Inr h_p
    | Inr h_q -> Inl h_q

(* (P \/ Q) /\ R => (P /\ R) \/ (Q /\ R) *)

(* (P /\ Q) \/ R => (P \/ R) /\ (Q \/ R) *)

(* ((P => R) /\ (Q => R)) <=> ((P \/ Q) => R) *)
let disj_elim : ('p -> 'r) * ('q -> 'r) -> (('p, 'q) sum -> 'r) =
 fun (h_p_r, h_q_r) ->
   function
   | Inl h_p -> h_p_r h_p
   | Inr h_q -> h_q_r h_q

let disj_elim' : (('p, 'q) sum -> 'r) -> ('p -> 'r) * ('q -> 'r) =
  fun h_p_ali_q_sledi_r ->
  (
    (fun h_p_r -> h_p_ali_q_sledi_r (Inl h_p_r)),
    (fun h_q_r ->  h_p_ali_q_sledi_r (Inr h_q_r))
  )

(* P \/ Q => P /\ Q *)
let disj_conj : ('p, 'q) sum -> 'p * 'q =
  fun h_p_ali_q -> failwith "Dokaz prepustimo za vajo"

let disj_conj' : ('p, 'q) sum -> 'p * 'q =
  fun h_p_ali_q ->
    let rec dokaz () = dokaz () in
    dokaz ()
