From Ltac2 Require Import Ltac2.
Declare ML Module "zesu-signature-gates.plugin".
Set Default Proof Mode "Classic".

(* Per-proof solver failure memo. The wrapped solver sites are deterministic
   and their budgets count nodes, so a site that failed on a goal fails again
   on the same conclusion with the same context. Within one proof, the memo
   records each failure under a key that hashes the site, the conclusion and
   every declaration of the context (name, type and body, through defined
   evars); the next call with that key fails at once. Only failures are
   recorded: a success is never assumed, so the memo can only make a search
   fail earlier. A changed or grown context (any declaration) is a new key.
   A goal or context with an undefined evar has no key and runs the site. *)
Ltac2 @ external zesu_failure_memo_key : string -> int list :=
  "zesu-signature-gates.plugin" "failure_memo_key".
Ltac2 @ external zesu_failure_memo_failed : int list -> bool :=
  "zesu-signature-gates.plugin" "failure_memo_failed".
Ltac2 @ external zesu_failure_memo_record : int list -> unit :=
  "zesu-signature-gates.plugin" "failure_memo_record".

(* A failure after a success (backtracking into the site) is not recorded.
   The key needs exactly one focused goal; with several goals or none (a
   site run on all side goals of a `by`), the site runs unmemoized:
   Control.goal would throw Not_focussed, which Control.case does not catch. *)
Ltac2 zesu_failure_memo (site : string) (tac : unit -> 'a) : 'a :=
  let goals := Ref.ref 0 in
  Control.enter (fun () => Ref.set goals (Int.add (Ref.get goals) 1));
  let key :=
    if Int.equal (Ref.get goals) 1 then
      match Control.case (fun () => zesu_failure_memo_key site) with
      | Val (key, _) => key
      | Err _ => []
      end
    else [] in
  match key with
  | [] => tac ()
  | _ :: _ =>
      if zesu_failure_memo_failed key then
        Control.zero (Tactic_failure (Some (Message.of_string
          "zesu_failure_memo: this site failed on this goal and context")))
      else
        let succeeded := Ref.ref false in
        Control.plus (fun () =>
            let result := tac () in
            Ref.set succeeded true;
            result)
          (fun error =>
            (if Ref.get succeeded then () else zesu_failure_memo_record key);
            Control.zero error)
  end.

(* Ltac1 sites bind the site name with
   `ltac2:(tac |- zesu_failure_memo_ltac1 "site" tac)`. *)
Ltac2 zesu_failure_memo_ltac1 (site : string) (tac : Ltac1.t) :=
  zesu_failure_memo site (fun () => Ltac1.run tac).
