


Fixpoint repeat {A : Type} (n : nat) (x : A) : list A :=
  match n with
  | O => []
  | S n' => x :: repeat n' x
  end.

(* Coverage is a  *)
Class Coverage {A : Type} :=
  {
    coverage_metric : A -> Z;
  }.


Definition coverage_loop (fuel : nat) (cprop : CProp ∅): G Result :=  
  let fix aux
    (fuel : nat) 
    (cprop : CProp ∅) 
    (passed : nat)
    (discards: nat)
    : G Result :=
    match fuel with
    | O => ret (mkResult discards false passed [])
    | S fuel' => 
        inputs 
        match res with
        | Normal seed false =>
            (* Fails *)
            let shrunk := shrinker cprop seed in
            let printed := printer cprop shrunk in
            ret (mkResult discards true (passed + 1) printed)
        | Normal _ true =>
            (* Passes *)
            aux fuel' cprop (passed + 1)%nat discards
        | Discard _ _ => 
          (* Discard *)
          aux fuel' cprop passed (discards + 1)%nat
        end
    end in
    aux fuel cprop 0%nat 0%nat
    .

