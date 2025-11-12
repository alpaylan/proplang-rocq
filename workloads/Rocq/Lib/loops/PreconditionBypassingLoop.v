

Definition runLoopBypassPreconditions (fuel : nat) (cprop : CProp ∅): G Result :=  
  let fix runLoop'
    (fuel : nat) 
    (cprop : CProp ∅) 
    (passed : nat)
    (discards: nat)
    : G Result :=
    match fuel with
    | O => ret (mkResult discards false passed [])
    | S fuel' => 
        res <- generate_and_run_bypassing_preconditions cprop (log2 (passed + discards)%nat);;
        match res with
        | Normal seed false =>
            (* Fails *)
            let shrunk := shrinker cprop seed in
            let printed := printer cprop shrunk in
            ret (mkResult discards true (passed + 1) printed)
        | Normal _ true =>
            (* Passes *)
            runLoop' fuel' cprop (passed + 1)%nat discards
        | Discard _ _ => 
          (* Discard *)
          runLoop' fuel' cprop passed (discards + 1)%nat
        end
    end in
    runLoop' fuel cprop 0%nat 0%nat
    .

    