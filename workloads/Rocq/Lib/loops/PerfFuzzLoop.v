Require Import String ZArith List Nat.

From QuickChick Require Import QuickChick.
From PropLang Require Import PropLang SeedPool.

Import ListNotations.
Import QcNotation.
Import MonadNotation.


Local Open Scope string.
Local Open Scope qc_scope.
Local Open Scope Z.
Local Open Scope nat_scope.
Local Open Scope prop_scope.

Record PerfResult := mkPerfResult {
  perf_passed: nat;
  perf_discards: nat;
  best_seed: list (string * string);
  best_feedback: Z; 
}.

#[global] Instance showPerfResult : Show PerfResult :=
{| show r := """discards"": " ++ show (perf_discards r) ++
            ", ""foundbug"": false" ++
            ", ""passed"": " ++ show (perf_passed r) ++
            ", ""counterexample"": """ ++  show_elem_list (best_seed r) ++ """" ++
            ", ""counterexample_time"": """ ++  show (best_feedback r) ++ """"
|}.


Definition with_timing : (unit -> bool) -> (bool * (bool * nat)) :=
  fun f => 
    let '(TResult result time start ending) := withTime f in
    (result, (true, (float_of_nat time))).


Definition perfFuzzLoop
      (fuel : nat) 
      (cprop : CProp ∅)
      {Pool : Type}
      {poolType: @SeedPool (⟦⦗cprop⦘⟧) Z Pool}
      (seeds : Pool)
      (utility: Utility) : G PerfResult :=
      let fix fuzzLoop' 
              (fuel : nat) 
              (passed : nat)
              (discards: nat)
              {Pool : Type}
              (seeds : Pool)
              (poolType: @SeedPool (⟦⦗cprop⦘⟧) Z Pool)
              (utility: Utility)
              (best_seed: (option (⟦⦗cprop⦘⟧ * Z)))
              : G PerfResult :=
            match fuel with
            | O => match best_seed with
                  | None => ret (mkPerfResult passed discards [] 0)
                  | Some (seed, feedback) =>
                    let printed := printer cprop seed in
                    ret (mkPerfResult passed discards printed feedback)
                  end
            | S fuel' => 
                let directive := sample seeds in
                input <- generator cprop directive (log2 (passed + discards));;
                match lift_opt_cprop cprop input with
                | None =>
                  let seeds' := match directive with
                                    | Generate => seeds
                                    | Mutate _ => revise seeds
                                    end in
                  fuzzLoop' fuel' passed (discards + 1) seeds' poolType utility best_seed
                | Some input =>
                  let '(result, feedback) := instrumented_runner cprop with_timing input in
                  match result with
                  | Some _ =>
                      (* Passes *)
                      match useful seeds feedback with
                      | true =>
                          let seeds' := invest (input, feedback) 
                          seeds in
                          let best_seed' := match best_seed with
                                            | Some (best_seed, best_feedback) => 
                                              if (feedback >? best_feedback) then Some (input, feedback)
                                              else Some (best_seed, best_feedback)
                                            | None => Some (input, feedback)
                                            end in
                          fuzzLoop' fuel' (passed + 1) discards seeds' poolType utility best_seed'
                      | false =>
                          let seeds' := match directive with
                                        | Generate => seeds
                                        | Mutate _ => revise seeds
                                        end in
                          fuzzLoop' fuel' (passed + 1) discards seeds' poolType utility best_seed
                      end
                  | None => 
                      fuzzLoop' fuel' passed (discards+1) (revise seeds) poolType utility best_seed
                  end
                end
            end in
          fuzzLoop' fuel 0 0 seeds poolType utility None.
