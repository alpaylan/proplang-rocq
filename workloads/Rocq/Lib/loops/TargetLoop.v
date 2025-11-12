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


Definition targetLoop
  (fuel : nat) 
  (cprop : CProp ∅)
  (feedback_function: ⟦⦗cprop⦘⟧ -> Z)
  {Pool : Type}
  {poolType: @SeedPool (⟦⦗cprop⦘⟧) Z Pool}
  (seeds : Pool)
  (utility: Utility) : G Result :=
  let fix targetLoop' 
         (fuel : nat) 
         (passed : nat)
         (discards: nat)
         {Pool : Type}
         (seeds : Pool)
         (poolType: @SeedPool (⟦⦗cprop⦘⟧) Z Pool)
         (utility: Utility) : G Result :=
        match fuel with
        | O => ret (mkResult discards false passed [])
        | S fuel' => 
            let directive := sample seeds in
            input <- generator cprop directive (log2 (passed + discards));;
            match lift_opt_cprop cprop input with
            | None =>
                let seeds' := match directive with
                            | Generate => seeds
                            | Mutate _ => revise seeds
                            end in
                targetLoop' fuel' passed (discards + 1) seeds' poolType utility
            | Some input =>
							let '(result, feedback) := instrumented_runner cprop with_instrumentation input in
							match result with
							| Some false =>
									(* Fails *)
									let shrunk := shrinker cprop input in
									let printed := printer cprop shrunk in
									ret (mkResult discards true (passed + 1) printed)
							| Some true =>
									(* Passes *)
									let feedback := feedback_function input in
									match useful seeds feedback with
									| true =>
											let seeds' := invest (input, feedback) seeds in
											targetLoop' fuel' (passed + 1) discards seeds' poolType utility
									| false =>
											let seeds' := match directive with
																		| Generate => seeds
																		| Mutate source => revise seeds
																		end in
											targetLoop' fuel' (passed + 1) discards seeds' poolType utility
									end
							| None =>
									(* Discard *)
									targetLoop' fuel' passed (discards + 1) seeds poolType utility
							end
						end
        end in
        targetLoop' fuel 0 0 seeds poolType utility.


