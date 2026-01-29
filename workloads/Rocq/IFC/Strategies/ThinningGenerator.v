(* ThinningGenerator.v

   Thinning Loop Strategy for IFC Testing

   This module implements a thinning loop that:
   1. Generates N candidate inputs (fanout)
   2. Scores each candidate by instruction n-gram coverage improvement
   3. Picks the best candidate and runs the test
   4. Tracks seen n-grams statefully across iterations

   This is adapted from the coverage_loop_guided pattern in CoverageLoop.v.
*)

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import TestingCommon.
Require Import Reachability.
Require Import SSNI.
Require Import LLNI.
Require Import SanityChecks.
Require Import Shrinking.
Require Import Printing.
Require Import InstrCoverage.
Require Import ZArith.
Require Import List.

From mathcomp Require Import ssreflect eqtype seq.
Import LabelEqType.
Import ListNotations.

From PropLang Require Import PropLang.
From PropLang Require Import SeedPool.
From PropLang.seedpool Require Import Heap.
From PropLang.seedpool Require Import Queue.
From PropLang.loops Require Import TargetLoop.

(* Import generators from TargetedGenerator (for gen_variation_SState, failed_SState, etc.) *)
Require Import TargetedGenerator.

Local Open Scope nat_scope.
Local Open Scope prop_scope.
Local Open Scope Z_scope.

(* ------------------------------------------------------ *)
(* ------------ Configuration --------------------------- *)
(* ------------------------------------------------------ *)

(* Default fanout - number of candidates per iteration *)
Definition default_fanout : nat := 5%nat.

(* Maximum number of seen n-grams to track (bounded for efficiency) *)
Definition max_seen_ngrams : nat := 500%nat.

(* ------------------------------------------------------ *)
(* ------------ Helper Functions ------------------------ *)
(* ------------------------------------------------------ *)

(* Sequence a list of generators into a generator of lists *)
Fixpoint sequenceG_thinning {A : Type} (gs : list (G A)) : G (list A) :=
  match gs with
  | [] => ret []
  | g :: gs' =>
      bindGen g (fun x =>
      bindGen (sequenceG_thinning gs') (fun xs =>
      ret (x :: xs)))
  end.

(* Repeat a generator n times *)
Fixpoint repeat_gen {A : Type} (n : nat) (g : G A) : list (G A) :=
  match n with
  | O => []
  | S n' => g :: repeat_gen n' g
  end.

(* Get list head with default *)
Definition list_hd_thinning {A : Type} (default : A) (l : list A) : A :=
  match l with
  | [] => default
  | x :: _ => x
  end.

(* Bounded update of seen n-grams *)
Definition update_seen_bounded (new_ngrams seen : list NGram) : list NGram :=
  let combined := ngram_union new_ngrams seen in
  firstn max_seen_ngrams combined.

(* ------------------------------------------------------ *)
(* ------------ Thinning Loop Implementation ------------ *)
(* ------------------------------------------------------ *)

(* A failed variation for default cases *)
Definition failed_Variation : @Variation SState :=
  Var bot failed_SState failed_SState.

(* Shrink loop for variations *)
Fixpoint shrink_VSState_loop (n : nat) (v : @Variation SState) : @Variation SState :=
  match n with
  | O => v
  | S n' =>
      match shrinkVSState v with
      | [] => v
      | v' :: _ =>
          match propLLNI default_table v' with
          | Some false => shrink_VSState_loop n' v'
          | _ => v
          end
      end
  end.

(* Score a variation by its n-gram coverage improvement *)
Definition score_variation (seen : list NGram) (v : @Variation SState) : nat :=
  let ngrams := variation_ngrams v in
  count_new_ngrams ngrams seen.

(* Thinning loop for instruction n-gram coverage

   Parameters:
   - fuel: maximum number of test iterations
   - cprop: the property to test
   - fanout: number of candidates to generate per iteration

   This loop generates multiple candidates, picks the one with best
   coverage improvement, runs it, and tracks seen n-grams.
*)
Definition thinning_loop_instr_cov
  (fuel : nat)
  (cprop : CProp ∅)
  (fanout : nat)
  (gen_fn : ⟦∅⟧ -> G (@Variation SState))
  (mut_fn : ⟦∅⟧ -> @Variation SState -> G (@Variation SState))
  : G Result :=
  let shrink_fn := fun (_ : ⟦∅⟧) (v : @Variation SState) => shrinkVSState v in
  let show_fn := fun (_ : ⟦∅⟧) (v : @Variation SState) => show v in
  let fix aux
    (fuel : nat)
    (passed : nat)
    (discards : nat)
    (seen : list NGram)
    : G Result :=
    match fuel with
    | O => ret (mkResult discards false passed [])
    | S fuel' =>
        (* Step 1: Generate N candidates *)
        bindGen (sequenceG_thinning (repeat_gen fanout (gen_fn 0%nat))) (fun candidates =>
        (* Step 2: Score candidates by coverage improvement *)
        let scored :=
          List.map (fun v => (v, score_variation seen v)) candidates in
        (* Step 3: Pick the best candidate (highest score) *)
        let best :=
          List.fold_left (fun acc x =>
            match acc, x with
            | (_, score1), (_, score2) =>
                if Nat.ltb score1 score2 then x else acc
            end) scored (list_hd_thinning (failed_Variation, 0%nat) scored) in
        let '(best_v, best_score) := best in
        let ngrams := variation_ngrams best_v in
        (* Step 4: Run the test on the best candidate *)
        match propLLNI default_table best_v with
        | Some false =>
            (* Failure - found a bug *)
            let shrunk_v := shrink_VSState_loop 10 best_v in
            let printed := [("v"%string, show shrunk_v)] in
            ret (mkResult discards true (passed + 1)%nat printed)
        | Some true =>
            (* Pass - update coverage and continue *)
            let seen' := update_seen_bounded ngrams seen in
            aux fuel' (passed + 1)%nat discards seen'
        | None =>
            (* Discard - precondition failed *)
            aux fuel' passed (discards + 1)%nat seen
        end)
    end in
    aux fuel 0%nat 0%nat [].

(* ------------------------------------------------------ *)
(* ------------ Exported Thinning Strategies ------------ *)
(* ------------------------------------------------------ *)

Axiom number_of_trials_thin : nat.
Extract Constant number_of_trials_thin => "max_int".

(* Thinning loop with regular generator and instruction coverage *)
Definition test_ThinLoop_Gen_InstrCov : G Result :=
  thinning_loop_instr_cov
    number_of_trials_thin
    prop_LLNI
    default_fanout
    (fun _ => gen_variation_SState)
    mutate_variation_for_instruction_coverage.

(* Thinning loop with gen-by-exec generator and instruction coverage *)
Definition test_ThinLoop_GenExec_InstrCov : G Result :=
  thinning_loop_instr_cov
    number_of_trials_thin
    prop_LLNI
    default_fanout
    (fun _ => gen_variation_exec_final)
    mutate_variation_for_instruction_coverage.

