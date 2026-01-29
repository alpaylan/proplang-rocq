(* UnifiedStrategies.v

   Unified Strategy Definitions for IFC Testing

   This module defines all 8 testing strategies in a unified way:

   | # | Strategy Name              | Loop        | Generator                   | Mutator                                 | Feedback          |
   |---|----------------------------|-------------|-----------------------------|-----------------------------------------|-------------------|
   | 1 | RunLoop_Gen                | runLoop     | gen_variation_SState        | (regenerate)                            | none              |
   | 2 | RunLoop_GenExec            | runLoop     | gen_variation_exec_SState   | (regenerate)                            | none              |
   | 3 | TargetLoop_Gen_Length      | targetLoop  | gen_variation_SState        | mutate_variation_for_length             | trace length      |
   | 4 | TargetLoop_Gen_InstrCov    | targetLoop  | gen_variation_SState        | mutate_variation_for_instruction_coverage | instruction n-grams |
   | 5 | TargetLoop_GenExec_Length  | targetLoop  | gen_variation_exec_SState   | mutate_variation_for_length             | trace length      |
   | 6 | TargetLoop_GenExec_InstrCov| targetLoop  | gen_variation_exec_SState   | mutate_variation_for_instruction_coverage | instruction n-grams |
   | 7 | ThinLoop_Gen_InstrCov      | thinning    | gen_variation_SState        | mutate_variation_for_instruction_coverage | instruction n-grams |
   | 8 | ThinLoop_GenExec_InstrCov  | thinning    | gen_variation_exec_SState   | mutate_variation_for_instruction_coverage | instruction n-grams |

   All strategies test the LLNI property. The different configurations vary only
   in their generation/mutation approach, not the property being tested.
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

(* Import existing strategies for generators and mutators *)
Require Import TargetedGenerator.
Require Import BespokeGenerator.

Local Open Scope nat_scope.
Local Open Scope prop_scope.
Local Open Scope Z_scope.

(* ------------------------------------------------------ *)
(* ------------ Configuration Constants ----------------- *)
(* ------------------------------------------------------ *)

Axiom unified_number_of_trials : nat.
Extract Constant unified_number_of_trials => "max_int".

(* Extraction directive for Nat.min to avoid OCaml recursive binding issue *)
Extract Inlined Constant Nat.min => "(fun a b -> if a < b then a else b)".

(* Fanout for thinning loop *)
Definition thinning_fanout : nat := 5%nat.

(* ------------------------------------------------------ *)
(* ------------ Common Property Definition -------------- *)
(* ------------------------------------------------------ *)

(* The shared LLNI Check - this is what all strategies test *)
Definition llni_check : @Variation SState -> bool :=
  fun v =>
    match propLLNI default_table v with
    | Some true => true
    | Some false => false
    | None => true  (* Treat precondition failure as pass for property check *)
    end.

(* Common shrinker and printer *)
Definition unified_shrink_variation (_ : ⟦∅⟧) (v : @Variation SState) : list (@Variation SState) :=
  shrinkVSState v.

Definition unified_show_variation (_ : ⟦∅⟧) (v : @Variation SState) : string := show v.

(* ------------------------------------------------------ *)
(* ------------ Strategy 1: RunLoop_Gen ----------------- *)
(* ------------------------------------------------------ *)

(* Property with regular generator, simple regeneration as mutation *)
Definition prop_RunLoop_Gen :=
  ForAll "v"
    (fun _ => gen_variation_SState)
    (fun _ _ => gen_variation_SState)  (* Regenerate on mutation *)
    unified_shrink_variation
    unified_show_variation
  (Check (@Variation SState · ∅)
    (fun '(v, _) => llni_check v)).

Definition test_RunLoop_Gen : G Result :=
  runLoop unified_number_of_trials prop_RunLoop_Gen.

(* ------------------------------------------------------ *)
(* ------------ Strategy 2: RunLoop_GenExec ------------- *)
(* ------------------------------------------------------ *)

(* Property with gen-by-exec generator *)
Definition prop_RunLoop_GenExec :=
  ForAll "v"
    (fun _ => gen_variation_exec_final)
    (fun _ _ => gen_variation_exec_final)  (* Regenerate on mutation *)
    unified_shrink_variation
    unified_show_variation
  (Check (@Variation SState · ∅)
    (fun '(v, _) => llni_check v)).

Definition test_RunLoop_GenExec : G Result :=
  runLoop unified_number_of_trials prop_RunLoop_GenExec.

(* ------------------------------------------------------ *)
(* ------------ Strategy 3: TargetLoop_Gen_Length ------- *)
(* ------------------------------------------------------ *)

(* Property with regular generator and length-based mutation *)
Definition prop_TargetLoop_Gen_Length :=
  ForAll "v"
    (fun _ => gen_variation_SState)
    mutate_variation_for_length
    unified_shrink_variation
    unified_show_variation
  (Check (@Variation SState · ∅)
    (fun '(v, _) => llni_check v)).

Definition test_TargetLoop_Gen_Length : G Result :=
  targetLoop
    unified_number_of_trials
    prop_TargetLoop_Gen_Length
    (fun input => feedback_fn (fst input))
    (FIFOSeedPool.(mkPool) tt)
    HillClimbingUtility.

(* ------------------------------------------------------ *)
(* ------------ Strategy 4: TargetLoop_Gen_InstrCov ----- *)
(* ------------------------------------------------------ *)

(* Property with regular generator and instruction coverage mutation *)
Definition prop_TargetLoop_Gen_InstrCov :=
  ForAll "v"
    (fun _ => gen_variation_SState)
    mutate_variation_for_instruction_coverage
    unified_shrink_variation
    unified_show_variation
  (Check (@Variation SState · ∅)
    (fun '(v, _) => llni_check v)).

(* Feedback function: use n-gram diversity *)
Definition feedback_instr_cov (input : @Variation SState * nat) : Z :=
  feedback_ngram_diversity tt (fst input).

Definition test_TargetLoop_Gen_InstrCov : G Result :=
  targetLoop
    unified_number_of_trials
    prop_TargetLoop_Gen_InstrCov
    feedback_instr_cov
    (FIFOSeedPool.(mkPool) tt)
    HillClimbingUtility.

(* ------------------------------------------------------ *)
(* ------------ Strategy 5: TargetLoop_GenExec_Length --- *)
(* ------------------------------------------------------ *)

(* Property with gen-by-exec generator and length-based mutation *)
Definition prop_TargetLoop_GenExec_Length :=
  ForAll "v"
    (fun _ => gen_variation_exec_final)
    mutate_variation_for_length
    unified_shrink_variation
    unified_show_variation
  (Check (@Variation SState · ∅)
    (fun '(v, _) => llni_check v)).

Definition test_TargetLoop_GenExec_Length : G Result :=
  targetLoop
    unified_number_of_trials
    prop_TargetLoop_GenExec_Length
    (fun input => feedback_fn (fst input))
    (FIFOSeedPool.(mkPool) tt)
    HillClimbingUtility.

(* ------------------------------------------------------ *)
(* ------------ Strategy 6: TargetLoop_GenExec_InstrCov - *)
(* ------------------------------------------------------ *)

(* Property with gen-by-exec generator and instruction coverage mutation *)
Definition prop_TargetLoop_GenExec_InstrCov :=
  ForAll "v"
    (fun _ => gen_variation_exec_final)
    mutate_variation_for_instruction_coverage
    unified_shrink_variation
    unified_show_variation
  (Check (@Variation SState · ∅)
    (fun '(v, _) => llni_check v)).

Definition test_TargetLoop_GenExec_InstrCov : G Result :=
  targetLoop
    unified_number_of_trials
    prop_TargetLoop_GenExec_InstrCov
    feedback_instr_cov
    (FIFOSeedPool.(mkPool) tt)
    HillClimbingUtility.

(* ------------------------------------------------------ *)
(* ------------ Thinning Loop Helper -------------------- *)
(* ------------------------------------------------------ *)

(* Sequence a list of generators *)
Fixpoint sequenceG_unified {A : Type} (gs : list (G A)) : G (list A) :=
  match gs with
  | [] => ret []
  | g :: gs' =>
      bindGen g (fun x =>
      bindGen (sequenceG_unified gs') (fun xs =>
      ret (x :: xs)))
  end.

(* Repeat a generator n times *)
Fixpoint repeat_gen_unified {A : Type} (n : nat) (g : G A) : list (G A) :=
  match n with
  | O => []
  | S n' => g :: repeat_gen_unified n' g
  end.

(* Failed variation for defaults *)
Definition unified_failed_Variation : @Variation SState :=
  Var bot failed_SState failed_SState.

(* Shrink loop *)
Fixpoint unified_shrink_loop (n : nat) (v : @Variation SState) : @Variation SState :=
  match n with
  | O => v
  | S n' =>
      match shrinkVSState v with
      | [] => v
      | v' :: _ =>
          match propLLNI default_table v' with
          | Some false => unified_shrink_loop n' v'
          | _ => v
          end
      end
  end.

(* Bounded seen set update *)
Definition max_seen : nat := 500%nat.

Definition update_seen (new_ngrams seen : list NGram) : list NGram :=
  firstn max_seen (ngram_union new_ngrams seen).

(* Score a variation *)
Definition unified_score (seen : list NGram) (v : @Variation SState) : nat :=
  count_new_ngrams (variation_ngrams v) seen.

(* Generic thinning loop *)
Definition thinning_loop
  (fuel : nat)
  (fanout : nat)
  (gen_fn : unit -> G (@Variation SState))
  : G Result :=
  let fix aux
    (fuel : nat)
    (passed : nat)
    (discards : nat)
    (seen : list NGram)
    : G Result :=
    match fuel with
    | O => ret (mkResult discards false passed [])
    | S fuel' =>
        (* Generate N candidates *)
        bindGen (sequenceG_unified (repeat_gen_unified fanout (gen_fn tt))) (fun candidates =>
        (* Score and pick best *)
        let scored := List.map (fun v => (v, unified_score seen v)) candidates in
        let default := (unified_failed_Variation, 0%nat) in
        let best :=
          List.fold_left (fun acc x =>
            match acc, x with
            | (_, s1), (_, s2) => if Nat.ltb s1 s2 then x else acc
            end) scored default in
        let '(best_v, _) := best in
        let ngrams := variation_ngrams best_v in
        (* Run test *)
        match propLLNI default_table best_v with
        | Some false =>
            let shrunk := unified_shrink_loop 10 best_v in
            ret (mkResult discards true (passed + 1)%nat [("v"%string, show shrunk)])
        | Some true =>
            aux fuel' (passed + 1)%nat discards (update_seen ngrams seen)
        | None =>
            aux fuel' passed (discards + 1)%nat seen
        end)
    end in
    aux fuel 0%nat 0%nat [].

(* ------------------------------------------------------ *)
(* ------------ Strategy 7: ThinLoop_Gen_InstrCov ------- *)
(* ------------------------------------------------------ *)

Definition test_ThinLoop_Gen_InstrCov : G Result :=
  thinning_loop
    unified_number_of_trials
    thinning_fanout
    (fun _ => gen_variation_SState).

(* ------------------------------------------------------ *)
(* ------------ Strategy 8: ThinLoop_GenExec_InstrCov --- *)
(* ------------------------------------------------------ *)

Definition test_ThinLoop_GenExec_InstrCov : G Result :=
  thinning_loop
    unified_number_of_trials
    thinning_fanout
    (fun _ => gen_variation_exec_final).

