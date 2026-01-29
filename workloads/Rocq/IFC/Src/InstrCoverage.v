(* Instruction Coverage Module

   This module provides instruction n-gram based coverage tracking for
   property-based testing of IFC programs. It extracts sequences of opcodes
   from instruction memory and provides feedback functions for guiding test
   generation toward greater instruction diversity.
*)

From QuickChick Require Import QuickChick.
Require Import List ZArith.
Import ListNotations.

From mathcomp Require Import ssreflect eqtype seq.

Require Import Instructions.
Require Import Machine.
Require Import TestingCommon.

Local Open Scope Z_scope.
Local Open Scope list_scope.

(* ------------------------------------------------------ *)
(* ---------- OpCode Extraction ------------------------- *)
(* ------------------------------------------------------ *)

(* Extract opcode from an instruction *)
Definition opcode_of_instr_opt (i : @Instr Label) : option OpCode :=
  opcode_of_instr i.

(* Extract all opcodes from instruction memory, filtering out None (Halt) *)
Definition extract_opcodes (imem : list (@Instr Label)) : list OpCode :=
  List.fold_right
    (fun i acc =>
      match opcode_of_instr_opt i with
      | Some op => op :: acc
      | None => acc
      end)
    [] imem.

(* ------------------------------------------------------ *)
(* ---------- N-gram Extraction ------------------------- *)
(* ------------------------------------------------------ *)

(* Extract pairs (bigrams) from a list *)
Fixpoint bigrams {A : Type} (xs : list A) : list (A * A) :=
  match xs with
  | [] => []
  | [_] => []
  | x :: (y :: _ as rest) => (x, y) :: bigrams rest
  end.

(* Extract triples (trigrams) from a list *)
Fixpoint trigrams {A : Type} (xs : list A) : list (A * A * A) :=
  match xs with
  | [] => []
  | [_] => []
  | [_; _] => []
  | x :: (y :: z :: _ as rest) => (x, y, z) :: trigrams rest
  end.

(* Combined n-gram type - either a pair or triple of opcodes *)
Inductive NGram :=
| Bigram : OpCode -> OpCode -> NGram
| Trigram : OpCode -> OpCode -> OpCode -> NGram.

(* Decidable equality for NGram *)
Definition ngram_eq_dec (n1 n2 : NGram) : {n1 = n2} + {n1 <> n2}.
Proof.
  destruct n1 as [o1 o2 | o1 o2 o3];
  destruct n2 as [o1' o2' | o1' o2' o3'].
  - destruct (opCode_eq_dec o1 o1'); destruct (opCode_eq_dec o2 o2');
    try (right; intro H; inversion H; contradiction).
    left; subst; reflexivity.
  - right; intro H; discriminate.
  - right; intro H; discriminate.
  - destruct (opCode_eq_dec o1 o1'); destruct (opCode_eq_dec o2 o2');
    destruct (opCode_eq_dec o3 o3');
    try (right; intro H; inversion H; contradiction).
    left; subst; reflexivity.
Defined.

Definition ngram_eqb (n1 n2 : NGram) : bool :=
  match ngram_eq_dec n1 n2 with
  | left _ => true
  | right _ => false
  end.

(* Extract all n-grams (bigrams and trigrams) from instruction memory *)
Definition instr_ngrams (imem : list (@Instr Label)) : list NGram :=
  let ops := extract_opcodes imem in
  let bi := List.map (fun '(x, y) => Bigram x y) (bigrams ops) in
  let tri := List.map (fun '(x, y, z) => Trigram x y z) (trigrams ops) in
  bi ++ tri.

(* Extract n-grams from an SState *)
Definition state_ngrams (st : SState) : list NGram :=
  instr_ngrams (st_imem st).

(* Extract n-grams from a Variation (union of both states' n-grams) *)
Definition variation_ngrams (v : @Variation SState) : list NGram :=
  let '(Var _ st1 st2) := v in
  state_ngrams st1 ++ state_ngrams st2.

(* ------------------------------------------------------ *)
(* ---------- N-gram Set Operations --------------------- *)
(* ------------------------------------------------------ *)

(* Check if an n-gram is in a list *)
Fixpoint ngram_mem (n : NGram) (ns : list NGram) : bool :=
  match ns with
  | [] => false
  | n' :: rest =>
      match ngram_eq_dec n n' with
      | left _ => true
      | right _ => ngram_mem n rest
      end
  end.

(* Remove duplicates from an n-gram list *)
Fixpoint ngram_nub (ns : list NGram) : list NGram :=
  match ns with
  | [] => []
  | n :: rest =>
      if ngram_mem n rest then ngram_nub rest else n :: ngram_nub rest
  end.

(* Count new n-grams not in the seen set *)
Definition count_new_ngrams (current seen : list NGram) : nat :=
  List.length (List.filter (fun n => negb (ngram_mem n seen)) current).

(* Union of two n-gram sets *)
Definition ngram_union (ns1 ns2 : list NGram) : list NGram :=
  ngram_nub (ns1 ++ ns2).

(* ------------------------------------------------------ *)
(* ---------- Feedback Functions ------------------------ *)
(* ------------------------------------------------------ *)

(* Feedback function for instruction coverage:
   Returns (count of new n-grams, updated seen set) *)
Definition feedback_instruction_coverage
  (seen : list NGram)
  (v : @Variation SState) : Z * list NGram :=
  let current := variation_ngrams v in
  let new_count := count_new_ngrams current seen in
  let seen' := ngram_union current seen in
  (Z.of_nat new_count, seen').

(* Simple feedback function that just returns the n-gram count improvement *)
Definition feedback_ngram_count
  (ctx : unit)
  (v : @Variation SState) : Z :=
  Z.of_nat (List.length (ngram_nub (variation_ngrams v))).

(* Stateful feedback for use with targetLoop - tracks the maximum seen *)
Definition feedback_ngram_diversity (_ : unit) (v : @Variation SState) : Z :=
  let ngrams := ngram_nub (variation_ngrams v) in
  Z.of_nat (List.length ngrams).

(* ------------------------------------------------------ *)
(* ---------- Instruction Diversity Metrics ------------- *)
(* ------------------------------------------------------ *)

(* Helper for opcode equality as bool *)
Definition opcode_eqb (x y : OpCode) : bool :=
  match opCode_eq_dec x y with
  | left _ => true
  | right _ => false
  end.

(* Count unique opcodes in an SState *)
Definition unique_opcode_count (st : SState) : nat :=
  let ops := extract_opcodes (st_imem st) in
  let fix nub_count (seen : list OpCode) (xs : list OpCode) : nat :=
    match xs with
    | [] => List.length seen
    | x :: rest =>
        if existsb (opcode_eqb x) seen
        then nub_count seen rest
        else nub_count (x :: seen) rest
    end
  in nub_count [] ops.

(* Count unique opcodes across a variation *)
Definition variation_unique_opcodes (v : @Variation SState) : nat :=
  let '(Var _ st1 st2) := v in
  let ops1 := extract_opcodes (st_imem st1) in
  let ops2 := extract_opcodes (st_imem st2) in
  let fix nub_count (seen : list OpCode) (xs : list OpCode) : nat :=
    match xs with
    | [] => List.length seen
    | x :: rest =>
        if existsb (opcode_eqb x) seen
        then nub_count seen rest
        else nub_count (x :: seen) rest
    end
  in nub_count [] (ops1 ++ ops2).

(* Combined feedback: weighted sum of n-gram diversity and unique opcodes *)
Definition feedback_combined_diversity (_ : unit) (v : @Variation SState) : Z :=
  let ngram_score := Z.of_nat (List.length (ngram_nub (variation_ngrams v))) in
  let opcode_score := Z.of_nat (variation_unique_opcodes v) in
  (* Weight n-grams more since they capture sequential patterns *)
  ngram_score * 2 + opcode_score.

