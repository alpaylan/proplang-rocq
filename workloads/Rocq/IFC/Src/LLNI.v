Require Import Coq.Strings.String.
Require Import Arith.EqNat.
Require Import ZArith.

From QuickChick Require Import QuickChick.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

Require Import Rules.
Require Import Machine.
Require Import TestingCommon.
Require Import Printing.

Open Scope string_scope.

Require Import Reachability.

Definition is_low lab st := isLow (pc_lab (st_pc st)) lab.

Fixpoint trace (n : nat) (t: table) (s : SState) : list SState :=
  match n, fstep t s with
  | S n', Some s' => s :: trace n' t s'
  | _, _ => cons s nil
  end.

Definition trace_indist (o : Label) (t1 t2 : list SState) : bool :=  
  let low1 := List.filter (is_low o) t1 in
  let low2 := List.filter (is_low o) t2 in
  List.forallb id (List.map (fun sts => indist o (fst sts) (snd sts)) (List.combine low1 low2)).

Axiom trace_fuel : nat.
Extract Constant trace_fuel => "10000".
Fixpoint propLLNI (t : table) (v : Variation) : option bool :=
  let '(Var lab st1 st2) := v in
  if indist lab st1 st2 && well_formed st1 && well_formed st2 then
    let tr1 := trace trace_fuel t st1 in
    let tr2 := trace trace_fuel t st2 in
    Some (trace_indist lab tr1 tr2)
      (* LEO: well formedness? *)
  else None.

(* ========================================================================= *)
(* Concrete LLNI Test Cases                                                    *)
(* ========================================================================= *)
(*
   These tests demonstrate information flow via secret-dependent branching.
   Two states differ only in a high-labeled (secret) register value.
   A BNZ instruction branches based on this secret.

   With the CORRECT default_table:
   - The BNZ rule is: JOIN (Lab1) (LabPC)
   - After BNZ, the new PC label becomes H ∪ L = H (high)
   - The L-observer cannot see the high-labeled PC difference
   - LLNI property PASSES (Some true) - as expected!

   With a BUGGY table (e.g., OpBNZ_3 mutation: LabPC only):
   - The new PC label stays L (ignoring the secret influence)
   - The L-observer can see the different PC addresses
   - LLNI property FAILS (Some false) - bug detected!
*)

Section LLNITestCases.

(* Instruction memory: BNZ branches by 2 if r0 != 0 *)
Definition test_imem : imem :=
  [:: BNZ 2%Z 0%Z; Nop; Halt].

(* State 1: Secret register r0 = 0 (will NOT branch) *)
Definition test_st1 : SState :=
  St test_imem
     (Memory.empty Atom)
     (ST [::])
     [:: Vint 0%Z @ H]   (* r0 = 0 with High label - secret *)
     (PAtm 0%Z L).       (* PC at address 0 with Low label - observable *)

(* State 2: Secret register r0 = 1 (will branch) *)
Definition test_st2 : SState :=
  St test_imem
     (Memory.empty Atom)
     (ST [::])
     [:: Vint 1%Z @ H]   (* r0 = 1 with High label - different secret! *)
     (PAtm 0%Z L).       (* Same observable PC *)

(* The variation: observer at level L *)
Definition test_variation : @Variation SState :=
  Var L test_st1 test_st2.

(*
   *** Testing with default_table (CORRECT implementation) ***

   Compute propLLNI default_table test_variation.

   Expected result with default_table: None OR Some true
   - None: because well_formed requires reachability computation which
     doesn't fully reduce in Coq's Compute.
   - If it did reduce: Some true because the correct BNZ rule taints the PC
     with the register label, making the divergent PCs HIGH (not observable).
*)

(* === Buggy table for testing: PC label doesn't get tainted === *)

Definition buggy_table_bnz : table := fun op =>
  match op with
  | OpBNZ => ≪ TRUE , __ , LabPC ≫   (* BUG: ignores register label! *)
  | _ => default_table op
  end.

(*
   *** Testing with buggy_table_bnz (BUGGY implementation) ***

   Compute propLLNI buggy_table_bnz test_variation.

   Expected result with buggy table: Some false
   - After BNZ, the new PC label stays L (not tainted with H)
   - st1 goes to PC address 1 with label L
   - st2 goes to PC address 2 with label L
   - L-observer can see addresses 1 vs 2 -> information leak detected!
*)

(*
   Execution trace analysis:

   Initial state (both st1 and st2):
   - imem: [BNZ 2 0; Nop; Halt]
   - PC: (0, L) - address 0, Low label

   After one step with buggy_table_bnz:
   - st1: r0 = 0, so m == 0, PC -> (j+1) = (0+1, L) = (1, L)
   - st2: r0 = 1 != 0, so PC -> (j+n) = (0+2, L) = (2, L)

   Both PCs have label L (observable to L-observer).
   PC addresses are 1 vs 2 (different and visible).
   -> LLNI violated! trace_indist returns false.
*)

End LLNITestCases.
