Require Import Coq.Strings.String.
Require Import Arith.EqNat.
Require Import ZArith.

From QuickChick Require Import QuickChick.

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
Extract Constant trace_fuel => "1000".
Fixpoint propLLNI (t : table) (v : Variation) : option bool :=
  let '(Var lab st1 st2) := v in
  if indist lab st1 st2 && well_formed st1 && well_formed st2 then
    let tr1 := trace trace_fuel t st1 in
    let tr2 := trace trace_fuel t st2 in
    Some (trace_indist lab tr1 tr2)
      (* LEO: well formedness? *)
  else None.
