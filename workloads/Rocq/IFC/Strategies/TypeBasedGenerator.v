From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import TestingCommon.
Require Import Reachability.
Require Import SSNI.
Require Import SanityChecks.
Require Import Shrinking.
Require Import Printing.
Require Import ZArith.

From mathcomp Require Import ssreflect eqtype seq.
Import LabelEqType.

From PropLang Require Import PropLang.

Local Open Scope prop_scope.

Derive Arbitrary for BinOpT.
Derive Arbitrary for Instr.
Derive Arbitrary for Pointer.
Derive Arbitrary for Value.
Derive Arbitrary for Atom.
Derive Arbitrary for Ptr_atom.
Derive Arbitrary for StackFrame.
Derive Arbitrary for Stack.
Derive Arbitrary for SState.
Derive Arbitrary for Variation.

(* PropLang definitions *)

Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".

Definition shrink_variation (_ : ⟦∅⟧) (v : @Variation SState) : list (@Variation SState) :=
  shrinkVSState v.

Definition show_variation_fn (_ : ⟦∅⟧) (v : @Variation SState) : string := show v.

Definition prop_SSNI :=
  ForAll "v"
    (fun _ => arbitrary)
    (fun _ _ => arbitrary)
    shrink_variation
    show_variation_fn
  (Check (@Variation SState · ∅)
    (fun '(v, _) =>
      match propSSNI_smart default_table v with
      | Some true => true
      | Some false => false
      | None => true
      end)).

Definition test_prop_SSNI := runLoop number_of_trials prop_SSNI.
(*! QuickProp test_prop_SSNI. *)
