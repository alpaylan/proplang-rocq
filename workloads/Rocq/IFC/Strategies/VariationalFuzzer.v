From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import MonadNotation.

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
From PropLang Require Import SeedPool.
From PropLang.seedpool Require Import Heap.
From PropLang.seedpool Require Import Queue.
From PropLang.loops Require Import FuzzLoop.

Local Open Scope prop_scope.

#[local] Instance FuzzyZ : Fuzzy Z :=
  {| fuzz n := choose (n - 5, n + 5)%Z |}.

Derive (Arbitrary, Fuzzy) for BinOpT.
Derive (Arbitrary, Fuzzy) for Instr.
Derive (Arbitrary, Fuzzy) for Pointer.
Derive (Arbitrary, Fuzzy) for Value.
Derive (Arbitrary, Fuzzy) for Atom.
Derive (Arbitrary, Fuzzy) for Ptr_atom.
Derive (Arbitrary, Fuzzy) for StackFrame.
Derive (Arbitrary, Fuzzy) for Stack.
Derive (Arbitrary, Fuzzy) for SState.
Derive (Arbitrary, Fuzzy) for Variation.

(* Custom generator that creates a variation with identical states *)
Definition gen_variation_copy : G (@Variation SState) :=
  l <- arbitrary;;
  st <- arbitrary;;
  ret (Var l st st).

(* PropLang definitions *)

Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".

Definition shrink_variation (_ : ⟦∅⟧) (v : @Variation SState) : list (@Variation SState) :=
  shrinkVSState v.

Definition show_variation_fn (_ : ⟦∅⟧) (v : @Variation SState) : string := show v.

Definition prop_SSNI :=
  ForAll "v"
    (fun _ => gen_variation_copy)
    (fun _ => fuzz)
    shrink_variation
    show_variation_fn
  (Check (@Variation SState · ∅)
    (fun '(v, _) =>
      match propSSNI_smart default_table v with
      | Some true => true
      | Some false => false
      | None => true
      end)).

Definition test_prop_SSNI := fuzzLoop number_of_trials prop_SSNI (FIFOSeedPool.(mkPool) tt) HillClimbingUtility.
(*! QuickProp test_prop_SSNI. *)
