Require Import String ZArith List.

From QuickChick Require Import QuickChick.
From PropLang Require Import PropLang.

Import ListNotations.
Import QcNotation.
Import MonadNotation.

Local Open Scope string.
Local Open Scope qc_scope.
Local Open Scope nat_scope.
Local Open Scope Z.
Local Open Scope prop_scope.


Record Seed {A F: Type} := {
  input: A;
  feedback: F;
  energy: Z;
}.

Definition mkSeed {A F: Type} (a: A) (f: F) (e: Z): Seed := {| input := a; feedback := f; energy := e |}.

Definition Temperature := Z.

Inductive Directive {A F: Type} :=
| Generate : Directive
| Mutate : @Seed A F -> Directive
.

#[global] Instance showDirective {A F: Type} `{Show (@Seed A F)}  : Show (@Directive A F) :=
{|
  show d := match d with
            | Generate => "Generate"
            | Mutate seed => "Mutate(" ++ show seed ++ ")"
            end
|}.

Definition generator (cprop: CProp ∅) (directive: @Directive ⟦⦗cprop⦘⟧ Z) (size: nat) : G ⟦⟬cprop⟭⟧ :=
  match directive with
  | Generate => generate_cprop cprop size
  | Mutate seed => mut_all cprop size (input seed)
  end.

Class SeedPool {A F Pool: Type} := {
  (* Creates an empty pool. *)
  mkPool  : unit -> Pool;
  (* Adds a useful seed into the pool. *)
  invest  : (A * F) -> Pool -> Pool;
  (* Decreases the energy of a seed after a useless trial. *)
  revise  : Pool -> Pool;
  (* Samples the pool for an input. *)
  sample  : Pool -> @Directive A F;
  (* Returns the best seed in the pool. *)
  best    : Pool -> option (@Seed A F);
}.

Class Utility {A F Pool: Type} `{SeedPool A F Pool} := {
  (* Returns true if the feedback is interesting. *)
  useful  : Pool -> F -> bool;
  (* Returns a metric of how interesting the feedback is. *)
  utility : Pool -> F -> Z;
}.

Class Scalar (A : Type) :=
  { scale : A -> Z }.

#[global] Instance ScalarZ : Scalar Z :=
  {| scale := fun x => x |}.

#[global] Instance ScalarNat : Scalar nat :=
{| scale := fun x => Z.of_nat x |}.

#[global] Instance HillClimbingUtility {A F Pool} `{SeedPool A F Pool} `{Scalar F} 
: Utility := 
{|
  useful  := fun pool feedback' => match best pool with
                                  | None => true
                                  | Some seed => (scale feedback') >? (scale (feedback seed))
                                  end;
  utility := fun pool feedback' => match best pool with
                                  | None => scale feedback'
                                  | Some seed => scale feedback' - (scale (feedback seed))
                                  end
|}.