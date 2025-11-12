From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import Coq.Program.Wf.
Require Import Lia.
Require Import List ZArith.
Import ListNotations.
Import MonadNotation.

Inductive Ctx :=
| EmptyCtx
| CtxBind : Type -> Ctx -> Ctx.

Declare Scope prop_scope.

Notation "'∅'" := EmptyCtx : prop_scope.
Notation " A '·' C " :=
  (CtxBind A C) (at level 70) : prop_scope.

Local Open Scope prop_scope.

Fixpoint interp_ctx (C : Ctx) : Type :=
  match C with
  | ∅ => nat
  | T·C => T * interp_ctx C
  end.

Notation "'⟦' C '⟧'" := (interp_ctx C) : prop_scope.

Inductive CProp : Ctx -> Type :=
| ForAll : forall
      {A: Type}
      {C: Ctx}
      (name: string)
      (generator : ⟦C⟧ -> G A)
      (mutator   : ⟦C⟧ -> A -> G A)
      (shrinker  : ⟦C⟧ -> A -> list A)
      (printer   : ⟦C⟧ -> A -> string),
      CProp (A · C) -> CProp C
| ForAllMaybe : forall
      {A: Type}
      {C: Ctx}
      (name: string)
      (generator : ⟦C⟧ -> G (option A))
      (mutator   : ⟦C⟧ -> A -> G (option A))
      (shrinker  : ⟦C⟧ -> A -> list A)
      (printer   : ⟦C⟧ -> A -> string),
      CProp (A · C) -> CProp C
| Implies : forall C
      (prop : ⟦C⟧ -> bool),
      CProp C -> CProp C 
| Check : forall C,
      (⟦C⟧ -> bool) -> CProp C.


Fixpoint input_types {C : Ctx}
         (cprop : CProp C) : Ctx :=
  match cprop with
  | @ForAll A _ _ _ _ _ _ cprop' =>
      A · (input_types cprop')
  | @ForAllMaybe A _ _ _ _ _ _ cprop' =>
      A · (input_types cprop')
  | Implies _ _ cprop' => (input_types cprop')
  | Check _ _ => ∅
  end.

Fixpoint input_types_opt {C : Ctx}
         (cprop : CProp C) : Ctx :=
  match cprop with
  | @ForAll A _ _ _ _ _ _ cprop' =>
      (option A) · (input_types_opt cprop')
  | @ForAllMaybe A _ _ _ _ _ _ cprop' =>
      (option A) · (input_types_opt cprop')
  | Implies _ _ cprop' => (input_types_opt cprop')
  | Check _ _ => ∅
  end.

Notation "'⦗' c '⦘'" := (@input_types _ c).
Notation "'⟬' c '⟭'" := (@input_types_opt _ c).

Fixpoint none_cprop {C : Ctx}
         (cprop : CProp C) : ⟦⟬cprop⟭⟧ :=
  match cprop with
  | @ForAll A _ _ _ _ _ _ cprop' =>
      (None, none_cprop cprop')
  | @ForAllMaybe A _ _ _ _ _ _ cprop' =>
      (None, none_cprop cprop')
  | Implies _ _ cprop' => none_cprop cprop'
  | Check _ _ => 0
  end.

Fixpoint lift_opt_cprop {C : Ctx} (cprop : CProp C) 
  : ⟦⟬cprop⟭⟧ -> option ⟦⦗cprop⦘⟧ :=
  match cprop with
  | @ForAll A _ _ _ _ _ _ cprop' =>
      fun '(oa, inps') =>
        match oa with
        | Some a =>
            match lift_opt_cprop cprop' inps' with
            | Some inps'' => Some (a, inps'')
            | None => None
            end
        | None => None
        end
  | @ForAllMaybe A _ _ _ _ _ _ cprop' =>
      fun '(oa, inps') =>
        match oa with
        | Some a =>
            match lift_opt_cprop cprop' inps' with
            | Some inps'' => Some (a, inps'')
            | None => None
            end
        | None => None
        end
  | Implies _ _ cprop' =>
      fun inps' => lift_opt_cprop cprop' inps'
  | Check _ _ =>
      fun _ => Some 0
  end.

(* Definition pullValues {C: Ctx} (cprop: CProp C) (opt_values: ⟦⟬cprop⟭⟧) : option ⟦⦗cprop⦘⟧.
Proof.
  induction cprop; simpl in *.
  - destruct opt_values as [a opt_values'].
    apply IHcprop in opt_values'.
    refine(
      match a, opt_values' with
      | Some a, Some values' => Some (a, values')
      | _, _ => None
      end).
  - destruct opt_values as [a opt_values'].
    apply IHcprop in opt_values'.
    refine(
      match a, opt_values' with
      | Some a, Some values' => Some (a, values')
      | _, _ => None
      end).
  - apply IHcprop in opt_values.
    refine(
      match opt_values with
      | Some values => Some values
      | _ => None
      end). 
  - exact (Some 0%nat).
Defined. *)

Definition arb : G nat := choose (0,10).
Definition gen (n : nat) : G nat := choose (0, n).
Definition mut (n : nat) : G nat :=
  choose (n - 3, n + 3).
Definition test (x y : nat) : bool := Nat.ltb y x.

Local Open Scope string.

Definition example :=
  @Implies (nat · (nat · ∅)) (fun '(y, (x, s)) => Nat.ltb x y) (
  @Check (nat · (nat · ∅)) (fun '(y, (x, s)) => test x y)).

Definition example' :=
  ForAll "x" (fun tt => arb) (fun tt => mut) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · ∅) "y" (fun '(x, _) => gen x) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @Check (nat · (nat · ∅))
             (fun '(y, (x, _)) => test x y))).

Inductive DiscardType := PreconditionFailure | GenerationFailure.

Inductive RunResult {C: Ctx} (cprop : CProp C) :=
| Normal : ⟦⦗cprop⦘⟧ -> bool -> RunResult cprop
| Discard : ⟦⟬cprop⟭⟧ -> DiscardType -> RunResult cprop.

Arguments Normal {C} {cprop}.
Arguments Discard {C} {cprop}.

Fixpoint generate_cprop {C : Ctx} (cprop : CProp C)
  : ⟦C⟧ -> G (⟦⟬cprop⟭⟧) :=
  match cprop with
  | ForAll _ gen mut shr pri cprop' =>
      fun env =>
        a <- gen env;;
        env <- generate_cprop cprop' (a,env);;
        ret (Some a,env)
  | ForAllMaybe  _ gen mut shr pri cprop' =>
      fun env =>
        a <- gen env;;
        match a with
        | Some a => env <- generate_cprop cprop' (a,env);;
                    ret (Some a,env)
        | None => ret (None, none_cprop cprop')
        end
  | Implies _ _ cprop' =>
      fun env => generate_cprop cprop' env
  | Check C prop =>
      fun env => ret 0
  end.

Definition generator (cprop : CProp ∅) : G ⟦⟬cprop⟭⟧ :=
  generate_cprop cprop 0.

(* Fixpoint run_cprop {C:Ctx} (cprop : CProp C)
         (cenv : ⟦C⟧)
         (fenv :  ⟦⦗cprop⦘⟧)
         {struct cprop}
  : option bool.
Proof.
  induction cprop; simpl in *.
  - destruct fenv as [a fenv'] eqn:H.
    apply IHcprop.
    + exact (a, cenv).
    + exact fenv'.
  - destruct fenv as [a fenv'] eqn:H.
    apply IHcprop.
    + exact (a, cenv).
    + exact fenv'.
  - destruct (prop cenv) eqn:E.
    + apply IHcprop.
      * exact cenv.
      * exact fenv.
    + exact None.
  - exact (Some (b cenv)).
Defined. *)

Fixpoint run_cprop {C:Ctx} (cprop : CProp C)
         {struct cprop}
  : ⟦C⟧ -> ⟦⦗cprop⦘⟧ -> option bool :=
  match cprop with
  | ForAll _ _ _ _ _ cprop' =>
      fun cenv '(a, fenv') =>
        run_cprop cprop' (a, cenv) fenv'
  | ForAllMaybe _ _ _ _ _ cprop' =>
      fun cenv '(a, fenv') =>
        run_cprop cprop' (a, cenv) fenv'
  | Implies _ prop cprop' =>
      fun cenv fenv => 
        match (prop cenv) with
        | true => None
        | false => None
        end
  | Check _ prop =>
      fun cenv _ => Some (prop cenv)
  end.


Definition runner (cprop: CProp ∅)
  : ⟦⦗cprop⦘⟧ -> option bool :=
  fun inps =>
    run_cprop cprop 0 inps.

Definition generate_and_run {C : Ctx}
         (cprop : CProp C)
  : ⟦C⟧ -> G (RunResult cprop) :=
  fun env =>
    input <- generate_cprop cprop env;;
    match lift_opt_cprop cprop input with
    | Some inps' =>
        match run_cprop cprop env inps' with
        | Some truth => ret (Normal inps' truth)
        | None => ret (Discard input (PreconditionFailure))
        end
    | None => ret (Discard input (PreconditionFailure))
    end.

Fixpoint run_bypassing_preconditions {C:Ctx} (cprop : CProp C)
         {struct cprop}
  : ⟦C⟧ ->  ⟦⦗cprop⦘⟧ -> bool :=
  match cprop with
  | ForAll _ _ _ _ _ cprop' =>
      fun cenv '(a, fenv') =>
        run_bypassing_preconditions cprop' (a, cenv) fenv'
  | ForAllMaybe _ _ _ _ _ cprop' =>
      fun cenv '(a, fenv') =>
        run_bypassing_preconditions cprop' (a, cenv) fenv'
  | Implies _ _ cprop' =>
      fun cenv fenv => run_bypassing_preconditions cprop' cenv fenv
  | Check _ prop =>
      fun cenv _ =>prop cenv
  end.

(* 
Fixpoint generate_and_run {C : Ctx}
         (cprop : CProp C)
  : ⟦C⟧ -> G (RunResult cprop).
Proof.
  destruct cprop as [? ? ? gen mut shr pri cprop'
                    |? ? ? gen mut shr pri cprop'
                    |? prop cprop'
                    |? prop].
  - intros env.
    refine (bindGen (gen env) (fun a => _)).
    refine (bindGen (@generate_and_run (A · C) cprop' (a, env)) (fun res => _)).
    destruct res as [env' truth | env' discard_type].
    + refine (ret (Normal _ truth)).
      simpl in *.
      refine (a, _).
      refine env'.
    + refine (ret (Discard _ discard_type)).
      simpl in *.
      refine (Some a, env').
  - intros env.
    refine (bindGen (gen env) (fun a => _)).
    refine (match a with Some a => _ | None => _ end).
    * refine (bindGen (@generate_and_run (A · C) cprop' (a, env)) (fun res => _)).
      destruct res as [env' truth | env' discard_type].
      + refine (ret (Normal _ truth)).
        simpl in *.
        refine (a, _).
        refine env'.
      + refine (ret (Discard _ discard_type)).
        simpl in *.
        refine (Some a, env').
    * refine (ret (Discard _ GenerationFailure)).
      simpl in *.
      refine (None, _).
      refine (none_cprop cprop').
  - intros env.
    destruct (prop env).
    * refine (bindGen (@generate_and_run C cprop' env) (fun res => _)).
      destruct res as [env' truth | env' discard_type].
      + refine (ret (Normal _ truth)).
        simpl in *.
        refine env'.
      + refine (ret (Discard _ discard_type)).
        simpl in *.
        refine env'.
    * refine (ret (Discard _ PreconditionFailure)).
      + simpl in *.
        refine (none_cprop cprop').
  - intros env.
    refine (ret (Normal _ (prop env))).
    refine 0.
Defined. *)



Fixpoint generate_and_run_bypassing_preconditions {C : Ctx}
         (cprop : CProp C)
  : ⟦C⟧ -> G (RunResult cprop).
Proof.
  destruct cprop as [? ? ? gen mut shr pri cprop'
                    |? ? ? gen mut shr pri cprop'
                    |? prop cprop'
                    |? prop].
  - intros env.
    refine (bindGen (gen env) (fun a => _)).
    refine (bindGen (@generate_and_run (A · C) cprop' (a, env)) (fun res => _)).
    destruct res as [env' truth | env' discard_type].
    + refine (ret (Normal _ truth)).
      simpl in *.
      refine (a, _).
      refine env'.
    + refine (ret (Discard _ discard_type)).
      simpl in *.
      refine (Some a, env').
  - intros env.
    refine (bindGen (gen env) (fun a => _)).
    refine (match a with Some a => _ | None => _ end).
    * refine (bindGen (@generate_and_run (A · C) cprop' (a, env)) (fun res => _)).
      destruct res as [env' truth | env' discard_type].
      + refine (ret (Normal _ truth)).
        simpl in *.
        refine (a, _).
        refine env'.
      + refine (ret (Discard _ discard_type)).
        simpl in *.
        refine (Some a, env').
    * refine (ret (Discard _ GenerationFailure)).
      simpl in *.
      refine (None, _).
      refine (none_cprop cprop').
  - intros env.
    refine (bindGen (@generate_and_run C cprop' env) (fun res => _)).
    destruct res as [env' truth | env' discard_type].
    + refine (ret (Normal _ truth)).
      simpl in *.
      refine env'.
    + refine (ret (Discard _ discard_type)).
      simpl in *.
      refine env'.
  - intros env.
    refine (ret (Normal _ (prop env))).
    refine 0.
Defined.

Fixpoint mut_all {C : Ctx}
         (cprop : CProp C)
  : ⟦C⟧ -> ⟦⦗cprop⦘⟧ -> (G (⟦⟬cprop⟭⟧)).
  Proof.
  destruct cprop as [? ? ? gen mut shr pri cprop'
                    |? ? ? gen mut shr pri cprop'
                    |? prop cprop'
                    |? prop].
  - intros env (x,xs).
    simpl in *.
    refine(bindGen (mut env x) (fun x' => _)).
    refine(bindGen (@mut_all (A · C) cprop' (x', env) xs) (fun xs' => _)).
    refine (ret (Some x', xs')).
  - intros env (x,xs).
    simpl in *.
    refine(bindGen (mut env x) (fun x' => _)).
    refine(match x' with Some x' => _ | None => _ end).
    * refine(bindGen (@mut_all (A · C) cprop' (x', env) xs) (fun xs' => _)).
      refine (ret (Some x', xs')).
    * refine (ret (None, none_cprop _)).
  - intros env xs.
    simpl in *.
    refine(bindGen (@mut_all C cprop' env xs) (fun xs' => _)).
    refine (ret xs').
  - intros env _.
    refine (ret 0).
Defined.  

Fixpoint mut_some {C : Ctx}
  (cprop : CProp C) 
: ⟦C⟧ -> ⟦⦗cprop⦘⟧ -> (G (⟦⟬cprop⟭⟧)).
Proof.
  destruct cprop as [? ? ? gen mut shr pri cprop'
                    |? ? ? gen mut shr pri cprop'
                    |? prop cprop'
                    |? prop].
  - intros env (x,xs).
    simpl in *.
    refine(bindGen (choose(0,1)) (fun mut_oracle => _)).
    refine(bindGen (mut env x) (fun x' => _)).
    refine(bindGen (@mut_some (A · C) cprop' (x', env) xs) (fun xs' => _)).
    refine(match mut_oracle with 0 => ret (Some x', xs') | _ => ret (Some x, xs') end).
  - intros env (x,xs).
    simpl in *.
    refine(bindGen (mut env x) (fun x' => _)).
    refine(match x' with Some x' => _ | None => _ end).
    * refine(bindGen (@mut_some (A · C) cprop' (x', env) xs) (fun xs' => _)).
      refine (ret (Some x', xs')).
    * refine (ret (None, none_cprop _)).
  - intros env xs.
    simpl in *.
    refine(bindGen (@mut_some C cprop' env xs) (fun xs' => _)).
    refine (ret xs').
  - intros env _.
    refine (ret 0).
Defined.


Fixpoint print_cprop {C : Ctx} (cprop : CProp C)
  : ⟦C⟧ -> ⟦⦗ cprop ⦘⟧ -> list (string * string).
Proof.
  destruct cprop as [? ? ? gen mut shr pri cprop'
                    |? ? ? gen mut shr pri cprop'
                    |? prop cprop'
                    |? prop].
  - intros env (a,inps').
    refine ((name, pri env a) :: (print_cprop (A · C) cprop' (a, env) inps')).
  - intros env (a,inps').
    refine ((name, pri env a) :: (print_cprop (A · C) cprop' (a, env) inps')).
  - intros env inps'.
    refine (print_cprop C cprop' env inps').
  - intros env _.
    refine nil.
Defined. 

Definition printer (cprop : CProp ∅) (input: ⟦⦗ cprop ⦘⟧)
  : list (string * string) := 
  print_cprop cprop 0 input.

Definition pri_opt {A} (pri: A -> string) (a: option A) : string :=
  match a with
  | Some a => "Some (" ++ pri a ++ ")"
  | None => "None"
  end.

Fixpoint ctx_opt (C: Ctx) : Type :=
  match C with
  | ∅ => unit
  | T·C => option T * ctx_opt C
  end.

Fixpoint print_opt {C : Ctx} (cprop : CProp C)
  : ⟦C⟧ -> ⟦⟬ cprop ⟭⟧ -> list (string * string).
Proof.
  destruct cprop as [? ? ? gen mut shr pri cprop'
                    |? ? ? gen mut shr pri cprop'
                    |? prop cprop'
                    |? prop].
  - intros env (a,inps'). 
    refine ((name, pri_opt (pri env) a) :: _).
    refine (match a with
            | Some a => print_opt (A · C) cprop' (a, env) inps'
            | None => nil
            end).
  - intros env (a,inps').
    refine ((name, pri_opt (pri env) a) :: _).
    refine (match a with
            | Some a => print_opt (A · C) cprop' (a, env) inps'
            | None => nil
            end).
  - intros env inps'.
    refine (print_opt C cprop' env inps').
  - intros env _.
    refine nil.
Defined. 


Fixpoint show_elem_list (l: list (string * string)) : string :=
  match l with
  | [] => ""
  | ((k, v) :: []) => (k ++ ": " ++ v) 
  | ((k, v) :: t) => (k ++ ": " ++ v ++ ", " ++ show_elem_list t)
  end.



Definition with_instrumentation (f: unit -> bool) : (bool * (bool * nat)) :=
  let f' := fun _ => Some (f tt) in
  let '(res, (useful, energy)) := withInstrumentation f' in
  match res with
  | Some true => (true, (useful, energy))
  | Some false => (false, (useful, energy))
  | None => (false, (useful, energy))
  end.

Fixpoint instrumented_run_and_test {C:Ctx} 
        (cprop : CProp C)
        (instrumentation_function: (unit -> bool) -> (bool * (bool * nat)))
        (cenv : ⟦C⟧)
        (fenv :  ⟦⦗cprop⦘⟧)
        {struct cprop}
  : option bool * Z.
Proof.
  induction cprop; simpl in *.
  - destruct fenv as [a fenv'] eqn:H.
    apply IHcprop.
    + exact (a, cenv).
    + exact fenv'.
  - destruct fenv as [a fenv'] eqn:H.
    apply IHcprop.
    + exact (a, cenv).
    + exact fenv'.
  - refine (
    let '(res, (useful, energy)) := instrumentation_function (fun _ => prop cenv) in
    match res with
    | true => (Some true, Z.of_nat energy) 
    | _ => (None, Z.of_nat energy)
    end).
  - refine (
      let '(res, (useful, energy)) := instrumentation_function (fun _ => b cenv) in
      match res with
      | true => (Some true, Z.of_nat energy)
      | _ => (Some false, Z.of_nat energy)
      end).
Defined.

Definition instrumented_runner 
  (cprop: CProp ∅)
  (instrumentation_function: (unit -> bool) -> (bool * (bool * nat)))
  : ⟦⦗cprop⦘⟧ -> option bool * Z :=
  fun inps =>
    instrumented_run_and_test cprop instrumentation_function 0 inps.



Fixpoint shrink_cprop
  {C : Ctx}
  (cprop : CProp C)
  (cenv :  ⟦C⟧)
  (fenv :  ⟦⦗cprop⦘⟧)
  {struct cprop}
  : option ⟦⦗cprop⦘⟧.
Proof.
  induction cprop; simpl in *.
  - destruct fenv as [a fenv']. 
    (* Recurse through the list of shrinks *)
    induction (shrinker cenv a).
    (* No more shrinks - try the next element of the property *)
    + destruct (shrink_cprop _ cprop (a,cenv) fenv') eqn:M.
      * exact (Some (a, i)).
      * exact None.
    (* More shrinks - run the property on the shrunk possibility. *)
    + destruct (run_cprop cprop (a0,cenv) fenv') eqn:T.
      * destruct b.
        (* Test succeeded - recurse down the list. *)
        -- apply IHl.
        (* Test failed - end with current result. *)
        -- exact (Some (a0, fenv')).     
      * (* Test discarded - recurse down the list. *)
        apply IHl.
  - destruct fenv as [a fenv']. 
  (* Recurse through the list of shrinks *)
  induction (shrinker cenv a).
  (* No more shrinks - try the next element of the property *)
  + destruct (shrink_cprop _ cprop (a,cenv) fenv') eqn:M.
    * exact (Some (a, i)).
    * exact None.
  (* More shrinks - run the property on the shrunk possibility. *)
  + destruct (run_cprop cprop (a0,cenv) fenv') eqn:T.
    * destruct b.
      (* Test succeeded - recurse down the list. *)
      -- apply IHl.
      (* Test failed - end with current result. *)
      -- exact (Some (a0, fenv')).     
    * (* Test discarded - recurse down the list. *)
      apply IHl.
  -  destruct (run_cprop cprop cenv fenv) eqn:T.
    * destruct b.
      -- apply IHcprop.
        ++ exact cenv.
        ++ exact fenv.
      -- exact None.
    * exact None.
  - exact None.
Defined.

Fixpoint shrink_loop (fuel : nat)
  (cprop: CProp ∅) (counterexample : ⟦⦗cprop⦘⟧) :
  ⟦⦗cprop⦘⟧ :=
  match fuel with
  | O => counterexample
  | S fuel' =>
      match shrink_cprop cprop 0%nat counterexample with
      | Some c' => shrink_loop fuel' cprop c'
      | None => counterexample
      end
  end.

Definition shrinker (cprop: CProp ∅) (counterexample : ⟦⦗cprop⦘⟧) : ⟦⦗cprop⦘⟧ := 
  shrink_loop 10 cprop counterexample.

  
Axiom float_of_nat : OCamlFloat -> nat.
Extract Constant float_of_nat => "Float.to_int".

Fixpoint mutate_and_run {C : Ctx}
         (cprop : CProp C)
  : ⟦C⟧ -> ⟦⦗cprop⦘⟧ -> G (RunResult cprop).
Proof.
  destruct cprop as [? ? ? gen mut shr pri cprop'
                    |? ? ? gen mut shr pri cprop'
                    |? prop cprop'
                    |? prop].
  - intros env (x, xs).
    refine (bindGen (mut env x) (fun a => _)).
    refine (bindGen (@mutate_and_run (A · C) cprop' (a, env) xs) (fun res => _)).
    destruct res as [env' truth | env' discard_type].
    + refine (ret (Normal _ truth)).
      simpl in *.
      refine (a, _).
      refine env'.
    + refine (ret (Discard _ discard_type)).
      simpl in *.
      refine (Some a, env').
  - intros env (x, xs).
    refine (bindGen (mut env x) (fun a => _)).
    refine (match a with Some a => _ | None => _ end).
    * refine (bindGen (@mutate_and_run (A · C) cprop' (a, env) xs) (fun res => _)).
      destruct res as [env' truth | env' discard_type].
      + refine (ret (Normal _ truth)).
        simpl in *.
        refine (a, _).
        refine env'.
      + refine (ret (Discard _ discard_type)).
        simpl in *.
        refine (Some a, env').
    * refine (ret (Discard _ GenerationFailure)).
      simpl in *.
      refine (None, _).
      refine (none_cprop cprop').
  - intros env seed.
    destruct (prop env).
    * refine (bindGen (@mutate_and_run C cprop' env seed) (fun res => _)).
      destruct res as [env' truth | env' discard_type].
      + refine (ret (Normal _ truth)).
        simpl in *.
        refine env'.
      + refine (ret (Discard _ discard_type)).
        simpl in *.
        refine env'.
    * refine (ret (Discard _ PreconditionFailure)).
      + simpl in *.
        refine (none_cprop cprop').
  - intros env seed.
    refine (ret (Normal _ (prop env))).
    refine 0%nat.
Defined.



Record Result := {
 discards: nat;
 foundbug: bool;
 passed: nat;
 counterexample: list (string * string);
}.

Definition mkResult 
  (discards: nat)
  (foundbug: bool)
  (passed: nat)
  (counterexample: list (string * string))
  : Result := {| discards := discards; foundbug := foundbug; passed := passed; counterexample := counterexample |}.

#[global] Instance showResult : Show Result :=
  {| show r := """discards"": " ++ show (discards r) ++
               ", ""foundbug"": " ++ show (foundbug r) ++
               ", ""passed"": " ++ show (passed r) ++
               ", ""counterexample"": """ ++  show_elem_list (counterexample r) ++ """"
  |}.


Definition runLoop (fuel : nat) (cprop : CProp ∅): G Result :=  
  let fix runLoop'
    (fuel : nat) 
    (cprop : CProp ∅) 
    (passed : nat)
    (discards: nat)
    : G Result :=
    match fuel with
    | O => ret (mkResult discards false passed [])
    | S fuel' => 
        res <- generate_and_run cprop (Nat.log2 (passed + discards)%nat);;
        match res with
        | Normal seed false =>
            (* Fails *)
            let shrunk := shrinker cprop seed in
            let printed := printer cprop shrunk in
            ret (mkResult discards true (passed + 1) printed)
        | Normal _ true =>
            (* Passes *)
            runLoop' fuel' cprop (passed + 1)%nat discards
        | Discard _ _ => 
          (* Discard *)
          runLoop' fuel' cprop passed (discards + 1)%nat
        end
    end in
    runLoop' fuel cprop 0%nat 0%nat
    .


Definition sample_sized (A : Type) (g : G A) (sz: nat) : A :=
  match g with
    | MkGen m =>
      let rnd := newRandomSeed in
      m sz rnd
  end.

Definition invoke {A : Type} (g : G A) : A :=
sample_sized A g 5.

Definition retx {A: Type} (a: A) : G A := ret a.

Open Scope nat_scope.

(*
Fixpoint lastCtx (C : Ctx) : ⟦ C ⟧-> nat :=
  match C with
  | nat => fun c => c
  | (_,C') => fun c => lastCtx C' c
  end.
*)     

Definition lastCtx (C : Ctx) : ⟦ C ⟧ -> nat.
  induction C; simpl in *.
  - exact id.
  - intros [_ c].
    exact (IHC c).
Defined.

Definition sized {A} (C : Ctx) (g : ⟦ C ⟧ -> nat -> G A) : ⟦ C ⟧ -> G A.
  intros ctx.
  exact (g ctx (lastCtx C ctx)).
Defined.
  
Definition exampleSized :=
  @ForAll _ ∅ "x" (fun s => (retx s)) (fun _ => mut) (fun _ => shrink) (fun _ => show) (
  @Check (nat · ∅)
              (fun '(x, _) => test x 3)).


Definition exampleSized' :=
  ForAll "x" (fun _ => (retx 100)) (fun _ => mut) (fun _ => shrink) (fun _ => show) (
  @Check (nat · ∅)
              (fun '(x, _) => test x 3)).

Definition sizedRetx {A : Type} (a : A) (n : nat) : G A :=
  ret a.

Definition exampleSized'' :=
  @ForAll _ ∅ "x" (sized _ (fun _ => sizedRetx 3)) (fun _ => mut) (fun _ => shrink) (fun _ => show) (
  @Check (nat · ∅)
              (fun '(x, _) => test x 3)).


Fixpoint instrumented_mutate_and_run {C : Ctx}
(cprop : CProp C) (instrumentation_function: (unit -> bool) -> (bool * (bool * nat)))
{struct cprop}
: ⟦C⟧ -> ⟦⦗cprop⦘⟧ -> G (RunResult cprop * Z).
Proof.
destruct cprop as [? ? ? gen mut shr pri cprop'
           |? ? ? gen mut shr pri cprop'
           |? prop cprop'
           |? prop].
- intros env (x, xs).
  refine (bindGen (mut env x) (fun a => _)).
  refine (bindGen (@instrumented_mutate_and_run (A · C) cprop' instrumentation_function (a, env) xs) (fun res => _)).
  destruct res as [res feedback].
  destruct res as [env' truth | env' discard_type].
  + refine (ret (Normal _ truth, feedback)).
    simpl in *.
    refine (a, env').
  + refine (ret (Discard _ discard_type, feedback)).
    simpl in *.
    refine (Some a, env').
  - intros env (x, xs).
    refine (bindGen (mut env x) (fun a => _)).
    refine (match a with Some a => _ | None => _ end).
    * refine (bindGen (@instrumented_mutate_and_run (A · C) cprop' instrumentation_function (a, env) xs) (fun res => _)).
      destruct res as [res feedback].
      destruct res as [env' truth | env' discard_type].
      + refine (ret (Normal _ truth, feedback)).
        simpl in *.
        refine (a, env').
      + refine (ret (Discard _ discard_type, feedback)).
        simpl in *.
        refine (Some a, env').
    * refine (ret (Discard _ GenerationFailure, 0%Z)).
      simpl in *.
      refine (None, none_cprop cprop').
  - intros env seed.
    simpl in *.
    refine (
      let '(res, (useful, energy)) := with_instrumentation (fun _ => prop env) in
      match res with
      | true => (bindGen (@instrumented_mutate_and_run C cprop' instrumentation_function env seed) (fun res => _))
      | false => (ret (Discard _ PreconditionFailure, (Z.of_nat energy)))
      end
      ).
    + destruct res as [res feedback].
      destruct res as [env' truth | env' discard_type].
      * refine (ret (Normal _ truth, feedback)).
        simpl in *.
        refine env'.
      * refine (ret (Discard _ discard_type, feedback)).
        simpl in *.
        refine env'.
    + simpl in *.
      refine (none_cprop cprop').
    - intros env seed.
      refine (
        let '(res, (useful, energy)) := instrumentation_function (fun _ => (prop env)) in
        ret (Normal _ (prop env), (Z.of_nat energy))
        ).
      refine 0.
Defined.


Fixpoint instrumented_generate_and_run {C : Ctx}
(cprop : CProp C)
(instrumentation_function: (unit -> bool) -> (bool * (bool * nat)))
{struct cprop}
: ⟦C⟧ -> G (RunResult cprop * Z).
Proof.
destruct cprop as [? ? ? gen mut shr pri cprop'
           |? ? ? gen mut shr pri cprop'
           |? prop cprop'
           |? prop].
- intros env.
  refine (bindGen (gen env) (fun a => _)).
  refine (bindGen (@instrumented_generate_and_run (A · C) cprop' instrumentation_function (a, env)) (fun res => _)).
  destruct res as [res feedback].
  destruct res as [env' truth | env' discard_type].
  + refine (ret (Normal _ truth, feedback)).
    simpl in *.
    refine (a, env').
  + refine (ret (Discard _ discard_type, feedback)).
    simpl in *.
    refine (Some a, env').
- intros env.
  refine (bindGen (gen env) (fun a => _)).
  refine (match a with Some a => _ | None => _ end).
  * refine (bindGen (@instrumented_generate_and_run (A · C) cprop' instrumentation_function (a, env)) (fun res => _)).
    destruct res as [res feedback].
    destruct res as [env' truth | env' discard_type].
    + refine (ret (Normal _ truth, feedback)).
      simpl in *.
      refine (a, env').
    + refine (ret (Discard _ discard_type, feedback)).
      simpl in *.
      refine (Some a, env').
  * refine (ret (Discard _ GenerationFailure, 0%Z)).
    simpl in *.
    refine (None, none_cprop cprop').
  - intros env.
    simpl in *.
    refine (
      let '(res, (useful, energy)) := with_instrumentation (fun _ => prop env) in
      match res with
      | true => (bindGen (@instrumented_generate_and_run C cprop' instrumentation_function env) (fun res => _))
      | false => (ret (Discard _ PreconditionFailure, (Z.of_nat energy)))
      end
      ).
    + destruct res as [res feedback].
      destruct res as [env' truth | env' discard_type].
      * refine (ret (Normal _ truth, feedback)).
        simpl in *.
        refine env'.
      * refine (ret (Discard _ discard_type, feedback)).
        simpl in *.
        refine env'.
    + simpl in *.
      refine (none_cprop cprop').
    - intros env.
      refine (
        let '(res, (useful, energy)) := instrumentation_function (fun _ => (prop env)) in
        ret (Normal _ (prop env), (Z.of_nat energy))
        ).
      refine 0.
Defined.


Definition test2 (x y : nat) : bool :=
  (negb (Nat.eqb y  x)).

Definition example2 :=
  @ForAll _ ∅ "x" (fun tt => arb) (fun tt => mut) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · ∅) "y" (fun '(x, _) => gen x) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @Check (nat · (nat · ∅))
              (fun '(y, (x, _)) => test2 x y))).


Definition example2' :=
  @Check (nat · (nat · ∅))
              (fun '(y, (x, _)) => test2 x y).

              

Definition example2'' :=
  @ForAll _ ∅ "x" (fun tt => arb) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · ∅) "y" (fun '(x, _) => gen x) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @Check (nat · (nat · ∅))
              (fun '(y, (x, _)) => test2 x y))).
              

Definition example3 :=
  @ForAll _ ∅ "x" (fun tt => arb) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · ∅) "y" (fun '(x, _) => gen x) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @Check (nat · (nat · ∅))
              (fun '(y, (x, _)) => (test2 x y)))).

  Definition fb :=
  (fun '(y, (x, tt)) => (2000 - (x - y) - (y - x))).

Definition example3' :=
  forAll arb (fun (x: nat)  =>
  forAll (gen x) (fun (y: nat)  =>
  test2 x y)).

#[local] Instance showUnit : Show unit :=
  {| show _ := "()" |}.

Fixpoint mk_shallow (C : Ctx) (cprop: CProp C) : ⟦C⟧ -> Checker :=
  match cprop with
  | @ForAll A C name gen mut shr pri cprop' =>
    fun env =>
    forAllShrinkShow (gen env) (shr env) (pri env) (fun a => mk_shallow (A · C) cprop' (a, env))
  | @ForAllMaybe A C name gen mut shr pri cprop' =>
    fun env =>
    forAllShrinkShowMaybe (gen env) (shr env) (pri env) (fun a => mk_shallow (A · C) cprop' (a, env))
  | Implies C prop cprop' =>
    fun env =>
    if prop env then mk_shallow C cprop' env
    else checker None
  | Check C prop =>
    fun env => 
    checker (prop env)
  end.

(* For testing, should move to instances properly *)
#[export] Instance FuzzyNat : Fuzzy nat := { fuzz x := ret x }.

Notation "'FOO' x ':' T ',' c" :=
  (ForAll "" (fun _ => @arbitrary T _)
            (fun _ => @fuzz T _)
            (fun _ => @shrink T _)
            (fun _ => @show T _)
            c)
    (at level 200, x ident, T at level 200, c at level 200, right associativity).

Definition typeOf {X} (x : X) := X.

Definition ttyp A C := 
  (string * (⟦ C ⟧ -> G A) * 
         (⟦ C ⟧ -> A -> G A) * 
         (⟦ C ⟧ -> A -> list A) *
         (⟦ C ⟧ -> A -> string))%type.

Definition ForAllCurried {A C}
  (t : string * (⟦ C ⟧ -> G A) * 
         (⟦ C ⟧ -> A -> G A) * 
         (⟦ C ⟧ -> A -> list A) *
         (⟦ C ⟧ -> A -> string)) : 
  CProp (A · C) -> CProp C :=
  let '(n,g,f,s,p) := t in
  ForAll n g f s p.

Notation "'FORALL' x1 'FORALL' x2 'FORALL' .. 'FORALL' xn ',' c" :=
  (ForAllCurried x1 (ForAllCurried x2 .. (ForAllCurried xn c) ..)) (at level 200).

Notation "x :- T" :=
  (("", (fun _ => @arbitrary T _),
         (fun _ => @fuzz T _),
         (fun _ => @shrink T _),
     (fun _ => @show T _)))
    (at level 99, T at next level).

Notation "x :- T 'gen:' g" :=
  (("", (fun _ => g),
         (fun _ => @fuzz T _),
         (fun _ => @shrink T _),
     (fun _ => @show T _)))
    (at level 99, T at next level).

Definition t1 : ttyp nat ∅ := ("x" :- nat).

Definition t2 :=
  FORALL x :- nat FORALL y :- nat , 
        (Check (nat · (nat · ∅)) (fun _ => true)).

Class Untuple (A : Type) :=
  { untuple : Ctx
  ; untuple_correct : ⟦untuple⟧ = A
  }.

#[local] Instance Untuple_empty : Untuple nat :=
  { untuple := ∅
  ; untuple_correct := eq_refl }.

Require Import Program.Tactics.

#[local] Program Instance Untuple_pair {A B} `{Untuple B} : Untuple (A * B) :=
  { untuple := A · @untuple B _ }.

Next Obligation.
destruct H.
simpl.
rewrite untuple_correct0.
reflexivity.
Defined.

Definition CHECK {A} `{Untuple A} (p : A -> bool) : CProp (@untuple A _).
  refine (Check (@untuple A _) _).
  rewrite untuple_correct.
  exact p.
Defined.

Print test.
(* test = fun x y : nat => y <? x 
     : nat -> nat -> bool *)
Definition t3 :=
  FORALL x :- nat
  FORALL y :- nat , 
  CHECK (fun '(y,(x,_)) => test x y).       

Definition t4 := 
  FORALL x :- nat gen:(choose (0, 10))
  FORALL y :- nat , 
  CHECK (fun '(y,(x,_)) => test x y).       

Print t4.

Derive Property test.
Print test_prop.
