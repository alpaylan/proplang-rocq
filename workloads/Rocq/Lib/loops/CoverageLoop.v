

(*
   QuickCover.v
   A minimal Coq port of quick-cover/src/HT.hs essentials.

   - Generic constructor labels: type C (with EqDec)
   - Generic type names:        type Ty (with EqDec)
   - Signature HT : list (Ty * list (C * list Ty))
   - Terms over C
   - Descriptions: Top | Cons | Next | Eventually
   - matchesb, splitN, covers (budgeted)
   - reachableEventually, gen/genC (budgeted, single-ctor "free")
   - coverage_from_spec : nat -> HT -> Ty -> list (Term C) -> Q

   Requires Coq's QArith for rational results.
*)

From Coq Require Import List Bool Lia Arith QArith.QArith.

From QuickChick Require Import QuickChick.

Import QcDefaultNotation.
Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

Open Scope qc_scope.


(* ---------- Terms over a ranked alphabet of constructors ---------- *)

Inductive Term (C:Type) :=
| T (c:C) (args: list (Term C)).

Arguments T {C} _ _.

(* ---------- Descriptions (patterns) ---------- *)


Inductive ConsList (C:Type) :=
| CNil
| CCons (c:C) (l: ConsList C).

#[local] Instance Dec_Eq_Cons {C} `{Dec_Eq C} : Dec_Eq (ConsList C).
Proof. dec_eq. Defined.

Inductive Desc (C:Type) :=
| Top
| Cons (c:C) (ds:list (Desc C)) *)
| Next (d:Desc C)
| Eventually (d:Desc C).
 


#[local] Instance Dec_Eq_Desc {C} `{Dec_Eq C} : Dec_Eq (Desc C).
Proof. dec_eq. Defined.

Print Dec_Eq_Desc. *)

Definition Dec_Eq_Desc (C : Type) (_ : Dec_Eq C) (x y: Desc C) :=
	(fun x y : Desc C =>
     Desc_rec (fun x0 : Desc C => forall x1 : Desc C, {x0 = x1} + {x0 <> x1})
       (fun x0 : Desc C =>
        match x0 as d return ({Top C = d} + {Top C <> d}) with
        | @Top _ => left eq_refl
        | Next d =>
            (fun d0 : Desc C =>
             right
               ((fun H0 : Top C = Next d0 =>
                 let H1 : False :=
                   eq_ind (Top C)
                     (fun e : Desc C =>
                      match e with
                      | @Top _ => True
                      | _ => False
                      end) I (Next d0) H0 in
                 False_ind False H1)
                :
                Top C <> Next d0)) d
        | Eventually d =>
            (fun d0 : Desc C =>
             right
               ((fun H0 : Top C = Eventually d0 =>
                 let H1 : False :=
                   eq_ind (Top C)
                     (fun e : Desc C =>
                      match e with
                      | @Top _ => True
                      | _ => False
                      end) I (Eventually d0) H0 in
                 False_ind False H1)
                :
                Top C <> Eventually d0)) d
        end)
       (fun (d : Desc C) (H : forall x0 : Desc C, {d = x0} + {d <> x0})
          (x0 : Desc C) =>
        match x0 as d0 return ({Next d = d0} + {Next d <> d0}) with
        | @Top _ =>
            right
              ((fun H1 : Next d = Top C =>
                let H2 : False :=
                  eq_ind (Next d)
                    (fun e : Desc C =>
                     match e with
                     | Next _ => True
                     | _ => False
                     end) I (Top C) H1 in
                False_ind False H2)
               :
               Next d <> Top C)
        | Next d0 =>
            (fun d1 : Desc C =>
             sumbool_rec
               (fun _ : {d = d1} + {d <> d1} =>
                {Next d = Next d1} + {Next d <> Next d1})
               (fun a : d = d1 =>
                left
                  (eq_ind_r (fun d2 : Desc C => Next d2 = Next d1) eq_refl a))
               (fun diseq : d <> d1 =>
                right
                  ((fun absurd : Next d = Next d1 =>
                    diseq
                      (let H1 : d = d1 :=
                         f_equal
                           (fun e : Desc C =>
                            match e with
                            | Next d2 => d2
                            | _ => d
                            end) absurd in
                       (fun H2 : d = d1 => H2) H1))
                   :
                   Next d <> Next d1)) (H d1)) d0
        | Eventually d0 =>
            (fun d1 : Desc C =>
             right
               ((fun H1 : Next d = Eventually d1 =>
                 let H2 : False :=
                   eq_ind (Next d)
                     (fun e : Desc C =>
                      match e with
                      | Next _ => True
                      | _ => False
                      end) I (Eventually d1) H1 in
                 False_ind False H2)
                :
                Next d <> Eventually d1)) d0
        end)
       (fun (d : Desc C) (H : forall x0 : Desc C, {d = x0} + {d <> x0})
          (x0 : Desc C) =>
        match
          x0 as d0 return ({Eventually d = d0} + {Eventually d <> d0})
        with
        | @Top _ =>
            right
              ((fun H1 : Eventually d = Top C =>
                let H2 : False :=
                  eq_ind (Eventually d)
                    (fun e : Desc C =>
                     match e with
                     | Eventually _ => True
                     | _ => False
                     end) I (Top C) H1 in
                False_ind False H2)
               :
               Eventually d <> Top C)
        | Next d0 =>
            (fun d1 : Desc C =>
             right
               ((fun H1 : Eventually d = Next d1 =>
                 let H2 : False :=
                   eq_ind (Eventually d)
                     (fun e : Desc C =>
                      match e with
                      | Eventually _ => True
                      | _ => False
                      end) I (Next d1) H1 in
                 False_ind False H2)
                :
                Eventually d <> Next d1)) d0
        | Eventually d0 =>
            (fun d1 : Desc C =>
             sumbool_rec
               (fun _ : {d = d1} + {d <> d1} =>
                {Eventually d = Eventually d1} +
                {Eventually d <> Eventually d1})
               (fun a : d = d1 =>
                left
                  (eq_ind_r
                     (fun d2 : Desc C => Eventually d2 = Eventually d1)
                     eq_refl a))
               (fun diseq : d <> d1 =>
                right
                  ((fun absurd : Eventually d = Eventually d1 =>
                    diseq
                      (let H1 : d = d1 :=
                         f_equal
                           (fun e : Desc C =>
                            match e with
                            | Eventually d2 => d2
                            | _ => d
                            end) absurd in
                       (fun H2 : d = d1 => H2) H1))
                   :
                   Eventually d <> Eventually d1)) 
               (H d1)) d0
        end) x y).

Arguments Top {C}.
Arguments Cons {C} _ _.
Arguments Next {C} _.
Arguments Eventually {C} _.


(* ---------- List helpers: nub, union, intersection by eqb ---------- *)

Fixpoint mem {A} `{Dec_Eq A} (x:A) (xs:list A) : bool :=
  match xs with
  | [] => false
  | y::ys => (x = y)? || mem x ys
  end.

Fixpoint nub {A} `{Dec_Eq A}  (xs:list A) : list A :=
  match xs with
  | [] => []
  | x::ys => if mem x ys then nub ys else x :: nub ys
  end.

Definition union_by {A} `{Dec_Eq A} (xs ys:list A) : list A :=
  nub (xs ++ ys).

Definition inter_by {A} `{Dec_Eq A} (xs ys:list A) : list A :=
  filter (fun x => mem x ys) xs.

(* Cartesian choices over a list of lists *)
Fixpoint choices {A} (xss:list (list A)) : list (list A) :=
  match xss with
  | [] => [[]]
  | xs::xss' => flat_map (fun x => map (cons x) (choices xss')) xs
  end.

(* ---------- Matching (test covers description) ---------- *)

Search forallb.

Fixpoint matches {C} `{Dec_Eq C} (t:Term C) (d:Desc C) (f: nat) : bool :=
	match f with
	| O => true
	| S f' =>
		match t, d with
		| _, Top => true
		| T c' args', Cons c args =>
				(c = c')?
				&& (Nat.eqb (List.length args) (List.length args'))
				&& List.forallb (fun '(arg, d') => matches arg d' f') (combine args' args)
		| T _ args, Next d' =>
				List.existsb (fun arg => matches arg d' f') args
		| T _ args, Eventually d' =>
				matches t d' f'
				|| List.existsb (fun arg => matches arg (Eventually d') f') args
		end
	end.

Fixpoint splitN (n l : nat) : list (list nat) :=
  match l with
  | O => [[]]                                   (* matches Haskell base: [ [] ] *)
  | S l' =>
      (* x ranges over 0..n (inclusive), then recurse on n - x for the tail *)
      let xs := seq 0 (S n) in
      flat_map (fun x => map (cons x) (splitN (n - x) l')) xs
  end.

Eval compute in splitN 2 3.
(* = [[0;0;2]; [0;1;1]; [0;2;0]; [1;0;1]; [1;1;0]; [2;0;0]] *)

(* ---------- Coverage computation ---------- *)

Fixpoint covers {C} `{Dec_Eq C} (n : nat) (t : Term C) : list (Desc C).
Proof.
refine(
    match n with
    | O => [Top]
    | S k =>
        match t with
        | T c args =>
            (* recurse into children with the same budget (n), like (covers n =<< args) *)
            let child_cov :=
              fold_right (fun u acc => nub (covers _ _ n u ++ acc)) [] args in
            (* distribute k across children; for each split ns, take choices of
               covers m arg for each (m,arg); wrap with Eventually (Cons c …) *)
            let cons_ev :=
              flat_map
                (fun ns =>
                   let dlists :=
                     map (fun p =>
                            let '(m,u) := p in covers _ _ m u)
                         (combine ns args) in
                   map (fun ds => Eventually (Cons c ds))
                       (choices dlists))
                (splitN k (List.length args)) in
            nub (child_cov ++ cons_ev)
        end
    end).

Defined.

Fixpoint covers (n: nat) (t: Term C) : list (Desc C) :=
	match n, t with
	| O, _ => [Top]
	| _, Term c args =>
			let arg_covers := map (covers n) args in
			let n
	end 

Fixpoint repeat {A : Type} (n : nat) (x : A) : list A :=
  match n with
  | O => []
  | S n' => x :: repeat n' x
  end.

(* Coverage is a  *)
Class Coverage {A : Type} :=
  {
    coverage_metric : A -> Z;
  }.


Definition coverage_loop (fuel : nat) (cprop : CProp ∅): G Result :=  
  let fix aux
    (fuel : nat) 
    (cprop : CProp ∅) 
    (passed : nat)
    (discards: nat)
    : G Result :=
    match fuel with
    | O => ret (mkResult discards false passed [])
    | S fuel' => 
        inputs 
        match res with
        | Normal seed false =>
            (* Fails *)
            let shrunk := shrinker cprop seed in
            let printed := printer cprop shrunk in
            ret (mkResult discards true (passed + 1) printed)
        | Normal _ true =>
            (* Passes *)
            aux fuel' cprop (passed + 1)%nat discards
        | Discard _ _ => 
          (* Discard *)
          aux fuel' cprop passed (discards + 1)%nat
        end
    end in
    aux fuel cprop 0%nat 0%nat
    .

