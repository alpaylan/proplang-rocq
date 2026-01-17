

Require Import String ZArith Nat List Bool Lia Arith.


From QuickChick Require Import QuickChick.
From PropLang Require Import PropLang.

Import QcDefaultNotation.
Import QcNotation.
Import ListNotations.
Import MonadNotation.

Set Implicit Arguments.
Set Asymmetric Patterns.

Local Open Scope qc_scope.
Local Open Scope nat_scope.
Local Open Scope prop_scope.




(* ---------- Terms over a ranked alphabet of constructors ---------- *)

Inductive Term (C:Type) :=
| T (c:C) (args: list (Term C)).

Arguments T {C} _ _.

(* ---------- Descriptions (patterns) ---------- *)


Inductive Desc (C:Type) :=
| Top
| Cons (c:C) (ds:list (Desc C))
| Next (d:Desc C)
| Eventually (d:Desc C).

Local Open Scope string_scope.
(* 
instance Show a => Show (Description a) where
  show Top = "⊤"
  show (Cons c []) = show c
  show (Cons c ts) = show c ++ "(" ++ intercalate ", " (show <$> ts) ++ ")"
  show (Eventually d) = "(⋄" ++ show d ++ ")"
  show (Next d) = "(⚬" ++ show d ++ ")"

   *)
#[local] Instance Show_Desc {C} `{Show C} : Show (Desc C) :=
  {
    show d :=
      let aux := fix aux (d:Desc C) : string :=
        match d with
        | Top => "⊤"
        | Cons c ds =>
            match ds with
            | [] => show c
            | _ =>
                let ds_str :=
                  String.concat ", " (map aux ds) in
                show c ++ "(" ++ ds_str ++ ")"
            end
        | Next d' =>
            "⚬" ++ aux d'
        | Eventually d' =>
            "<>" ++ aux d'
        end
      in aux d
  }.



(* ---------- Decidable equality for descriptions ---------- *) 

Fixpoint Desc_eq {C} `{Dec_Eq C} (c1 c2 : Desc C) {struct c1}:
  {c1 = c2} + {c1 <> c2}.
Proof.  
  destruct c1; destruct c2;
    try solve [right; discriminate].
  - left; auto.
  - remember H as D. clear HeqD. destruct H. destruct (dec_eq c c0).
    + symmetry in e. subst.
      generalize dependent ds0.
      induction ds; intros ds'; destruct ds';
        try solve [right; discriminate].
      * left; auto.
      * destruct (Desc_eq C D a d).
        -- subst.
           destruct (IHds ds').
           ++ inversion e; subst; clear e;
              left; auto.
           ++ right; intros Contra;
                inversion Contra; subst; auto.
        -- right; intros Contra;
             inversion Contra; subst; auto.
    + right; intros Contra; inversion Contra; subst; auto.
  - destruct (Desc_eq C H c1 c2);
      try solve [left; subst; auto];
      try solve [right; intros Contra; inversion Contra; subst; auto].
  - destruct (Desc_eq C H c1 c2);
      try solve [left; subst; auto];
      try solve [right; intros Contra; inversion Contra; subst; auto].
Defined.

#[local] Instance Dec_Eq_Desc {C} `{Dec_Eq C} : Dec_Eq (Desc C) :=
  {
    dec_eq := Desc_eq
  }.

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

Fixpoint covers' {C} `{Dec_Eq C} (n : nat) (t : Term C) (f : nat) : list (Desc C) :=
  match f with
  | O => []
  | S f' =>
    match n with
    | O => [Top]
    | S k =>
        match t with
        | T c args =>
            (* recurse into children with the same budget (n), like (covers' n =<< args) *)
            let child_cov :=
              fold_right (fun u acc => nub (covers' n u f' ++ acc)) [] args in
            (* distribute k across children; for each split ns, take choices of
               covers' m arg for each (m,arg); wrap with Eventually (Cons c …) *)
            let cons_ev :=
              flat_map
                (fun ns =>
                   let dlists :=
                     map (fun p =>
                            let '(m,u) := p in covers' m u f')
                         (combine ns args) in
                   map (fun ds => Eventually (Cons c ds))
                       (choices dlists))
                (splitN k (List.length args)) in
            nub (child_cov ++ cons_ev)
        end
    end
  end.

Definition covers {C} `{Dec_Eq C} (n : nat) (t : Term C) : list (Desc C) :=
  covers' n t 1000.

(* ---------- Hypothesis Table (HT) for type-directed generation ---------- *)
(*
   HT maps type names to lists of (constructor, argument types).
   This is used for generating descriptions based on a grammar/type signature.

   In Haskell: type HT a = Map Ty [(a, [Ty])]

   For now, we use a simpler approach where the user provides a
   `to_term` function to convert their data type to Term.
*)

(* Placeholder for future HT-based generation *)
(*
Definition reachableNext {C} (h : list (C * list C)) (t : C) : list C :=
  flat_map snd (filter (fun '(c, _) => (c = t)?) h).

Fixpoint reachableEventually_aux {C} `{Dec_Eq C}
  (h : list (C * list C)) (visited : list C) (frontier : list C) (fuel : nat) : list C :=
  match fuel with
  | O => visited
  | S fuel' =>
      let new_types := flat_map (reachableNext h) frontier in
      let unvisited := filter (fun t => negb (mem t visited)) new_types in
      match unvisited with
      | [] => visited
      | _ => reachableEventually_aux h (visited ++ unvisited) unvisited fuel'
      end
  end.

Definition reachableEventually {C} `{Dec_Eq C}
  (h : list (C * list C)) (t : C) : list C :=
  reachableEventually_aux h [t] [t] 100.
*)



Inductive ExTree :=
| ExLeaf
| ExNode (l: ExTree) (k: nat) (r: ExTree).

#[local] Instance Show_ExTree : Show ExTree :=
  {
    show tr :=
      let aux := fix aux (tr:ExTree) : string :=
        match tr with
        | ExLeaf => "Leaf"
        | ExNode l k r =>
            "Node (" ++ aux l ++ ") " ++ (show k) ++ " (" ++ aux r ++ ")"
        end
      in aux tr
  }.

#[local] Instance Dec_Eq_ExTree : Dec_Eq ExTree.
Proof. dec_eq. Defined.

Fixpoint term_of_tree (tr: ExTree) : Term ExTree :=
  match tr with
  | ExLeaf => T ExLeaf []
  | ExNode l k r => T (ExNode l k r) [term_of_tree l; term_of_tree r]
  end.

Eval compute in
  map show (covers 2 (term_of_tree (ExNode (ExNode ExLeaf 0 ExLeaf) 1 (ExNode ExLeaf 2 ExLeaf))) ).

Eval compute in
  map show (covers 2 (term_of_tree ExLeaf)).


Eval compute in
  map show (covers 2 (term_of_tree (ExNode ExLeaf 0 ExLeaf))).


Inductive Arith :=
| Add (x y : Arith)
| Mul (x y : Arith)
| Zero
| One
| Two.

#[local] Instance Show_Arith : Show Arith :=
  {
    show a :=
      let aux := fix aux (a:Arith) : string :=
        match a with
        | Zero => "0"
        | One => "1"
        | Two => "2"
        | Add x y => "(" ++ aux x ++ " + " ++ aux y ++ ")"
        | Mul x y => "(" ++ aux x ++ " * " ++ aux y ++ ")"
        end
      in aux a
  }.
#[local] Instance Dec_Eq_Arith : Dec_Eq Arith.
Proof. dec_eq. Defined.

Fixpoint term_of_arith (a: Arith) : Term Arith :=
  match a with
  | Zero => T Zero []
  | One => T One []
  | Two => T Two []
  | Add x y => T (Add x y) [term_of_arith x; term_of_arith y]
  | Mul x y => T (Mul x y) [term_of_arith x; term_of_arith y]
  end.

Eval compute in
  map show (covers 2 (term_of_arith (Add (Mul One Two) (Add One Two)))).


Inductive BoolList :=
| Nil
| ConsB (b: bool) (bs: BoolList).

#[local] Instance Show_BoolList : Show BoolList :=
  {
    show bl :=
      let aux := fix aux (bl:BoolList) : string :=
        match bl with
        | Nil => "nil"
        | ConsB b bs => "cons(" ++ (show b) ++ ", " ++ aux bs ++ ")"
        end
      in aux bl
  }.
#[local] Instance Dec_Eq_BoolList : Dec_Eq BoolList.
Proof. dec_eq. Defined.

Fixpoint term_of_boollist (bl: BoolList) : Term BoolList :=
  match bl with
  | Nil => T Nil []
  | ConsB b bs => T (ConsB b bs) [term_of_boollist bs]
  end.
Eval compute in
  map show (covers 2 (term_of_boollist (ConsB true (ConsB false (ConsB true Nil))))).
  (* ---------- Coverage loop ---------- *)

Fixpoint repeat {A : Type} (n : nat) (x : A) : list A :=
  match n with
  | O => []
  | S n' => x :: repeat n' x
  end.

(* Sequence a list of generators into a generator of lists *)
Fixpoint sequenceG {A : Type} (gs : list (G A)) : G (list A) :=
  match gs with
  | [] => ret []
  | g :: gs' =>
      x <- g;;
      xs <- sequenceG gs';;
      ret (x :: xs)
  end.

(* Helper to get list head with default *)
Definition list_hd {A : Type} (default : A) (l : list A) : A :=
  match l with
  | [] => default
  | x :: _ => x
  end.


(* Basic coverage loop - generates inputs and runs tests *)
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
        res <- generate_and_run cprop 0;;
        match res with
        | Normal seed false =>
            (* Fails - found a bug *)
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
    aux fuel cprop 0%nat 0%nat.

(*
   Coverage-guided loop with description tracking.

   This is the Rocq port of quick-cover's ccomb algorithm:
   - Generate multiple candidate inputs (fanout)
   - For each candidate, compute coverage (descriptions it satisfies)
   - Select the candidate that maximizes coverage improvement
   - Track seen descriptions to avoid redundant tests

   Parameters:
   - fuel: maximum number of tests to run
   - cprop: the property to test
   - strength: coverage strength (k in quick-cover)
   - fanout: number of candidates to generate per round
   - to_term: function to convert input to Term for coverage computation
*)

Definition coverage_improvement {C} `{Dec_Eq C}
  (ds : list (Desc C)) (seen : list (Desc C)) : nat :=
  List.length (filter (fun d => negb (mem d seen)) ds).

Definition update_coverage {C} `{Dec_Eq C}
  (ds : list (Desc C)) (seen : list (Desc C)) : list (Desc C) :=
  union_by ds seen.

(* Coverage-guided loop with fanout selection *)
Definition coverage_loop_guided
  {C : Type} `{Dec_Eq C}
  (fuel : nat)
  (cprop : CProp ∅)
  (strength : nat)
  (fanout : nat)
  (to_term : ⟦⦗cprop⦘⟧ -> Term C)
  : G Result :=
  let fix aux
    (fuel : nat)
    (passed : nat)
    (discards : nat)
    (seen : list (Desc C))
    : G Result :=
    match fuel with
    | O => ret (mkResult discards false passed [])
    | S fuel' =>
        (* Generate fanout candidates *)
        candidates <-
          sequenceG (repeat fanout (generate_and_run cprop 0));;
        (* Find the best candidate based on coverage improvement *)
        let scored :=
          map (fun res =>
            match res with
            | Normal seed _ =>
                let term := to_term seed in
                let ds := covers strength term in
                let improvement := coverage_improvement ds seen in
                (res, ds, improvement)
            | Discard _ _ => (res, [], 0)
            end) candidates in
        (* Select best candidate (highest improvement) *)
        let default := (Discard (none_cprop cprop) GenerationFailure, @nil (Desc C), 0) in
        let best :=
          fold_left (fun acc x =>
            match acc, x with
            | (_, _, imp1), (_, _, imp2) =>
                if Nat.ltb imp1 imp2 then x else acc
            end) scored (list_hd default scored) in
        match best with
        | (Normal seed false, _, _) =>
            (* Found a bug *)
            let shrunk := shrinker cprop seed in
            let printed := printer cprop shrunk in
            ret (mkResult discards true (passed + 1) printed)
        | (Normal seed true, ds, _) =>
            (* Passes - update coverage and continue *)
            let seen' := update_coverage ds seen in
            aux fuel' (passed + 1) discards seen'
        | (Discard _ _, _, _) =>
            (* All candidates discarded *)
            aux fuel' passed (discards + 1) seen
        end
    end in
    aux fuel 0 0 [].

