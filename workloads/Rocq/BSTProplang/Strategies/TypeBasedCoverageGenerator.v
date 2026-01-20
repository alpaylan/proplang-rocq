From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import List ZArith.
Import ListNotations.
Import MonadNotation.

From BSTProplang Require Import Impl.
From BSTProplang Require Import Spec.
From PropLang Require Import PropLang.
From PropLang Require Import CoverageLoop.

Local Open Scope prop_scope.

(* ---------- Type-based generation using QuickChick's derived Arbitrary ---------- *)

Derive (Arbitrary, Show) for Tree.

#[local] Instance dec_eq_tree : Dec_Eq Tree.
Proof. dec_eq. Defined.
(* ---------- Term conversion for coverage computation ---------- *)

(* Convert BST Tree to Term for coverage analysis *)
Fixpoint term_of_bst (t : Tree) : Term Tree :=
  match t with
  | Leaf => T Leaf []
  | Node l k v r => T t [term_of_bst l; term_of_bst r]
  end.

(* ---------- Test configuration ---------- *)

Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".

Axiom Time : Type.
Extract Constant Time => "int".

Axiom getCurrentTime : unit -> Time.
Extract Constant getCurrentTime => "fun _ -> Unix.gettimeofday ()".

Axiom timePassed : Time -> Time -> nat.
Extract Constant timePassed => "fun t1 t2 -> ((Float.to_int ((t2 -. t1) *. 1000000.0)))".

(* ---------- Timed results for benchmarking ---------- *)

Record TimedResult := mkTimedResult {
  result: Result;
  time : nat;
}.

Open Scope string_scope.
#[global] Instance showTimedResult : Show TimedResult :=
  {| show r := show (result r) ++
          ", ""time"": " ++ show (time r) |}.

Local Open Scope nat_scope.

(* ---------- Naive timed loop (baseline) ---------- *)

Definition timedRunLoop (max_time : nat) (cprop : CProp ∅): G TimedResult :=
  let start_time := getCurrentTime tt in
  let fix runLoop'
    (fuel : nat)
    (cprop : CProp ∅)
    (passed : nat)
    (discards: nat)
    : G TimedResult :=
  let current_time := getCurrentTime tt in
  if max_time <=? (timePassed start_time current_time) then
    ret (mkTimedResult (mkResult discards false passed []) (timePassed start_time current_time))
  else
    match fuel with
    | O => ret (mkTimedResult (mkResult discards false passed []) (timePassed start_time current_time))
    | S fuel' =>
      res <- generate_and_run cprop (Nat.log2 (passed + discards)%nat);;
      match res with
      | Normal seed false =>
        let shrunk := shrinker cprop seed in
        let printed := printer cprop shrunk in
        ret (mkTimedResult (mkResult discards true (passed + 1) printed) (timePassed start_time current_time))
      | Normal _ true =>
        runLoop' fuel' cprop (passed + 1)%nat discards
      | Discard _ _ =>
        runLoop' fuel' cprop passed (discards + 1)%nat
      end
    end in
    runLoop' number_of_trials cprop 0%nat 0%nat.

(* ---------- Coverage-guided timed loop ---------- *)

Definition coverage_strength : nat := 2.  (* reduced from 2 for performance *)
Definition coverage_fanout : nat := 5.   (* reduced from 10 for performance *)

Definition timedCoverageLoop (max_time : nat) (cprop : CProp ∅)
  (to_term : ⟦⦗cprop⦘⟧ -> Term Tree) : G TimedResult :=
  let start_time := getCurrentTime tt in
  let fix coverageLoop'
    (fuel : nat)
    (passed : nat)
    (discards : nat)
    (seen : list (Desc Tree))
    : G TimedResult :=
  let current_time := getCurrentTime tt in
  if max_time <=? (timePassed start_time current_time) then
    ret (mkTimedResult (mkResult discards false passed []) (timePassed start_time current_time))
  else
    match fuel with
    | O => ret (mkTimedResult (mkResult discards false passed []) (timePassed start_time current_time))
    | S fuel' =>
      (* Generate fanout candidates *)
      candidates <- sequenceG (repeat coverage_fanout (generate_and_run cprop (Nat.log2 (passed + discards))));;
      (* Score each candidate by coverage improvement *)
      let scored :=
        map (fun res =>
          match res with
          | Normal seed _ =>
              let term := to_term seed in
              let ds := covers coverage_strength term in
              let improvement := coverage_improvement ds seen in
              (res, ds, improvement)
          | Discard _ _ => (res, [], 0)
          end) candidates in
      (* Select best candidate *)
      let default := (Discard (none_cprop cprop) GenerationFailure, @nil (Desc Tree), 0) in
      let best :=
        fold_left (fun acc x =>
          match acc, x with
          | (_, _, imp1), (_, _, imp2) =>
              if Nat.ltb imp1 imp2 then x else acc
          end) scored (list_hd default scored) in
      match best with
      | (Normal seed false, _, _) =>
          let shrunk := shrinker cprop seed in
          let printed := printer cprop shrunk in
          ret (mkTimedResult (mkResult discards true (passed + 1) printed) (timePassed start_time current_time))
      | (Normal _ true, ds, _) =>
          let seen' := update_coverage ds seen in
          coverageLoop' fuel' (passed + 1) discards seen'
      | (Discard _ _, _, _) =>
          coverageLoop' fuel' passed (discards + 1) seen
      end
    end in
    coverageLoop' number_of_trials 0 0 [].

(* ---------- Property definitions ---------- *)

Definition prop_InsertValid :=
  @ForAll _ ∅ "t" (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t, _) => isBST t) (
  ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
  ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
  Check (nat · (nat · (Tree · ∅)))
  (fun '(v, (k, (t, _))) => (isBST (insert k v t))))))).

(* Term converter for InsertValid property inputs *)
Definition term_InsertValid (input : ⟦⦗prop_InsertValid⦘⟧) : Term Tree :=
  match input with (t, _) => term_of_bst t end.

(* Coverage-guided test *)
Definition test_prop_InsertValid :=
  coverage_loop_guided_optimized number_of_trials prop_InsertValid coverage_strength coverage_fanout term_InsertValid.

(* ---------- InsertPost property ---------- *)

Definition prop_InsertPost :=
  @ForAll _ ∅ "t" (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t, _) => isBST t) (
  ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
  ForAll "k'" (fun _ => arbitrary) (fun _ k' => arbitrary) (fun _ => shrink) (fun _ => show) (
  ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
  Check (nat · (nat · (nat · (Tree · ∅))))
  (fun '(v, (k', (k, (t, _)))) => ((find k' (insert k v t) = if k =? k' then Some v else find k' t)?))))))).

Definition term_InsertPost (input : ⟦⦗prop_InsertPost⦘⟧) : Term Tree :=
  match input with (t, _) => term_of_bst t end.

Definition test_prop_InsertPost :=
  coverage_loop_guided_optimized number_of_trials prop_InsertPost coverage_strength coverage_fanout term_InsertPost.

(* ---------- InsertModel property ---------- *)

Definition prop_InsertModel :=
  @ForAll _ ∅ "t" (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t, _) => isBST t) (
  ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
  ForAll "v" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
  Check (nat · (nat · (Tree · ∅)))
  (fun '(v, (k, (t, _))) => ((toList (insert k v t) = L_insert (k, v) (deleteKey k (toList t)))?)))))).

Definition term_InsertModel (input : ⟦⦗prop_InsertModel⦘⟧) : Term Tree :=
  match input with (t, _) => term_of_bst t end.

Definition test_prop_InsertModel := coverage_loop_guided_optimized number_of_trials prop_InsertModel coverage_strength coverage_fanout term_InsertModel.

(* ---------- DeleteInsert property ---------- *)

Definition prop_DeleteInsert :=
  @ForAll _ ∅ "t" (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t, _) => isBST t) (
  ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
  ForAll "k'" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
  ForAll "v'" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
  Check (nat · (nat · (nat · (Tree · ∅))))
  (fun '(v', (k', (k, (t, _)))) => (delete k (insert k' v' t) =|= if k =? k' then delete k t else insert k' v' (delete k t)))))))).

Definition term_DeleteInsert (input : ⟦⦗prop_DeleteInsert⦘⟧) : Term Tree :=
  match input with (t, _) => term_of_bst t end.

Definition test_prop_DeleteInsert := coverage_loop_guided_optimized number_of_trials prop_DeleteInsert coverage_strength coverage_fanout term_DeleteInsert.

(* ---------- InsertInsert property ---------- *)

Definition prop_InsertInsert :=
  @ForAll _ ∅ "t" (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t, _) => isBST t) (
  ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
  ForAll "k'" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
  ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
  ForAll "v'" (fun _ => arbitrary) (fun _ v' => arbitrary) (fun _ => shrink) (fun _ => show) (
  Check (nat · (nat · (nat · (nat · (Tree · ∅)))))
  (fun '(v', (v, (k', (k, (t, _))))) => (insert k v (insert k' v' t) =|= if k =? k' then insert k v t else insert k' v' (insert k v t))))))))).

Definition term_InsertInsert (input : ⟦⦗prop_InsertInsert⦘⟧) : Term Tree :=
  match input with (t, _) => term_of_bst t end.

Definition test_prop_InsertInsert := coverage_loop_guided_optimized number_of_trials prop_InsertInsert coverage_strength coverage_fanout term_InsertInsert.

(* ---------- InsertUnion property ---------- *)

Definition prop_InsertUnion :=
  @ForAll _ ∅ "t" (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t, _) => isBST t) (
  @ForAll _ (Tree · ∅) "t'" (fun '(_, s) => arbitrary) (fun '(_, s) _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · _) (fun '(t', _) => isBST t') (
  ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
  ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
  Check (nat · (nat · (Tree · (Tree · ∅))))
  (fun '(v, (k, (t', (t, _)))) => (insert k v (union t t') =|= union (insert k v t) t')))))))).

Definition term_InsertUnion (input : ⟦⦗prop_InsertUnion⦘⟧) : Term Tree :=
  match input with (t, (t', _)) =>
    (* Use union of both trees for coverage *)
    CoverageLoop.T (union t t') [term_of_bst t; term_of_bst t']
  end.

Definition test_prop_InsertUnion := coverage_loop_guided_optimized number_of_trials prop_InsertUnion coverage_strength coverage_fanout term_InsertUnion.

(* ---------- UnionDeleteInsert property ---------- *)

Definition prop_UnionDeleteInsert :=
  @ForAll _ ∅ "t " (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t, _) => isBST t) (
  @ForAll _ (Tree · ∅) "t'" (fun '(_, s) => arbitrary) (fun '(_, s) _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · _) (fun '(t', _) => isBST t') (
  ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
  ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
  Check (nat · (nat · (Tree · (Tree · ∅))))
  (fun '(v, (k, (t', (t, _)))) => ((union (delete k t) (insert k v t') =|= insert k v (union t t')))))))))).

Definition term_UnionDeleteInsert (input : ⟦⦗prop_UnionDeleteInsert⦘⟧) : Term Tree :=
  match input with (t, (t', _)) =>
    CoverageLoop.T (union t t') [term_of_bst t; term_of_bst t']
  end.

Definition test_prop_UnionDeleteInsert := coverage_loop_guided_optimized number_of_trials prop_UnionDeleteInsert coverage_strength coverage_fanout term_UnionDeleteInsert.

(* ---------- DeleteValid property ---------- *)

Definition prop_DeleteValid :=
  @ForAll _ ∅ "t" (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t, _) => isBST t) (
  ForAll "k" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
  Check (nat · (Tree · ∅))
  (fun '(k, (t, _)) => (isBST (delete k t)))))).

Definition term_DeleteValid (input : ⟦⦗prop_DeleteValid⦘⟧) : Term Tree :=
  match input with (t, _) => term_of_bst t end.

Definition test_prop_DeleteValid := coverage_loop_guided_optimized number_of_trials prop_DeleteValid coverage_strength coverage_fanout term_DeleteValid.

(* ---------- UnionValid property ---------- *)

Definition prop_UnionValid :=
  @ForAll _ ∅ "t1" (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t1, _) => isBST t1) (
  @ForAll _ (Tree · ∅) "t2" (fun '(_, s) => arbitrary) (fun '(_, s) _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · _) (fun '(t2, _) => isBST t2) (
  Check (Tree · (Tree · ∅))
  (fun '(t2, (t1, _)) => (isBST (union t1 t2))))))).

Definition term_UnionValid (input : ⟦⦗prop_UnionValid⦘⟧) : Term Tree :=
  match input with (t1, (t2, _)) =>
    CoverageLoop.T (union t1 t2) [term_of_bst t1; term_of_bst t2]
  end.

Definition test_prop_UnionValid := coverage_loop_guided_optimized number_of_trials prop_UnionValid coverage_strength coverage_fanout term_UnionValid.

(* ---------- DeletePost property ---------- *)

Definition prop_DeletePost :=
  @ForAll _ ∅ "t" (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t, _) => isBST t) (
  ForAll "k" (fun _ => arbitrary) (fun _ _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  ForAll "k'" (fun _ => arbitrary) (fun _ _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Check (nat · (nat · (Tree · ∅)))
  (fun '(k', (k, (t, _))) => ((find k' (delete k t) = if k =? k' then None else find k' t)?)))))).

Definition term_DeletePost (input : ⟦⦗prop_DeletePost⦘⟧) : Term Tree :=
  match input with (t, _) => term_of_bst t end.

Definition test_prop_DeletePost := coverage_loop_guided_optimized number_of_trials prop_DeletePost coverage_strength coverage_fanout term_DeletePost.

(* ---------- UnionPost property ---------- *)

Definition prop_UnionPost :=
  @ForAll _ ∅ "t" (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t, _) => isBST t) (
  @ForAll _ (Tree · ∅) "t'" (fun '(_, s) => arbitrary) (fun '(_, s) _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
  Check (nat · (Tree · (Tree · ∅)))
  (fun '(k, (t', (t, _))) => (let lhs := find k (union t t') in
                              match (find k t) with
                              | Some rhs => (lhs = (Some rhs))?
                              | None => match (find k t') with
                                        | Some rhs => (lhs = (Some rhs))?
                                        | None => (lhs = None)?
                                        end
                              end)))))).

Definition term_UnionPost (input : ⟦⦗prop_UnionPost⦘⟧) : Term Tree :=
  match input with (t, (t', _)) =>
    CoverageLoop.T (union t t') [term_of_bst t; term_of_bst t']
  end.

Definition test_prop_UnionPost := coverage_loop_guided_optimized number_of_trials prop_UnionPost coverage_strength coverage_fanout term_UnionPost.

(* ---------- DeleteModel property ---------- *)

Definition prop_DeleteModel :=
  @ForAll _ ∅ "t" (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t, _) => isBST t) (
  ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
  Check (nat · (Tree · ∅))
  (fun '(k, (t, _)) => ((toList (delete k t) = deleteKey k (toList t))?))))).

Definition term_DeleteModel (input : ⟦⦗prop_DeleteModel⦘⟧) : Term Tree :=
  match input with (t, _) => term_of_bst t end.

Definition test_prop_DeleteModel := coverage_loop_guided_optimized number_of_trials prop_DeleteModel coverage_strength coverage_fanout term_DeleteModel.

(* ---------- UnionModel property ---------- *)

Definition prop_UnionModel :=
  @ForAll _ ∅ "t" (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t, _) => isBST t) (
  @ForAll _ (Tree · ∅) "t'" (fun '(_, s) => arbitrary) (fun '(_, s) _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · _) (fun '(t', _) => isBST t') (
  Check (Tree · (Tree · ∅))
  (fun '(t', (t, _)) => ((toList (union t t') = L_sort (L_unionBy (fun x y => x) (toList t) (toList t')))?)))))).

Definition term_UnionModel (input : ⟦⦗prop_UnionModel⦘⟧) : Term Tree :=
  match input with (t, (t', _)) =>
    CoverageLoop.T (union t t') [term_of_bst t; term_of_bst t']
  end.

Definition test_prop_UnionModel := coverage_loop_guided_optimized number_of_trials prop_UnionModel coverage_strength coverage_fanout term_UnionModel.

(* ---------- InsertDelete property ---------- *)

Definition prop_InsertDelete :=
  @ForAll _ ∅ "t" (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t, _) => isBST t) (
  ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
  ForAll "k'" (fun _ => arbitrary) (fun _ k' => arbitrary) (fun _ => shrink) (fun _ => show) (
  ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
  Check (nat · (nat · (nat · (Tree · ∅))))
  (fun '(v, (k', (k, (t, _)))) => ((insert k v (delete k' t) =|= if k =? k' then insert k v t else delete k' (insert k v t))))))))).

Definition term_InsertDelete (input : ⟦⦗prop_InsertDelete⦘⟧) : Term Tree :=
  match input with (t, _) => term_of_bst t end.

Definition test_prop_InsertDelete := coverage_loop_guided_optimized number_of_trials prop_InsertDelete coverage_strength coverage_fanout term_InsertDelete.

(* ---------- DeleteDelete property ---------- *)

Definition prop_DeleteDelete :=
  @ForAll _ ∅ "t" (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t, _) => isBST t) (
  ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
  ForAll "k'" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
  Check (nat · (nat · (Tree · ∅)))
  (fun '(k', (k, (t, _))) => ((delete k (delete k' t) =|= delete k' (delete k t)))))))).

Definition term_DeleteDelete (input : ⟦⦗prop_DeleteDelete⦘⟧) : Term Tree :=
  match input with (t, _) => term_of_bst t end.

Definition test_prop_DeleteDelete := coverage_loop_guided_optimized number_of_trials prop_DeleteDelete coverage_strength coverage_fanout term_DeleteDelete.

(* ---------- DeleteUnion property ---------- *)

Definition prop_DeleteUnion :=
  @ForAll _ ∅ "t" (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t, _) => isBST t) (
  @ForAll _ (Tree · ∅) "t'" (fun '(_, s) => arbitrary) (fun '(_, s) _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · _) (fun '(t', _) => isBST t') (
  ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
  Check (nat · (Tree · (Tree · ∅)))
  (fun '(k, (t', (t, _))) => (delete k (union t t') =|= union (delete k t) (delete k t')))))))).

Definition term_DeleteUnion (input : ⟦⦗prop_DeleteUnion⦘⟧) : Term Tree :=
  match input with (t, (t', _)) =>
    CoverageLoop.T (union t t') [term_of_bst t; term_of_bst t']
  end.

Definition test_prop_DeleteUnion := coverage_loop_guided_optimized number_of_trials prop_DeleteUnion coverage_strength coverage_fanout term_DeleteUnion.

(* ---------- UnionUnionIdem property ---------- *)

Definition prop_UnionUnionIdem :=
  @ForAll _ ∅ "t" (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t, _) => isBST t) (
  Check (Tree · ∅)
  (fun '(t, _) => (union t t =|= t)))).

Definition term_UnionUnionIdem (input : ⟦⦗prop_UnionUnionIdem⦘⟧) : Term Tree :=
  match input with (t, _) => term_of_bst t end.

Definition test_prop_UnionUnionIdem := coverage_loop_guided_optimized number_of_trials prop_UnionUnionIdem coverage_strength coverage_fanout term_UnionUnionIdem.

(* ---------- UnionUnionAssoc property ---------- *)

Definition prop_UnionUnionAssoc :=
  @ForAll _ ∅ "t1" (fun _ => arbitrary)(fun s _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · ∅) (fun '(t1, _) => isBST t1) (
  @ForAll _ (Tree · ∅) "t2" (fun '(_, s) => arbitrary) (fun '(_, s) _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · _) (fun '(t2, _) => isBST t2) (
  @ForAll _ (Tree · (Tree · ∅)) "t3" (fun '(_, (_, s)) => arbitrary) (fun '(_, (_, s)) _ => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Tree · _) (fun '(t3, _) => isBST t3) (
  Check (Tree · (Tree · (Tree · ∅)))
  (fun '(t3, (t2, (t1, _))) => (union (union t1 t2) t3 =|= union t1 (union t2 t3))))))))).

Definition term_UnionUnionAssoc (input : ⟦⦗prop_UnionUnionAssoc⦘⟧) : Term Tree :=
  match input with (t1, (t2, (t3, _))) =>
    CoverageLoop.T (union (union t1 t2) t3) [term_of_bst t1; term_of_bst t2; term_of_bst t3]
  end.

Definition test_prop_UnionUnionAssoc := coverage_loop_guided_optimized number_of_trials prop_UnionUnionAssoc coverage_strength coverage_fanout term_UnionUnionAssoc.
