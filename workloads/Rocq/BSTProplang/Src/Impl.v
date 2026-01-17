
Require Import List ZArith. Import ListNotations.
Require Extraction.
From QuickChick Require Import QuickChick.
Import QcNotation.

Inductive Tree :=
| Leaf
| Node : Tree -> nat -> nat -> Tree -> Tree.

Derive (Show) for Tree.


Axiom fuel : nat. Extract Constant fuel => "100000".



Fixpoint insert (k : nat) (v: nat) (t : Tree) :=
  match t with
  | Leaf => Node Leaf k v Leaf
  | Node l k' v' r =>
  (*! *)
    if k <? k' then Node (insert k v l) k' v' r
    else if k' <? k then Node l k' v' (insert k v r)
    else Node l k' v r
  (*!! insert_1 *)
  (*!
    Node Leaf k v Leaf
  *)
  (*!! insert_2 *)
  (*!
    if k <? k' then Node (insert k v l) k' v' r
    else Node l k' v r
  *)
  (*!! insert_3 *)
  (*!
    if k <? k' then Node (insert k v l) k' v' r
    else if k' <? k then Node l k' v' (insert k v r)
    else Node l k' v' r
  *)
  (* !*)
  end.

Fixpoint join (l: Tree) (r: Tree) :=
  match l, r with
  | Leaf, _ => r
  | _, Leaf => l
  | Node l k v r, Node l' k' v' r' =>
    Node l k v (Node (join r l') k' v' r')
  end
.
  

Fixpoint delete (k: nat) (t: Tree) :=
  match t with
  | Leaf => Leaf
  | Node l k' v' r =>
  (*! *)
  if k <? k' then Node (delete k l) k' v' r
  else if k' <? k then Node l k' v' (delete k r)
  else join l r
  (*!! delete_4 *)
  (*!
  if k <? k' then delete k l
  else if k' <? k then delete k r
  else join l r
  *)
  (*!! delete_5 *)
  (*!
  if k' <? k then Node (delete k l) k' v' r
  else if k <? k' then Node l k' v' (delete k r)
  else join l r
  *)
  (* !*)
  end.



Fixpoint below (k: nat) (t: Tree) :=
  match k, t with
  | _, Leaf => Leaf
  | k, Node l k' v r =>
    if k <=? k' then below k l
    else Node l k' v (below k r)
  end.

Fixpoint above (k: nat) (t: Tree) :=
  match k, t with
  | _, Leaf => Leaf
  | k, (Node l k' v r) =>
    if k' <=? k then above k r
    else Node (above k l) k' v r
  end.




Fixpoint union_ (l: Tree) (r: Tree) (f: nat) :=
  match f with
  | 0 => Leaf
  | S f' =>
    match l, r with
    | Leaf, _ => r
    | _, Leaf => l
    (*! *)
    | (Node l k v r), t =>
      Node (union_ l (below k t) f') k v (union_ r (above k t) f')
    (*!! union_6 *)
    (*!
    | (Node l k v r), (Node l' k' v' r') =>
      Node l k v (Node (union_ r l' f') k' v' r')
    *)
    (*!! union_7 *)
    (*!
    | (Node l k v r), (Node l' k' v' r') =>
      if k =? k' then Node (union_ l l' f') k v (union_ r r' f')
      else if k <? k' then Node l k v (Node (union_ r l' f') k' v' r')
      else union_ (Node l' k' v' r') (Node l k v r) f'
    *)
    (*!! union_8 *)
    (*!
    | (Node l k v r), (Node l' k' v' r') =>
    if k =? k'  then Node (union_ l l' f') k v (union_ r r' f')
    else if k <? k'   then Node (union_ l (below k l') f') k v
                            (union_ r (Node (above k l') k' v' r') f')
      else union_ (Node l' k' v' r') (Node l k v r) f'
    *)
    (* !*)
    end
  end
.

Definition union (l: Tree) (r: Tree) :=
  union_ l r fuel.


Fixpoint find (k: nat) (t: Tree): option nat :=
  match k, t with
  | _, Leaf => None
  | k, (Node l k' v' r) =>
    if k <? k' then find k l
    else if k' <? k then find k r
    else Some v'
  end
.


Fixpoint size (t: Tree) :=
  match t with
  | Leaf => 0
  | Node l k v r => 1 + size l + size r
  end
.






