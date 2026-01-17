Require Import Lia ZArith.
From PropLang Require Import SeedPool.

Module LeftistHeap.

  Inductive LTree (A : Type) : Type :=
  | E : LTree A
  | N : nat -> A -> LTree A -> LTree A -> LTree A.

  Arguments E {A}.
  Arguments N {A} _ _ _ _.

  Definition right_spine {A : Type} (t : LTree A) : nat :=
  match t with
    | E => 0
    | N r _ _ _ => r
  end.

  Inductive LeftBiased {A : Type} : LTree A -> Prop :=
    | LeftBiased_E : LeftBiased E
    | LeftBiased_N :
        forall (v : A) (l r : LTree A),
          (right_spine r <= right_spine l)%nat ->
          LeftBiased l -> LeftBiased r ->
            LeftBiased (N (1 + right_spine r) v l r).

  Inductive Elem {A : Type} (x : A) : LTree A -> Prop :=
    | Elem_root :
        forall (n : nat) (l r : LTree A), Elem x (N n x l r)
    | Elem_l :
        forall (n : nat) (v : A) (l r : LTree A),
          Elem x l -> Elem x (N n v l r)
    | Elem_r :
        forall (n : nat) (v : A) (l r : LTree A),
          Elem x r -> Elem x (N n v l r).

  Definition Heap {A F: Type} := LTree (@Seed A F).

  Definition seed_in_z {A F: Type} `{Scalar F} (x: @Seed A F) : Z := scale (feedback x).

  Inductive isHeap {A F: Type} `{Scalar F} : @Heap A F -> Prop :=
    | isHeap_E : isHeap E
    | isHeap_N :
        forall  (n: nat) (v: Seed) (l r : Heap),
          (forall x : @Seed A F, Elem x l -> (seed_in_z v >= seed_in_z x)%Z) -> isHeap l ->
          (forall x : @Seed A F, Elem x r -> (seed_in_z v >= seed_in_z x)%Z) -> isHeap r ->
            isHeap (N n v l r).

  #[global] Hint Constructors LTree LeftBiased Elem isHeap : core.

  Definition balance {A F: Type}
    (v : @Seed A F) (l r : Heap) : Heap :=
    if (right_spine r <=? right_spine l)%nat
    then N (1 + right_spine r) v l r
    else N (1 + right_spine l) v r l.

  Fixpoint size {A F: Type} (t : @Heap A F) : nat :=
  match t with
    | E => 0
    | N _ _ l r => 1 + size l + size r
  end.

  Definition sum_of_sizes
    {A F: Type}
    (p : @Heap A F * @Heap A F) : nat :=
    size (fst p) + size (snd p).

  Function merge {A F: Type} (p : @Heap A F * @Heap A F) (witness: Scalar F) {measure sum_of_sizes p} : @Heap A F :=
  match p with
    | (E, t2) => t2
    | (t1, E) => t1
    | (N _ v l r as t1, N _ v' l' r' as t2) =>
        if ((seed_in_z v) >=? (seed_in_z v'))%Z
        then balance v l (merge (r, t2) witness)
        else balance v' l' (merge (t1, r') witness)
  end.
  Proof.
  1-2: intros; cbn; lia.
  Defined.

  Definition empty {A F: Type} (tt: unit) : @Heap A F := E.

  Definition isEmpty {A F: Type} (t : @Heap A F) : bool :=
  match t with
    | E => true
    | _ => false
  end.

  Definition singleton {A F: Type} (x : @Seed A F) : Heap := N 1 x E E.

  Definition insert {A F: Type} `{w: Scalar F} (x : @Seed A F) (t : Heap) : Heap :=
  @merge A F (singleton x, t) w.

  Definition findMax {A F: Type} (t : Heap) : option (@Seed A F) :=
  match t with
    | E => None
    | N _ v _ _ => Some v
  end.

  Definition deleteMax {A F: Type} `{w: Scalar F} (t : Heap) : option Seed * Heap :=
  match t with
    | E => (None, E)
    | N _ v l r => (Some v, @merge A F (l, r) w)
  end.

  Definition extractMax {A F: Type} `{w: Scalar F}
  (t : Heap) : option (Seed * Heap) :=
  match t with
    | E => None
    | N _ v l r => Some (v, @merge A F (l, r) w)
  end.

End LeftistHeap.

#[global] Instance HeapSeedPool {A F: Type} `{Scalar F} : @SeedPool A F (@LeftistHeap.Heap A F) :=
{| mkPool _ := LeftistHeap.empty tt;
  invest seed pool := match seed with
                      | (a, f) => LeftistHeap.insert (mkSeed a f 100%Z) pool
                      end ;
  revise pool :=  match LeftistHeap.extractMax pool with
                  | None => pool
                  | Some (seed, rest) =>
                    let '{| input := a; feedback := f; energy := n|} := seed in
                    if (n =? 0)%Z then rest
                    else LeftistHeap.insert (mkSeed a f (n - 1)%Z) rest
                  end ;
  sample pool := match LeftistHeap.extractMax pool with
                 | None => Generate
                 | Some (seed, _) => Mutate seed
                 end ;
  best pool := match LeftistHeap.extractMax pool with
               | None => None
               | Some (seed, _) => Some seed
               end
|}.
