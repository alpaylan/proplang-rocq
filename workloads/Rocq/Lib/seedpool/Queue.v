

Module Queue.
  Local Open Scope list_scope.

  Definition mkQueue {T: Type} : unit -> list T :=
    fun _ => nil.

  Definition is_empty {T: Type} (q: list T) : bool :=
    match q with
    | [] => true
    | _ => false
    end.

  Definition push_front {T: Type} (seed: T) (q: list T) : list T :=
    q ++ [seed].
  
  Definition push_back {T: Type} (seed: T) (q: list T) : list T :=
    seed :: q.

  Definition pop_back {T: Type} (q: list T) : option (T * list T) :=
    match q with
    | [] => None
    | h :: t => Some (h, t)
    end.

  Definition pop_front {T: Type} (q: list T) : option (T * list T) :=
    match rev q with
    | [] => None
    | h :: t => Some (h, rev t)
    end.

End Queue.

Module FIFOQueue.
  Import Queue.

  Definition t := list.

  Definition mkFIFOQueue {T: Type} : unit -> t T :=
    mkQueue.

  Definition is_empty {T: Type} (q: t T) : bool :=
    is_empty q.

  Definition push {T: Type} (seed: T) (q: t T) : t T :=
    push_back seed q.

  Definition pop {T: Type} (q: t T) : option (T * t T) :=
    pop_front q.

End FIFOQueue.

Module FILOQueue.
  Import Queue.

  Definition t := list.

  Definition mkFILOQueue {T: Type} : unit -> t T :=
    mkQueue.

  Definition is_empty {T: Type} (q: t T) : bool :=
    is_empty q.

  Definition push {T: Type} (seed: T) (q: t T) : t T :=
    push_front seed q.

  Definition pop {T: Type} (q: t T) : option (T * t T) :=
    pop_front q.

End FILOQueue.
    

Import FIFOQueue.

#[global] Instance FIFOSeedPool {A F: Type}  `{Scalar F} : @SeedPool A F (FIFOQueue.t (@Seed A F)) :=
{| mkPool _ := FIFOQueue.mkFIFOQueue tt;
  invest seed pool := match seed with 
                      | (a, f) => FIFOQueue.push (mkSeed a f 100) pool
                      end ;
  revise pool :=  match FIFOQueue.pop pool with
                  | None => pool
                  | Some (h, t) => 
                      let '{| input := a; feedback := f; energy := n|} := h in
                      if (n =? 0) then t
                      else FIFOQueue.push (mkSeed a f (n - 1)) t
                  end ;
  sample pool := match FIFOQueue.pop pool with
                 | None => Generate
                 | Some(h, _) => if (energy h =? 0) 
                              then Generate
                              else Mutate h
                 end ;
  best pool := let fix maxSeed (cmax: option (@Seed A F)) (q: FIFOQueue.t (@Seed A F)) `{Scalar F} : option (@Seed A F) :=
                match q with
                | [] => cmax
                | h :: t => match cmax with
                            | None => maxSeed (Some h) t
                            | Some seed => if ((scale (feedback h)) >? (scale (feedback seed))) then maxSeed (Some h) t else maxSeed (Some seed) t
                            end
                end in
                maxSeed None pool
|}.



Import FILOQueue.

#[global] Instance FILOSeedPool {A F: Type}  `{Scalar F} : @SeedPool A F (FILOQueue.t (@Seed A F)) :=
{| mkPool _ := FILOQueue.mkFILOQueue tt;
  invest seed pool := match seed with 
                      | (a, f) => FILOQueue.push (mkSeed a f 1) pool
                      end ;
  revise pool :=  match FILOQueue.pop pool with
                  | None => pool
                  | Some (h, t) => 
                      let '{| input := a; feedback := f; energy := n|} := h in
                      if (n =? 0) then t
                      else FILOQueue.push (mkSeed a f (n - 1)) t
                  end ;
  sample pool := match FILOQueue.pop pool with
                 | None => Generate
                 | Some(h, _) => if (energy h =? 0) 
                              then Generate
                              else Mutate h
                 end ;
  best pool := let fix maxSeed (cmax: option (@Seed A F)) (q: FIFOQueue.t (@Seed A F)) `{Scalar F} : option (@Seed A F) :=
                match q with
                | [] => cmax
                | h :: t => match cmax with
                            | None => maxSeed (Some h) t
                            | Some seed => if ((scale (feedback h)) >? (scale (feedback seed))) then maxSeed (Some h) t else maxSeed (Some seed) t
                            end
                end in
                maxSeed None pool
|}.


