

(* 
Record DoubleQueuePool {A E : Type} := {
  hpq: list (A * E);
  lpq: list (A * E);
}.

Definition insertHighPrioritySeed {A E: Type} (seed: (A * E)) (pool: DoubleQueuePool) : DoubleQueuePool :=
  {| hpq := (seed :: (hpq pool)) ; lpq := (lpq pool) |}.

Definition insertLowPrioritySeed {A E: Type} (seed: (A * E)) (pool: DoubleQueuePool) : DoubleQueuePool :=
  {| hpq := (hpq pool) ; lpq := (seed :: (lpq pool)) |} .

Fixpoint maxSeed {A E: Type} `{OrdType E} (cmax: option (A * E)) (q: list (A * E)) : option A :=
  match q with
  | [] => match cmax with
          | None => None
          | Some (a, e) => Some a
          end
  | (h :: t) => match cmax with
                | None => maxSeed (Some h) t
                | Some (a, e) => if leq e (snd h) then maxSeed (Some h) t else maxSeed (Some (a, e)) t
                end
  end.

Definition sampleSeedDQP {A E : Type} `{OrdType E} (pool: DoubleQueuePool) : option A * DoubleQueuePool :=
  match (hpq pool) with
  | []  => (maxSeed None (lpq pool), pool)
  | _   => (maxSeed None (hpq pool), pool)
  end.


  #[global] Instance SeedPoolDQP {A E : Type} `{OrdType E} : @SeedPool A E (@DoubleQueuePool A E) :=
  {| mkPool _ := {| hpq := []; lpq := [] |};
     schedule pool seed := pool;
     insert seed pool := {| hpq := seed :: (hpq pool); lpq := lpq pool |};
     sample pool :=
       match (hpq pool) with
       | []  => (maxSeed None (lpq pool), pool)
       | _   => (maxSeed None (hpq pool), pool)
       end
  |}. *)
  