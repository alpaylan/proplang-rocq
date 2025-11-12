
Record SingletonPool {A F: Type} := {
  seed: option (@Seed A F);
}.

#[global] Instance StaticSingletonPool {A F: Type} : @SeedPool A F (@SingletonPool A F) :=
  {| mkPool _ := {| seed := None |};
     invest seed pool := match seed with 
                         | (a, f) => {| seed := Some (mkSeed a f 1) |}
                         end ;
     revise pool := pool ;
     sample pool := match seed pool with
                    | None => Generate
                    | Some seed => Mutate seed
                    end ;
     best pool := seed pool
  |}.

#[global] Instance DynamicMonotonicSingletonPool {A F: Type} : @SeedPool A F (@SingletonPool A F) :=
  {| mkPool _ := {| seed := None |};
    invest seed pool := match seed with 
                        | (a, f) => {| seed := Some (mkSeed a f 1) |}
                        end ;
    revise pool :=  match seed pool with
                    | None => pool
                    | Some seed => 
                      let '{| input := a; feedback := f; energy := n |} := seed in
                      {| seed := Some (mkSeed a f (n - 1)) |}
                    end ;               
    sample pool := match seed pool with
                   | None => Generate
                   | Some seed => if (energy seed =? 0) 
                                    then Generate
                                    else Mutate seed

                   end ;
    best pool := seed pool
|}.

#[global] Instance DynamicResettingSingletonPool {A F: Type} : @SeedPool A F (@SingletonPool A F) :=
  {| mkPool _ := {| seed := None |};
    invest seed pool := match seed with 
                        | (a, f) => {| seed := Some (mkSeed a f 1) |}
                        end ;
    revise pool := match seed pool with
                   | None => pool
                   | Some seed => 
                     let '{| input := a; feedback := f; energy := n |} := seed in
                     {| seed := Some (mkSeed a f (n - 1)) |}
                   end ;
    sample pool := match seed pool with
                   | None => Generate
                   | Some seed => if (energy seed =? 0) 
                                    then Generate
                                    else Mutate seed
                   end ;
    best pool := match seed pool with
                 | None => None
                 | Some seed => if (energy seed =? 0) then None else Some seed
                 end
|}.
