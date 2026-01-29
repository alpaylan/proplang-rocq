From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import TestingCommon.
Require Import Reachability.
Require Import SSNI.
Require Import LLNI.
Require Import SanityChecks.
Require Import Shrinking.
Require Import Printing.
Require Import ZArith.

From mathcomp Require Import ssreflect eqtype seq.
Import LabelEqType.

From PropLang Require Import PropLang.
From PropLang Require Import SeedPool.
From PropLang.seedpool Require Import Heap.
From PropLang.seedpool Require Import Queue.
From PropLang.loops Require Import TargetLoop.

Local Open Scope nat_scope.
Local Open Scope prop_scope.

(* ------------------------------------------------------ *)
(* ------------ Targeted Generator Constants ------------ *)
(* ------------------------------------------------------ *)
(* We increase code_len to allow for longer execution traces *)

Module C.

Definition min_no_frames := 2.
Definition max_no_frames := 4.
Definition min_frame_size := 2%Z.
Definition max_frame_size := 4%Z.

(* Increased code length for longer sequences *)
Definition code_len := 20.

Definition min_no_prins := 2.
Definition max_no_prins := 4.

Definition no_registers := 10.
End C.

(* ------------------------------------------------------ *)
(* ----- Generation of primitives ----------------------- *)
(* ------------------------------------------------------ *)

Definition gen_from_length (len : Z) :=
  choose (0, len - 1)%Z.

Definition gen_from_nat_length (len : nat) :=
  choose (0, Z.of_nat len - 1)%Z.

Record Info := MkInfo
  { def_block : mframe
  ; code_len  : Z
  ; data_len  : list (mframe * Z)
  ; no_regs   : nat
  }.

Class SmartGen (A : Type) := {
  smart_gen : Info -> G A
}.

Definition gen_BinOpT : G BinOpT :=
  elems_ BAdd [:: BAdd; BMult; BJoin; BFlowsTo; BEq].

Definition gen_label : G Label :=
  elems_ bot all_labels.

Definition gen_label_between_lax (l1 l2 : Label) : G Label :=
  elems_ l2 (filter (fun l => isLow l1 l) (allThingsBelow l2)).

#[global] Instance smart_gen_label : SmartGen Label :=
{|
  smart_gen _info := gen_label
|}.

Definition gen_high_label (obs : Label) : G Label :=
  elems_ H (filter (fun l => negb (isLow l obs)) (allThingsBelow H)).

Definition gen_pointer (inf : Info) : G Pointer :=
    let '(MkInfo def _ dfs _) := inf in
    bindGen (elems_ (def, Z0) dfs) (fun mfl =>
    let (mf, len) := mfl in
    bindGen (gen_from_length len) (fun addr =>
    returnGen (Ptr mf addr))).

#[global] Instance smart_gen_pointer : SmartGen Pointer :=
  {|
    smart_gen := gen_pointer
  |}.

Definition gen_int (inf : Info) : G Z :=
  freq_ (pure Z0)
            [:: (10, arbitrary);
                (1 , pure Z0);
                (10, gen_from_length (code_len inf))].

#[global] Instance smart_gen_int : SmartGen Z :=
  {|
    smart_gen := gen_int
  |}.

Definition gen_value (inf : Info) : G Value :=
  let '(MkInfo def cl dfs _) := inf in
    freq_ (liftGen Vint arbitrary)
              [:: (1, liftGen Vint  (smart_gen inf));
                  (1, liftGen Vptr  (smart_gen inf));
                  (1, liftGen Vlab  (smart_gen inf))].

#[global] Instance smart_gen_value : SmartGen Value :=
  {|
    smart_gen := gen_value
  |}.

Definition gen_atom (inf : Info) : G Atom :=
  liftGen2 Atm (smart_gen inf) (smart_gen inf).

#[global] Instance smart_gen_atom : SmartGen Atom :=
  {|
    smart_gen := gen_atom
  |}.

Definition gen_PC (inf : Info) : G Ptr_atom :=
  bindGen (smart_gen inf) (fun pcLab =>
  bindGen (gen_from_length (code_len inf)) (fun pcPtr =>
  returnGen (PAtm pcPtr pcLab))).

#[global] Instance smart_gen_pc : SmartGen Ptr_atom :=
  {|
    smart_gen := gen_PC
  |}.

(* ------------------------------------------------------ *)
(* --- Generation of groups of primitives --------------- *)
(* ------------------------------------------------------ *)

Definition gen_registers (inf : Info) : G regSet :=
  vectorOf (no_regs inf) (smart_gen inf).

#[global] Instance smart_gen_registers : SmartGen regSet :=
  {|
    smart_gen := gen_registers
  |}.

Definition smart_gen_stack_loc inf : G StackFrame :=
    bindGen (smart_gen inf) (fun regs =>
    bindGen (smart_gen inf) (fun pc   =>
    bindGen (gen_from_nat_length (no_regs inf)) (fun target =>
    bindGen (smart_gen inf) (fun retLab =>
    returnGen (SF pc regs target retLab))))).

Definition smart_gen_stack inf : G Stack :=
  freq_ (pure (ST nil))
            [:: (1, pure (ST nil));
                (9, bindGen (smart_gen_stack_loc inf) (fun sl =>
                    returnGen (ST [:: sl])))].

(* ------------------------------------------------------ *)
(* ---------- Instruction generation -------------------- *)
(* ------------------------------------------------------ *)

Fixpoint groupRegisters (st : SState) (rs : regSet)
         (dptr cptr num lab : list regId) (n : Z) :=
  match rs with
    | nil => (dptr, cptr, num, lab)
    | (Vint i @ _) :: rs' =>
      let cptr' := if (Z.leb 0 i && Z.ltb i (Z_of_nat (List.length (st_imem st))))%bool
                   then n :: cptr else cptr in
      groupRegisters st rs' dptr cptr' (n :: num) lab (Z.succ n)
    | (Vptr p @ _ ) :: rs' =>
      groupRegisters st rs' (n :: dptr) cptr num lab (Z.succ n)
    | (Vlab _ @ _) :: rs' =>
      groupRegisters st rs' dptr cptr num (n :: lab) (Z.succ n)
  end.

Definition onNonEmpty {A : Type} (l : list A) (n : nat) :=
  match l with
    | nil => 0
    | _   => n
  end.

(* Instruction generation favoring instructions that allow longer traces *)
Definition ainstrSSNI (st : SState) : G Instr :=
  let '(St im m stk regs pc ) := st in
  let '(dptr, cptr, num, lab) :=
      groupRegisters st regs [::] [::] [::] [::] Z0 in
  let genRegPtr := gen_from_length (Zlength regs) in
  freq_ (pure Nop) [::
    (* Nop - safe, keeps execution going *)
    (5, pure Nop);
    (* Halt - avoid to get longer traces *)
    (0, pure Halt);
    (* PcLab *)
    (10, liftGen PcLab genRegPtr);
    (* Lab *)
    (10, liftGen2 Lab genRegPtr genRegPtr);
    (* MLab *)
    (onNonEmpty dptr 10, liftGen2 MLab (elems_ Z0 dptr) genRegPtr);
    (* PutLab *)
    (10, liftGen2 PutLab gen_label genRegPtr);
    (* BCall - important for interesting control flow *)
    (20 * onNonEmpty cptr 1 * onNonEmpty lab 1,
     liftGen3 BCall (elems_ Z0 cptr) (elems_ Z0 lab) genRegPtr);
    (* BRet *)
    (if negb (emptyList (unStack stk)) then 50 else 0, pure BRet);
    (* Alloc *)
    (100 * onNonEmpty num 1 * onNonEmpty lab 1,
     liftGen3 Alloc (elems_ Z0 num) (elems_ Z0 lab) genRegPtr);
    (* Load *)
    (onNonEmpty dptr 15, liftGen2 Load (elems_ Z0 dptr) genRegPtr);
    (* Store *)
    (onNonEmpty dptr 80, liftGen2 Store (elems_ Z0 dptr) genRegPtr);
    (* Write *)
    (onNonEmpty dptr 80, liftGen2 Write (elems_ Z0 dptr) genRegPtr);
    (* Jump - enable loops for longer traces *)
    (onNonEmpty cptr 20, liftGen Jump (elems_ Z0 cptr));
    (* BNZ - conditional branching for interesting paths *)
    (onNonEmpty num 20,
      liftGen2 BNZ (choose (Zminus (0%Z) (1%Z), 2%Z))
                   (elems_ Z0 num));
    (* PSetOff *)
    (10 * onNonEmpty dptr 1 * onNonEmpty num 1,
     liftGen3 PSetOff (elems_ Z0 dptr) (elems_ Z0 num) genRegPtr);
    (* Put *)
    (10, liftGen2 Put arbitrary genRegPtr);
    (* BinOp *)
    (onNonEmpty num 15,
     liftGen4 BinOp gen_BinOpT (elems_ Z0 num)
              (elems_ Z0 num) genRegPtr);
    (* MSize *)
    (onNonEmpty dptr 10, liftGen2 MSize (elems_ Z0 dptr) genRegPtr);
    (* PGetOff *)
    (onNonEmpty dptr 10, liftGen2 PGetOff (elems_ Z0 dptr) genRegPtr);
    (* Mov *)
    (10, liftGen2 Mov genRegPtr genRegPtr)
].

Definition instantiate_instructions st : G SState :=
  let '(St im m s r pc) := st in
  bindGen (ainstrSSNI st) (fun instr =>
  let im' := nseq (List.length im) instr in
  returnGen (St im' m s r pc)).

(* ------------------------------------------------------ *)
(* -------- Variations ---------------------------------- *)
(* ------------------------------------------------------ *)

Class SmartVary (A : Type) := {
  smart_vary : Label -> Info -> A -> G A
}.

Definition gen_vary_atom (obs: Label) (inf : Info) (a : Atom) : G Atom :=
  let '(v @ l) := a in
  if flows l obs then returnGen a
  else
    freq_ (returnGen a)
      [:: (1, bindGen (gen_value inf) (fun v => returnGen (v @ l)))
      ;(9, match v with
             | Vint  _ =>
               liftGen2 Atm (liftGen Vint (smart_gen inf)) (pure l)
             | Vptr  p =>
               liftGen2 Atm (liftGen Vptr (smart_gen inf)) (pure l)
             | Vlab  _ =>
               liftGen2 Atm (liftGen Vlab (smart_gen inf)) (pure l)
           end)
       ].

#[global] Instance smart_vary_atom : SmartVary Atom :=
{|
  smart_vary := gen_vary_atom
|}.

Definition gen_vary_pc (obs: Label) (inf : Info) (pc : Ptr_atom)
: G Ptr_atom :=
  let '(PAtm addr lpc) := pc in
  if isLow lpc obs then pure pc
  else
    bindGen (gen_from_length (code_len inf)) (fun pcPtr =>
    bindGen (gen_high_label obs) (fun pcLab =>
    returnGen (PAtm pcPtr pcLab))).

#[global] Instance smart_vary_pc : SmartVary Ptr_atom :=
{|
  smart_vary := gen_vary_pc
|}.

Definition gen_var_frame (obs: Label) (inf : Info) (f : frame)
: G frame :=
    let '(Fr lab data) := f in
    let gen_length :=
        choose (List.length data, S (List.length data)) in
    let gen_data :=
        bindGen gen_length (fun len => vectorOf len (smart_gen inf)) in
    if isHigh lab obs then
      bindGen gen_data (fun data' => returnGen (Fr lab data'))
    else
      bindGen (sequenceGen (map (smart_vary obs inf) data))
              (fun data' => returnGen (Fr lab data')).

#[global] Instance smart_vary_frame : SmartVary frame :=
{|
  smart_vary := gen_var_frame
|}.

Definition handle_single_mframe obs inf (m : memory) (mf : mframe)
: G memory :=
  match get_memframe m mf with
    | Some f =>
      bindGen (smart_vary obs inf f) (fun f' =>
      match upd_memframe m mf f' with
        | Some m' => returnGen m'
        | None    => returnGen m
      end)
    | None => returnGen m
  end.

Fixpoint foldGen {A B : Type} (f : A -> B -> G A) (l : list B) (a : A)
: G A := nosimpl(
  match l with
    | [::] => returnGen a
    | (x :: xs) => bindGen (f a x) (foldGen f xs)
  end).

Definition gen_vary_memory  obs inf (m : memory)
: G memory :=
  let all_mframes := get_blocks all_labels m in
  foldGen (handle_single_mframe obs inf) all_mframes m.

#[global] Instance smart_vary_memory : SmartVary memory :=
{|
  smart_vary := gen_vary_memory
|}.

Definition gen_vary_stack_loc (obs: Label) (inf : Info)
           (s : StackFrame)
: G StackFrame :=
    let '(SF pc rs r lab) := s in
    if isLow ∂pc obs then
      bindGen (sequenceGen (map (smart_vary obs inf) rs)) (fun rs' =>
      returnGen (SF pc rs' r lab ))
    else
      bindGen (vectorOf (no_regs inf) (smart_gen inf)) (fun rs' =>
      bindGen (smart_vary obs inf pc) (fun pc' =>
      bindGen (smart_gen inf) (fun lab' =>
      bindGen (gen_from_nat_length (no_regs inf)) (fun r' =>
      returnGen (SF pc' rs' r' lab'))))).

Definition gen_vary_low_stack (obs : Label) (inf : Info) (s : list StackFrame)
: G (list StackFrame) :=
  sequenceGen (map (gen_vary_stack_loc obs inf) s).

Definition gen_vary_stack (obs : Label) (inf : Info) (s : Stack)
: G Stack :=
 liftGen ST (gen_vary_low_stack obs inf (unStack s)).

#[global] Instance smart_vary_stack : SmartVary Stack :=
{|
  smart_vary := gen_vary_stack
|}.

Definition gen_vary_SState (obs: Label) (inf : Info) (st: SState) : G SState :=
    let '(St im μ s r pc) := st in
    if isLow ∂pc obs then
      bindGen (sequenceGen (map (smart_vary obs inf) r)) (fun r' =>
      bindGen (smart_vary obs inf μ) (fun μ' =>
      bindGen (smart_vary obs inf s) (fun s' =>
      returnGen (St im μ' s' r' pc))))
    else
      bindGen (smart_vary obs inf pc) (fun pc' =>
      bindGen (smart_vary obs inf μ) (fun μ' =>
      bindGen (smart_vary obs inf s) (fun s' =>
      bindGen (vectorOf (no_regs inf) (smart_gen inf)) (fun r' =>
      returnGen (St im μ' s' r' pc'))))).

#[global] Instance smart_vary_SState : SmartVary SState :=
  {|
    smart_vary := gen_vary_SState
  |}.

(* ------------------------------------------------------ *)
(* -------- Memory and State Generation ----------------- *)
(* ------------------------------------------------------ *)

Fixpoint gen_init_mem_helper (n : nat) (ml : memory * list (mframe * Z)) :=
  match n with
    | O    => returnGen ml
    | S n' =>
      let (m, l) := ml in
      bindGen (choose (C.min_frame_size,
                       C.max_frame_size)) (fun frame_size =>
      bindGen gen_label (fun lab =>
         match (alloc frame_size lab bot (Vint Z0 @ bot) m) with
           | Some (mf, m') =>
             gen_init_mem_helper n' (m', (mf,frame_size) :: l)
           | None => gen_init_mem_helper n' ml
         end))
  end.

Definition gen_init_mem : G (memory * list (mframe * Z)):=
  bindGen (choose (C.min_no_frames,
                      C.max_no_frames)) (fun no_frames =>
  gen_init_mem_helper no_frames (Memory.empty Atom, [::])).

Definition failed_SState : SState :=
  (St [::] (Memory.empty Atom) (ST [::]) [::] (PAtm Z0 bot)).

Definition populate_frame inf (m : memory) (mf : mframe) : G memory :=
  match get_memframe m mf with
    | Some (Fr lab data) =>
      bindGen (vectorOf (List.length data) (smart_gen inf)) (fun data' =>
      match upd_memframe m mf (Fr lab data') with
        | Some m' => returnGen m'
        | _ => pure m
      end)
    | _ => pure m
  end.

Definition populate_memory inf (m : memory) : G memory :=
  let all_frames := [seq fst p | p <- data_len inf] in
  foldGen (populate_frame inf) all_frames m.

Definition instantiate_stamps (st : SState) : SState := st.

Definition get_blocks_and_sizes (m : memory) :=
  map
    (fun b =>
    let length :=
        match get_memframe m b with
          | Some fr =>
            let 'Fr _ data := fr in List.length data
          | _ => 0
        end in (b, Z.of_nat length)) (get_blocks all_labels m).

Definition gen_variation_SState : G (@Variation SState) :=
  bindGen gen_init_mem (fun init_mem_info =>
  let (init_mem, dfs) := init_mem_info in
  let imem := nseq (C.code_len) Nop in
  match dfs with
    | (def, _) :: _ =>
      let inf := MkInfo def (Z.of_nat C.code_len) dfs C.no_registers in
      bindGen (smart_gen inf) (fun pc =>
      bindGen (smart_gen inf) (fun regs =>
      bindGen (smart_gen_stack inf) (fun stk =>
      bindGen (populate_memory inf init_mem) (fun m =>
      let st := St imem m stk regs pc in
      bindGen (instantiate_instructions st) (fun st =>
      let st := instantiate_stamps st in
      bindGen (gen_label_between_lax bot top) (fun obs =>
      bindGen (smart_vary obs inf st) (fun st' =>
      returnGen (Var obs st st'))))))))
    | _ => returnGen (Var bot failed_SState failed_SState)
  end).

(* ------------------------------------------------------ *)
(* -------- Smart Mutation for Longer Traces ------------ *)
(* ------------------------------------------------------ *)

(* Default Info for use in mutations *)
Definition default_info : Info :=
  MkInfo (0%Z, bot) (Z.of_nat C.code_len) [::] C.no_registers.

(* Get Info from an SState's memory *)
Definition info_from_state (st : SState) : Info :=
  let '(St im m _ _ _) := st in
  let dfs := get_blocks_and_sizes m in
  match dfs with
  | (def, _) :: _ => MkInfo def (Z.of_nat (List.length im)) dfs C.no_registers
  | _ => default_info
  end.

(* Mutate a single instruction to be "safer" - less likely to halt early *)
Definition mutate_instr_safer (st : SState) (i : Instr) : G Instr :=
  match i with
  | Halt =>
    (* Never halt - replace with Nop or generate a safe instruction *)
    freq_ (pure Nop)
          [:: (5, pure Nop);
              (5, ainstrSSNI st)]
  | _ =>
    (* Usually keep original, sometimes replace with a new safe instruction *)
    freq_ (pure i)
          [:: (8, pure i);
              (1, pure Nop);
              (1, ainstrSSNI st)]
  end.

(* Generate a backward jump or control flow instruction *)
Definition gen_backward_jump (current_pc : Z) (st : SState) : G (@Instr Label) :=
  (* Just generate a safe instruction - the targeting mechanism
     will naturally favor sequences that lead to longer traces *)
  ainstrSSNI st.

(* Mutate instruction memory to encourage longer traces *)
Definition mutate_imem (imem : list (@Instr Label)) (st : SState) : G (list (@Instr Label)) :=
  freq_ (pure imem)
        [:: (* Strategy 1: Make existing instructions safer *)
            (6, sequenceGen (map (mutate_instr_safer st) imem));
            (* Strategy 2: Generate entirely new instruction sequence *)
            (3, bindGen (ainstrSSNI st) (fun instr =>
                 pure (nseq (List.length imem) instr)));
            (* Strategy 3: Keep original *)
            (1, pure imem)].

(* Mutate an SState to encourage longer execution *)
Definition mutate_state_for_length (st : SState) : G SState :=
  let '(St im m s r pc) := st in
  let inf := info_from_state st in
  (* Mutate instruction memory *)
  bindGen (mutate_imem im st) (fun im' =>
  (* Sometimes mutate registers to have valid pointers *)
  bindGen (freq_ (pure r)
             [:: (7, pure r);
                 (3, vectorOf (List.length r) (smart_gen inf))]) (fun r' =>
  (* Keep the same PC, memory, and stack to maintain execution context *)
  returnGen (St im' m s r' pc))).

(* Main mutator: mutate a Variation while preserving indistinguishability *)
Definition mutate_variation_for_length (_ : ⟦∅⟧) (v : @Variation SState)
  : G (@Variation SState) :=
  let '(Var obs st1 st2) := v in
  let inf := info_from_state st1 in
  (* Mutate st1 *)
  bindGen (mutate_state_for_length st1) (fun st1' =>
  (* Generate matching variation of st2 that stays indistinguishable *)
  bindGen (smart_vary obs inf st1') (fun st2' =>
  returnGen (Var obs st1' st2'))).

(* ------------------------------------------------------ *)
(* -------- Feedback Function for Targeting ------------- *)
(* ------------------------------------------------------ *)

(* Count the number of steps in a trace - longer is better *)
Definition trace_length (t : table) (st : SState) : nat :=
  List.length (trace trace_fuel t st).

(* Feedback function: returns the minimum trace length of both states *)
(* We want to target variations where BOTH states execute for many steps *)
(* Returns 0 for diverging traces (those that hit fuel limit) to filter them out *)
Definition feedback_fn (v : @Variation SState) : Z :=
  let '(Var _ st1 st2) := v in
  let len1 := trace_length default_table st1 in
  let len2 := trace_length default_table st2 in
  (* Filter out diverging inputs: if either trace hits fuel limit, return 0 *)
  if (trace_fuel <=? len1)%nat || (trace_fuel <=? len2)%nat
  then Z.of_nat 0
  else Z.of_nat (Nat.min len1 len2).

(* Wrapper for PropLang *)
Definition feedback_function (_ : ⟦∅⟧) (v : @Variation SState) : Z :=
  feedback_fn v.

(* ------------------------------------------------------ *)
(* -------- Gen-by-Exec Integration --------------------- *)
(* ------------------------------------------------------ *)

(* Helper: set instruction at PC location *)
Definition instr_set (m:imem) (pc:Ptr_atom) (i : Instr) : option (seq (@Instr Label)) :=
  let '(PAtm idx _) := pc in
  update_list_Z m idx i.

(* Gen-by-exec: generates instructions during execution *)
(* This is adapted from BespokeGenerator.v *)
Fixpoint gen_by_exec (t : table) (fuel : nat) (st : SState) : G SState :=
  let '(St im m stk rs (PAtm addr pcl)) := st in
  match fuel with
  | O => returnGen st
  | S fuel' =>
    match instr_lookup im (PAtm addr pcl) with
    | Some Nop =>
      (* If it is a noop, generate *)
      bindGen (ainstrSSNI st) (fun i =>
      match instr_set im (PAtm addr pcl) i with
      | Some im' =>
        let st' := St im' m stk rs (PAtm addr pcl) in
        gen_by_exec t fuel' st'
      | None => returnGen st
      end)
    | Some _ =>
      (* Existing instruction, execute *)
      match fstep t st with
      | Some st' =>
        gen_by_exec t fuel' st'
      | None => returnGen st
      end
    | None =>
      (* Out of bounds, terminate *)
      returnGen st
    end
  end.

Axiom gen_exec_fuel : nat.
Extract Constant gen_exec_fuel => "30".

(* Execute for N steps and return intermediate state *)
Definition trace_n (n : nat) (t : table) (st : SState) : option (SState * nat) :=
  let fix go fuel current steps :=
    match fuel with
    | O => Some (current, steps)
    | S fuel' =>
      match fstep t current with
      | Some next => go fuel' next (S steps)
      | None => Some (current, steps)
      end
    end
  in go n st 0.

(* Mutate by executing and generating instructions at Nop slots *)
(* Apply gen-by-exec directly to the state to fill Nop slots along *)
(* the execution path, then reset to original state with new imem *)
Definition mutate_by_exec (st : SState) : G SState :=
  (* Apply gen-by-exec directly from the original state *)
  (* This fills Nop slots during execution, generating instructions *)
  (* that are valid for the actual execution path from this state *)
  bindGen (gen_by_exec default_table gen_exec_fuel st) (fun st_exec =>
  (* Extract instruction memory with filled Nops *)
  let '(St exec_imem _ _ _ _) := st_exec in
  (* Reset to original state but with the new instruction memory *)
  let '(St _ orig_m orig_stk orig_regs orig_pc) := st in
  returnGen (St exec_imem orig_m orig_stk orig_regs orig_pc)).

(* Hybrid mutator: combines gen-by-exec with smart mutation *)
(* 70% gen-by-exec, 30% original smart mutation *)
Definition mutate_variation_hybrid (ctx : ⟦∅⟧) (v : @Variation SState)
  : G (@Variation SState) :=
  let '(Var obs st1 st2) := v in
  let inf := info_from_state st1 in
  freq_ (mutate_variation_for_length ctx v) [::
    (3, mutate_variation_for_length ctx v);   (* Original: 30% *)
    (7, bindGen (mutate_by_exec st1) (fun st1' =>  (* Gen-by-exec: 70% *)
        bindGen (smart_vary obs inf st1') (fun st2' =>
        returnGen (Var obs st1' st2'))))
  ].

(* Generate initial seeds using gen-by-exec - keeps final state *)
(* Unlike BespokeGenerator's version which resets state, this keeps *)
(* the final execution state to provide meaningful starting points *)
Definition gen_init_exec_mem : G (memory * list (mframe * Z)):=
  bindGen (choose (2, 4)) (fun no_frames =>
  gen_init_mem_helper no_frames (Memory.empty Atom, [::])).

Definition gen_variation_exec_final : G (@Variation SState) :=
  bindGen gen_init_exec_mem (fun init_mem_info =>
  let (init_mem, dfs) := init_mem_info in
  let imem := nseq (C.code_len) Nop in
  match dfs with
  | (def, _) :: _ =>
      let code_len : Z := Z.of_nat C.code_len in
      let no_regs := C.no_registers in
      let inf := MkInfo def code_len dfs no_regs in
      bindGen (smart_gen inf) (fun pc =>
      bindGen (smart_gen inf) (fun regs =>
      bindGen (smart_gen_stack inf) (fun stk =>
      bindGen (populate_memory inf init_mem) (fun m =>
      let st := St imem m stk regs pc in
      bindGen (instantiate_instructions st) (fun st =>
      let st := instantiate_stamps st in
      (* Apply gen-by-exec and KEEP the final state *)
      bindGen (gen_by_exec default_table gen_exec_fuel st) (fun st_final =>
      bindGen (gen_label_between_lax bot top) (fun obs =>
      (* Use original inf - it has valid frame info from initial memory *)
      bindGen (smart_vary obs inf st_final) (fun st' =>
      returnGen (Var obs st_final st')))))))))
    | _ => returnGen (Var bot failed_SState failed_SState)
  end).

(* ------------------------------------------------------ *)
(* -------- Mutation for Instruction Coverage ----------- *)
(* ------------------------------------------------------ *)

(* Instruction types grouped by behavior for diversity mutation *)
Definition control_flow_instrs : list nat := [:: 5; 6; 7; 8]. (* BNZ, Jump, BCall, BRet weights *)
Definition memory_instrs : list nat := [:: 9; 10; 11; 12].    (* Load, Store, Write, Alloc *)
Definition arithmetic_instrs : list nat := [:: 13; 14].        (* BinOp, Mov *)
Definition label_instrs : list nat := [:: 15; 16; 17].         (* Lab, PcLab, PutLab, MLab *)

(* Generate instruction with bias toward a specific category *)
Definition gen_diverse_instr (st : SState) : G Instr :=
  let '(St im m stk regs pc ) := st in
  let '(dptr, cptr, num, lab) :=
      groupRegisters st regs [::] [::] [::] [::] Z0 in
  let genRegPtr := gen_from_length (Zlength regs) in
  (* Bias toward less common instructions to increase diversity *)
  freq_ (pure Nop) [::
    (* Increased weight for control flow *)
    (3, pure Nop);
    (* Memory operations - important for IFC *)
    (onNonEmpty dptr 20, liftGen2 Load (elems_ Z0 dptr) genRegPtr);
    (onNonEmpty dptr 100, liftGen2 Store (elems_ Z0 dptr) genRegPtr);
    (onNonEmpty dptr 100, liftGen2 Write (elems_ Z0 dptr) genRegPtr);
    (150 * onNonEmpty num 1 * onNonEmpty lab 1,
     liftGen3 Alloc (elems_ Z0 num) (elems_ Z0 lab) genRegPtr);
    (* Control flow - critical for finding IFC bugs *)
    (30 * onNonEmpty cptr 1 * onNonEmpty lab 1,
     liftGen3 BCall (elems_ Z0 cptr) (elems_ Z0 lab) genRegPtr);
    (if negb (emptyList (unStack stk)) then 80 else 0, pure BRet);
    (onNonEmpty cptr 30, liftGen Jump (elems_ Z0 cptr));
    (onNonEmpty num 40,
      liftGen2 BNZ (choose (Zminus (0%Z) (1%Z), 2%Z))
                   (elems_ Z0 num));
    (* Label operations - important for testing label handling *)
    (15, liftGen PcLab genRegPtr);
    (15, liftGen2 Lab genRegPtr genRegPtr);
    (onNonEmpty dptr 15, liftGen2 MLab (elems_ Z0 dptr) genRegPtr);
    (15, liftGen2 PutLab gen_label genRegPtr);
    (* Arithmetic and pointer ops *)
    (onNonEmpty num 15,
     liftGen4 BinOp gen_BinOpT (elems_ Z0 num)
              (elems_ Z0 num) genRegPtr);
    (15 * onNonEmpty dptr 1 * onNonEmpty num 1,
     liftGen3 PSetOff (elems_ Z0 dptr) (elems_ Z0 num) genRegPtr);
    (onNonEmpty dptr 15, liftGen2 PGetOff (elems_ Z0 dptr) genRegPtr);
    (onNonEmpty dptr 15, liftGen2 MSize (elems_ Z0 dptr) genRegPtr);
    (* Basic ops *)
    (15, liftGen2 Put arbitrary genRegPtr);
    (15, liftGen2 Mov genRegPtr genRegPtr)
  ].

(* Mutate instruction memory to increase instruction diversity *)
Definition mutate_imem_for_diversity (imem : list (@Instr Label)) (st : SState)
  : G (list (@Instr Label)) :=
  freq_ (pure imem)
        [:: (* Strategy 1: Replace some instructions with diverse new ones *)
            (5, sequenceGen (map (fun i =>
                  freq_ (pure i) [::
                    (7, pure i);
                    (3, gen_diverse_instr st)]) imem));
            (* Strategy 2: Generate entirely new diverse instruction sequence *)
            (4, bindGen (gen_diverse_instr st) (fun instr =>
                 pure (nseq (List.length imem) instr)));
            (* Strategy 3: Keep original *)
            (1, pure imem)].

(* Mutate state to encourage instruction diversity *)
Definition mutate_state_for_diversity (st : SState) : G SState :=
  let '(St im m s r pc) := st in
  let inf := info_from_state st in
  (* Mutate instruction memory for diversity *)
  bindGen (mutate_imem_for_diversity im st) (fun im' =>
  (* Sometimes refresh registers to enable different instruction types *)
  bindGen (freq_ (pure r)
             [:: (6, pure r);
                 (4, vectorOf (List.length r) (smart_gen inf))]) (fun r' =>
  returnGen (St im' m s r' pc))).

(* Main mutator for instruction coverage: mutate to increase instruction diversity *)
Definition mutate_variation_for_instruction_coverage (_ : ⟦∅⟧) (v : @Variation SState)
  : G (@Variation SState) :=
  let '(Var obs st1 st2) := v in
  let inf := info_from_state st1 in
  (* Mutate st1 for diversity *)
  bindGen (mutate_state_for_diversity st1) (fun st1' =>
  (* Generate matching variation of st2 that stays indistinguishable *)
  bindGen (smart_vary obs inf st1') (fun st2' =>
  returnGen (Var obs st1' st2'))).

(* ------------------------------------------------------ *)
(* -------- PropLang Definitions ------------------------ *)
(* ------------------------------------------------------ *)

Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".

(* Extraction directive for Nat.min to avoid OCaml recursive binding issue *)
Extract Inlined Constant Nat.min => "(fun a b -> if a < b then a else b)".

Definition shrink_variation (_ : ⟦∅⟧) (v : @Variation SState) : list (@Variation SState) :=
  shrinkVSState v.

Definition show_variation_fn (_ : ⟦∅⟧) (v : @Variation SState) : string := show v.

(* Property using LLNI (multi-step non-interference) *)
Definition prop_LLNI :=
  ForAll "v"
    (fun _ => gen_variation_SState)
    mutate_variation_for_length   (* Smart mutator for targeting longer traces *)
    shrink_variation
    show_variation_fn
  (Check (@Variation SState · ∅)
    (fun '(v, _) =>
      match propLLNI default_table v with
      | Some true => true
      | Some false => false
      | None => true
      end)).

(* Targeted test runner using targetLoop *)
Definition test_prop_LLNI :=
  targetLoop
    number_of_trials
    prop_LLNI
    (fun input => feedback_fn (fst input))
    (FIFOSeedPool.(mkPool) tt)
    HillClimbingUtility.

(* Also provide SSNI property for comparison *)
Definition prop_SSNI :=
  ForAll "v"
    (fun _ => gen_variation_SState)
    (fun _ _ => gen_variation_SState)
    shrink_variation
    show_variation_fn
  (Check (@Variation SState · ∅)
    (fun '(v, _) =>
      match propSSNI_smart default_table v with
      | Some true => true
      | Some false => false
      | None => true
      end)).

Definition test_prop_SSNI := runLoop number_of_trials prop_SSNI.

(* Hybrid LLNI: uses regular generator for seeds but hybrid mutation *)
(* The key insight is that gen-by-exec works as a MUTATION operator *)
(* on existing good seeds, not as an initial generator *)
Definition prop_LLNI_hybrid :=
  ForAll "v"
    (fun _ => gen_variation_SState)           (* Regular initial generator *)
    mutate_variation_hybrid                   (* Use hybrid mutator (70% exec) *)
    shrink_variation
    show_variation_fn
  (Check (@Variation SState · ∅)
    (fun '(v, _) =>
      match propLLNI default_table v with
      | Some true => true
      | Some false => false
      | None => true
      end)).

(* Targeted test runner for hybrid approach *)
Definition test_prop_LLNI_hybrid :=
  targetLoop
    number_of_trials
    prop_LLNI_hybrid
    (fun input => feedback_fn (fst input))
    (FIFOSeedPool.(mkPool) tt)
    HillClimbingUtility.

(*! QuickProp test_prop_LLNI. *)
