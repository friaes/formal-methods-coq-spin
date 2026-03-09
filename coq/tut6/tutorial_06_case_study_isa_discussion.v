Require Import Strings.String.
Require Import Orders OrderedTypeEx.
Require Import FMapList FMapFacts.
Require Import Lia.
Require Import ZArith.

Import ListNotations.

(** * Case Study - Instruction Set Architectures  *)

  (** HERE WE DISCUSS THE KEY TAKE AWAYS FROM THE CASE STUDY
      YOU MAY JUMP THROUGH THIS DOCUMENT BY SEARCHING FOR THE FOLLOWING
      STRING: !!!
  *)  


(** ** FP - Binary Numbers *)

  (** Before starting we need some boilerplate definitions, that we're going to use.*)

  (** Being designed for microcontroller, the AVR ISA uses 8-bit binary numbers. Which is why we
  start by defining a binary representation of numbers below. Granted, this is not the most
  efficient way to represent binary numbers in Coq, but it is simple and enough for our purpose. *)

  (* bit *)
  Definition bit : Type := bool. (* A bit is a bool *)

  (* bin *)
  Notation B0 := false. (* B0 is false *)
  Notation B1 := true. (* B1 is true *)

  Definition bin : Type := list bit. (* A binary number is a list of bits *)

  (** The function testbit_bin returns true if the bit at position p of the binary number b is
  B1. Otherwise it returns false. *)
  Definition testbit_bin (b : bin) (p : nat) : bool := nth p b B0.

(** ** FP - The State Machine - Types *)

  (** Now that we have a working representation for binary numbers, we can start implementing a
  small portion of the AVR ISA.
  
  Let's first get some basics out of the way. An ISA is all about instructions (it's called 
  _instruction_ set architecture for a reason). These instructions are fetched and executed 
  by a so called state-machine. The state-machine changes its state depending on the instruction
   it encounters.
    
  This is a textual representation of the structure of our state machine:

      Program Counter : 0
      Status Register :   ZC
                        0b00
      Register File  :
                        register  value
                          16       0
                          17       5
      Program Memory  :
                        address   instruction
                          0       nop
                          1       ldi 16 135
                          2       add 16 17

  - The register file (RF) contains multiple registers in which our data is stored. Register addresses 
    (see above under "register") are represented as natural numbers, we usually use the addresses 16 to 31.
    The registers values ("value") stored in the registers are also represented as natural numbers.
  - The program memory (PM) contains the instructions. The PM addresses ("address") are represented as natural 
    numbers. The instructions are represented by their mnemonics (names that humans can remember) and
    their parameters ("instruction").
  - The program counter (PC) points to the next instruction in the PM that will be executed. It is
    represented as a natural number. 
  - The status register (SREG) contains flags, which store information about the result of a
    previously executed instruction. Flags only contain either the value 0 or 1. The zero flag (Z) is 
    usually set to 1, if the result of the last executed instruction is zero. The carry flag (C) is
    usually set to 1, if the result of the last executed instruction is greater than the register
    size. Note we're only going to use two of the normally eight flags. Therefore it will be represented
    as a single binary number with two bits.

  So in the example above the program counter points to the first instruction (nop) and the register 
  file contains two initialized registers (16 and 17). The program memory contains three instructions
  nop, ldi and add.

  Depending on the instruction that the state machine encounters, it may manipulate the data values 
  stored in the register file (RF) and change the status register (SREG). *)

  (** Since we now know what the state machine looks like, we can start implementing it in Coq.
  We start by defining the basic types that we will use to built the more complex state machine. *)

  (** Both PM and RF are addressable by positive numbers. We assume infinite memory to keep things 
  simple, which is why we use our beloved unbounded natural numbers as addresses. We might change 
  our mind later which is why we pack them into a wrapper-type: *)

  Definition addr : Type := nat.  (* Addresses for PM and RF are natural numbers *)

  (** Now what does this memory contain?

  According to the official ISA documentation it contains 8-bit binary values. But again, for
  the sake of simplicity we choose to keep things natural: *)

  Definition data := nat. (* Data values of registers are represented as nat *)

  (** We also think, that this will make proving theorems about our ISA and assembly programs simpler. *)

  (** Instructions are referenced through mnemonics followed by input parameters. Since both are 
  specific to the instructions, we have to create a specific type for them: *)

  Inductive instr : Type :=
      | nop (* no operation *)
      | ldi (r : addr) (i : nat)  (* load immediate value*)
      | add (r1 : addr) (r2 : addr). (* addition *)

  (** We will discover the exact behavior of these instructions later. *)
  
  (** Note this is an inductive type. Everything in there is an instruction. Everything not in there
  is not an instruction. Also note that we simply describe how the instructions look, not what they
  actually do. *)

  (** We then model the memory (Register File RF and Program Memory PM) as simple key-value stores, 
  called maps. Here, we use an existing implementation of maps which we  instantiate under the name 
  NatMaps. *)

  Module NatMaps := FMapList.Make(Nat_as_OT).  (* maps have natural numbers as keys *)

  (** Note: You don't have to understand how to use this NatMaps module. We'll define a few helper
  functions further down the line and then only use those. *)

  Definition register_file := NatMaps.t data. (* register file is a function from nat/addr to data *)
  Definition program_memory := NatMaps.t instr. (* program memory is a function from nat/addr to instr *)

  (** Now lets setup the status register. We're only going to use two of the normally available
  eight flags. *)

  Definition status_register := bin. (* the status register is a single binary value *)

  (** We use fz and fc to represent the zero and carry flags. *)
  Definition flag : Type := nat. (* a flag refers to a bit in the status register (sreg) *)
  Definition fz : flag := 0. (* zero flag is at position 0 of the sreg *)
  Definition fc : flag := 1. (* carry flag is at position 1 of the sreg *)

  (* Lets tie the whole thing together into a single structure called state. *)

  Record state :=
    make_state {
      pc : addr; 
      sreg : status_register;
      rf : register_file;
      pm : program_memory;
    }.

  (** This state structure is going to change with the execution of each instruction. *)

  (** Lets add another boolean to indicate whether an instruction executed successfully 
  (true) or not (false). *)

  (** The state monad is a pair of the state and a boolean. *)
  Definition state_monad : Type := (state * bool).

(** ** FP - The State Machine - Functions *)

  (** Now that we have all our types together that represent our state machines syntax, lets
  start implementing the semantics of the instructions. *)

  (** Before we start modelling the behavior of each single instruction, we declare a few simple
  helper functions for state manipulation. *)

  (** Returns the next instruction referenced by the program counter pc.
  If it is not found, it returns None. *)
  Definition fetch_instr (st : state) : option instr :=
    NatMaps.find (pc st) (pm st).

  (** Tries to fetch the value stored in register r. If it is not found, it returns None. *)
  Definition get_reg (st : state) (r : addr) := 
    NatMaps.find r (rf st).

  (** Stores the nat n in the register r. *)
  Definition set_reg (st : state) (r : addr) (n : nat) :=
    NatMaps.add r n (rf st).

  (** The functions list_regs and pp_state are helper functions used to pretty print states *)
  (** They are a little obscure, but you don't need to understand them. Their output will be
  explained as we go along. *)

  Fixpoint list_regs (st : state) (regs : list addr) : list (addr * nat) :=
    match regs with
    | nil  => nil
    | x :: xs => match (get_reg st x) with
      | Some r => (x, r) :: (list_regs st xs)
      | None => (x, 0) :: (list_regs st xs)
      end
    end.

  Definition pp_state (st' : state_monad) (regs : list addr) :
    (bool * (string * addr) * (bin)) * (list (addr * nat)) :=  
    match st' with
      | (st, msg) => (msg, ("PC"%string, (pc st)) , (sreg st), (list_regs st regs))
    end.

(** ** FP - Instruction semantic *)

  (** Now we can finally start implementing some instructions 🎉
  Below you'll find an excerpt of the instruction description from the official AVR ISA. *)

  (** 
    NOP - No Operation
    ------------------
    Description: This instruction performs a single cycle No Operation.
    Operation: No
    Syntax: nop
    Operands: None
    Program Counter: PC ← PC + 1 

    Status Register (SREG) and Boolean Formula:
    Z: -
    C: -
  *)

  (** Note the notation PC ← PC + 1 states that the value PC + 1 is assigned to the program counter. *)

  (** Below is our implementation of the NOP instruction according to the description from the 
  instruction set manual. *)
  Definition exec_nop (st : state) : state_monad :=
    ((make_state  (* create a new state*)
      (S (pc st)) (* pc is the pc of st incremented by one *)
      (sreg st)   (* sreg is the same of st *)
      (rf st)     (* rf is the same of st *)
      (pm st)),   (* pm is the same of st *)
      true)       (* instruction executed successfully *)
    . 

  (** ****
    Exercise - nop_q1_ai
    --------------------

    Given the following machine state, what would be the next state after the execution of ONE 
    instruction according to the instruction set manual?

        Program Counter : 0
        Status Register :   ZC
                          0b00
        Register File  :
                          register  value
                            16       0
                            17       0
        Program Memory  :
                          address   instruction
                            0       nop
                            1       nop

    !!! SOLUTION

        Program Counter : 1
                            ZC
        Status Register : 0b00
        Register File  :
                          register  value
                            16       0
                            17       0
        Program Memory  :
                          address   instruction
                            0       nop
                            1       nop

   !!! COMMENT: Program Counter is increased by one 


  *)

  (** Lets test the behavior of the state machine above: *)

  Definition st_nop_q1_ai : state :=
    make_state 0  [B0;B0] (* PC SREG *)
      (NatMaps.add 17 0 (NatMaps.add 16 0 (NatMaps.empty data))) (* RF *)
      (NatMaps.add 1 nop (NatMaps.add 0 nop (NatMaps.empty instr))). (* PM *)

  Compute pp_state (exec_nop st_nop_q1_ai) [16;17].

  (** Note that we're executing the instructions directly on the state. We do this, because
  we have not implemented a method to fetch and executes the instructions directly from the PM. *)

  (** The output of the function pp_state is a tuple with the following structure:

  B1,                 The first element is a bit indicating whether the instruction executed successfully (B1) or not (B0).
  ("PC"%string, 1),   The second element is a tuple with the string "PC" and the value of the program counter (1).
  B0 (B0 T),          The third element contains the Z and C values (both B0) of the status register.
  [(16, 0); (17, 0)]) The fourth element is a list of tuples with the register addresses (16 and 17) and their values (both 0). *)

  (** Now lets implement the LDI instruction. The LDI instruction loads a constant value into a register. *)

  (** 
    LDI - Load Immediate
    ------------------
    Description: Loads an 8-bit constant directly to register 16 to 31
    Operation: Rd ← K
    Syntax: ldi Rd, k 
    Operands:  0 ≤ K ≤ 255 (* !!! *)
    Program Counter: PC ← PC + 1

    Status Register (SREG) and Boolean Formula:
    Z: -
    C: -
  *)

  (** **** 
    Exercise - ldi_impl
    -------------------
    Implement the instruction according to the description from the instruction set manual. You 
    may use the implementation of exec_nop as a template. *)

  Definition exec_ldi (st : state) (r : addr) (i : nat) : state_monad :=
    if ((leb 0 i) && (leb i 255)) then (* !!! *)
    ((make_state
      (S (pc st))
      (sreg st)
      (set_reg st r i)
      (pm st)),
      true)
    else (st, false).

  (** ****
    Exercise - ldi_q1_ai
    --------------------

    Given the following machine state, what would be the next state after the execution of ONE 
    instruction according to the instruction set manual?

        Program Counter : 0
        Status Register :   ZC
                          0b00
        Register File  :
                          register  value
                            16       0
                            17       0
        Program Memory  :
                          address   instruction
                            0       ldi 16 135
                            1       nop

    !!! SOLUTION:

        Program Counter : 1
                            ZC
        Status Register : 0b00
        Register File  :
                          register  value
                            16       135
                            17       0
        Program Memory  :
                          address   instruction
                            0       ldi 16 135
                            1       nop

  !!! COMMENT: Happy path, the instruction executes successfully. 

  *)

  (* Lets test the behavior of the state machine. *)
  
  Definition st_ldi_q1_ai : state :=
    make_state 0  [B0;B0] (* PC SREG *)
      (NatMaps.add 17 0 (NatMaps.add 16 0 (NatMaps.empty data))) (* RF *)
      (NatMaps.add 1 nop (NatMaps.add 0 (ldi 16 135) (NatMaps.empty instr))). (* PM *)

  Compute pp_state (exec_ldi st_ldi_q1_ai 16 135) [16;17].

  (** ****
    Exercise - ldi_q1_ae
    --------------------
    After seeing the output of the function pp_state, do you think your answer to the previous 
    question was correct?

    !!! COMMENT: Since we're in the happy path, everything will execute as expected.

  *)



  (** ****
    Exercise - ldi_q2_ai
    --------------------
    Given the following machine state, what would be the next state after the execution of **TWO**
    instructions according to the instruction set manual?

        Program Counter : 0
        Status Register :   ZC
                          0b00
        Register File  :
                          register  value
                            16       0
                            17       0
        Program Memory  :
                          address   instruction
                            0       nop
                            1       ldi 16 270


      !!! COMMENT / SOLUTION:
      We do not know how the machine operates. This case is not covered
      in the Instruction Set Manual (at least not in the parts that we saw here).

      In our model, we do not change the state, but return FALSE in the
      second element of our state monad.

      e.g. (previous_state, FALSE)
      
      Therefore we know that we're in a state that should never be reached.
  *)

  (* Lets test the behavior of the state machine. *)
  Definition st_ldi_q2_ai : state :=
    make_state 0  [B0;B0] (* PC SREG *)
      (NatMaps.add 17 0 (NatMaps.add 16 0 (NatMaps.empty data))) (* RF *)
      (NatMaps.add 1 nop (NatMaps.add 0 (ldi 16 270) (NatMaps.empty instr))). (* PM *)

  Compute pp_state (exec_ldi (fst (exec_nop st_ldi_q2_ai )) 16 270) [16;17].

 (** ****
    Exercise - ldi_q2_ae
    --------------------
    After seeing the output of the function pp_state, do you think your answer to the previous 
    question was correct?

    !!! COMMENT / SOLUTION:
    This should execute successfully. Even in case of a naive implementation of 
    ldi_exec (e.g. one that does not check the size of the error).
  
  *)

  (** The ADD instruction adds two registers together and stores the result in the destination register. *)

  (**
    ADD - Add without Carry 
    ------------------
    Description: Adds two registers Rd and Rr and places the result in the destination register Rd.
    Operation: Rd ← Rd + Rr
    Syntax: ADD Rd,Rr
    Operands: -
    Program Counter: PC ← PC + 1

    Status Register (SREG) and Boolean Formula:
    Z: ¬R7 ∧ ¬R6 ∧ ¬R5 ∧ ¬R4 ∧ ¬R3 ∧ ¬R2 ∧ ¬R1 ∧ ¬R0
    C: Rd7 ∧ Rr7 ∨ Rr7 ∧ ¬R7 ∨ ¬R7 ∧ Rd7
  *)

  (** This instruction is a little more complex than the previous instructions, which is why we 
  will implement it in several steps. *)

  (** This function returns true when bit n of a natural number b is 1 otherwise it returns false. *)
  Definition testbit := Nat.testbit.

  (** Computes the value of the Z flag.*)
  (** The z-flag is set to true, when the operations result is zero. Otherwise it is set to false. *)
  Definition add_z  (r : nat) : bool :=
    (negb (testbit r 7)) && (negb (testbit r 6)) &&
    (negb (testbit r 5)) && (negb (testbit r 4)) &&
    (negb (testbit r 3)) && (negb (testbit r 2)) &&
    (negb (testbit r 1)) && (negb (testbit r 0)).

  (** Computes the value of the C flag.*)
  (** The carry flag is set to true in case of an overflow. In other words, if the result is greater 
  than 255 *)
  Definition add_c (m n r : nat) : bool :=
    (testbit m 7) && (testbit n 7) ||
    (testbit n 7) && (negb (testbit r 7)) ||
    (negb (testbit r 7)) && (testbit m 7).

  (** Sets the flags according to the boolean formula in the instruction set manual *)
  Definition setflags_add  (m n r : nat) : bin := 
      [(add_z r);(add_c m n r)].

  (** Finally the implementation according to the instruction set manual *)
  Definition exec_add (st : state) (r1 r2 : addr) : state_monad :=
      match (get_reg st r1) , (get_reg st r2) with
        | Some m, Some n =>
            let r := (m + n) in
            ((make_state
            (S (pc st))
            (setflags_add m n r)
            (set_reg st r1 r)
            (pm st)),
            true)
        | _, _ => (st, false)
      end.

  (** ****
    Exercise - add_q1_ai
    --------------------
    Given the following machine state, what would be the next state after the execution of **TWO**
    instructions according to the instruction set manual?

        Program Counter : 0
        Status Register :   ZC
                          0b00
        Register File  :
                          register  value
                            16       130
                            17       140
        Program Memory  :
                          address   instruction
                            0       nop
                            1       add 16 17

      !!! COMMENT / SOLUTION:
      This case is covered in the Instruction Set Manual but the instruction
      description is amgiuous. This is why our implementation fails to
      reflect the correct behavior.
 
  *)

  (* Lets test the behavior of the state machine. *)
  Definition st_add_q1_ai : state :=
    make_state 0  [B0;B0] (* PC SREG *)
      (NatMaps.add 17 140 (NatMaps.add 16 130 (NatMaps.empty data))) (* RF *)
      (NatMaps.add 1 nop (NatMaps.add 0 (add 16 17) (NatMaps.empty instr))). (* PM *)

  Compute pp_state (exec_add (fst (exec_nop st_add_q1_ai )) 16 17) [16;17].

 (** ****
    Exercise - add_q1_ae
    --------------------
    After seeing the output of the function pp_state, do you think your answer to the previous 
    question was correct?

    !!! COMMENT / SOLUTION:
    Same problem as with ldi. We do not detect any errors by testing the behavior
    with simple executions.

  *)


(** ** TP - Proofs on Instruction Semantics *)

  (** Below are some helper lemmas that we will use to prove the properties of the
  instructions. *)

  (** The function NatMaps.add returns a map with the value v at key k. *)
  Lemma maps_add_find : forall r b m,  (NatMaps.find (elt:=nat) r (NatMaps.add r b m)) = Some b.
  Proof.
    intros. subst. apply NatMaps.find_1. apply NatMaps.add_1. reflexivity.
  Qed.

  (** Reading a register value immediately after setting it, is always successful *)
  Lemma set_get_reg : forall (st : state) (r : addr) (v : nat), 
    get_reg (make_state (pc st) (sreg st) (set_reg st r v) (pm st)) r = Some v.
  Proof.
  intros. unfold get_reg. simpl. unfold set_reg. rewrite maps_add_find. reflexivity.
  Qed.

  (** ****
    Exercise - nop_p1
    -----------------
    Prove the theorem below about the behavior of nop or explain why it is not possible to prove it. *)

  (** When executing a NOP instruction, the program counter is incremented by one. Everything else
  remains unchanged. *)
  Lemma nop_pc : forall (st : state),
    fst (exec_nop st) =
      (make_state (S (pc st)) (sreg st) (rf st) (pm st)) .
  Proof.
    intros. simpl. reflexivity.
  Qed.

  (** ****
    Exercise - nop_q1_ap
    --------------------

    Given the following machine state, what would be the next state after the execution of ONE 
    instruction according to the instruction set manual?

        Program Counter : 0
        Status Register :   ZC
                          0b00
        Register File  :
                          register  value
                            16       0
                            17       0
        Program Memory  :
                          address   instruction
                            0       nop
                            1       nop

    !!! SOLUTION

        Program Counter : 1
                            ZC
        Status Register : 0b00
        Register File  :
                          register  value
                            16       0
                            17       0
        Program Memory  :
                          address   instruction
                            0       nop
                            1       nop
  *)


  (** **** 
    Exercise - ldi_p1
    -----------------
    Prove the theorem below about the behavior of ldi or explain why it is not possible to prove it. *)

  (** When executing a LDI instruction on register r with a natural number i where i is between
  0 and 255, the register r is set to i. *)
  Lemma ldi_p1 : forall (st st' : state) r i,
    st' = fst(exec_ldi st r i) ->
    0 <= i -> i <= 255 ->
    get_reg st' r = Some i.
    Proof.
      intros. subst.
      unfold exec_ldi.
      destruct (0 <=? i) eqn: B1; try(rewrite Nat.leb_nle in B1; contradiction).
      destruct(i <=? 255) eqn: B2; try(rewrite Nat.leb_nle in B2; contradiction).
      apply set_get_reg.
    Qed.

  (** ****
    Exercise - ldi_q1_ap
    --------------------

    Given the following machine state, what would be the next state after the execution of ONE 
    instruction according to the instruction set manual?

        Program Counter : 0
        Status Register :   ZC
                          0b00
        Register File  :
                          register  value
                            16       0
                            17       0
        Program Memory  :
                          address   instruction
                            0       ldi 16 135
                            1       nop

    !!! SOLUTION

        Program Counter : 1
                            ZC
        Status Register : 0b00
        Register File  :
                          register  value
                            16       135
                            17       0
        Program Memory  :
                          address   instruction
                            0       ldi 16 135
                            1       nop

    !!! COMMENT: Nothing changes in the happy path.

  *)

  (** ****
    Exercise - ldi_p2
    -----------------
    Prove the theorem below about the behavior of ldi or explain
    why it is not possible to prove it. *)

  (** Hint: You might want to use Nat.leb_le and/or Nat.le_ngt. *)

  (** When executing a LDI instruction on register r with a natural number i where i is
  greater than 255, the execution fails. This makes sense, because a register should only
  be able to hold one byte. *)
  Lemma ldi_p2 : forall (st : state) r i, i > 255 -> snd (exec_ldi st r i) = false.
    Proof.
      intros. subst.
      unfold exec_ldi.
      destruct (0 <=? i) eqn: B3.
        -  destruct(i <=? 255) eqn: B4.
            -- rewrite Nat.leb_le in B4. apply Nat.le_ngt in B4. contradiction.
            -- simpl. reflexivity.
        - rewrite Nat.leb_nle in B3. apply not_le in B3. inversion B3.
    Qed.

  (** 

    !!! COMMENT: This proof is only successful, if the implementation of ldi_exec
    considers the bounded register size.

  *)


  (** ****
    Exercise - ldi_q2_ap
    --------------------
    Given the following machine state, what would be the next state after the execution of **TWO**
    instructions according to the instruction set manual?

        Program Counter : 0
        Status Register :   ZC
                          0b00
        Register File  :
                          register  value
                            16       0
                            17       0
        Program Memory  :
                          address   instruction
                            0       nop
                            1       ldi 16 270

    !!! COMMENT: After attempting the proof, we may discover the potential error in exec_ldi and update our model. 
    
    We do not know how a real life microcontroller would behave in such a situation
    (or whether this kind of situation can even occur). But we know that we never want this to
    happen. Therefore any model that allows us to prove the absence of such situations is good enough for us.
    
  
  *)

  (* ** ****
    Exercise - add_p1
    -----------------
    Prove the theorem below about the behavior of add or explain why it is not possible to prove it. *)

  (** When executing an ADD instruction on registers r1 and r2, the value of register r1 is set to the sum of the values of r1 and r2 and smaller than 256. *)

  Lemma add_p1: forall (st st' : state) (r1 r2 : addr) (n m r : nat),
    st' = fst(exec_add st r1 r2) ->
    get_reg st r1 = Some m -> get_reg st r2 = Some n ->
    r = m + n ->
    get_reg st' r1 = Some r /\ r < 256. 
  Proof.
      intros. subst. split.
      - unfold exec_add. rewrite H0. rewrite H1. apply set_get_reg.
      - admit.
  (* FILL IN HERE *) Admitted.

 (** Your Explanation:

    !!! This is impossible to prove because our implementation does not reflect the
    behavior (implicitely) described in the Instruction Set Manual.

  *)


  (** ****
    Exercise - add_q1_ap1
    --------------------
    Given the following machine state, what would be the next state after the execution of **TWO**
    instructions according to the instruction set manual?

        Program Counter : 0
        Status Register :   ZC
                          0b00
        Register File  :
                          register  value
                            16       130
                            17       140
        Program Memory  :
                          address   instruction
                            0       nop
                            1       add 16 17

    !!! SOLUTION

        Program Counter : 2
                            ZC
        Status Register : 0b01 !!! set carry flag
        Register File  :
                          register  value
                            16       14 !!! compute (130 + 140) mod 256
                            17       140
        Program Memory  :
                          address   instruction
                            0       nop
                            1       add 16 17

    !!! COMMENT: Remember, we are describing the behavior according to the Instruction Set
    Manual NOT of our implementation.

  *)

  (** The description of the add instruction is ambiguous. Which is why our implementation
  did not really correspond to what should be happening. *)

  (** Engineers with a little more experience would know that "Operation: Rd ← Rd + Rr" will
  only store the first 8 bits of Rd + Rr. If Rd + Rr needs 9 bits, the carry flag is set
  and will act as a magical 9th bit.
  *)

  (** So lets adapt our exec_add first to reflect that change. *)
  Definition exec_add' (st : state) (r1 r2 : addr) : state_monad :=
      match (get_reg st r1) , (get_reg st r2) with
        | Some m, Some n =>
            (* the mod 256 ensures that the result of the addition is 
            truncated after 8-bit. *)
            let r := ((m + n) mod 256) in 
            ((make_state
            (S (pc st))
            (* our carry flag should work as defined in the ISA, no change here*)
            (setflags_add m n r) 
            (set_reg st r1 r)
            (pm st)),
            true)
        | _, _ => (st, false)
      end.

  (** !!! As can be seen below, exec_add' seems to behave correctly now: *)
  Compute pp_state (exec_add' (fst (exec_nop st_add_q1_ai  )) 16 17) [16;17].


  (** A small helper lemma, that you can ignore. *)
  Lemma mod_ab : forall (n m : nat), n <> 0 -> m mod n < n.
   intros. destruct n; simpl; try (destruct (snd (Nat.divmod m (S n) 0 (S n)))); lia.
  Qed.

  (** The same proof now passes for add_p1'. *)
  Lemma add_p1' : forall (st st' : state) (r1 r2 : addr) (n m r : nat),
    st' = fst(exec_add' st r1 r2) ->
    get_reg st r1 = Some m -> get_reg st r2 = Some n ->
    r = (m + n) mod 256 ->
    get_reg st' r1 = Some r /\ r < 256. 
  Proof.
      intros. subst. split.
      - unfold exec_add'. rewrite H0. rewrite H1. apply set_get_reg.
      - apply mod_ab. auto. 
  Qed.

  (** ****
    Exercise - add_q1_ap1'
    --------------------
    Given the following machine state, what would be the next state after the execution of **TWO**
    instructions according to the instruction set manual?

        Program Counter : 0
        Status Register :   ZC
                          0b00
        Register File  :
                          register  value
                            16       130
                            17       140
        Program Memory  :
                          address   instruction
                            0       nop
                            1       add 16 17

    !!! COMMENT / SOLUTION: After the proof, we are much more confident that our
    new implementation add_exec' behaves correctly.
  *)

  (** ****
    Exercise - add_q2
    -----------------

    Consider the instruction add 16 17 and the respective values for r16 and r17 
    shown below. State whether the carry flag will be set according to our current
    implementation (not the ISA) of the ISA.

    #  r16   r17   carry   confidence  explanation / comment
    0  1     5     no      3            I'm always right 
    1  130   140
    2  200   5
    3  255   256
    4  500   5

  *)

  (* Lets test the behavior of the state machine. *)
  Definition st_add_q3_ai1 : state :=
    make_state 0  [B0;B0] (* PC SREG *)
      (NatMaps.add 17 140 (NatMaps.add 16 130 (NatMaps.empty data))) (* RF *)
      (NatMaps.add 0 (add 16 17) (NatMaps.empty instr)). (* PM *)
  Definition st_add_q3_ai2 : state :=
    make_state 0  [B0;B0] (* PC SREG *)
      (NatMaps.add 17 5 (NatMaps.add 16 200 (NatMaps.empty data))) (* RF *)
      (NatMaps.add 0 (add 16 17) (NatMaps.empty instr)). (* PM *)
  Definition st_add_q3_ai3 : state :=
    make_state 0  [B0;B0] (* PC SREG *)
      (NatMaps.add 17 255 (NatMaps.add 16 256 (NatMaps.empty data))) (* RF *)
      (NatMaps.add 0 (add 16 17) (NatMaps.empty instr)). (* PM *)
  Definition st_add_q3_ai4 : state :=
    make_state 0  [B0;B0] (* PC SREG *)
      (NatMaps.add 17 500 (NatMaps.add 16 5 (NatMaps.empty data))) (* RF *)
      (NatMaps.add 0 (add 16 17) (NatMaps.empty instr)). (* PM *)

  Compute pp_state (exec_add' (fst (exec_nop st_add_q3_ai1 )) 16 17) [16;17].
  Compute pp_state (exec_add' (fst (exec_nop st_add_q3_ai2 )) 16 17) [16;17].
  Compute pp_state (exec_add' (fst (exec_nop st_add_q3_ai3 )) 16 17) [16;17].
  Compute pp_state (exec_add' (fst (exec_nop st_add_q3_ai4 )) 16 17) [16;17].

 (** ****
    Exercise - add_q2_ae
    --------------------
    After seeing the output of the function pp_state, do you think your answers to 
    the previous questions were correct?

    If not, please give your new answer (edit the template below):

    #  r16   r17   carry   confidence  explanation / comment
    0  1     5     no      3            I'm always right 
    1  130   140
    2  200   5
    3  255   256
    4  500   5

  !!! This is an example highlights another error in our model of the
  of the add instruction. The edge case add 255 256 does is not handled
  correctly with respect to the carry flag.
  
  So in some cases, test executing stuff may help with debugging. But the
  test cases have to be chosen carefully.
  
  However, since a register should never contain a value greater than 255,
  this should not be a big issue.

  *)

  (** ****
    Exercise - add_p2
    -----------------
    Prove the theorem below about the behavior of add or explain why it is not possible to prove it. *)

  Definition add_carry_true : Prop := forall (st st' : state) (stm : state_monad) (r1 r2 : addr) (b : bin),
    forall (m n : nat),
    stm = exec_add st r1 r2 ->
    st' = fst stm ->
    get_reg st r1 = Some m ->
    get_reg st r2 = Some n ->
    256 <= m + n ->
    testbit_bin (sreg st') fc = true.
  
  (** !!! Inutiviely, add_carry_true should be provable. But it is not. We already
  know why, thanks to our carefully chosen test executions. *)
  
  Definition add_carry_false : Prop := forall (st st' : state) (stm : state_monad) (r1 r2 : addr) (b : bin),
    exists (m n : nat),
    stm = exec_add st r1 r2 ->
    st' = fst stm ->
    get_reg st r1 = Some m ->
    get_reg st r2 = Some n ->
    256 <= m + n /\
    testbit_bin (sreg st') fc = false.

  Lemma add_p2 : add_carry_true \/ add_carry_false.
  Proof.
    (* start with either right. or left. *)
    right. unfold add_carry_false.
    intros. exists 255. exists 256. intros. 
    split. 
      - lia.
      - rewrite H in H0. rewrite H0. subst. unfold exec_add.
       rewrite H1. rewrite H2. simpl. reflexivity.
  Qed.

  (** !!! The test execution allowed us to find a discrepancy between our model 
  and the expected behavior of the add instruction.
  
  The proofs above show that our model indeed does not handle the edge
  case (e.g. 255 + 256) correctly.

  But this case will never occur in a real microcontroller. The ISA is very clear
  on the fact, that the register size does not exceed 255.
  
  So we have to update our model to reflect this. We could for example:
  - Type level: Use a bounded type for register values instead of the unbounded nat
  - Function level: Change get_reg to return None if it reads an out of bound values.
  - Proof level: Add the assumption that n and m are smaller than 255.
  *)
