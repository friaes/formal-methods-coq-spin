Require Import Coq.Arith.PeanoNat.
Require Import Nat.
Require Import List.

(** * Propositions and the inner workings of Coq *)

(** ** FP - The Type Prop *)

  (** Recall that even propositions in Coq have a type, namely the type [[Prop]].
  We observed this in the example below from the first chapter about TP but 
  didn't elaborate on it. *)

 Check (forall (x : nat), x = x). (* has type [[Prop]] (still surprised, that
                                      everything has a type?) *)

  (** So propositions are of type [[Prop]] which can also be treated like any type
  we have seen so far. We can, for example, give them names using the keyword
  [[Definition]]. *)

  Definition allxeqx := forall (x : nat), x = x.

  Check allxeqx. (* Prop *)

  (** Similar to types, we can define our own propositions using the [[Inductive]]
  keyword. *)

  (** The proposition [[True]], has a single constructor [[I]], which returns 
  True. *)

  Inductive True : Prop :=
    | I : True.

  Check True.

  (** Note that the [[True]] we defined here, has nothing to do with the [[true]] of type
  [[bool]] that we defined at the beginning of this tutorial. *)

  Check true. (* true : bool *)
  Check True. (* True : Prop *)
  
  (** The proposition [[False]], has no constructors at all. This is, because
  there should be no way to construct a proof of [[False]]. *)

  Inductive False : Prop := .

  Check False.

  (** Let us now introduce implication using the [[Notation]] keyword (yes I'm serious): *)

  Notation "A -> B" := (forall (_ : A), B) : type_scope.

  (** The [[Notation]] statement above says that the implication arrows are just
    another form of quantifying over two Types A and B. Indeed implication is actually just a specialized
    form of the forall quantifier. *)
 
  (** Now that we have implication, we can define conjunction: *)

  Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.


  Arguments conj [P] [Q].
  Notation "P /\ Q" := (and P Q) : type_scope.

  (**  
    You can read the [[->]] like an implication. Therefore definition can be read like this:  
    If [[P]] is a [[Prop]] and if [[Q]] is a [[Prop]] then [[and P Q]] is also a [[Prop]]

    You can also read the [[->]] like a function.
    [[and]] is a type with a single constructor named conj, which is a function that
    takes in a value of type [[Prop]] ([[P]]), a value of type [[Prop]] ([[Q]]), and returns
    a value of type [[Prop]] ([[A /\ B]]), which is just infix notation for [[and A B]].
    Another way of putting that is that conj takes in evidence of A, evidence of B, and returns
    evidence of and A B. 

  *)

  Check and True True.
  Check and True False.
  Check conj.

  (** Note that the proposition [[and]] is not the same as the boolean function [[andb]]
  we defined earlier. *)

  Check and. (* Prop -> Prop -> Prop *)
  Check andb. (* bool -> bool -> bool *)

  (** The same applies to the proposition [[or]] and its boolean counterpart [[orb]]*)

  Inductive or (P Q : Prop) : Prop :=
    | or_introl : P -> or P Q
    | or_intror : Q -> or P Q.
    
  Arguments or_introl [P] [Q].
  Arguments or_intror [P] [Q].
  Notation "P \/ Q" := (or P Q) : type_scope.

  Check or.
  Check orb.

  (** Let us add another type that does not have a boolean counterpart. The existential
  quantifier: *)

  Inductive ex {A : Type} (P : A -> Prop) : Prop :=
    | ex_intro : forall x : A, P x -> ex P.

  Notation "'exists' x , p" :=
    (ex (fun x => p))
      (at level 200, right associativity) : type_scope.

  (** To say that there is some x of type T such that some property P holds of x, we write ∃ x : T, P.
  As with ∀, the type annotation : T can be omitted if Coq is able to infer from the context what the type
  of x should be. *)

(** ** FP - Programming with Propositions *)

  (** Let us start by defining a few simple functions on type [[Prop]].*)

  (** [[not]] negates a proposition [[P]]. *)

  Definition not (P:Prop) := P -> False.

  Check not. (* Prop -> Prop *)
  Check negb. (* bool -> bool *)

  Notation "~ x" := (not x) : type_scope.
  Notation "x <> y" := (~(x = y)) : type_scope.

  (** The logical equivalence [[iff]] is established when two propositions [[P]] and [[Q]] imply each other. *)

  Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

  Module iff_notation.

  Notation "P <-> Q" := (iff P Q)
                        (at level 95, no associativity)
                        : type_scope.

  End iff_notation.

  (** The function Even leverages existential quantification and returns a value of type [[Prop]]. *)

  Definition Even (x : nat) : Prop := exists n, x = double n.

  Check Even : nat -> Prop.

(** ** TP - Proving is Programming *)

  (** Below you'll find a few theorems and their proofs about [[Prop]] which will
  also introduce you to some new tactics fresh off the marked. 🍍🍐🍅🥦🥔  *)

  (** The [[apply]] tactic allows you to apply existing theorems or hypotheses to 
  the proof goal or other hypotheses. *)

  Lemma finish_apply_on_goal:
    forall (A : Prop), A -> A.
  Proof.
    intros A HA. (* Introduce hypotheses *)

    (* Note HA matches A exactly. We can't rewrite because it is not 
    an equality. *)

    apply HA. (* Finish proof by applying HA which matches the goal *)
  Qed.

  Theorem silly1 : forall (p q : Prop),
    p = q ->
    p = q.
  Proof.
    intros p q eq.
    apply eq. (* Rewrite possible but not needed because hypotheses matches goal *)
  Qed.

  (* Hint: the title of the following two lemmas are self-explaining. *)

  (** You can only apply on a goal if the goal matches the RIGHT side of the
  implication. *)

  Lemma apply_on_goal:
    forall (A B : Prop), A -> (A -> B) -> B.
  Proof.
    intros A B HA HAB.
    apply HAB. (* goal matches RIGHT side of implication *)
    apply HA.
  Qed.

  (** You can only apply on a hypothesis if the goal matches the LEFT side of the
  implication. *)

  Lemma apply_on_hypothesis:
    forall (A B : Prop), A -> (A -> B) -> B.
  Proof.
    intros A B HA HAB.
    apply HAB in HA. (* hypothesis HA matches LEFT side of implication *)
    apply HA.
  Qed.

  (** **** Exercise: (silly_ex) *) (** Prove the theorem below. *)
  (** Only use the tactics [[intros]] and [[apply]]. *)

  Theorem silly_ex : forall p,
    (forall n, even n = true -> even (S n) = false) ->
    (forall n, even n = false -> odd n = true) ->
    even p = true ->
    odd (S p) = true.
  Proof.
    intros.
    apply H0.
    apply H.
    apply H1.
   Qed.
    
    

  (** As mentioned before, you can use apply with previously defined theorems,
  not just hypotheses in the context. *)

  Lemma mul_2_even: forall (n : nat), even (2*n) = true.
  Search (2 * _). (* Search existing theorems. That match the pattern 2 * _.
                      found Nat.even_even. *)
  apply Nat.even_mul. (* Apply the matching theorem. *)
  Qed.

  (** **** Exercise: (rev_exercise1) *) (** Prove the theorem below. *)
  (** Use [[rev_involutive]] as part of your (relatively short) solution to this exercise.
      You do not need induction. *)

  Check rev_involutive. (* forall (A : Type) (l : list A), rev (rev l) = l *)

  Theorem rev_exercise1 : forall (l l' : list nat),
    l = rev l' ->
    l' = rev l.
  Proof.
    intros.
    rewrite H.
    rewrite rev_involutive.
    reflexivity.
  Qed.
    
    

  (** **** Exercise: (apply_rewrite) *) 
  (** Briefly explain the difference between the tactics apply and rewrite. What 
  are the situations where both can usefully be applied? *)

  (*

    [[apply]] is used to match a goal or an hypothesis with a known hypothesis, while [[rewrite]] 
    replaces a term using an equality. both can be used when an equality lets convert the goal.
  
  *)

  (** The example below could be solved using rewrite. But let us solve it using
  [[apply]] and a tactic called [[symmetry]]. *)

  Example symmetry_example: forall (p q : Prop),
  p = q ->
  q = p.
  Proof.
    intros p q H.
    (* Here we cannot use apply directly...*)
    Fail apply H.
    (* but we can use the symmetry tactic, which switches the left and right
    sides of an equality in the goal.*)
    symmetry.
    apply H. Qed.

  (** This is possible because equality is a symmetric relation. The [[symmetry]] tactic is
  actually just a shortcut for a theorem that proves the symmetry of equality. *)

  Check eq_sym.
  Print eq_sym.

  (** The same applies to the transitivity of equality. The [[transitivity]] tactic
  allows you to prove that if [[A = B]] and [[B = C]], then [[A = C]]. *)

  Example transitivity_example : forall (A B C : Prop), (A = B) -> (B = C) -> (A = C).
  Proof.
    intros A B C HAB HBC.
    transitivity B. (* Apply the transitivity tactic *)
    - apply HAB.
    - apply HBC.
  Qed.

  (** Injectivity is a property of functions that allows us to prove that if two
  functions are equal, then their arguments must also be equal. In Coq, we can
  prove injectivity using the [[f_equal]] tactic. *)

  (** Use [[f_equal]] to change a goal of the form f x = f y into x = y. *)

  Theorem f_equal_example : forall (n m : nat),
    n = m -> S n = S m.
  Proof.
   intros n m H.
    f_equal. (* Change a goal of the form f x = f y into x = y *) 
             (* This is possible because all constructors are injective. *)
    apply H.
  Qed.

  (** Note there are other relations that are symmetric (e.g. [[and]]), transitive (e.g.
  [[leq]]), or injective (e.g. [[square nat -> nat]]). *)
  
  (** The tactics [[symmetry]], [[transitivity]]
  and [[f_equal]] will work for any relation (function) for which the respective property
  has been proven. *)
  
  (** Similarily [[rewrite]] and [[reflexivity]] can be for example used with iff statements,
  not just equalities. To enable this behavior, we have to import the Coq library that supports it: *)

  Example iff_example : forall (A B : Prop), A <-> B -> B <-> A.
  Proof.
    intros A B H.
    symmetry. (* The standardnlibrary contains proofs that <-> is reflexive,
                 symmetric and transitive. This enables the use of rewrite and
                 reflexivity on statements containing <->. *)
    apply H.
  Qed.

  (** Now let us do some proofs about the logical connectives that we've introduced earlier. *)
  
  (** To prove a conjunction, use the [[split]] tactic. This will generate two subgoals,
   one for each part of the statement: *)

   Example and_example : forall (A B : Prop), A -> B -> A /\ B.
   Proof.
   intros A B HA HB.
   split.
    - apply HA.
    - apply HB.
  Qed.

  (** The tactic [[discriminate]] allows you to finish a proof that contains
  contradictory assumptions. This is possible thanks of the principle of disjointness,
  which says that two terms beginning with different constructors (like O and S, or true
  and false) can never be equal. *)

  Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
  Proof.
    intros n m contra. discriminate contra.
  Qed.

  (** **** Exercise: (plus_is_O) *)  (** Proof the theorem below using [[split]] and
  [[discriminate]] *)

  (** Hint 1: You'll have to do induction on both subgoals after the [[split]]. *)
  (** Hint 2: Do induction on different variables. *)
  (** Hint 3: Rewrite with [[Nat.add_comm]], if simplification does not work on a hypothesis. *)

  Check Nat.add_comm.
  Search (_ + 0).

  Lemma plus_is_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
  Proof.
    intros.
    split.
      - induction n.
        + reflexivity.
        + discriminate H.
      - induction n.
        + rewrite <- H. reflexivity.
        + discriminate H.
  Qed.


  (** If you find yourself with a conjunction in a hypothesis use destruct to
  to turn it into two hypotheses which contain one side of the conjunction respectively. *)

  Lemma and_example2 :
    forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
  Proof.
    intros n m H.
    destruct H as [Hn Hm]. (* destruct the conjunction H into two hypotheses *)
    rewrite Hn. rewrite Hm.
    reflexivity.
  Qed.

  (** **** Exercise: (proj2) *)  (** Prove the theorem below. *)

  Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
  Proof.
    intros.
    apply H.
  Qed.

  (** Disjunction is a bit different. You can use the [[left]] and [[right]]
  tactics to prove disjunctions. These tactics will generate a subgoal for each
  side of the disjunction. *)

  Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
  Proof.
    intros A B HA.
    left.
    apply HA.
  Qed.

  Lemma zero_or_succ :
    forall n : nat, n = 0 \/ n = S (pred n).
  Proof.
    intros. destruct n.
    - left. reflexivity.
    - right. reflexivity.
  Qed.

  (** **** Exercise: (mult_is_O) *)  (** Prove the theorem below. *)
  (** Hint: You may use the tactic [[discriminate]] to finish the proof. *)
  
  Search (_ * 0).

  Lemma mult_is_O :
    forall n m, n * m = 0 -> n = 0 \/ m = 0.
  Proof.
   intros. destruct n.
     - left. reflexivity.
     - destruct m.
       + right. reflexivity.
       + discriminate H.
  Qed.

  (** **** Exercise: (or_commut) *)  (** Prove the theorem below. *)

  Theorem or_commut : forall P Q : Prop,
    P \/ Q -> Q \/ P.
  Proof.
   intros. destruct H.
     - right. apply H.
     - left. apply H.
  Qed.

  (** Remember that from False you can prove anything. This is called the principle of
  explosion. In Coq, this is represented by the [[ex_falso_quodlibet]] theorem. *)

  Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
  Proof.
    intros P contra.
    destruct contra.
  Qed.

  (** The tactic [[unfold]] allows you to unfold the definition of a function or
  a proposition. This is useful when you want to see the inner workings of a
  definition or when you want to simplify a proof by removing the function
  application. *)

 Theorem not_False :
    ~False.
  Proof.
    unfold not. intros H. destruct H. Qed.

  Theorem contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q.
  Proof.
    intros P Q [HP HNA]. unfold not in HNA.
    apply HNA in HP. destruct HP. Qed.

  Theorem double_neg : forall P : Prop,
    P -> ~~P.
  Proof.
    intros P H. unfold not. intros G. apply G. apply H. Qed.

  (** ** Exercise: (not_both_true_and_false) *)  (** Prove the theorem below. *)
  Theorem not_both_true_and_false : forall P : Prop,
    ~ (P /\ ~P).
  Proof.
    unfold not. intros. destruct H. apply H0. apply H. Qed.

  (** Like conjunction, equivalence can also be proved using the [[split]] tactic. *)

  Theorem iff_sym : forall P Q : Prop,
    (P <-> Q) -> (Q <-> P).
  Proof.
    intros P Q [HAB HBA].
    split.
    - apply HBA.
    - apply HAB. Qed.


(** Let us summarize what we have defined so far in our universe of [[Prop]]:
    - [[True]]  to represent proposition that are true. A proposition [[P]] is considered true
                when there is evidence or proof for [[P]].
    - [[False]] to represent propositions that we do not have evidence for ie. there is no proof.
    - [[->]]    implication as a special use case of the quantifier [[forall]]
    - [[and]]   conjunction and [[or]] disjunction as types to construct more complex propositions 
    - [[<->]]   if and only if as [[P -> Q /\ Q -> P]]
    - [[not]]   as a function that returns a more complex proposition [[P -> False]] (leveraging
      implication and False)

    Note that we implemented all of this by relying solely on the features of functional programming
    and the quantifier [[forall]].
    
    There are other interesting facts about the inner workings of Coq related to this. We're going
    to discuss them in the following (smaller) subsections. *)

(** *** Decidability and propositional logic - Bool vs. Prop *)

  (**
  We've seen two different ways of expressing logical claims in Coq: with booleans (of type bool),
  and with propositions (of type Prop).

  Here are the key differences between bool and Prop:

                                            bool     Prop
                                            ====     ====
            decidable?                      yes       no
            useable with match?             yes       no 
            works with rewrite tactic?      no        yes

  *)

  (** To profit from the advantages of both worlds, we can proof for example the equivalence
  between boolean functions and their propositional counterparts. *)

  Theorem eqb_eq : forall n1 n2 : nat,
    n1 =? n2 = true <-> n1 = n2.
  Proof.
    intros n1 n2. split.
    - apply Nat.eqb_eq.
    - intros H. rewrite H. rewrite Nat.eqb_refl. reflexivity.
  Qed.

  (** Here an example on how to leverage these equivalences in our proofs. *)
  Lemma plus_eqb_example : forall n m p : nat,
    n =? m = true -> n + p =? m + p = true.
  Proof.
    intros n m p H.
    rewrite eqb_eq in H.
    rewrite H.
    rewrite eqb_eq.
    reflexivity.
  Qed.

(** *** Classical vs. Constructive Logic *)

  (** In logic, we distinguish between classical and constructive approaches.
  - Classical logic allows the use of the law of excluded middle and other
    non-constructive principles.
  - Constructive logic requires that proofs are constructed explicitly.

  As we have seen, Coq uses a constructive logic ([[Prop]] are built using constructors)
  and has therefore, by default, no law of excluded middle.
  *)

  (** If one wants to use the law of the excluded middle in Coq, it
  has to be introduced as an axiom. *)

  Axiom excluded_middle : forall P : Prop, P \/ ~P.

  (** Example proof using the excluded middle axiom: *)

  Theorem example_excluded_middle : forall P : Prop, ~ ~ P -> P.
  Proof.
    intros P H.
    destruct (excluded_middle P) as [H0 | H0].
    - assumption.
    - apply ex_falso_quodlibet. 
      apply H. 
      assumption.
  Qed.

(** *** Curry-Howard Correspondence *)

  (**
    In the Curry-Howard correspondence, a type [[A]] represents a logical proposition [[A]].
    A value of type [[A]]  represents a proof of the proposition [[A]]. In other words
    if one can construct a value of type [[A]], one has proven the proposition [[A]]. A function
    [[f: A -> B]] transforms a proof of [[A]] (element of type [[A]]) into a proof of [[B]]
    (element of type [[B]]).

      propositions (A : Prop) ~  types        (A : Type)
      proofs       (a : A)    ~  data values  (a : A)   
      implications A -> B     ~  functions    (A => B)

    This is what is happening behind the scenes in Coq. When we prove theorems, we are
    actually writing functions that construct values. These values are then checked by 
    Coq's type checker against the corresponding types of the propositions. If the 
    types match, it confirms that the constructed value is a valid proof of the
    proposition.
  *)

  (** The example below illustrates this correspondence. The proposition [[ev n]] states that
  the number [[n]] is even. The constructor [[ev_0]] takes no arguments and returns a proof
  of [[ev 0]]. The constructor [[ev_SS]] is a function that takes a proof of [[ev n]] and returns
  a proof of [[ev (S (S n))]]. *)

  Inductive ev : nat -> Prop :=
    | ev_0 : ev 0
    | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

  Check ev_SS.
  Check ev 4.

  Theorem ev_4 : ev 4.
  Proof.
    Show Proof.
    apply ev_SS. (* apply constructor ev_SS *)
    Show Proof.
    apply ev_SS.
    Show Proof.
    apply ev_0.
    Show Proof.
  Qed.

  (** Behind the scenes, theorem [[ev_4]] is a function that constructs a value of type [[ev 4]]. *)