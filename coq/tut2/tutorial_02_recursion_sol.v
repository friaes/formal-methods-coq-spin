(** * Recursion *)

(** ** FP - Recursive Types *)
(** {https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html#lab32} *)

  (** Enumerated types are a little bit boring in the sense, that its constructors
  are just simple names and have no other "constructing-ability" outside that. *)

  (** Let us define something that cannot be enumerated, something that is...
  infinite 😮 like natural numbers. To do this we introduce a new concept called
  "recursion". Recursion allows us to define something by referring to a (simpler)
  part of itself. *)

  Module NatPlayground.

  Inductive nat : Type := 
    | O
    | S (n : nat).

  (** Note that the parameter [[n]] of the constructor [[S]] takes a value of type
  [[nat]], which is the exact type which we are defining. Yes, we are referring to
  [[nat]] while defining [[nat]] 🤯. In other words, we are defining [[nat]]
  recursively. This is what allows us to define infinite types like natural
  numbers.

  This inductive definition can therefore be read like this:
  - O is a natural number and (we call this the base case, here it corresponds to a zero)
  - everything that is constructed by an S followed by a natural number is also a
    natural number (we call this the inductive step).

  Agreed, this is a very simple definition of natural numbers. Nevertheless we
  will see that it is very powerful.

  *)

  (** Now let us see how we can construct natural numbers, using the two
  constructors O and S.
  *)

  Check O.
  Check S O.

  (** O and S O are of type nat as expected. *)

  Fail Check O S. (* Remove the [[Fail]] to see the error. *)

  (** Check O S fails because none our definitions allow such a construction. *)

  End NatPlayground.

  (** Recap:

  - Constructors describe how elements of a given type [[T]] can be constructed.
  - Everything that can be constructed using the constructor of type a [[T]] has type [[T]].
  - Everything that can not be constructed like this is not of said type.
  - Inductive definitions are often defined by a
    -- Base case (simple constructor) and an 
    -- Inductive step (by leveraging recursion on a parameter of its own type).
  *)

(** ** FP - Recursive Functions *)
  Module NatPlayground2.
  (** Let us define some properties about our type of natural numbers. The function
  below computes the predecessor of a natural number. *)

  Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

  Check pred.
  Check pred 0.
  Check pred (S O).
  Check pred 1.

  Compute pred (S (S O)).

  Compute pred (1+5).

  (** Like with our functions on [[bool]] we match the parameter against the
  constructors of our type [[nat]]. In the first case, where [[n]] is matched
  against the constructor [[O]], the function returns [[O]]. So we're basically
  stating that the predecessor of the natural number 0 is 0. In the second
  case [[n]] is matched against something of the form [[S n']] (note [[n']] is not
  the same as [[n]]) then the return value is [[n']].
  *)

  (** Here we define a function that takes an argument of type [[nat]] and has a
  return value of type [[bool]]. *)

  Definition is_zero (n : nat) : bool :=
  match n with
    | O     => true
    | S n'  => false
  end.

  Check is_zero.
  Check is_zero O.
  Check is_zero 42.

  Compute is_zero 0.
  Compute is_zero 42.


  Compute (is_zero (pred 0)).
  Compute is_zero (pred 1).

  (** Next we're going to declare some more interesting functions on natural
  numbers.

  We declare a function, that computes whether a given number [[n]] of type [[nat]] is even.
  We want to compute even numbers recursively. Recursive functions are functions that
  call themselves. To define recursive functions in Coq we use the keyword
  [[Fixpoint]].
  *)

  Fixpoint even (n:nat) : bool :=
  match n with 
    | O        => true 
    | S O      => false
    | S (S n') => even n'
  end.

  (** This declaration can be read like this:

  Take the argument [[n]] and match it against the patterns below. In case you
  match [[n]] to
  - [[O]] then return [[true]],
  - 1 then return [[false]],
  - [[n' + 2]] then call the function [[even]] again to check wether [[n']] is an even number

  Coq ensures that recursive functions that are declared with the [[Fixpoint]]
  keyword terminate. For example, Coq won't accept the inverse declaration of the
  last step ("in case you match [[n]] to [[n']] then check whether [[n' + 2]]) is
  an even number"). 
  *)

  Fail Fixpoint infinite_even (n:nat) : bool := (* Remove [[Fail]] to see the error *)
  match n with
    | O        => true 
    | S O      => false
    | n'       => infinite_even (S ( S n'))
  end. 

  (** **** Exercise: (c_odd) *)
  (** Define [[odd]] that checks whether a number [[n]] is odd. You do not need
  [[Fixpoint]] for this exercise. *)

  Definition odd (n:nat)  : bool :=
    negb (even n).

  (** The recursive function [[plus]] takes two arguments of type [[nat]] (or as
  we have learned one argument of type [[nat -> nat]] 😉) *)

  Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

  Compute plus 2 5. (* 7 *)

  (** Note that one can abbreviate [[(n : nat) (m : nat)]] with [[(n m : nat)]] as
  illustrated by [[mult]] below. This works of course only when [[n]] and [[m]]
  have the same type. *)

  Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

  Compute mult 2 5. (* 10 *)

  (** You may also match against two parameters at the same time. As shown below
  with [[minus]]. *)
  Fixpoint minus (n m : nat) : nat :=
  match n, m with
    | O   , _     => O 
    | S _ , O     => n 
    | S n', S m'  => minus n' m'
  end.

  Compute minus 10 20. (* 0 *)
  Compute minus 20 15. (* 5 *)

  (** Again, we may want to write [[x + y]] instead of [[plus x y]] in some
  situations, which is why we introduce the notations below. *)

  Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope. 
  Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
  Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

  (** **** Exercise: (c_factorial) *)
  (** Define a [[factorial]] that computes the factorial of a number [[n]]:
  factorial(0)  =  1
  factorial(n)  =  n * factorial(n-1)     (where n>0)
  *)
  Fixpoint factorial (n:nat)  : nat :=
    match n with
        | O => 1
        | S n' => n * factorial n'
    end.

  (** **** Exercise: (q_eqb_1) *)
  (** Study the function declared below and describe in your own words what it does. *)

  Fixpoint eqb (n m : nat) : bool :=
  match n with
    | O => match m with
        | O => true
        | S m' => false end
    | S n' => match m with
        | O => false
        | S m' => eqb n' m' end
  end.

  (** 
    It compares the natural numbers [[n]] and [[m]] and returns the boolean [[true]] when
    [[n]] is equal to [[m]].

    The function is implemented using two match clauses. The first matches [[n]]
    against:
    - [[O]]. If this is the case, then we match [[m]] against:
        - [[O]]. Then both [[n]] and [[m]] are zero, and therefore equal,
          so we return [[true]].
        - [[S m']]. Then [[m]] is not zero, but [[n]] is, so they are not equal,
          and we return [[false]].
    - [[S n']]. If this is the case, then we match [[m]] against:
        - [[O]]. Then [[m]] is zero, but [[n]] is not, so they are not equal,
          and we return [[false]].
        - [[S m']]. Then neither [[n]] nor [[m]] are zero. We therefore subtract
          one from both numbers and call [[eqb]] again.

    The two arguments become smaller with each call of [[eqb]] until one of them reaches zero,
    at which point we can determine whether they are equal or not.
  
  *)

  (** **** Exercise: (q_leb) *)
  (** Study the function declared below and describe in your own words what it does. *)

  Fixpoint leb (n m : nat) : bool :=
  match n with
    | O => true
    | S n' => match m with
      | O => false
      | S m' => leb n' m' end
  end.

  (**
    It compares the natural numbers [[n]] and [[m]] and returns the boolean [[true]] when
    [[n]] is less than or equal to [[m]].

    The function is implemented using two match clauses. The first matches [[n]] against:
    - [[O]]. If this is the case, then [[n]] is zero, which is the smallest possible natural 
      number, so it is less than or equal to any [[m]], and we return [[true]].
    - [[S n']]. If this is the case, then we match [[m]] against:
        - [[O]]. Then [[m]] is zero, which is smaller than [[n]], so [[n]] is not less than
          or equal to [[m]], and we return [[false]].
        - [[S m']]. Then neither [[n]] nor [[m]] are zero. We therefore subtract one from
          both numbers and call [[leb]] again.

    The two arguments become smaller with each call of [[leb]] until one of them reaches zero,
    at which point we can determine whether [[n]] is less than or equal to [[m]] or not.
  *)

  (** **** Exercise: (q_eqb_2) *)
  (** Check the functions behavior using the statements below. Describe in your own
  words what you observe and whether it corresponds to your previous answer.
  Please do not change your answer above. If you want to correct it, do so here. *)

  Compute (eqb 4 5).
  Compute (eqb 5 5).
  Compute (eqb 6 5).

  (** 
    Results as expected. 

  *)


  (** **** Exercise: (q_leb_2) *)
  (** Check the functions behavior using the statements below. Describe in your own
  words what you observe and whether it corresponds to your previous answer.
  Please do not change your answer above. If you want to correct it, do so here. *)

  Compute (leb 4 5).
  Compute (leb 5 5).
  Compute (leb 6 5).

  (** 
    Results as expected.

  *)

  (** Since now know what we're doing (note this does not mean that what we're
  doing is correct). We can add some fancy notation. *)
  Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
  Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

  Compute (4 =? 5).
  Compute (5 =? 5).
  Compute (6 =? 5).

  Compute (4 <=? 5).
  Compute (5 <=? 5).
  Compute (6 <=? 5).
  End NatPlayground2.

(** ** TP - Proofs on Recursive Objects *)

  Import Nat.
  (** Let us state and prove a theorem about natural numbers. But before we do so... *)

  (** Remember how [[n + m]] is just another notation
  for calling the previously defined function [[plus n m]]. Take a look at the
  declaration of the [[Fixpoint plus]]. Trace down it's execution step by step,
  by assuming that only the first argument is known [[plus 0 m]]. *)

  (** **** Exercise: (q_retrace_simpl_1) *)
  (** Explain how [[simpl]] behaves when simplifying  [[0 + m]]. *) 

  (**
    When simplifying [[0 + m]], the [[simpl]] tactic will use the definition of the [[plus]] function to rewrite the expression.

    The [[plus]] function is defined as:
    Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

    When [[n]] is [[0]], the [[match]] clause will select the first branch, which returns [[m]]. Therefore, [[0 + m]] will be simplified to [[m]].

    In other words, [[simpl]] will replace [[0 + m]] with [[m]], effectively removing the [[0 + ]] part, since adding [[0]] to any number does not change the value of that number.

  *)

  (** Ok, now we're ready, set, prove! *)
  
  Theorem plus_O_n : forall m : nat, 0 + m = m.
  Proof.
    intros m. simpl. reflexivity.
  Qed.

  (** Smooth... Let's do the same but inverse the adders. *)

  (** Like before, go through [[Fixpoint plus]] step by step, but this time
  assume that only the second argument is known [[plus n 0]]. *)

  (** **** Exercise: (q_retrace_simpl_2) *)
  (** Explain how [[simpl]] behaves when simplifying  [[n + 0]]. *) 

  (**
    When simplifying [[n + 0]], the [[simpl]] tactic will not be able to simplify the expression further because the value of [[n]] is unknown.

    The [[plus]] function is defined as:
    Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

    The [[match]] clause will try to match [[n]] with the pattern [[O]], but since [[n]] is a variable, it may or may not be [[O]]. Therefore, the [[simpl]] tactic will not be able to apply the first branch of the [[match]] clause, and the expression [[n + 0]] will not be simplified.

  *) 

  (** And now gently step through the proof below. *)

  Theorem try_1_plus_n_O : forall n : nat, n + 0 = n.
  Proof.
    intros n. simpl.
    
    
    
    
    
    
    










    admit. (* stuck *)
  Admitted.

  (** Did you observe how [[simpl]] fails to simplify the term [[n + 0]]?
  Don't worry we'll get to the bottom of this in the exercise below 🕵️ *)

  (** **** Exercise: (q_retrace_simpl_3) *)
  (** Explain why [[simpl]] can simplify [[0 + n]] but not [[n + 0]]. *) 

  (** 
    See previous answers.

  *)

  (** Will the proof below work? Answer the question first, then try to
   do the proof yourself: *)

  (** **** Exercise: (q_mult_l_r) *)
  (** Explain how you would tackle the proof [[mult_0_l]] and [[mult_0_r]] below and
  whether it is possible with the tactics we know so far. *) 

  (**
    Since the implementation of [[mult]] is structurally similar to [[plus]], we can expect that the proof of [[mult_0_l]] and [[mult_0_r]] will be similar to the proof of [[plus_O_n]].

  *)

  (** **** Exercise: (p_mult_0_l) *) (** Prove the theorem below if it is 
  possible with our current tactics. *)

  Theorem mult_0_l : forall (m : nat), mult 0 m = 0.
  Proof.
    intros. simpl. reflexivity.
  Qed.

  (** **** Exercise: (p_mult_0_r) *) (** Prove the theorem below if it is
  possible with our current tactics. *)

  Theorem mult_0_r : forall (n : nat), mult n 0 = 0.
  Proof.
    intros. simpl. admit. Admitted. (* Not possible with current tactics *)


  (** Like in mathematical proofs, we sometimes want to rewrite terms. In Coq we
  can do this based on previously made assumptions or proven lemmas. Observe how
  intros is also used to introduce the left side of the implication into our list
  of hypotheses.
  *)

  Theorem plus_id_example : forall n m:nat, n = m -> n + n = m + m.
  Proof.  
    intros n m.   (* move both quantifiers into the context: *)
    intros H.     (* move the hypothesis into the context: *)
    rewrite -> H. (* rewrite the goal using the hypothesis: *)
    reflexivity.
  Qed.

  (** The tactic [[rewrite]] rewrites the term in the proof goal with the left or
  right side (depending on the direction of the arrow -> or <-) of an equality in
  our list of assumptions. *)

  (** **** Exercise: (p_plus_id_exercise) *) (** Prove the theorem below. *)

  Theorem plus_id_exercise : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
  Proof.
    intros. rewrite -> H. rewrite -> H0. reflexivity.
  Qed.

  (** The tactic [[rewrite]] can also be used to rewrite using previously proven
   lemmas. *) 

  (** For example the proofs below use [[mult_n_0]] and [[mult_n_Sm]] that have been
  proven in Coqs standard library. *)
  Check mult_n_O.  (* 0 = n * 0 *)
  Check mult_n_Sm. (* n * m + n = n * S m *)
  Search (_ * 0).

  (** **** Exercise: (p_mult_n_0_m_0) *) (** Prove the theorem below. *)
  (** Hint: You may use rewrite with the theorems [[mult_n_O]] and [[mult_n_Sm]]. *)

  Theorem mult_n_0_m_0 : forall p q : nat,
    (p * 0) + (q * 0) = 0.
  Proof.
    intros p q.
    rewrite <- mult_n_O.
    rewrite <- mult_n_O.
    reflexivity. Qed.


    (** **** Exercise: (p_mult_n_1) *) (** Prove the theorem below. *)
    (** Hint you may use rewrite with the theorems [[mult_n_O]] and [[mult_n_Sm]]. *)
  Theorem mult_n_1 : forall p : nat,
    p * 1 = p.
  Proof.
    intros. rewrite <- mult_n_Sm. rewrite <- mult_n_O. reflexivity.
  Qed.

  (** In some situations, we want to prove a statement by reasoning about the
  different values a variable can take. To do this we use the tactic [[destruct
  x]], where [[x]] is the variable of which we want to make a case analysis about. *)

  (** Before stepping through the proof below, let's review the declaration of the
  type [[bool]]. *)

  (** Exercise: (q_review_bool) *) (** How many constructors does the type [[bool]]
  have? Name them. *)

  (**
    The type [[bool]] has two constructors:
    - [[true]]
    - [[false]]

  *)

  Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
  Proof.
    intros b.
    destruct b eqn:E.
    - reflexivity.
    - reflexivity.
  Qed.

  (** [[destruct]] splits the proof-goal into two cases, one where [[b]] takes the
  value [[true]] and one where [[b]] takes the value [[false]]. Note that they
  correspond to the two constructors that make up our type [[bool]]. *)

  (** The [[eqn:E]] is used to give a name to the equation that is generated by the destruct
  tactic. *)

  (** Sometimes it is useful to use [[destruct]] on a subgoal. You may use the symbols
  [-], [+], [*]  or any repetition of those to structure the proof into different levels
  of subgoals. *)

  Theorem andb_commutative : forall b c, andb b c = andb c b.
  Proof.
    intros b c. destruct b eqn:Eb.
    - destruct c eqn:Ec.
      + reflexivity.
      + reflexivity.
    - destruct c eqn:Ec.
      + reflexivity.
      + reflexivity.
  Qed.

  (** Curly braces can also be used to that end. *)

  Theorem andb_commutative' : forall b c, andb b c = andb c b.
  Proof.
    intros b c. destruct b eqn:Eb.
    { destruct c eqn:Ec.
      { reflexivity. }
      { reflexivity. } }
    { destruct c eqn:Ec.
      { reflexivity. }
      { reflexivity. } }
  Qed.

  (** A combination of bullets and braces is also possible. *)

  Theorem andb3_exchange :
    forall b c d, andb (andb b c) d = andb (andb b d) c.
  Proof.
    intros b c d. destruct b eqn:Eb.
    - destruct c eqn:Ec.
      { destruct d eqn:Ed.
        - reflexivity.
        - reflexivity. }
      { destruct d eqn:Ed.
        - reflexivity.
        - reflexivity. }
    - destruct c eqn:Ec.
      { destruct d eqn:Ed.
        - reflexivity.
        - reflexivity. }
      { destruct d eqn:Ed.
        - reflexivity.
        - reflexivity. }
  Qed.

  (** Now let us consider an example that warrants a destruct on a non-enumerable
  datatype. Our much beloved, natural numbers.
  *)

  Theorem plus_1_neq_0 : forall n : nat,
    (n + 1) =? 0 = false.
  Proof.
    intros n.
    destruct n as [ | n'] eqn:E.
    - reflexivity.
    - reflexivity.
  Qed.

  (** The tactic [[destruct]] splits the proof goal into two cases corresponding
  to our two constructors. One being the base-case [[O]] and the other one being the
  inductive step [[S n']]. *)

  (** The [[ | n']] is used to give the name [n'] to the argument of the constructor [S]
  (since O has no arguments there is nothing to the left of the |). *)

  (** Before introducing the next tactic, let's apply what we've learned so far 
  on a few exercises. *)

  (** **** Exercise: (p_andb_true_elim2) *) (** Prove the theorem below. *)

  (** Hint 1: You will eventually need to destruct both booleans, as in the theorems above.
  But its best to delay introducing the hypothesis until after you have an opportunity to
  simplify it. *)

  (** Hint 2: When you reach a contradiction in the hypotheses, focus on how to
  rewrite with that contradiction. *)

  Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
  Proof.
    intros b c.
    destruct b eqn:Eb.
    - destruct c eqn:Ec.
      -- simpl. intros H. reflexivity.
      -- simpl. intros H. rewrite H. reflexivity.
    - destruct c eqn:Ec.
      -- simpl. intros H. reflexivity.
      -- simpl. intros H. rewrite H. reflexivity.
  Qed.

  (** **** Exercise: (p_zero_nbeq_plus_1) *) (** Prove the theorem below. *)
  Theorem zero_nbeq_plus_1 : forall n : nat,
    0 =? (n + 1) = false.
  Proof.
    intros n. destruct n as [| n'] eqn:E.
    - simpl. reflexivity.
    - simpl. reflexivity.
  Qed.


  (** **** Exercise: (p_identity_fn_applied_twice) *) (** Prove the theorem below. *)

  Theorem identity_fn_applied_twice :
    forall (f : bool -> bool),
    (forall (x : bool), f x = x) ->
    forall (b : bool), f (f b) = b.
  Proof.
    intros f H b.
    rewrite H. rewrite H. reflexivity.
  Qed.

  (** **** Exercise: (p_negation_fn_applied_twice) *) (** Prove the theorem below. *)
  Theorem negation_fn_applied_twice :
    forall (f : bool -> bool),
    (forall (x : bool), f x = negb x) ->
    forall (b : bool), f (f b) = b.
  Proof.
    intros f H b.
    rewrite H. rewrite H. destruct b eqn:Eb.
    - simpl. reflexivity.
    - simpl. reflexivity.
  Qed.

  (** **** Exercise: (p_andb_eq_orb) *) (** Prove the theorem below. *)
  (** (Hint: This one can be a bit tricky,
  depending on how you approach it.  You will probably need both
  [destruct] and [rewrite], but destructing everything in sight is
  not the best way.) *)

  Theorem andb_eq_orb :
    forall (b c : bool),
    (andb b c = orb b c) ->
    b = c.
  Proof.
    intros b c.
    destruct b.
    - destruct c.
      -- simpl. reflexivity.
      -- simpl. intros H. rewrite H. reflexivity.
    - destruct c.
      -- simpl. intros H. rewrite H. reflexivity.
      -- simpl. reflexivity.
  Qed.

  (** ... That was fun right? Ok let's continue. *)

  (** Remember our attempt to prove [[n + 0 = n]] where we got stuck? Maybe we can
  use destruct to solve it! *)

  Theorem try_2_plus_n_O : forall n : nat, n + 0 = n.
  Proof.
    intros n. simpl.
    destruct n.
    - simpl. reflexivity. (* Yes 🤩 *)
    - simpl. admit. (* Stuck again 😞 *)
  Admitted.

  (** If only, we could rely on the discrete mathematicians' all-time favorite
  proof technique. Yes, you know which one I'm talking about - [[induction]]. *)

  (** **** Exercise: (q_add_0_r) *) (** Prove the theorem [[add_0_r]] by hand using
  mathematical induction. *)

  (** Hint: If you don't know or remember how mathematical induction works 
  you can look it up on the internet or in a book on discrete mathematics. *)

  (** 
    add_0_r: forall (n : nat), n + 0 = n.
    
    FILL IN HERE

  *)

  (** {https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html#lab62} *)

  Theorem add_0_r : forall (n : nat), n + 0 = n.
  Proof.
    intros n. induction n as [|n' IHn'].
    - reflexivity. (* n = 0 *) 
    - simpl. rewrite -> IHn'.  (* n = S n' *)
      reflexivity.
  Qed.

  (** When stepping though the proof above, you'll notice that [[induction]] works
  pretty much like [[destruct]], with the only difference being the added induction
  hypothesis [[IHn']] in the inductive step (the second case). *)

  (** Train your induction skills on the exercises below. You might need previously
  proven results. *)

  (** **** Exercise: (plus_n_Sm) *) (** Prove the theorem below. *)
  Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
  Proof.
    intros n m. induction n as [|n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
  Qed.

  (** **** Exercise: (add_comm) *) (** Prove the theorem below. *)
  Theorem add_comm : forall n m : nat,
    n + m = m + n.
  Proof.
    intros n m. induction n as [|n' IHn'].
    - simpl. rewrite -> add_0_r. reflexivity.
    - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
  Qed.

  (** **** Exercise: (add_assoc) *) (** Prove the theorem below. *)
  Theorem add_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
  Proof.
    intros n m p. induction n as [|n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
  Qed.

  (** **** Exercise: (q_mul_0_r) *) (** Prove the theorem [[mul_0_r]] by hand using
  mathematical induction. *)

  (** 
    mul_0_r: forall (n : nat), n * 0 = 0.

    Base case:
    We need to show that [[0 * 0 = 0]].
    By definition of mult (O => O), we have [[0 * 0 = 0]], so the base case holds.

    Inductive step:
    Assume that [[k * 0 = 0]] for some arbitrary natural number [[k]].
    We need to show that [[(k + 1) * 0 = 0]].

    Using the definition of mult (S n' => plus m (mult n' m)), we have:
    [(k + 1) * 0 = 0 + (k * 0)]. 
    Using the definition of plus (O => m), we have:
    [0 + (k * 0) = k * 0]. 

    By the inductive hypothesis,
    [[k * 0 = 0]].

    Therefore, we have:
    [(k + 1) * 0 = 0 + (k * 0) = k * 0 = 0].

    So, the inductive step holds.
  *)

  (** **** Exercise: (p_mul_0_r) *) (** Prove the theorem below. *)
  Theorem mul_0_r : forall n : nat,
    n * 0 = 0.
  Proof.
    intros n. induction n as [|n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
  Qed.


  (** **** Exercise: (p_eqb_refl) *) (** Prove the theorem below. *)
  Theorem eqb_refl : forall n : nat, (n =? n) = true.
  Proof.
    intros n. induction n as [|n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
  Qed. 

  (** **** Exercise: (p_even_S) *) (** Prove the theorem below. *)
  Theorem even_S : forall n : nat, even (S n) = negb (even n).
  Proof.
    intros n. induction n as [|n' IHn'].
    - simpl. reflexivity.
    - rewrite -> IHn'. simpl. rewrite -> negb_involutive. reflexivity.
  Qed.
