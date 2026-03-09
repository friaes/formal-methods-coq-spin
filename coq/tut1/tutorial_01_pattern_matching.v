(** * Functional Programming and Theorem Proving with Coq *)

(* ################################################################# *)

(** * Attribution *)
  (** This tutorial draws heavily and contains significant excerpts 
  from the "Software Foundations" book by Benjamin C. Pierce et al. The
  authors of this tutorial have obtained permission from the original authors to
  use this material for educational purposes within a classroom setting. All
  credit for the content derived from the Software Foundations book belongs to the
  original authors. **)

(** * Overview *)

  (** The art of Formal Theorem Proving encompasses three major fields, which we
  are going to introduce in this class:
  - Logic, which is the field of study whose subject matter is proofs -- 
    unassailable arguments for the truth of particular propositions.
  - Functional programming (FP), can be seen as as a method of programming that
    simplifies reasoning about programs and as a bridge between programming
    and logic.
    We use FP to describe our logic by leveraging:
    --  A type system which is used to describe our logics syntax.
        In other words we use the type system to describe how terms
        of our logic can be written down.
    --  Functions, which are used to describe our logics semantics. In other
        words to give meaning to the syntactic constructs described by types.
  - Formal Theorem Proving (TP), is used to prove facts about our logic.
    This is done with so called Proof Assistants. They, are hybrid tools that 
    automate the more routine aspects of building formal proofs while depending on
    human guidance for more difficult aspects. 

  The proof assistant Coq itself can be viewed as a combination of a small but
  extremely expressive functional programming language plus a set of tools for
  stating and proving logical assertions.
  *)


(** * Pattern Matching *)

(** ** FP - Enumerated Types *)
(** {https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html#lab22}*)

  (** A type is a set of data values. In Coq, everything belongs to a type.

  New types are defined inductively by using a list of so called "constructors".
  They are called constructors because they can be used to construct elements of a
  given type.
  
  Everything that can be constructed by the constructors of an
  arbitrary type [[A]] belongs to said type and - more importantly - everything
  that cannot be constructed like this, does not belong to said type [[A]].

  In Coq we declare new types using the keyword [[Inductive]] followed by the name
  of the type a colon and the type of the type (yes even types have types in Coq).
  The [[:=]] separates the type header from the list of its constructors. The constructors
  are separated by the symbol [[|]]. The end of the definition is declared using a
  [[.]].
  *) 

  (** Let us define an enumerated type for boolean values: *)
  Inductive bool : Type := 
    | true 
    | false.

  (** We defined a new enumerated type called [[bool]]. It contains the
  constructors [[true]] and [[false]]. It is called an enumerated type, because
  its definition contains a finite (thus enumerable or countable) set of elements.

  Since this is an inductive definition, every [[true]] and every [[false]] we
  encounter from now on are of type [[bool]]. Conversely nothing else is of type
  [[bool]]. *)

  (** Lets check for ourselves what type [[true]] has: *)

  Check true. (* true : bool *)

  (** Let us construct a type from another type. We do this by using so called
  (type-) parameters. *)

  Inductive rgb : Type := 
    | red 
    | green
    | blue.

  Inductive color : Type :=
    | black
    | white
    | primary (p : rgb).

  (** We declare the constructor [[primary]] by using a parameter [[p]] of type
  [[rgb]]. The parameter stands for "anything that has type rgb".

  So in other words the definition of [[color]] can be read like this:
  - black is a color
  - white is a color
  - primary followed by something of type rgb is a color.

  Note that [[rgb]] and [[color]] are both still enumerated types because they
  consist of a finite set of simple constructors.
  *)

  Check black. (** color *)
  Check red. (** rgb *)
  Check primary red. (** color *)

(** ** FP - Pattern-Matching Functions *)

  (** In the previous section we declared types like [[bool]]
  and [[color]] by stating how elements of such types can be constructed (syntax).

  We have however not given a description of what [[bool]] or [[color]] actually
  are. There is no meaning (semantics) attached to our definitions.

  The meaning of types comes from the way we use them in computations. In Coq we
  can do this by declaring functions, that describe legal ways of how elements of
  a given type can be manipulated and transformed.
  *)

  (** Coq provides various ways to declare functions. Simple functions can be
  declared by using the keyword [[Definition]], which is not only used to declare
  functions but also terms in general.
  *)

  (** To illustrate this, let us first define a simple term of type [[bool]] *)

  Definition the_boolean_true : bool := true.

  (** ... check its type, *)

  Check the_boolean_true. (* As expected it is of type bool. *)

  (** ... and compute its value. *)

  Compute the_boolean_true. (* The computed value is [[true]], what a surprise! *)

  (** Now let us define a function that negates a boolean. *)

  Definition negb (b:bool) : bool :=
  match b with
    | true => false 
    | false => true
  end.

  (** We just defined a term and gave it the name [[negb]]. This term takes one
  parameter [[b]] of type [[bool]] and has itself the type [[bool]].

  What makes this term a function is the fact that it takes a parameter ([[b]] of
  type [[bool]]) and returns a value (of type [[bool]]).

  So what is its type? Think of the answer before checking.
  *)

  Check negb. 

  (** [[negb]] has type [[bool -> bool]] which means that its type is a function
  [[->]] from [[bool]] to [[bool]] (yes functions have types, and their type is
  the function-type).
  *)

  (** Let us consider the body of the function. The statement [[match b with | ...
  | ... end. ]] instructs Coq to match the value stored in the parameter [[b]]
  against the patterns listed after [[with]]. Coq will start at the top of the
  list and match [[b]] with whatever is on the left side of the [[=>]]. If there
  is a match, the function stops and returns whatever is to the right of the [[=>]] and
  stops. Note that the order of the listed patterns matters.

  This construct is called pattern matching and is very common in functional
  programming.
  *)

  (** Let us do a first "real" computation, using the newly declared function-term
  [[negb]]. *)

  Compute negb true. (* evaluates to false *)

  (** We saw that [[negb]] is of type [[bool -> bool]]. Let us see what the type
  of [[negb true]] is. *)

  Check negb true. (* bool *)

  (** We can also check the type of [[negb]] applied to an arbitrary argument
  denoted [[_]] *)

  Check negb _. (* bool *)

  (** Let us declare a multi-argument function [[andb]] that computes the
  conjunction of two booleans.*) 

  Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true  => b2 
    | false => false
  end.

  (** Our definition states that [[andb]] has two parameters [[b1]] and
  [[b2]] of type [[bool]] and has a return value of type [[bool]].

  So [[andb]] is of type [[bool -> bool -> bool]] as we can see below.
  *)

  Check andb. (* bool -> bool -> bool *)

  (** What is the type of [[andb true true]]? *)

  Check andb true true. (* bool *)

  (** Now let us do something bold and call [[andb]] with only one argument. It will
  surely result in a huge error! 😈 *)
  Check andb true. (* bool -> bool *)

  (** 🤯 What, no error? This is a good moment to note that technically, there is no such
  thing as multi-argument functions in Coq. Behind the scenes [[andb]] is a
  function that takes a boolean [[b1]] as an argument and returns another
  function, which takes boolean [[b2]] as an argument. This function then returns
  the final boolean.

  Declaring [[andb]] like we did above is therefore another way of writing:
  *)

  Definition andb_behind_the_scenes (b1: bool) : bool -> bool :=
  fun b2 => match b1 with
    | true => b2
    | false => false
  end.

  (** This translation of multiple argument functions into multiple
  single-argument functions is called currying. It is named after the
  mathematician Haskell Brooks Curry and a common concept in functional
  programming languages.
  *)


  (** **** Exercise: (c_orb) *)
  (** Define a function [[orb]] that computes the disjunction of two
  booleans [[b1]] and [[b2]]. Using pattern matching. *)

  Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true  => true 
    | false => b2
  end.

  (** These commands introduce another way of calling [[andb]] and [[orb]]. *)
  Notation "x && y" := (andb x y). (* [[x && y]] is another way of writing [[andb x y]]. *)
  Notation "x || y" := (orb x y).  (* [[x || y]] is another way of writing [[orb x y]]. *)

  (** Of course we could have also implemented these function with conditionals
  by using an [[if]] [[then]] [[else]]. *)

  Definition negb' (b:bool) : bool :=
  if b then false
  else true.

  Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.

  Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.

  (** Remember that there is no such thing as a canonical [[bool]] type, we defined it ourselves.
  [[If]] works with variables of any type that contains exactly two constructors. 
  *)

  Inductive yinyang : Type :=
  | yin
  | yang.

  Definition transform (y : yinyang) : yinyang :=
  if y then yang else yin.

  Compute transform yin. (* yang *)
  Compute transform yang. (* yin *)

  (** As you can see, it's not black magic. Coq simply checks whether the variable [[y]] evaluates
  to the first constructor. If this is the case, the code after [[then]] is executed. Otherwise,
  the code after [[else]] is executed. *)

  (** Let's see what happens if we try this with a type that has more than two constructors: *)

  Fail Definition is_red_rgb' (c : rgb) : bool := 
  if c then true else false. (* If is only for inductive types with two constructors. *)

  (** Let's fix that using good ol' pattern matching. *)
  Definition is_red_rgb (c : rgb) : bool := 
  match c with
  | red => true
  | green => false
  | blue => false
  end.

  (** Note how is_red_rgb takes as input an argument of type [[rgb]] and returns an argument 
  or type [[bool]]. Yes, this is possible in functional programming just saying. *)

  (** **** Exercise: (c_is_ying) *)
  (** Implement two functions that check whether a yinyang is yin.
  One using [[if]] [[then]] [[else]] and another using [[match]]. *)

  Definition is_ying_if (y : yinyang) : bool :=
  if y then true else false.

  Definition is_ying_match (y : yinyang) : bool :=
  match y with
  | yin => true
  | _ => false
  end.
  
  Compute is_ying_if yin.
  Compute is_ying_match yin.

  (** Let's do some pattern matching on types that use parameters: *)
  Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

  (** The name of the placeholder [[p]] has been chose arbitrarily. If 
  you're too cool to care about parameter names, you might also
  simply write [[_]] instead. *) 

  Definition isred' (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.
  
  (** The [[_]] behaves like a wildcard and matches with anything.*)

  (** Of course this could also be simplified by applying the wildcard
  to the constructors. *)

  Definition isred (c : color) : bool :=
  match c with
  | primary red => true
  | _ => false
  end.

  (** Types that contain only one constructor, with multiple parameters, are
  often used to represent tuples. *)

  (**  They are used to represent types that have a fixed lenght of elements.
  For example a nybble consists of exactly 4 bits.*)

  Inductive bit : Type :=
  | B1
  | B0.

  Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

  Check (bits B1 B0 B1 B0). (* nybble *)

  (** You can access the single elements in a tuple using the function [[fst]] and
  [[snd]] *)

  Definition first_nybble (b : nybble) : bit :=
    match b with
    | (bits b0 _ _ _) => b0
    end.

  (** Note how we use the wildcard (_) to avoid inventing variable names that
  will not be used.*)

  (** The same is done with the following function that tests
  whether all bits in a nybble are set to [[B0]]: *)

  Definition all_zero (b : nybble) : bool :=
    match b with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
    end.

Compute (all_zero (bits B1 B0 B1 B0)). (* false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)). (* true : bool *)

  (** **** Exercise: (c_last_nybble) *)
  (** Implement a function that returns the last bit of a nybble. *)

  Definition last_nybble (b : nybble) : bit :=
  match b with
    | (bits _ _ _ b0) => b0
    end.

   (** **** Exercise: (c_even_nybble) *)
  (** Implement a function that checks whether a nybble represents an even number. *)
  Definition even_nybble (b : nybble) : bool :=
  match b with
  | (bits B0 _ _ _) => true
  | _ => false
  end.

  (** **** Exercise: (c_odd_nybble) *)
  (** Implement a function that checks whether a nybble represents an odd number. *)
  Definition odd_nybble (b : nybble) : bool :=
  negb (even_nybble b).


(** ** TP - Proofs on Enumerated Types and Simple Functions *)

  (** So far we have defined a few datatypes and have given them meaning using
  functions. We did all of this using the functional programming language of Coq.

  Now lets state and prove some statements about them! This is the part were
  we introduce the actual features that make Coq a proof assistant and not "just"
  a functional programming language. 

  Lets take a look at a single statement, you'll notice it reads pretty much like
  a statement in a mathematical text.
  *)    

  Check (forall (b : bool), b = b). (* has type [[Prop]] (still surprised, that
                                      everything has a type?) *)

  (** The [[Prop]] stands for proposition. Which is the term we're going to use
  from now on. To prove a proposition in Coq, we have to embed it into a theorem.
  We do this by using the keywords [[Example]], [[Lemma]] or [[Theorem]] (all are essentially
  the same) followed by its name and a colon. After the colon comes a formal
  proposition which has the type [[Prop]] and which is terminated by a [[.]].

  The actual proof is enclosed between the keywords [[Proof.]] and [[Qed.]]. It
  consists of a sequence of so called proof-tactics (or just tactics).
  *)

  Lemma bool_eq_bool : forall (b : bool), b = b.
  Proof.
    reflexivity.
  Qed.

  (**
  Tactics are built-in commands that manipulate the proof state in legal ways. The
  users job is to guide Coq through the proof by instructing it on which proof
  tactic to use. Coq's job is to make finding and using the right tactic as
  convenient as possible (automation, search features etc.), to update the
  proof-state and finally to check whether the proof holds or not.
  *)

  Lemma false_and_false : forall (b : bool), (andb false b) = false.
  Proof.
    intros b. simpl. reflexivity.
  Qed.

  (** To proof these statements, we use the following tactics:
    - [[intros b]] This tactic takes facts that can be inferred from the proof-term 
      and introduces them as assumptions to the proof state. In this case it introduces
      the assumption that [[b]] is a boolean.  
    - [[simpl]] Simplifies the proof goal as far as it can. It does this by (partially)
      executing the functions in the proof goal.
    - [[reflexivity]] Finishes the proof by observing that both terms on each side of
      the [[=]] are equal.
  *)

  (** The Admitted command can be used as a placeholder for an incomplete proof. We use it in exercises to indicate the parts that we're leaving for you -- i.e., your job is to replace Admitteds with real proofs.
  *)

  (** **** Exercise: (p_andb) *)
  (** Prove the following statements about the behavior of andb. *)
  Example test_andb1: (andb true false) = false.
    Proof. simpl. reflexivity. Qed.
  Example test_andb2: (andb false false) = false.
    Proof. simpl. reflexivity. Qed.
  Example test_andb3: (andb false true) = false.
    Proof. simpl. reflexivity. Qed.
  Example test_andb4: (andb true true) = true.
    Proof. simpl. reflexivity. Qed.

  (** **** Exercise: (p_orb) *)
  (** Check your implementation of the orb function by proving the following statements. *)
  Example test_orb1: (orb true false) = true.
    Proof. simpl. reflexivity. Qed.
  Example test_orb2: (orb false false) = false.
    Proof. simpl. reflexivity. Qed.
  Example test_orb3: (orb false true) = true.
    Proof. (* FILL IN HERE *) Admitted.
  Example test_orb4: (orb true true) = true.
    Proof. simpl. reflexivity. Qed.



  (** **** Exercise: (p_neg_even_nybble_is_odd) *)
  (** Prove the following statement about the behavior of even_nybble and
  odd_nybble. *)
  (** Hint: The reflexivity tactic also does some simplification and works
  on some terms that are not completely simplified by [[simpl]]. *)

  Definition my_nybble := bits B0 B1 B0 B0.
  
  Lemma neg_even_nybble_is_odd: 
    negb (even_nybble my_nybble) = odd_nybble my_nybble.
    Proof. 
      unfold odd_nybble.
      simpl. 
      reflexivity. 
    Qed.