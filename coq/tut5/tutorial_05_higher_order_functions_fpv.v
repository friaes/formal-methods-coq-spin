Require Import Nat.
Require Import Coq.Lists.List.
Import ListNotations.

(** ** FP - Higher-Order Functions - Functions that take functions as arguments *)

  (** https://softwarefoundations.cis.upenn.edu/lf-current/Poly.html#lab134 *)
  
  (** Functions that take functions as arguments are called higher-order functions *)

  (** Let's consider a simple example first. The function doit3times takes three
  arguments. An implicit arbitrary type [[X : Type]], a function [[f]] of type 
  [[X -> X]] and [[n]] of Type [[X]]. The return value is also of type [[X]].

  The function body consists of a call to [[f]] with the argument being the return
  value of another call to [[f]] that takes as argument the return value of a
  final call to [[f]] on [[n]].
 
  [[f]] can be any function that takes an arbitrary type [[X]] as argument and
  returns a value of type [[X]].
  *)

  Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

  (** Observe how [[doit3times]] behaves. *)
  Check doit3times.

  Definition plus1 (n : nat) := S n.

  Compute plus1 1. (* 2 *)
  Compute doit3times plus1 1. (* 4 *)

  (** The function plus1 is so simple. It doesn't even warrant a name don't you agree?
  Coq allows us to write anonymous functions on the fly, using the syntax: [[fun]] 
  followed by function arguments, then [[=>]] followed by the function body. *)

  Check (fun n => S n). (* This function is nameless *)
  Compute (fun n => S n) 1.

  Compute doit3times (fun n => n * n) 2. (* 256 *)

  (** The fixpoint [[filter]] is another example of a higher order function. It takes 
  a type [[X]] a function [[test: X -> bool]] and a [[list X]] as arguments.
  It returns a [[list X]] which contains only those elements of [[l]] that, 
  when applied to [[test]] return [[true]]. *)

  Fixpoint filter {X:Type} (test: X -> bool) (l:list X) : list X :=
    match l with
    | [] => []
    | h :: t => 
      if test h then h :: (filter test t)
      else filter test t
    end.

  Compute filter (even) [2;3;4;5;6;7]. (* [2; 4; 6] *)

  (** [[countoddmembers']] leverages filter to compute the number of odd numbers
  in a [[list nat]]. *)

  Definition countoddmembers' (l:list nat) : nat :=
  length (filter odd l).

  Compute countoddmembers' [1;0;3;1;4;5]. (* 4 *)
  Compute countoddmembers' [0;2;4]. (* 3 *)
  Compute countoddmembers' []. (* 0 *)

  (** **** Exercise: (filter_even_gt_7) *) 
  (** Use filter (instead of Fixpoint) to write a Coq function filter_even_gt7 that
  takes a list of natural numbers as input and returns a list of just those that are
  even _and_ greater than 8. *)

  Definition filter_even_gt7 (l : list nat) : list nat := 
  filter (fun n => 7 <? n) (filter even l).

  Compute filter_even_gt7 [1;2;6;9;10;3;12;8]. (* [10;12;8]*)

  Compute filter_even_gt7 [5;2;6;19;129]. (* [] *)

  (** The Fixpoint [[map]] applies its function-type argument [[f]] to each
  element of a list [[l]] and returns that new list. *)

  (** https://softwarefoundations.cis.upenn.edu/lf-current/Maps.html *)
  
  Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
    match l with
    | [] => []
    | h :: t => (f h) :: (map f t)
    end.

  Compute map (plus 1) [1;2;3]. (* [2; 3; 4] *)

 (** Now that we've seen functions that take functions as arguments. Are there
 functions that return functions? *)

  (** ***** Exercise: (fun_return_fun) *)
  (** Argue wheter it is possible to write a function that returns a function.
  If you think it is possible give an example. *)

  (** 
      It might possible using the syntax [[fun]], but i don't know how to apply it
  *)

  (** Lets' build a new datatype called [[total_map]], that virtually implements
  a key-value store (note [[total_map]] has nothing to do with the [[map]] from
  before).*)

  (** A key-value store is a data structure that associates keys with values.
  For example one could have strings as keys and emojis as values and implement 
  a [[total_map]] called animals which contains the following key-value pairs:

    key -> value
    cat -> 🐱
    dog -> 🐶
    cow -> 🐮
  
  So if we want to retreive the cat emoji we would do something like:
  animals["cat"] or animals.get("cat") and it would return 🐱. The syntax will
  be different in Coq but the idea is the same.
  *)
    
  (** We want to use strings as keys, which is why we import the String module. *)
  Require Import Strings.String.
  (** We also need to open the String module to use its functions. *)
  Open Scope string_scope.

  Check "Hello, world". (* string *)

  (** Now we have all the tools we need to define our key-value store. We will
  define it as a function that takes an arbitrary type [[A]] as an argument 
  and returns a function from [[string]] to [[A]]. *)

  Definition total_map (A : Type) := string -> A.

  (** Note, there are other ways to implement maps in Coq. For example, one
  could leverage lists as shown in Software Foundations chapter Lists.

  https://softwarefoundations.cis.upenn.edu/lf-current/Lists.html#lab114
  *)

  (** Intuitively, a total map over an element type [A] is just a
  function that can be used to look up [string]s, yielding [A]s. *)

  (** Below you'll find an instantiation of our animals map. It takes
  a string and returns a string. The map is total because it returns
  a value for every possible key. *)
  
  Definition animals : total_map string :=
    fun s =>
      match s with
      | "cat" => "🐱"
      | "dog" => "🐶"
      | "cow" => "🐮"
      | _     => "🐾" (* <- default value *)
      end. 

  (** We can now use the map to look up the emoji for a given animal. *)
  Compute animals "cat". (* 🐱 *)
  Compute animals "dog". (* 🐶 *)

  (** Lets go back to the general case and create some abstract functions,
  that work on all maps: *)

  (** The function [t_empty] yields an empty total map, given a default
  element; this map always returns the default element when applied
  to any string. *)

  Definition t_empty {A : Type} (v : A) : total_map A :=
    (fun _ => v).

  Compute t_empty 0 "somekey". (* 0 is the default element *)
  Compute t_empty "🐾" "cow". (* 🐾 is the default element *)


  (** More interesting is the map-updating function, which takes a map [m],
  a key [x], and a value [v] and returns a new map. This new map behaves like
  the old one, except that it returns [v] when applied to [x].
  *)
  Definition t_update {A : Type} (m : total_map A)
                      (x : string) (v : A) :=
    fun x' => if String.eqb x x' then v else m x'.

  Check (t_update (t_empty 0) "somekey" 1). (* string -> nat *)

  (** This definition is a nice example of higher-order programming:
  [t_update] takes a _function_ [m] and yields a new function
  [fun x' => ...] that behaves like the desired map. *)

  (* Here we add one element of type nat to the empty map *)
  Compute (t_update (t_empty 0) "somekey" 1) "somekey". (* 1 *)

  (* Here we add one element of type string to the empty map *)
  Compute           (t_update (t_empty "🐾") "cow" "🐮") "cow". (* 🐮 *)

  (* Here we add two elements of type string to the empty map *)
  Compute (t_update (t_update (t_empty "🐾") "cow" "🐮") "cat" "🐱" ) "cat". (* 🐱 *)

  (** We can build a map taking [string]s to [bool]s, where ["foo"] and ["bar"]
  are mapped to [true] and every other key is mapped to [false], like this: *)

  Definition examplemap :=
    t_update (t_update (t_empty false) "foo" true)
            "bar" false.

  Compute examplemap "foo". (* true *)

  (** Note that [[t_update]], as it is implemented above, generates a function 
  that contains a bunch of interleaving [[if then else]] clauses.
  
  So unfolding our examplemap above would look like this:

  fun somekey =>
    if somekey = "bar" then true else 
      if somekey = "foo" then true else
        t_empty false

  Compare this to our definition of [[animals]] which demonstrates another aproach.
  *) 

  (** Next, let's introduce some notations to facilitate working with maps. *)

  (** First, we use the following notation to represent an empty total
  map with a default value. *)
  Notation "'_' '!->' v" := (t_empty v)
    (at level 100, right associativity).

  Definition example_empty := (_ !-> false). (* false is the default value *)

  (** Next a convenient notation for [[t_update]]. *)
  Notation "x '!->' v ';' m" := (t_update m x v)
                                (at level 100, v at next level, right associativity).

  (** The animal and example maps above can now be defined as follows: *)

  Definition animal' :=
    ("cat" !-> "🐱";
     "dog" !-> "🐶";
     "cow" !-> "🐮";
     _      !-> "🐾"). (* <- default value *)

  Compute animal' "dog". (* 🐶 *)

  Definition examplemap' :=
    ( "bar" !-> true;
      "foo" !-> true;
      _     !-> false
    ).

  (** Lastly, we define _partial maps_ on top of total maps.
  A partial map with elements of type [A] is a total map with type [[option A]]. 
  
  The idea is that if, given a key [[k]] the map does contain a corresponding
  value [[v]], it will return [[Some v]]. Otherwise it returns the default value
  which is set to [[None]].
*)

  Definition partial_map (A : Type) := total_map (option A).

  (** The empty partial map is a total map that always returns [None]. *) 
  Definition empty {A : Type} : partial_map A :=
    t_empty None.

  (** The function [update] takes a partial map [m], a key [x], and a value
  [v] and returns a new partial map. This new map behaves like the old
  one, except that it returns [Some v] when applied to [x]. *)
  Definition update {A : Type} (m : partial_map A)
            (x : string) (v : A) :=
    (x !-> Some v ; m).

  (** We introduce a similar notation for partial maps: *)
  Notation "x '|->' v ';' m" := (update m x v)
    (at level 100, v at next level, right associativity).

  (** We can also hide the last case when it is empty. *)
  Notation "x '|->' v" := (update empty x v)
    (at level 100).

  (** Here the examples we had before can be redefined as partial maps. *)
  Definition animal'' :=
    ("cat" |-> "🐱";
     "dog" |-> "🐶";
     "cow" |-> "🐮").
  
  Compute animal'' "dog". (* Some 🐶 *)
  Compute animal'' "cat". (* Some 🐱 *)

  Definition examplemap'' :=
    ("bar" |-> true;
     "foo" |-> true).

  Compute examplemap'' "foo". (* Some true *)


Require Import Nat.
Require Import PeanoNat.
Require Import Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Close Scope string_scope.

(** ** TP - Proofs on Higher-Order Functions *)

 (** We can now prove some properties of our higher-order functions. *)

  (** The first property about filter is that it returns a list of the same
  length as the original list. *)

  (** **** Exercise: (filter_length) *) (* Prove the lemma below. *)
  
  (** Hint: When dealing with inequalities, it is often useful to use the
  [[Search]] feature to find applicable theorems. *)
  
  Search (S(_) <= S(_)).
  Search (_ <= S(_)).

  Lemma filter_length : forall (X : Type) (test : X -> bool) (l : list X),
    List.length (filter test l) <= List.length l.
  Proof.
    intros. induction l.
      - reflexivity.
      - simpl. destruct (test a).
        + simpl. apply le_n_S, IHl.
        + apply le_S, IHl.
  Qed.

  (** The lemma below showcases a new tactic called [[assert]]. It allows
  us to prove small results within a larger proof. And introduce a new 
  hypothesis into the context. *)

  Lemma even_countoddmembers : forall (n : nat) (l : list nat),
    even n = true ->
    countoddmembers' (n :: l) = countoddmembers' l.
  Proof.
    intros n l E.
    unfold countoddmembers'. simpl.
    (* We have E: even n = true, therefore odd n = false *)
    (* Lets state this as an inline inline proof by using the assert tactic. *)
    assert (H: forall (n : nat), even n = true -> odd n = false).
    (* Now we have two subgoals to prove. The first one is the goal of the assert 
    statement. The second one is the original goal of the lemma. *)
    - intros. unfold odd. unfold negb. rewrite H. reflexivity. (* assert proving H *)
    - apply H in E. rewrite E. simpl. reflexivity. (* continue with lemma using H *)
  Qed.

  (** The lemma below states that if we filter a list of even numbers, the
  result will have no odd numbers. *)

  (** Note how we're applying the lemma [[even_countoddmembers]] to prove this and
  how Coq fails to infer the arguments for [[even_countoddmembers]]. We therefore
  need to provide them explicitly using the [[with]] keyword. *)

  Lemma filter_even : forall (l : list nat),
    countoddmembers' (filter even l) = 0.
  Proof.
    intros.
    induction l as [| h t IH].
    - simpl. reflexivity.
    - simpl. destruct (even h) eqn: E.
      + Fail apply even_countoddmembers in E. (* Unable to find an instance for the variable l *)
        apply even_countoddmembers with h (filter even t) in E. (* Use with to provide the arguments *)
        rewrite E. simpl. rewrite IH. reflexivity.
      + apply IH.
  Qed.

  
  (** Lets apply what we've learned ([[assert]]), [[with]]) and
  prove the lemma below. *)
  
  Search (S(_) = S(_)).

  (** **** Exercise: (filter_odd) *) (* Prove the lemma below. *)
  Lemma filter_odd : forall (l : list nat),
    countoddmembers' (filter odd l) = List.length (filter odd l).
  Proof.
    intros. unfold countoddmembers'. induction l.
      - simpl. reflexivity.
      - simpl. destruct (odd a) eqn:E.
        + simpl. rewrite E. simpl. apply eq_S. apply IHl.
        + apply IHl.
  Qed.

  Open Scope string_scope.

  (** We can now prove some properties about total maps. *)

  (** The first property is that the empty map always returns the default value. *)

  (** **** Exercise: (t_apply_empty) *) (** Prove the lemma below. *)
  Lemma t_apply_empty : forall (A : Type) x  (v : A),
    (_ !-> v) x = v.
  Proof. 
    intros. unfold t_empty. reflexivity.
  Qed.

  (** The second property is that the update function returns the value that was
  used to update the map when applied to the same key. *)
  Search (_ =? _).

  (** **** Exercise: (t_update_eq) *) (** Prove the lemma below. *)
  Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
  Proof.
    intros. unfold t_update. rewrite String.eqb_refl. reflexivity.
  Qed.

  (** The third property is that if we update a map with a different key, the
  value of the map at the original key is unchanged. *)

  (** **** Exercise: (t_update_neq) *) (** Prove the lemma below. *)

  Lemma t_update_neq : forall (A : Type) (m : total_map A) x y v,
    x <> y -> (x !-> v ; m) y = m y.
  Proof.
    intros A m x y v E. unfold t_update.
    destruct (x =? y) eqn: E'.
    - apply String.eqb_eq in E'. unfold "<>" in E. apply E in E'. destruct E'.
    - reflexivity. 
  Qed.

  (** The next few properties require an axiom called
  functional extensionality. This axiom states that if two functions
  are equal on all inputs, then they are equal. It can be used like an inverse
  of the [[f_equal]] tactic. *)
  
  Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

  (** t_update_shadow states that if we update a map with the same key
  twice, the second update is the one that matters. *)

  Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
  Proof.
    intros A m x v1 v2. apply functional_extensionality.
    intros x'. unfold t_update. destruct (String.eqb x x').
    - reflexivity.
    - reflexivity.
  Qed.

  (** Theorem t_update_same states that if we update a map with the same key
  and value, the map is unchanged. *)

  (** **** Exercise: (t_update_same) *) (** Prove the theorem below. *)
  (** The proof has a similar structure to the one of [[t_update_shadow]]. *)

  Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
  Proof.
    intros. apply functional_extensionality. 
    intros. unfold t_update. destruct (String.eqb x x0) eqn:E.
    - apply String.eqb_eq in E. f_equal. apply E.
    - reflexivity.
  Qed.
  (** Theorem t_update_permute states that if we update a map with two different
  keys, the order of the updates does not matter. *)

  (** **** Exercise: (t_update_permute) *) (** Prove the theorem below. *)

  Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                    v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
  Proof.
    intros. unfold "<>" in H. apply eqb_neq in H. apply functional_extensionality.
    intros. unfold t_update. destruct (String.eqb x1 x) eqn:E1.
      - apply String.eqb_eq in E1. 
        rewrite <- E1. rewrite H. reflexivity.
      - destruct (String.eqb x2 x) eqn:E2.
        + reflexivity.
        + reflexivity.
  Qed.      

  (** Now we have proven all the properties we wanted about total maps. We want
  to do the same for partial maps. *)

  (** ***** Exercise: (update_empty) *) (** Prove the lemma below. *)
  (** Hint: Use the lemma [[t_update_empty]] to prove this one. *)
  

  Lemma apply_empty : forall (A : Type) (x : string),
    @empty A x = None.
  Proof.
   intros. unfold empty. apply t_apply_empty. 
  Qed.

  (** The proofs of the lemmas below all have the same structure *)

 Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
    (x |-> v ; m) x = Some v.
  Proof.
    intros. unfold update. rewrite t_update_eq.
    reflexivity.
  Qed.

  Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1 ->
    (x2 |-> v ; m) x1 = m x1.
  Proof.
    intros A m x1 x2 v H.
    unfold update. rewrite t_update_neq.
    - reflexivity.
    - apply H.
  Qed.

  Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
  Proof.
    intros A m x v1 v2. unfold update. rewrite t_update_shadow.
    reflexivity.
  Qed.

  Theorem update_same : forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
  Proof.
    intros A m x v H. unfold update. rewrite <- H.
    apply t_update_same.
  Qed.

  Theorem update_permute : forall (A : Type) (m : partial_map A)
                                  x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
  Proof.
    intros A m x1 x2 v1 v2. unfold update.
    apply t_update_permute.
  Qed.

  (** This concludes our tutorial on higher-order functions. *)