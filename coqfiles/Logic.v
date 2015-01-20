(** * Logic: Logic in Coq *)

Require Export MoreProp. 


(** Coq's built-in logic is very small: the only primitives are
    [Inductive] definitions, universal quantification ([forall]), and
    implication ([->]), while all the other familiar logical
    connectives -- conjunction, disjunction, negation, existential
    quantification, even equality -- can be encoded using just these.

    This chapter explains the encodings and shows how the tactics
    we've seen can be used to carry out standard forms of logical
    reasoning involving these connectives. *)

(* ########################################################### *)
(** * Conjunction *)

(** The logical conjunction of propositions [P] and [Q] can be
    represented using an [Inductive] definition with one
    constructor. *)

Inductive and (P Q : Prop) : Prop := conj : P -> Q -> (and P Q). 

(** Note that, like the definition of [ev] in a previous
    chapter, this definition is parameterized; however, in this case,
    the parameters are themselves propositions, rather than numbers. *)

(** The intuition behind this definition is simple: to
    construct evidence for [and P Q], we must provide evidence
    for [P] and evidence for [Q].  More precisely:

    - [conj p q] can be taken as evidence for [and P Q] if [p]
      is evidence for [P] and [q] is evidence for [Q]; and

    - this is the _only_ way to give evidence for [and P Q] --
      that is, if someone gives us evidence for [and P Q], we
      know it must have the form [conj p q], where [p] is
      evidence for [P] and [q] is evidence for [Q]. 

   Since we'll be using conjunction a lot, let's introduce a more
   familiar-looking infix notation for it. *)

Notation "P /\ Q" := (and P Q) : type_scope.

(** (The [type_scope] annotation tells Coq that this notation
    will be appearing in propositions, not values.) *)

(** Consider the "type" of the constructor [conj]: *)

Check conj.
(* ===>  forall P Q : Prop, P -> Q -> P /\ Q *)

(** Notice that it takes 4 inputs -- namely the propositions [P]
    and [Q] and evidence for [P] and [Q] -- and returns as output the
    evidence of [P /\ Q]. *)

(** Besides the elegance of building everything up from a tiny
    foundation, what's nice about defining conjunction this way is
    that we can prove statements involving conjunction using the
    tactics that we already know.  For example, if the goal statement
    is a conjuction, we can prove it by applying the single
    constructor [conj], which (as can be seen from the type of [conj])
    solves the current goal and leaves the two parts of the
    conjunction as subgoals to be proved separately. *)

Theorem and_example : 
  (beautiful 0) /\ (beautiful 3).
Proof.
  apply conj.
  Case "left". apply b_0.
  Case "right". apply b_3.  Qed.

(** Just for convenience, we can use the tactic [split] as a shorthand for
    [apply conj]. *)

Theorem and_example' : 
  (ev 0) /\ (ev 4).
Proof.
  split.
    Case "left". apply ev_0.
    Case "right". apply ev_SS. apply ev_SS. apply ev_0.  Qed.

(** Conversely, the [inversion] tactic can be used to take a
    conjunction hypothesis in the context, calculate what evidence
    must have been used to build it, and add variables representing
    this evidence to the proof context. *)

Theorem proj1 : forall P Q : Prop, 
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ]. 
  apply HP.  Qed.

(** **** Exercise: 1 star, optional (proj2) *)
Theorem proj2 : forall P Q : Prop, 
  P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ]. 
  apply HQ.  Qed.
(** [] *)

Theorem and_commut : forall P Q : Prop, 
  P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [HP HQ]. 
  split.  
    Case "left". apply HQ. 
    Case "right". apply HP.  Qed.
  

(** **** Exercise: 2 stars (and_assoc) *)
(** In the following proof, notice how the _nested pattern_ in the
    [inversion] breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP: P], [HQ : Q], and [HR : R].  Finish the proof from there: *)

Definition assoc {A: Type} (binop: A -> A -> A): Prop :=
  forall a b c: A, binop a (binop b c) = binop (binop a b) c.

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split. split. apply HP. apply HQ. apply HR.
Qed.
(** [] *)

(** **** Exercise: 2 stars (even__ev) *)
(** Now we can prove the other direction of the equivalence of [even]
   and [ev], which we left hanging in chapter [Prop].  Notice that the
   left-hand conjunct here is the statement we are actually interested
   in; the right-hand conjunct is needed in order to make the
   induction hypothesis strong enough that we can carry out the
   reasoning in the inductive step.  (To see why this is needed, try
   proving the left conjunct by itself and observe where things get
   stuck.) *)

Theorem even__ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  (* Hint: Use induction on [n]. *)
  (* FILL IN HERE *) Admitted.
(** [] *)



(* ###################################################### *)
(** ** Iff *)

(** The handy "if and only if" connective is just the conjunction of
    two implications. *)

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) 
                      (at level 95, no associativity) 
                      : type_scope.

Theorem iff_implies : forall P Q : Prop, 
  (P <-> Q) -> P -> Q.
Proof.  
  intros P Q H. 
  inversion H as [HAB HBA]. apply HAB.  Qed.

Theorem iff_sym : forall P Q : Prop, (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H. 
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB.  Qed.

(** **** Exercise: 1 star, optional (iff_properties) *)
(** Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof. intros. unfold iff. split. tauto. tauto. Qed.


Theorem iff_trans : transitive iff. 
Proof.
  unfold transitive.
  intros. inversion H. inversion H0.
  split. intros. apply H3. apply H1. apply H5.
  intros. apply H2. apply H4. apply H5.
Qed.


(** Hint: If you have an iff hypothesis in the context, you can use
    [inversion] to break it into two separate implications.  (Think
    about why this works.) *)
(** [] *)



(** Some of Coq's tactics treat [iff] statements specially, thus
    avoiding the need for some low-level manipulation when reasoning
    with them.  In particular, [rewrite] can be used with [iff]
    statements, not just equalities. *)

(* ############################################################ *)
(** * Disjunction *)

(** Disjunction ("logical or") can also be defined as an
    inductive proposition. *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q. 

Notation "P \/ Q" := (or P Q) : type_scope.

(** Consider the "type" of the constructor [or_introl]: *)

Check or_introl.
(* ===>  forall P Q : Prop, P -> P \/ Q *)

(** It takes 3 inputs, namely the propositions [P], [Q] and
    evidence of [P], and returns, as output, the evidence of [P \/ Q].
    Next, look at the type of [or_intror]: *)

Check or_intror.
(* ===>  forall P Q : Prop, Q -> P \/ Q *)

(** It is like [or_introl] but it requires evidence of [Q]
    instead of evidence of [P]. *)

(** Intuitively, there are two ways of giving evidence for [P \/ Q]:

    - give evidence for [P] (and say that it is [P] you are giving
      evidence for -- this is the function of the [or_introl]
      constructor), or

    - give evidence for [Q], tagged with the [or_intror]
      constructor. *)

(** Since [P \/ Q] has two constructors, doing [inversion] on a
    hypothesis of type [P \/ Q] yields two subgoals. *)

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ.  Qed.

(** From here on, we'll use the shorthand tactics [left] and [right]
    in place of [apply or_introl] and [apply or_intror]. *)

Theorem or_commut' : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". right. apply HP.
    Case "right". left. apply HQ.  Qed.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof. 
  intros P Q R. intros H. inversion H as [HP | [HQ HR]]. 
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR.  Qed.

(** **** Exercise: 2 stars (or_distributes_over_and_2) *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros. inversion H. inversion H0. left. apply H2.
  inversion H1. left. apply H3. right. split. apply H2. apply H3.
Qed.
(** [] *)

(** **** Exercise: 1 star, optional (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros. split. 
  apply or_distributes_over_and_1. apply or_distributes_over_and_2.
Qed.
(** [] *)

(* ################################################### *)
(** ** Relating [/\] and [\/] with [andb] and [orb] (advanced) *)

(** We've already seen several places where analogous structures
    can be found in Coq's computational ([Type]) and logical ([Prop])
    worlds.  Here is one more: the boolean operators [andb] and [orb]
    are clearly analogs of the logical connectives [/\] and [\/].
    This analogy can be made more precise by the following theorems,
    which show how to translate knowledge about [andb] and [orb]'s
    behaviors on certain inputs into propositional facts about those
    inputs. *)

Theorem andb_prop : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H.  Qed.

Theorem andb_true_intro : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

(** **** Exercise: 2 stars, optional (bool_prop) *)
Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof. 
  intros. destruct b. simpl in H. right. apply H.
  left. reflexivity. Qed.

Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros. destruct b. left. reflexivity. simpl in H. right. apply H.
Qed.

Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
  intros. split. destruct b. inversion H. reflexivity.
  destruct b. simpl in H. inversion H. simpl in H. apply H.
Qed.
(** [] *)



(* ################################################### *)
(** * Falsehood *)

(** Logical falsehood can be represented in Coq as an inductively
    defined proposition with no constructors. *)

Inductive False : Prop := . 

(** Intuition: [False] is a proposition for which there is no way
    to give evidence. *)


(** Since [False] has no constructors, inverting an assumption
    of type [False] always yields zero subgoals, allowing us to
    immediately prove any goal. *)

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof. 
  intros contra.
  inversion contra.  Qed. 

(** How does this work? The [inversion] tactic breaks [contra] into
    each of its possible cases, and yields a subgoal for each case.
    As [contra] is evidence for [False], it has _no_ possible cases,
    hence, there are no possible subgoals and the proof is done. *)

(** Conversely, the only way to prove [False] is if there is already
    something nonsensical or contradictory in the context: *)

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.  Qed.

(** Actually, since the proof of [False_implies_nonsense]
    doesn't actually have anything to do with the specific nonsensical
    thing being proved; it can easily be generalized to work for an
    arbitrary [P]: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  inversion contra.  Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from
    falsehood follows whatever you please."  This theorem is also
    known as the _principle of explosion_. *)


(* #################################################### *)
(** ** Truth *)

(** Since we have defined falsehood in Coq, one might wonder whether
    it is possible to define truth in the same way.  We can. *)

(** **** Exercise: 2 stars, advanced (True) *)
(** Define [True] as another inductively defined proposition.  (The
    intution is that [True] should be a proposition for which it is
    trivial to give evidence.) *)

Inductive True : Prop := i_am_true.
(** [] *)

(** However, unlike [False], which we'll use extensively, [True] is
    used fairly rarely. By itself, it is trivial (and therefore
    uninteresting) to prove as a goal, and it carries no useful
    information as a hypothesis. But it can be useful when defining
    complex [Prop]s using conditionals, or as a parameter to 
    higher-order [Prop]s. *)

(* #################################################### *)
(** * Negation *)

(** The logical complement of a proposition [P] is written [not
    P] or, for shorthand, [~P]: *)

Definition not (P:Prop) := P -> False.

(** The intuition is that, if [P] is not true, then anything at
    all (even [False]) follows from assuming [P]. *)

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

(** It takes a little practice to get used to working with
    negation in Coq.  Even though you can see perfectly well why
    something is true, it can be a little hard at first to get things
    into the right configuration so that Coq can see it!  Here are
    proofs of a few familiar facts about negation to get you warmed
    up. *)

Theorem not_False : 
  ~ False.
Proof.
  unfold not. intros H. inversion H.  Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof. 
  (* WORKED IN CLASS *)
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA. 
  apply HNA in HP. inversion HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** Exercise: 2 stars, advanced (double_neg_inf) *)
(** Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_:
(* FILL IN HERE *)
   []
*)

(** **** Exercise: 2 stars (contrapositive) *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros. unfold not. unfold not in H0. intros. apply H in H1.
  apply H0 in H1. apply H1.
Qed.
(** [] *)

(** **** Exercise: 1 star (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros. unfold not. intros. inversion H. apply H1 in H0. apply H0.
Qed.
(** [] *)

(** **** Exercise: 1 star, advanced (informal_not_PNP) *)
(** Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(* FILL IN HERE *)
(** [] *)

Theorem five_not_even :  
  ~ ev 5.
Proof. 
  (* WORKED IN CLASS *)
  unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn]. 
  inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1.  Qed.

(** **** Exercise: 1 star (ev_not_ev_S) *)
(** Theorem [five_not_even] confirms the unsurprising fact that five
    is not an even number.  Prove this more interesting fact: *)

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof. 
  unfold not. intros n H. induction H. 
  intros. inversion H. intros. inversion H0.
  apply IHev in H2. apply H2.
Qed.
(** [] *)

(** Note that some theorems that are true in classical logic are _not_
    provable in Coq's (constructive) logic.  E.g., let's look at how
    this proof gets stuck... *)

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not in H. 
  (* But now what? There is no way to "invent" evidence for [~P] 
     from evidence for [P]. *) 
  Abort.

(** **** Exercise: 5 stars, advanced, optional (classical_axioms) *)
(** For those who like a challenge, here is an exercise
    taken from the Coq'Art book (p. 123).  The following five
    statements are often considered as characterizations of
    classical logic (as opposed to constructive logic, which is
    what is "built in" to Coq).  We can't prove them in Coq, but
    we can consistently add any one of them as an unproven axiom
    if we wish to work in classical logic.  Prove that these five
    propositions are equivalent. *)

Definition peirce := forall P Q: Prop, ((P->Q)->P)->P.
Definition classic := forall P:Prop, ~~P -> P.
Definition excluded_middle := forall P:Prop, P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, ~(~P /\ ~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, (P->Q) -> (~P\/Q). 

(* FILL IN HERE *)
(** [] *)

(* ########################################################## *)
(** ** Inequality *)

(** Saying [x <> y] is just the same as saying [~(x = y)]. *)

Notation "x <> y" := (~ (x = y)) : type_scope.

(** Since inequality involves a negation, it again requires
    a little practice to be able to work with it fluently.  Here
    is one very useful trick.  If you are trying to prove a goal
    that is nonsensical (e.g., the goal state is [false = true]),
    apply the lemma [ex_falso_quodlibet] to change the goal to
    [False].  This makes it easier to use assumptions of the form
    [~P] that are available in the context -- in particular,
    assumptions of the form [x<>y]. *)

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.  
    apply ex_falso_quodlibet.
    apply H. reflexivity.   Qed.

Lemma succ_neq : forall n m, n <> m -> S n <> S m.
Proof. 
  intros n.
  induction n. intros. destruct m.
  unfold not in H. apply ex_falso_quodlibet. apply H. reflexivity.
  unfold not. intros. inversion H0.
  intros. destruct m. unfold not. intros. inversion H0.
  unfold not. intros. inversion H0. unfold not in H.
  apply H. rewrite H2. reflexivity.
Qed.

(** **** Exercise: 2 stars (false_beq_nat) *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof. 
  intros n m neq. generalize dependent m. induction n. 
  Case "n = 0". induction m. 
    SCase "m = 0".
      unfold not. intros. apply ex_falso_quodlibet. apply neq. reflexivity.
    SCase "m = S m".
     intros. simpl. reflexivity.
  Case "n = S n". destruct m. 
    SCase "m = 0".
      simpl. intros. reflexivity.
    SCase "m = S m".
      simpl. intros. apply IHn. unfold not. intros. rewrite -> H in neq.
      unfold not in neq. apply neq. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (beq_nat_false) *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  intros n m neq. generalize dependent m.
  induction n.
  Case "n = 0". destruct m.
    SCase "m = 0". simpl. intros. inversion neq.
    SCase "m = S m". simpl. unfold not. intros. inversion H.
  Case "n = S n". destruct m.
    SCase "m = 0". simpl. unfold not. intros. inversion H.
    SCase "m = S m". 
      simpl. unfold not. intros. apply IHn in neq. inversion H. contradiction.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (ble_nat_false) *)
Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  intros n m ble. generalize dependent m.
  induction n. destruct m. simpl. intros. inversion ble.
  simpl. intros. inversion ble.
  destruct m. simpl. intros. unfold not. intros. inversion H.
  simpl. intros. apply IHn in ble.
  unfold not. intros contra. inversion contra. unfold not in ble.
  rewrite H0 in ble. apply ble. apply le_n. unfold not in ble.
  apply ble. apply Sn_le_Sm__n_le_m. apply contra.
Qed.  
(** [] *)

Lemma beq_nat_true_eq: forall n m, n = m -> beq_nat n m = true.
Proof.
  intros n. induction n. 
  intros. rewrite <- H. reflexivity.
  intros. rewrite -> H. rewrite <- beq_nat_refl. reflexivity.
Qed.

Definition boolfunc_prop_equiv {A B: Type} 
  (boolfunc: A -> B -> bool) (prop: A -> B -> Prop) :=
  forall (x: A) (y: B), (boolfunc x y = true -> prop x y) /\
                 (boolfunc x y = false -> ~(prop x y)) /\ 
                 (prop x y -> boolfunc x y = true) /\
                 (~(prop x y) -> boolfunc x y = false).

Check eq.

Lemma beq_nat_works : boolfunc_prop_equiv beq_nat eq.
Proof.
  unfold boolfunc_prop_equiv. intros.
  split. apply beq_nat_true. split. apply beq_nat_false.
  split. apply beq_nat_true_eq. apply false_beq_nat.
Qed.

(* ############################################################ *)
(** * Existential Quantification *)

(** Another critical logical connective is _existential
    quantification_.  We can express it with the following
    definition: *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(** That is, [ex] is a family of propositions indexed by a type [X]
    and a property [P] over [X].  In order to give evidence for the
    assertion "there exists an [x] for which the property [P] holds"
    we must actually name a _witness_ -- a specific value [x] -- and
    then give evidence for [P x], i.e., evidence that [x] has the
    property [P]. 

*)


(** Coq's [Notation] facility can be used to introduce more
    familiar notation for writing existentially quantified
    propositions, exactly parallel to the built-in syntax for
    universally quantified propositions.  Instead of writing [ex nat
    ev] to express the proposition that there exists some number that
    is even, for example, we can write [exists x:nat, ev x].  (It is
    not necessary to understand exactly how the [Notation] definition
    works.) *)

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(** We can use the usual set of tactics for
    manipulating existentials.  For example, to prove an
    existential, we can [apply] the constructor [ex_intro].  Since the
    premise of [ex_intro] involves a variable ([witness]) that does
    not appear in its conclusion, we need to explicitly give its value
    when we use [apply]. *)

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.

(** Note that we have to explicitly give the witness. *)

(** Or, instead of writing [apply ex_intro with (witness:=e)] all the
    time, we can use the convenient shorthand [exists e], which means
    the same thing. *)

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2. 
  reflexivity.  Qed.

(** Conversely, if we have an existential hypothesis in the
    context, we can eliminate it with [inversion].  Note the use
    of the [as...] pattern to name the variable that Coq
    introduces to name the witness value and get evidence that
    the hypothesis holds for the witness.  (If we don't
    explicitly choose one, Coq will just call it [witness], which
    makes proofs confusing.) *)
  
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm]. 
  exists (2 + m).
  apply Hm.  Qed. 

(** **** Exercise: 1 star, optional (english_exists) *)
(** In English, what does the proposition 
      ex nat (fun n => beautiful (S n))
]] 
    mean? *)

(* We have a proposition on numbers that states "the successor of this number is 
   beautiful". So the proposition states, "there exists a natural number whose
   successor is beautiful." In fact, let's prove this silly thing. *)

Theorem exists_beautiful_succ: exists n, beautiful (S n).
Proof. exists 2. apply b_3. Qed.

(** **** Exercise: 1 star (dist_not_exists) *)
(** Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros. unfold not. intros. inversion H0. apply H1. apply H.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (not_exists_dist) *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros.
  unfold excluded_middle in H.   
  unfold not in H. unfold not in H0.
  destruct H with (P:=P x). apply H1. apply ex_falso_quodlibet.
  apply H0. exists x. apply H1.
Qed.
(** [] *)

(** **** Exercise: 2 stars (dist_exists_or) *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros. split.
  Case "->".
    intros. inversion H. inversion H0.
    left. exists witness. apply H1.
    right. exists witness. apply H1.
  Case "->".
    intros. inversion H. inversion H0.
    exists witness. left. apply H1.
    inversion H0. exists witness. right. apply H1.
Qed.
(** [] *)

(* ###################################################### *)
(** * Equality *)

(** Even Coq's equality relation is not built in.  It has (roughly)
    the following inductive definition. *)

(* (We enclose the definition in a module to avoid confusion with the
    standard library equality, which we have used extensively
    already.) *)

Module MyEquality.

Inductive eq {X:Type} : X -> X -> Prop :=
  refl_equal : forall x, eq x x.
(** Standard infix notation: *)

Notation "x = y" := (eq x y) 
                    (at level 70, no associativity) 
                    : type_scope.

(** The definition of [=] is a bit subtle.  The way to think about it
    is that, given a set [X], it defines a _family_ of propositions
    "[x] is equal to [y]," indexed by pairs of values ([x] and [y])
    from [X].  There is just one way of constructing evidence for
    members of this family: applying the constructor [refl_equal] to a
    type [X] and a value [x : X] yields evidence that [x] is equal to
    [x]. *)


(** **** Exercise: 2 stars (leibniz_equality) *)
(** The inductive definitions of equality corresponds to _Leibniz equality_: 
   what we mean when we say "[x] and [y] are equal" is that every 
   property on [P] that is true of [x] is also true of [y].  *)

Lemma leibniz_equality : forall (X : Type) (x y: X), 
  x = y -> forall P : X -> Prop, P x -> P y.
Proof.
  intros. inversion H. rewrite <- H2. apply H0.
Qed.
(** [] *)

(** We can use
    [refl_equal] to construct evidence that, for example, [2 = 2].
    Can we also use it to construct evidence that [1 + 1 = 2]?  Yes:
    indeed, it is the very same piece of evidence!  The reason is that
    Coq treats as "the same" any two terms that are _convertible_
    according to a simple set of computation rules.  These rules,
    which are similar to those used by [Eval compute], include
    evaluation of function application, inlining of definitions, and
    simplification of [match]es.
*)

Lemma four: 2 + 2 = 1 + 3. 
Proof.
  apply refl_equal. 
Qed.

(** The [reflexivity] tactic that we have used to prove equalities up
to now is essentially just short-hand for [apply refl_equal]. *)

End MyEquality.


(* ###################################################### *)
(** * Evidence-carrying booleans. *)

(** So far we've seen two different forms of equality predicates:
[eq], which produces a [Prop], and
the type-specific forms, like [beq_nat], that produce [boolean]
values.  The former are more convenient to reason about, but
we've relied on the latter to let us use equality tests 
in _computations_.  While it is straightforward to write lemmas
(e.g. [beq_nat_true] and [beq_nat_false]) that connect the two forms,
using these lemmas quickly gets tedious. 

It turns out that we can get the benefits of both forms at once 
by using a construct called [sumbool]. *)

Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B 
 | right : B -> sumbool A B.

Notation "{ A } + { B }" :=  (sumbool A B) : type_scope.

(** Think of [sumbool] as being like the [boolean] type, but instead
of its values being just [true] and [false], they carry _evidence_
of truth or falsity. This means that when we [destruct] them, we
are left with the relevant evidence as a hypothesis -- just as with [or].
(In fact, the definition of [sumbool] is almost the same as for [or].
The only difference is that values of [sumbool] are declared to be in
[Set] rather than in [Prop]; this is a technical distinction 
that allows us to compute with them.) *) 

(** Here's how we can define a [sumbool] for equality on [nat]s *)

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      left. reflexivity.
    SCase "m = S m'".
      right. intros contra. inversion contra.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      right. intros contra. inversion contra.
    SCase "m = S m'". 
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal.  apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined. 

(** Read as a theorem, this says that equality on [nat]s is decidable:
that is, given two [nat] values, we can always produce either 
evidence that they are equal or evidence that they are not.
Read computationally, [eq_nat_dec] takes two [nat] values and returns
a [sumbool] constructed with [left] if they are equal and [right] 
if they are not; this result can be tested with a [match] or, better,
with an [if-then-else], just like a regular [boolean]. 
(Notice that we ended this proof with [Defined] rather than [Qed]. 
The only difference this makes is that the proof becomes _transparent_,
meaning that its definition is available when Coq tries to do reductions,
which is important for the computational interpretation.)

Here's a simple example illustrating the advantages of the [sumbool] form. *)

Definition override' {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X:Type) x1 k1 (f : nat->X),
  f k1 = x1 ->
  forall k2, (override' f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 f. intros Hx1 k2.
  unfold override'.
  destruct (eq_nat_dec k1 k2).   (* observe what appears as a hypothesis *)
  Case "k1 = k2".
    rewrite <- e.
    symmetry. apply Hx1.
  Case "k1 <> k2". 
    reflexivity.  Qed.

(** Compare this to the more laborious proof (in MoreCoq.v) for the 
   version of [override] defined using [beq_nat], where we had to
   use the auxiliary lemma [beq_nat_true] to convert a fact about booleans
   to a Prop. *)


(** **** Exercise: 1 star (override_shadow') *)
Theorem override_shadow' : forall (T:Type) out1 out2 in1 in2 (func : nat->T),
  (override' (override' func in1 out2) in1 out1) in2 = 
  (override' func in1 out1) in2.
Proof.
  intros. unfold override'. 
  destruct (eq_nat_dec in1 in2). reflexivity. reflexivity.
Qed.
(** [] *)

(* ####################################################### *)
(** ** Inversion, Again (Advanced) *)

(** We've seen [inversion] used with both equality hypotheses and
    hypotheses about inductively defined propositions.  Now that we've
    seen that these are actually the same thing, we're in a position
    to take a closer look at how [inversion] behaves...

    In general, the [inversion] tactic

    - takes a hypothesis [H] whose type [P] is inductively defined,
      and

    - for each constructor [C] in [P]'s definition,

      - generates a new subgoal in which we assume [H] was
        built with [C],

      - adds the arguments (premises) of [C] to the context of
        the subgoal as extra hypotheses,

      - matches the conclusion (result type) of [C] against the
        current goal and calculates a set of equalities that must
        hold in order for [C] to be applicable,
        
      - adds these equalities to the context (and, for convenience,
        rewrites them in the goal), and

      - if the equalities are not satisfiable (e.g., they involve
        things like [S n = O]), immediately solves the subgoal. *)

(** _Example_: If we invert a hypothesis built with [or], there are two
   constructors, so two subgoals get generated.  The
   conclusion (result type) of the constructor ([P \/ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.

   _Example_: If we invert a hypothesis built with [and], there is
   only one constructor, so only one subgoal gets generated.  Again,
   the conclusion (result type) of the constructor ([P /\ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.  The
   constructor does have two arguments, though, and these can be seen
   in the context in the subgoal.

   _Example_: If we invert a hypothesis built with [eq], there is
   again only one constructor, so only one subgoal gets generated.
   Now, though, the form of the [refl_equal] constructor does give us
   some extra information: it tells us that the two arguments to [eq]
   must be the same!  The [inversion] tactic adds this fact to the
   context.  *)


(** **** Exercise: 1 star, optional (dist_and_or_eq_implies_and) *)  
Lemma dist_and_or_eq_implies_and : forall P Q R,
       P /\ (Q \/ R) /\ Q = R -> P/\Q.
Proof.
  intros. inversion H. inversion H1. 
  destruct H2. split. apply H0. apply H2. rewrite -> H3.
  split. apply H0. apply H2.
Qed.

(** [] *)




(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (all_forallb) *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
  | all_nil  : all P []
  | all_cons : forall l x, P x -> all P l -> all P (x::l).

Remark all_even_stupid: all ev [2; 4; 10].
Proof.
  apply all_cons. apply ev_SS. apply ev_0.
  apply all_cons. apply ev_SS. apply ev_SS. apply ev_0.
  apply all_cons. apply ev_SS. apply ev_SS. apply ev_SS. apply ev_SS. apply ev_SS. apply ev_0.
  apply all_nil.
Qed.

(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

Theorem forallb_works: forall T l test,
  forallb (X:=T) test l = true -> all (fun x => test x = true) l.
Proof.
  intros. induction l.
  apply all_nil.
  simpl in H. apply all_cons.
  apply andb_true_elim1 in H. apply H.
  apply andb_true_elim2 in H. apply IHl. apply H.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge) *)
(** One of the main purposes of Coq is to prove that programs match
    their specifications.  To this end, let's prove that our
    definition of [filter] matches a specification.  Here is the
    specification, written out informally in English.

    Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example, 
    [1,4,6,2,3]
    is an in-order merge of
    [1,6,2]
    and
    [4,3].
    Your job is to translate this specification into a Coq theorem and
    prove it.  (Hint: You'll need to begin by defining what it means
    for one list to be a merge of two others.  Do this with an
    inductive relation, not a [Fixpoint].)  *)

Inductive inorder_merge {T: Type}: list T -> list T -> list T -> Prop :=
  | iom_nil_l: forall l, inorder_merge l [] l
  | iom_nil_r: forall l, inorder_merge [] l l
  | iom_cons: forall x y l1 l2 l, inorder_merge l1 l2 l -> 
                                  inorder_merge (x::l1) (y::l2) (x::y::l).

Example iom_1: inorder_merge [1;6;3] [4;2] [1;4;6;2;3].
Proof. apply iom_cons. apply iom_cons. apply iom_nil_l. Qed.

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2) *)
(** A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, advanced (no_repeats) *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros. 
  induction xs. 
    Case "xs empty". right. apply H.
    Case "xs nonempty".
      inversion H.
      SCase "ai_here: x is at the head of xs++ys".
        left. apply ai_here.
      SCase "ai_later: x is in the tail of xs++ys".
        apply IHxs in H1. inversion H1.
        SSCase "x appears in xs". left. apply ai_later. apply H3.
        SSCase "x appears in ys". right. apply H3.
Qed.

Lemma nil_app: forall (X: Type) (l: list X), l ++ [] = l.
Proof. intros. induction l. reflexivity. simpl. rewrite IHl. reflexivity. Qed.

Lemma nothing_in_empty: forall (X: Type) (x: X), ~(appears_in x []).
Proof. unfold not. intros. inversion H. Qed.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros. induction xs.
  Case "x is empty". destruct ys.
    SCase "ys is empty". inversion H. simpl. apply H0. rewrite -> nil_app. apply H0.
    SCase "ys is nonempty". simpl. inversion H. 
      apply ex_falso_quodlibet. apply nothing_in_empty in H0. apply H0.
      apply H0.
  Case "x is nonempty". inversion H.
    SCase "x is in x0::xs". simpl. inversion H0.
      SSCase "x is head of xs". apply ai_here.
      SSCase "x is in tail of xs". apply ai_later. apply IHxs. left. apply H2.
    SCase "x is in ys". 
      simpl. apply ai_later. apply IHxs. right. apply H0.
Qed.

(** Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)

Definition disjoint {T: Type} (l1 l2: list T): Prop :=
  forall x:T, appears_in x l1 -> ~(appears_in x l2).

Theorem disjoint_sym: forall T, symmetric (disjoint (T:=T)). 
Proof.
  unfold symmetric. unfold disjoint. unfold not.
  intros T l1 l2 H. intros x contains contra.
  apply H in contra. apply contra. apply contains.
Qed.
  
(** Next, use [appears_in] to define an inductive proposition
    [no_repeats X l], which should be provable exactly when [l] is a
    list (with elements of type [X]) where every member is different
    from every other.  For example, [no_repeats nat [1,2,3,4]] and
    [no_repeats bool []] should be provable, while [no_repeats nat
    [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)

Inductive no_repeats {T:Type}: list T -> Prop :=
  | no_repeats_nil: no_repeats []
  | no_repeats_cons: forall x l, ~(appears_in x l) -> no_repeats (x::l).

Example not_norepeats_11: ~(no_repeats [1;1]).
Proof. unfold not. intros. inversion H. apply H1. apply ai_here. Qed.

Inductive monotonic_increase: list nat -> Prop :=
  | incr_nil: monotonic_increase []
  | incr_cons: forall l n, 
      monotonic_increase l -> all (fun m => n <= m) l -> monotonic_increase (n::l).

Definition has_upper_bound (n: nat) (l: list nat): Prop := all (fun m => m <= n) l.
Definition has_lower_bound (n: nat) (l: list nat): Prop := all (fun m => n <= m) l.

Theorem all_applies: forall (T:Type) (elem:T) (l:list T) (P: T -> Prop), 
  appears_in elem l -> all P l -> P elem.
Proof. intros. induction H.
  inversion H0. apply H2.
  inversion H0. apply IHappears_in. apply H4.
Qed.

Theorem all_implication: forall (T: Type) (l: list T) (P1 P2: T -> Prop),
  (forall x, P1 x -> P2 x) -> all P1 l -> all P2 l.
Proof.
  (* Note to self: There's some connection here to category theory... *)
  intros. induction l.
  apply all_nil.
  apply all_cons. inversion H0.
  apply H in H3. apply H3.
  inversion H0. apply IHl. apply H4.
Qed.

Theorem monotonic_is_bounded:
  forall lowest l,
  monotonic_increase (lowest::l) -> has_lower_bound lowest l.
Proof.
  intros.
  inversion H.
  unfold has_lower_bound. apply H3.
Qed.

Inductive strict_increase: list nat -> Prop :=
  | si_nil: strict_increase []
  | si_cons: forall n l, 
      strict_increase l -> all (fun m => n < m) l -> strict_increase (n::l).

Lemma lt_impl_le: forall n m, n < m -> n <= m.
Proof.
  intros. unfold lt in H. apply Sn_le_m_n_le_m in H. apply H.
Qed.

Theorem strict_increase_implies_monotonic_increase: forall l,
  strict_increase l -> monotonic_increase l.
Proof.
  intros.
  induction H. apply incr_nil.
  (* Here we need to show that any n is <= any element of l. *)
  assert (n_le: all (fun x => n <= x) l).
    destruct l. apply all_nil.
    apply all_cons. inversion H0.
    apply lt_impl_le. apply H3.
Admitted.

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [no_repeats] and [++] (list append).  *)

Lemma lt_trans: forall a b c, a < b -> b < c -> a < c.
Proof.
  unfold lt. intros. apply Sn_le_m_n_le_m in H0.
  apply le_trans with (a:=S a) (b:=b). apply H. apply H0.
Qed.

Lemma Sn_neq_n: forall n, ~(S n = n).
Proof. unfold not. intros. induction n. inversion H. 
  inversion H. apply IHn. apply H1. Qed.

Lemma Sn_not_le_n: forall n, ~(S n <= n).
Proof. unfold not. intros. induction n.
  inversion H.
  apply Sn_le_Sm__n_le_m in H. apply IHn. apply H.
Qed.

Lemma ordered_naturals: forall n m, n < m -> ~(m <= n).
Proof. 
  intros n. unfold not. induction n.
  intros. destruct m. inversion H. 
  inversion H. rewrite <- H2 in H0. apply Sn_not_le_n in H0. apply H0.
  inversion H0.
  intros. inversion H. rewrite <- H1 in H0. apply Sn_le_Sm__n_le_m in H0.
  rewrite <- H1 in H. apply Sn_not_le_n in H0. apply H0.
  rewrite <- H2 in H0. apply Sn_le_Sm__n_le_m in H0.
  assert (S n <= n).
    apply Sn_le_m_n_le_m.
    apply le_trans with (a:= S(S n)) (b:=m0) (c:=n). apply H1. apply H0.
  apply Sn_not_le_n in H3. apply H3.
Qed.

Theorem disjoint_bounds: forall n m l1 l2, 
   has_upper_bound n l1 -> has_lower_bound m l2 -> n < m -> disjoint l1 l2.
Proof.
   intros n m l1 l2 bounded_up bounded_down n_lt_m.
   unfold disjoint. intros elem isinl1.
   (* because elem is in l1, we know that it must be <= n. *)
   assert (elem <= n). 
     apply all_applies with (P := fun e => le e n) (l:=l1). 
     apply isinl1. apply bounded_up.
   assert (elem_lt_m: elem < m). 
     inversion H. apply n_lt_m. apply lt_trans with (b:=n).
     rewrite <- H1. unfold lt. apply n_le_m__Sn_le_Sm. apply H0. apply n_lt_m.
   unfold not. intros contra.
   (* If elem appears in l2, then m <= elem. *)
   assert (m_le_elem: m <= elem).
     apply all_applies with (P := le m) (l:=l2). apply contra. apply bounded_down.
  (* But we earlier proved elem < m, so we have a contradiction. *)
  apply ordered_naturals in elem_lt_m. apply elem_lt_m. apply m_le_elem.
Qed.

(** [] *)


(** **** Exercise: 3 stars (nostutter) *)
(** Formulating inductive definitions of predicates is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all (except from your study group partner, if
    you have one).

    We say that a list of numbers "stutters" if it repeats the same
    number consecutively.  The predicate "[nostutter mylist]" means
    that [mylist] does not stutter.  Formulate an inductive definition
    for [nostutter].  (This is different from the [no_repeats]
    predicate in the exercise above; the sequence [1,4,1] repeats but
    does not stutter.) *)

Inductive nostutter:  list nat -> Prop :=
  | nostutter_nil: nostutter []
  | nostutter_single: forall n, nostutter [n]
  | nostutter_multi: forall n m l, 
      n <> m -> nostutter l -> 
      hd_opt l <> Some m -> 
      nostutter (n::m::l).

Example nostutter_141: nostutter [1;4;1].
Proof.
  apply nostutter_multi. unfold not. intros. inversion H.
  apply nostutter_single. simpl. unfold not. intros contra.
  inversion contra.
Qed.

Example not_nostutter_114: ~(nostutter [1;1;4]).
Proof. 
  unfold not. intros contra. inversion contra. 
  unfold not in H2. apply H2. reflexivity.
Qed.

(** Make sure each of these tests succeeds, but you are free
    to change the proof if the given one doesn't work for you.
    Your definition might be different from mine and still correct,
    in which case the examples might need a different proof.
   
    The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)

Example test_nostutter_1:      nostutter [3;1;4;1;5;6].
  apply nostutter_multi. unfold not; intros noteq; inversion noteq.
  apply nostutter_multi. unfold not; intros noteq; inversion noteq.
  apply nostutter_multi. unfold not; intros noteq; inversion noteq.
  apply nostutter_nil. unfold not; intros noteq; inversion noteq.
  unfold not; intros noteq; inversion noteq.
  unfold not; intros noteq; inversion noteq.
Qed.

(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_2:  nostutter [].
Proof. apply nostutter_nil. Qed.

(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_3:  nostutter [5].
Proof. apply nostutter_single. Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof. unfold not. intros contra. inversion contra.
  simpl in H4. unfold not in H4. apply H4. reflexivity.
Qed.  

(* 
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.
*)
(** [] *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle) *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  intros. induction l1. reflexivity.
  simpl. rewrite IHl1. reflexivity.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros. induction l.
  inversion H.
  inversion H.
  exists []. simpl. exists l. reflexivity.
  apply IHl in H1.  
Admitted.  


(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | repeats_head: forall x l, repeats (x::x::l)
  | repeats_inside: forall x l, repeats l -> repeats (x::l).


(** Now here's a way to formalize the pigeonhole principle. List [l2]
   represents a list of pigeonhole labels, and list [l1] represents an
   assignment of items to labels: if there are more items than labels,
   at least two items must have the same label.  You will almost
   certainly need to use the [excluded_middle] hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1 l2:list X),
  excluded_middle -> 
  (forall x, appears_in x l1 -> appears_in x l2) -> 
  length l2 < length l1 -> 
  repeats l1.  
Proof.  intros X l1. induction l1.
  intros l2 excl_mid appears contra.
  simpl in contra. inversion contra.
  intros l2 excl_mid appears smaller.
  
  (* FILL IN HERE *) Admitted.
(** [] *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)

