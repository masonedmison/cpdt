Require Import List.

Require Import CpdtTactics.

Set Implicit Arguments.

(* Note about the exercises:

For all of the versions of pred, to get some hands on practice,
try to implement a safe head function (for plain coq lists).

Some hints: if you want to do this for polymorphic lists (and why not?),
the type of the list elements should be in Set, not Type (try it).

Depending on how you set up the postcondition, you may need to add [eauto]
instead of just using [crush].
*)

(* Exercise (Optional): Write a safe head function. It should have type

head_string1 (A : type) (l : list A) : (length l) > 0 -> nat
*)

(* Exercise (10 min.)
Write a function that takes a value of type sig, and returns
the witness value.

Try to write the same function for ex. What goes wrong?
*)

(* Some syntax for subset types *)

(* Read: Contradicted hypothesis. *)
Notation "!" := (False_rec _ _).

(* Read: Produced a value e, along with a proof that proposition
holds of e. *)
Notation "[ e ]" := (exist _ e _).

Definition pred_strong : forall n : nat, n > 0 -> {m : nat | n = S m}.
  refine (fun n =>
    match n with
      | O => fun _ => !
      | S n' => fun _ => [n']
    end); crush.
Defined.

(* Exercise (30 min.)

Use this safe predecessor function to define a safe "minus 2" function,
with type

pred2_strong : forall (n : nat), n > 1 -> {m : nat | n = S (S m)}

*)

(* Exercise (Optional)

Though defining functions that offer correctness guarantees is
requires a little more upfront work, they often compose better than
more weakly typed functions. For example, suppose we start with our
original predecessor function:

pred_strong1 : forall (n : nat), (n > 0) -> nat.

Try to use pred_strong1 to define a function

pred2_partial : forall (n : nat), (n > 1) -> nat.

*)

(** * Detour: Decidable Proposition Types *)

(* Convention: the left constructor corresponds to success, while
the right constructor corresponds to failure. *)

(* Read: Found a witness of success, and a proof. *)
Notation "'Yes'" := (left _ _).

(* Read: Found a witness of failure, and a proof. *)
Notation "'No'" := (right _ _).

(* Read: If x succeeds, then take the proof of success and
convert to a proof of success for the entire expression.
Same if x fails. *)
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

(* One example of [sumbool] is the decidable equality type,
which indicates that given two values, we can come up with a proof of
equality, or a proof of disequality. For instance, we can do this for
[nat]. *)

Definition eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
  refine (fix f (n m : nat) : {n = m} + {n <> m} :=
    match n, m with
      | O, O => Yes
      | S n', S m' => Reduce (f n' m')
      | _, _ => No
    end); congruence.
Defined.

(* Exercise (20 min.)

Write down the proof obligations that are generated by refine.
There's no need to write down every last hypothesis, just try to
write informally what is to be proved, under what hypothesis.
Try to do this without peeking.

For example, the first obligation should be:

Prove (0 = 0) under no hypothesis.

*)

(* Read: if x returns a positive result, return a positive result.
Otherwise, evaluate y. *)
Notation "x || y" := (if x then Yes else Reduce y).

(* Exercise (30 min.): Write a decidable equality function for
list A, assuming a decidable equality for A.

Hint: It might be good to start with some new notation...
*)

(** * Partial Subset Types *)

Inductive maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x : A, P x -> maybe P.

(** We can define some new notations, analogous to those we defined
for subset types. *)

(* Read: there is maybe an element x that satisfies P. *)
Notation "{{ x | P }}" := (maybe (fun x => P)).

(* Read: we failed to find an x, for some reason. *)
Notation "??" := (Unknown _).

(* Read: we found an x, and here is the proof that P x is
is satisfiable. *)
Notation "[| x |]" := (Found _ x _).

(* In the failure case, we don't provide any proof at all. The
implementation that always fails could be given this type. We
want to rule these out, and we'll use the [sumor] type, which
is either a value, or a proof. *)

Print sumor.

(* We add notations for easy use of the [sumor] constructors. *)

(* Read: here is a proof of B. (Convention: proof of failure) *)
Notation "!!" := (inright _ _).

(* Read: we found a witness x to the proposition P, and a proof that
P x. Note: only works when the "value" type in [sumor] is a subset
type. *)
Notation "[|| x ||]" := (inleft _ [x]).

(* Now, we can give a version of pred that works on all inputs,
and is fully specified. *)

(** * Monadic Notations *)

(* Read: If e1 produces a witness, see if e2 produces a witness.
If e1 fails, fail. *)
Notation "x <- e1 ; e2" := (match e1 with
                             | Unknown => ??
                             | Found x _ => e2
                           end)
(right associativity, at level 60).

(* Read: If e1 produces a proof of failure, produce a proof of failure.
If e1 produces a witness and a proof of success, evaulate e2. *)
Notation "x <-- e1 ; e2" := (match e1 with
                               | inright _ => !!
                               | inleft (exist x _) => e2
                             end)
(right associativity, at level 60).

(** * A Type-Checking Example *)

(* Let's use these ideas to build a certified typechecker. First,
our language... *)

Inductive exp : Set :=
| Nat : nat -> exp
| Plus : exp -> exp -> exp
| Bool : bool -> exp
| And : exp -> exp -> exp.

Inductive type : Set := TNat | TBool.

Inductive hasType : exp -> type -> Prop :=
| HtNat : forall n,
  hasType (Nat n) TNat
| HtPlus : forall e1 e2,
  hasType e1 TNat
  -> hasType e2 TNat
  -> hasType (Plus e1 e2) TNat
| HtBool : forall b,
  hasType (Bool b) TBool
| HtAnd : forall e1 e2,
  hasType e1 TBool
  -> hasType e2 TBool
  -> hasType (And e1 e2) TBool.

(* We build a equality type decision procedure for [type]. *)

Definition eq_type_dec : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
  decide equality.
Defined.

(* Notation for typechecker *)

(* Read: If e1 succeeds (produces a witness), then do e2. Else, fail. *)
Notation "e1 ;; e2" := (if e1 then e2 else ??)
  (right associativity, at level 60).

Definition typeCheck : forall e : exp, {{t | hasType e t}}.
  Hint Constructors hasType.

  refine (fix F (e : exp) : {{t | hasType e t}} :=
    match e return {{t | hasType e t}} with
      | Nat _ => [|TNat|]
      | Plus e1 e2 =>
        t1 <- F e1;
        t2 <- F e2;
        eq_type_dec t1 TNat;; (* Assert that t1 is a nat *)
        eq_type_dec t2 TNat;; (* Assert that t2 is a nat *)
        [|TNat|]
      | Bool _ => [|TBool|]
      | And e1 e2 =>
        t1 <- F e1;
        t2 <- F e2;
        eq_type_dec t1 TBool;;
        eq_type_dec t2 TBool;;
        [|TBool|]
    end); crush.
Defined.

(* sumor typechecker *)

(* Read: Same as e1 ;; e2, except if we fail this time, we get a proof
of failure, which we can return. *)
Notation "e1 ;;; e2" := (if e1 then e2 else !!)
  (right associativity, at level 60).

(** Next, we prove a helpful lemma, which states that a given
expression can have at most one type. *)

Lemma hasType_det : forall e t1,
  hasType e t1
  -> forall t2, hasType e t2
    -> t1 = t2.
  induction 1; inversion 1; crush.
Qed.

Definition typeCheck' : forall e : exp, {t : type | hasType e t} + {forall t, ~ hasType e t}.
  Hint Constructors hasType.
  (** We register all of the typing rules as hints. *)

  Hint Resolve hasType_det.
  (* Note that [hasType_det] has forall bound variables that don't
     show up in the final type, and so we need [eauto] to apply it. *)

  (** The implementation can be translated from our previous
      implementation, just by switching a few notations. *)

  refine (fix F (e : exp) : {t : type | hasType e t} + {forall t, ~ hasType e t} :=
    match e return {t : type | hasType e t} + {forall t, ~ hasType e t} with
      | Nat _ => [||TNat||]
      | Plus e1 e2 =>
        t1 <-- F e1;
        t2 <-- F e2;
        eq_type_dec t1 TNat;;;
        eq_type_dec t2 TNat;;;
        [||TNat||]
      | Bool _ => [||TBool||]
      | And e1 e2 =>
        t1 <-- F e1;
        t2 <-- F e2;
        eq_type_dec t1 TBool;;;
        eq_type_dec t2 TBool;;;
        [||TBool||]
    end); clear F; crush' tt hasType; eauto.
Defined.

(* Exercise (45 min.)

Add pairs to the language.

*)
