(* Lecture 9, CIS 670, Fall 2012 *)
(* General Recursion *)
Require Import Arith List.
Require Import CpdtTactics Coinductive.
Require Import Recdef.
Set Implicit Arguments.

(* We know that the syntaction restriction on Fixpoint can prevent us
to define in a natural way interesting algorithms. Let us seke
where we get stuck on attempting a standard merge sort
implementation. *)

(* We have a set equipped with some "less-than-or-equal-to" test. *)
Section mergeSort.
  Variable A : Type.
  Variable le : A -> A -> bool.
 

(* We need to define some auxiliary functions. A standard function
inserts an element into a sorted list, preserving sortedness. *)

  Fixpoint insert (x : A) (ls : list A) : list A :=
    match ls with
      | nil => x :: nil
      | h :: ls' =>
	if le x h
	  then x :: ls
	  else h :: insert x ls'
    end.

  Fixpoint merge (ls1 ls2 : list A) : list A :=
    match ls1 with
      | nil => ls2
      | h :: ls' => insert h (merge ls' ls2)
    end.

  Fixpoint partition (ls : list A) : list A * list A :=
    match ls with
      | nil => (nil, nil)
      | h :: nil => (h :: nil, nil)
      | h1 :: h2 :: ls' =>
	let (ls1, ls2) := partition ls' in
	  (h1 :: ls1, h2 :: ls2)
    end.

  (** Now, let us try to write the final sorting function *(**
[[ *)
  Fixpoint mergeSort (ls : list A) : list A :=
    if leb (length ls) 1
      then ls
      else let lss := partition ls in
	merge (mergeSort (fst lss)) (mergeSort (snd lss)).
*)


(* Exercise (10 min.) Write a sorting program using the natural
definition of the quicksort algorithm and check where the troubles
come out. *)



(* A first solution. (thanks Catalin!) *)

(* The problem is that the recursive call is on the result of
partition and we have no evidence that this result is smaller than ls. 
So, let us try to provide this evidence. *)

  Lemma partition_wf : forall len ls, 2 <= length ls <= len
    -> let (ls1, ls2) := partition ls in
      length ls1  < length ls /\ length ls2 < length ls.
    induction len; crush; do 2 (destruct ls; crush);
      destruct (le_lt_dec 2 (length ls));
        repeat (match goal with
                  | [ _ : length ?E < 2 |- _ ] => destruct E
                  | [ _ : S (length ?E) < 2 |- _ ] => destruct E
                  | [ IH : _ |- context[partition ?L] ] =>
                    specialize (IH L); destruct (partition L); destruct IH
                end; crush).
  Defined.
  
(* It is convenient also to prove the following additional lemmas *)
  
  Lemma partition_wf1
    : forall len ls, 2 <= length ls <= len 
      -> length (fst (partition ls)) < length ls.
    intros;  generalize (@partition_wf(length ls) ls);
    destruct (partition ls); destruct 1; crush.
  Defined.
  
  Lemma partition_wf2
    : forall len ls, 2 <= length ls <= len
      -> length (snd (partition ls)) < length ls.
    intros; generalize (@partition_wf(length ls) ls);
      destruct (partition ls); destruct 1; crush.
  Defined.

(*Now using the lemma we have just proved we can write our
implementation of mergeSort*)

Function mergeSort (ls : list A) {measure length ls} : list A :=
    if leb (length ls) 1
      then ls
      else let lss := partition ls in
        merge (mergeSort (fst lss)) (mergeSort (snd lss)).
  intros; apply partition_wf2 with (length ls). rewrite leb_iff_conv in *. omega.
  intros. apply partition_wf1 with (length ls). rewrite leb_iff_conv in *. omega.
Defined.

(* Note that we are using Function Coq 8.4 feature with an annotation
{measure length ls} of the well funded ordeering that can be used to
prove mergeSort terminating.
http://coq.inria.fr/V8.2pl1/refman/Reference-Manual004.html#toc15 *)

(* Exercise (30 min). Define quickSort using Function. 

My solution to this exercise is using the following code for quickSort

qS [] = []
qS x :: xs = (qS (filter (< x) xs)) ++ (x :: qS (filter (> x) xs))

You can try to write this or another implementation for quickSort. Another
implementation can maybe make the homework more challenging
 *)

(* Another solution: accessibility relation *)

(*Function is a wrapper for a methodology to build functions
terminating following a well funded relation provided by the user.*)

  Print well_founded.

(*The bulk of the definitional work devolves to the accessibility
relation [Acc]. *)

  Print Acc.

(* Let us define a co-inductive relation for the notion of "absence of
infinite decreasing chains" and prove that any accessible element
cannot be the beginning of any infinite decreasing chain. *)

  CoInductive isChain A (R : A -> A -> Prop) : stream A -> Prop :=
  | ChainCons : forall x y s, isChain R (Cons y s)
    -> R y x
    -> isChain R (Cons x (Cons y s)).

  Lemma noChains' : forall A (R : A -> A -> Prop) x, Acc R x
    -> forall s, ~isChain R (Cons x s).
induction 1; crush;
      match goal with
        | [ H : isChain _ _ |- _ ] => inversion H; eauto
      end.
  Qed.

  Theorem noChains : forall A (R : A -> A -> Prop), well_founded R
    -> forall s, ~isChain R s.
    destruct s; apply noChains'; auto.
  Qed.


(** Absence of infinite decreasing chains implies absence of
infinitely nested recursive calls.The [Fix] combinator from the
standard library formalizes that intuition: *)


(* Exercise (10 min) Define a well founded relation between the
booleans true and false and prove it well founded *)

(* Let us now use the combinator Fix to write mergeSort*)

  Check Fix.

(*Similarly to what we have done before, we have to provide a
well-founded relation explicitly.*)

  Definition lengthOrder (ls1 ls2 : list A) :=
    length ls1 < length ls2.

  Hint Constructors Acc.

  Lemma lengthOrder_wf' : forall len, forall ls, length ls <= len -> Acc lengthOrder ls.
    unfold lengthOrder; induction len; crush; eauto.
  Defined.

Check lengthOrder_wf'.

  Theorem lengthOrder_wf : well_founded lengthOrder.
    red; intro; eapply lengthOrder_wf'; eauto.
  Defined.

(* Notice that we have to prove the same lemma we proved before for
partition. This time with respect to lengthOrder. *)

  Lemma partition_wf' : forall len ls, 2 <= length ls <= len
    -> let (ls1, ls2) := partition ls in
      lengthOrder ls1 ls /\ lengthOrder ls2 ls.
    unfold lengthOrder; induction len; crush; do 2 (destruct ls; crush);
      destruct (le_lt_dec 2 (length ls));
        repeat (match goal with
                  | [ _ : length ?E < 2 |- _ ] => destruct E
                  | [ _ : S (length ?E) < 2 |- _ ] => destruct E
                  | [ IH : _ |- context[partition ?L] ] =>
                    specialize (IH L); destruct (partition L); destruct IH
                end; crush).
  Defined.

  Ltac partition := intros ls ?; intros; generalize (@partition_wf (length ls) ls);
    destruct (partition ls); destruct 1; crush.

  Lemma partition_wf1' : forall ls, 2 <= length ls
    -> lengthOrder (fst (partition ls)) ls.
    partition.
  Defined.

  Lemma partition_wf2' : forall ls, 2 <= length ls
    -> lengthOrder (snd (partition ls)) ls.
    partition.
  Defined.

  Hint Resolve partition_wf1' partition_wf2'.

Check Fix.

  Definition mergeSort' : list A -> list A.
    refine (Fix lengthOrder_wf (fun _ => list A)
      (fun (ls : list A)
        (mergeSort' : forall ls' : list A, lengthOrder ls' ls -> list A) =>
        if le_lt_dec 2 (length ls)
	  then let lss := partition ls in
            merge (mergeSort' (fst lss) _) (mergeSort' (snd lss) _)
	  else ls)); subst lss; eauto.
  Defined.
End mergeSort.


(* Testing *)
Eval compute in mergeSort leb (1 :: 2 :: 36 :: 8 :: 19 :: nil).
Eval compute in mergeSort' leb (1 :: 2 :: 36 :: 8 :: 19 :: nil).

(* Exercise (30 min) Use the same methodology to write quickSort and
test it.*)

(* Let's prove that [mergeSort'] has the expected computational behavior. *)

Theorem mergeSort'_eq : forall A (le : A -> A -> bool) ls,
  mergeSort' le ls = if le_lt_dec 2 (length ls)
    then let lss := partition ls in
      merge le (mergeSort' le (fst lss)) (mergeSort' le (snd lss))
    else ls.
  intros; apply (Fix_eq (@lengthOrder_wf A) (fun _ => list A)); intros.
  match goal with
    | [ |- context[match ?E with left _ => _ | right _ => _ end] ] => destruct E
  end; simpl; f_equal; auto.
Qed.

(** As a final test of our definition's suitability, we can extract to OCaml. *)

Extraction mergeSort.
Extraction mergeSort'.

(* Exercise  (15 min) Prove a quickSort1_eq statement and extract your definition of quckSort*)

(* Another approach to General Recursion: Non-Termination Monad
Inspired by Domain Theory *)

Section computation.
  Variable A : Type.

  Definition computation :=
    {f : nat -> option A
      | forall (n : nat) (v : A),
	f n = Some v
	-> forall (n' : nat), n' >= n
	  -> f n' = Some v}.

  Definition runTo (m : computation) (n : nat) (v : A) :=
    proj1_sig m n = Some v.


  Definition run (m : computation) (v : A) :=
    exists n, runTo m n v.
End computation.

(* Some tactics, lemma proofs, and hint commands, to be used in
proving facts about computations. *)

Hint Unfold runTo.

Ltac run' := unfold run, runTo in *; try red; crush;
  repeat (match goal with
            | [ _ : proj1_sig ?E _ = _ |- _ ] =>
              match goal with
                | [ x : _ |- _ ] =>
                  match x with
                    | E => destruct E
                  end
              end
            | [ |- context[match ?M with exist _ _ => _ end] ] => let Heq := fresh "Heq" in
              case_eq M; intros ? ? Heq; try rewrite Heq in *; try subst
            | [ _ : context[match ?M with exist _ _ => _ end] |- _ ] => let Heq := fresh "Heq" in
              case_eq M; intros ? ? Heq; try rewrite Heq in *; subst
            | [ H : forall n v, ?E n = Some v -> _,
                _ : context[match ?E ?N with Some _ => _ | None => _ end] |- _ ] =>
              specialize (H N); destruct (E N); try rewrite (H _ (eq_refl _)) by auto; try discriminate
            | [ H : forall n v, ?E n = Some v -> _, H' : ?E _ = Some _ |- _ ] => rewrite (H _ _ H') by auto
          end; simpl in *); eauto 7.

Ltac run := run'; repeat (match goal with
                            | [ H : forall n v, ?E n = Some v -> _
                                |- context[match ?E ?N with Some _ => _ | None => _ end] ] =>
                              specialize (H N); destruct (E N); try rewrite (H _ (eq_refl _)) by auto; try discriminate
                          end; run').

Lemma ex_irrelevant : forall P : Prop, P -> exists n : nat, P.
  exists 0; auto.
Qed.

Hint Resolve ex_irrelevant.

Require Import Max.

Theorem max_spec_le : forall n m, n <= m /\ max n m = m \/ m <= n /\ max n m = n.
  induction n; destruct m; simpl; intuition;
    specialize (IHn m); intuition.
Qed.

Ltac max := intros n m; generalize (max_spec_le n m); crush.

Lemma max_1 : forall n m, max n m >= n.
  max.
Qed.

Lemma max_2 : forall n m, max n m >= m.
  max.
Qed.

Hint Resolve max_1 max_2.

Lemma ge_refl : forall n, n >= n.
  crush.
Qed.

Hint Resolve ge_refl.

Hint Extern 1 => match goal with
                   | [ H : _ = exist _ _ _ |- _ ] => rewrite H
                 end.
(* end tactics *)


(* A simple first example of a computation. *)

Section Bottom.
  Variable A : Type.

  Definition Bottom : computation A.
    exists (fun _ : nat => @None A); abstract run.
  Defined.

  Theorem run_Bottom : forall v, ~run Bottom v.
    run.
  Qed.
End Bottom.

(* We want to use computation to define a monad. *)

Section Return.
  Variable A : Type.
  Variable v : A.

  Definition Return : computation A.
    intros; exists (fun _ : nat => Some v); abstract run.
  Defined.

  Theorem run_Return : run Return v.
    run.
  Qed.
End Return.

Section Bind.
  Variables A B : Type.
  Variable m1 : computation A.
  Variable m2 : A -> computation B.

  Definition Bind : computation B.
    exists (fun n =>
      let (f1, _) := m1 in
      match f1 n with
	| None => None
	| Some v =>
	  let (f2, _) := m2 v in
	    f2 n
      end); abstract run.
  Defined.

  Theorem run_Bind : forall (v1 : A) (v2 : B),
    run m1 v1
    -> run (m2 v1) v2
    -> run Bind v2.
    run; match goal with
           | [ x : nat, y : nat |- _ ] => exists (max x y)
         end; run.
  Qed.
End Bind.


Notation "x <- m1 ; m2" :=
  (Bind m1 (fun x => m2)) (right associativity, at level 70).

(* And proving the standard monad laws.*)


Definition meq A (m1 m2 : computation A) := forall n, proj1_sig m1 n = proj1_sig m2 n.

Theorem left_identity : forall A B (a : A) (f : A -> computation B),
  meq (Bind (Return a) f) (f a).
  run.
Qed.

Theorem right_identity : forall A (m : computation A),
  meq (Bind m (@Return _)) m.
  run.
Qed.

Theorem associativity : forall A B C (m : computation A)
  (f : A -> computation B) (g : B -> computation C),
  meq (Bind (Bind m f) g) (Bind m (fun x => Bind (f x) g)).
  run.
Qed.

(** Now we come to the piece most directly inspired by domain
theory. *)

Section lattice.
  Variable A : Type.

  Definition leq (x y : option A) :=
    forall v, x = Some v -> y = Some v.
End lattice.

Check leq.

Section Fix.

  Variables A B : Type.

  Variable f : (A -> computation B) -> (A -> computation B).

  Hypothesis f_continuous : forall n v v1 x,
    runTo (f v1 x) n v
    -> forall (v2 : A -> computation B),
      (forall x, leq (proj1_sig (v1 x) n) (proj1_sig (v2 x) n))
      -> runTo (f v2 x) n v.

  Fixpoint Fix' (n : nat) (x : A) : computation B :=
    match n with
      | O => Bottom _
      | S n' => f (Fix' n') x
    end.


  Hint Extern 1 (_ >= _) => omega.
  Hint Unfold leq.

  Lemma Fix'_ok : forall steps n x v, proj1_sig (Fix' n x) steps = Some v
    -> forall n', n' >= n
      -> proj1_sig (Fix' n' x) steps = Some v.
    unfold runTo in *; induction n; crush;
      match goal with
        | [ H : _ >= _ |- _ ] => inversion H; crush; eauto
      end.
  Qed.

  Hint Resolve Fix'_ok.

  Hint Extern 1 (proj1_sig _ _ = _) => simpl;
    match goal with
      | [ |- proj1_sig ?E _ = _ ] => eapply (proj2_sig E)
    end.

  Definition Fix : A -> computation B.
    intro x; exists (fun n => proj1_sig (Fix' n x) n); abstract run.
  Defined.

 (* We can prove that [Fix] obeys the expected computation rule. *)

  Theorem run_Fix : forall x v,
    run (f Fix x) v
    -> run (Fix x) v.
    run; match goal with
           | [ n : nat |- _ ] => exists (S n); eauto
         end.
  Qed.
End Fix.

(*Other lemmas and tactics.*)

Lemma leq_Some : forall A (x y : A), leq (Some x) (Some y)
  -> x = y.
  intros ? ? ? H; generalize (H _ (eq_refl _)); crush.
Qed.

Lemma leq_None : forall A (x y : A), leq (Some x) None
  -> False.
  intros ? ? ? H; generalize (H _ (eq_refl _)); crush.
Qed.

Ltac mergeSort1 := run;
  repeat (match goal with
            | [ |- context[match ?E with O => _ | S _ => _ end] ] => destruct E
          end; run);
  repeat match goal with
           | [ H : forall x, leq (proj1_sig (?f x) _) (proj1_sig (?g x) _) |- _ ] =>
             match goal with
               | [ H1 : f ?arg = _, H2 : g ?arg = _ |- _ ] =>
                 generalize (H arg); rewrite H1; rewrite H2; clear H1 H2; simpl; intro
             end
         end; run; repeat match goal with
                            | [ H : _ |- _ ] => (apply leq_None in H; tauto) || (apply leq_Some in H; subst)
                          end; auto.

(*end tactics*)

(* We can now write our version of mergeSort *)

Definition mergeSort'' : forall A, (A -> A -> bool) -> list A -> computation (list A).
  refine (fun A le => Fix
    (fun (mergeSort'' : list A -> computation (list A))
      (ls : list A) =>
      if le_lt_dec 2 (length ls)
	then let lss := partition ls in
          ls1 <- mergeSort'' (fst lss);
          ls2 <- mergeSort'' (snd lss);
          Return (merge le ls1 ls2)
	else Return ls) _); abstract mergeSort1.
Defined.

(* Testing. *)

Lemma test_mergeSort'' : run (mergeSort'' leb (1 :: 2 :: 36 :: 8 :: 19 :: nil))
  (1 :: 2 :: 8 :: 19 :: 36 :: nil).
  exists 4; reflexivity.
Qed.

(* We can also now write recursive functions that sometimes fail to
terminate. *)

Ltac looper := unfold leq in *; run;
  repeat match goal with
           | [ x : unit |- _ ] => destruct x
           | [ x : bool |- _ ] => destruct x
         end; auto.


Definition looper : bool -> computation unit.
  refine (Fix (fun looper (b : bool) =>
    if b then Return tt else looper b) _); abstract looper.
Defined.

Lemma test_looper : run (looper true) tt.
  exists 1; reflexivity.
Qed.

(*Exercise (30 min)
Use the monad defined above to write the following partial function:

iter x = if x = 0  then [] else x::iter (x +1 )
*)


(* Another approach: Co-Inductive Non-Termination Monads v1 *)


CoInductive thunk (A : Type) : Type :=
| Answer : A -> thunk A
| Think : thunk A -> thunk A.

CoFixpoint TBind A B (m1 : thunk A) (m2 : A -> thunk B) : thunk B :=
  match m1 with
    | Answer x => m2 x
    | Think m1' => Think (TBind m1' m2)
  end.

(* We can prove that [Answer] and [TBind] form a monad for [thunk].
 As usual for this sort of proof, a key element is choosing an
 appropriate notion of equality for [thunk]s. *)

CoInductive thunk_eq A : thunk A -> thunk A -> Prop :=
| EqAnswer : forall x, thunk_eq (Answer x) (Answer x)
| EqThinkL : forall m1 m2, thunk_eq m1 m2 -> thunk_eq (Think m1) m2
| EqThinkR : forall m1 m2, thunk_eq m1 m2 -> thunk_eq m1 (Think m2).

Section thunk_eq_coind.
  Variable A : Type.
  Variable P : thunk A -> thunk A -> Prop.

  Hypothesis H : forall m1 m2, P m1 m2
    -> match m1, m2 with
         | Answer x1, Answer x2 => x1 = x2
         | Think m1', Think m2' => P m1' m2'
         | Think m1', _ => P m1' m2
         | _, Think m2' => P m1 m2'
       end.

  Theorem thunk_eq_coind : forall m1 m2, P m1 m2 -> thunk_eq m1 m2.
    cofix; intros;
      match goal with
        | [ H' : P _ _ |- _ ] => specialize (H H'); clear H'
      end; destruct m1; destruct m2; subst; repeat constructor; auto.
  Qed.
End thunk_eq_coind.

(* We need a function similar to one we saw in Chapter 5, to pull
apart and reassemble a [thunk] in a way that provokes reduction of
co-recursive calls. *)

Definition frob A (m : thunk A) : thunk A :=
  match m with
    | Answer x => Answer x
    | Think m' => Think m'
  end.

Theorem frob_eq : forall A (m : thunk A), frob m = m.
  destruct m; reflexivity.
Qed.


Theorem thunk_eq_frob : forall A (m1 m2 : thunk A),
  thunk_eq (frob m1) (frob m2)
  -> thunk_eq m1 m2.
  intros; repeat rewrite frob_eq in *; auto.
Qed.

Ltac findDestr := match goal with
                    | [ |- context[match ?E with Answer _ => _ | Think _ => _ end] ] =>
                      match E with
                        | context[match _ with Answer _ => _ | Think _ => _ end] => fail 1
                        | _ => destruct E
                      end
                  end.

Theorem thunk_eq_refl : forall A (m : thunk A), thunk_eq m m.
  intros; apply (thunk_eq_coind (fun m1 m2 => m1 = m2)); crush; findDestr; reflexivity.
Qed.

Hint Resolve thunk_eq_refl.

Theorem tleft_identity : forall A B (a : A) (f : A -> thunk B),
  thunk_eq (TBind (Answer a) f) (f a).
  intros; apply thunk_eq_frob; crush.
Qed.

Theorem tright_identity : forall A (m : thunk A),
  thunk_eq (TBind m (@Answer _)) m.
  intros; apply (thunk_eq_coind (fun m1 m2 => m1 = TBind m2 (@Answer _))); crush;
    findDestr; reflexivity.
Qed.

Lemma TBind_Answer : forall (A B : Type) (v : A) (m2 : A -> thunk B),
  TBind (Answer v) m2 = m2 v.
  intros; rewrite <- (frob_eq (TBind (Answer v) m2));
    simpl; findDestr; reflexivity.
Qed.

Hint Rewrite TBind_Answer.

(** printing exists $\exists$ *)

Theorem tassociativity : forall A B C (m : thunk A) (f : A -> thunk B) (g : B -> thunk C),
  thunk_eq (TBind (TBind m f) g) (TBind m (fun x => TBind (f x) g)).
  intros; apply (thunk_eq_coind (fun m1 m2 => (exists m,
    m1 = TBind (TBind m f) g
    /\ m2 = TBind m (fun x => TBind (f x) g))
  \/ m1 = m2)); crush; eauto; repeat (findDestr; crush; eauto).
Qed.

(** As a simple example, here is how we might define a tail-recursive
factorial function. *)

CoFixpoint fact (n acc : nat) : thunk nat :=
  match n with
    | O => Answer acc
    | S n' => Think (fact n' (S n' * acc))
  end.

(** To test our definition, we need an evaluation relation that
characterizes results of evaluating [thunk]s. *)

Inductive eval A : thunk A -> A -> Prop :=
| EvalAnswer : forall x, eval (Answer x) x
| EvalThink : forall m x, eval m x -> eval (Think m) x.

Hint Rewrite frob_eq.

Lemma eval_frob : forall A (c : thunk A) x,
  eval (frob c) x
  -> eval c x.
  crush.
Qed.

Theorem eval_fact : eval (fact 5 1) 120.
  repeat (apply eval_frob; simpl; constructor).
Qed.

Notation "x <- m1 ; m2" :=
  (TBind m1 (fun x => m2)) (right associativity, at level 70).

(* Now consider another very similar definition, this time of a Fibonacci number function. *)

(** %\vspace{-.3in}%[[
CoFixpoint fib (n : nat) : thunk nat :=
  match n with
    | 0 => Answer 1
    | 1 => Answer 1
    | _ => n1 <- fib (pred n);
      n2 <- fib (pred (pred n));
      Answer (n1 + n2)
  end.
]]

Coq complains that the guardedness condition is violated. *)


(* Another approach: Co-Inductive Non-Termination Monads v2*)

CoInductive comp (A : Type) : Type :=
| Ret : A -> comp A
| Bnd : forall B, comp B -> (B -> comp A) -> comp A.

Inductive exec A : comp A -> A -> Prop :=
| ExecRet : forall x, exec (Ret x) x
| ExecBnd : forall B (c : comp B) (f : B -> comp A) x1 x2, exec (A := B) c x1
  -> exec (f x1) x2
  -> exec (Bnd c f) x2.

(** We can also prove that [Ret] and [Bnd] form a monad according to a
notion of [comp] equality based on [exec]. *)

Hint Constructors exec.

Definition comp_eq A (c1 c2 : comp A) := forall r, exec c1 r <-> exec c2 r.

Ltac inverter := repeat match goal with
                          | [ H : exec _ _ |- _ ] => inversion H; []; crush
                        end.

Theorem cleft_identity : forall A B (a : A) (f : A -> comp B),
  comp_eq (Bnd (Ret a) f) (f a).
  red; crush; inverter; eauto.
Qed.

Theorem cright_identity : forall A (m : comp A),
  comp_eq (Bnd m (@Ret _)) m.
  red; crush; inverter; eauto.
Qed.

Lemma cassociativity1 : forall A B C (f : A -> comp B) (g : B -> comp C) r c,
  exec c r
  -> forall m, c = Bnd (Bnd m f) g
   -> exec (Bnd m (fun x => Bnd (f x) g)) r.
  induction 1; crush.
  match goal with
    | [ H : Bnd _ _ = Bnd _ _ |- _ ] => injection H; clear H; intros; try subst
  end.
  move H3 after A.
  generalize dependent B0.
  do 2 intro.
  subst.
  crush.
  inversion H; clear H; crush.
  eauto.
Qed.

Lemma cassociativity2 : forall A B C (f : A -> comp B) (g : B -> comp C) r c,
  exec c r
  -> forall m, c = Bnd m (fun x => Bnd (f x) g)
   -> exec (Bnd (Bnd m f) g) r.
  induction 1; crush.
  match goal with
    | [ H : Bnd _ _ = Bnd _ _ |- _ ] => injection H; clear H; intros; try subst
  end.
  move H3 after B.
  generalize dependent B0.
  do 2 intro.
  subst.
  crush.
  inversion H0; clear H0; crush.
  eauto.
Qed.

Hint Resolve cassociativity1 cassociativity2.

Theorem cassociativity : forall A B C (m : comp A) (f : A -> comp B) (g : B -> comp C),
  comp_eq (Bnd (Bnd m f) g) (Bnd m (fun x => Bnd (f x) g)).
  red; crush; eauto.
Qed.


(* Not only can we define the Fibonacci function with the new monad,
but even our running example of merge sort becomes definable.  *)

Notation "x <- m1 ; m2" := (Bnd m1 (fun x => m2)).

CoFixpoint mergeSort''' A (le : A -> A -> bool) (ls : list A) : comp (list A) :=
  if le_lt_dec 2 (length ls)
    then let lss := partition ls in
      ls1 <- mergeSort''' le (fst lss);
      ls2 <- mergeSort''' le (snd lss);
      Ret (merge le ls1 ls2)
    else Ret ls.

Definition frob' A (c : comp A) :=
  match c with
    | Ret x => Ret x
    | Bnd _ c' f => Bnd c' f
  end.

Lemma exec_frob : forall A (c : comp A) x,
  exec (frob' c) x
  -> exec c x.
  destruct c; crush.
Qed.

(*Testing.*)

Lemma test_mergeSort''' : exec (mergeSort''' leb (1 :: 2 :: 36 :: 8 :: 19 :: nil))
  (1 :: 2 :: 8 :: 19 :: 36 :: nil).
  repeat (apply exec_frob; simpl; econstructor).
Qed.

(* Exercise (10 min) Do the same for quickSort *)

(* Exercise (10 min) Do the same for fibonacci *)