Require Import Arith Bool List.
Add LoadPath "~/Desktop/CIS670/cpdt/src/".
Require Import CpdtTactics MoreSpecif.

Set Implicit Arguments.

(* Exercise (40 min) : The one invariant that rbtrees don't take 
   into account is the fact that rbtrees are binary search trees.
   That is, every key in a node's left subtree is less than
   the key of the node, which is less than every key in the
   node's right subtree. Use dependent types to capture this 
   invariant by defining a binary search tree (independently of
   rbtree). The tree should be indexed by lower and upper bounds
   on the tree:
   
   Inductive btree : nat -> nat -> Set :=
   ...
   
   Define insertion on your tree and prove its correctness.
   That is, define a 'present' predicate that tells when
   an entry is present in a tree and prove that if
   y is present in insert x t then y=x or y is present in t.
   You may define insertion only for variables within
   the bounds of the tree you already have: 

   insert : forall m n (t : btree m n) x, m < x < n -> btree m n

   ** If you are having guardedness condition problems when trying
      to define insert using a refine followed by crush, 
      it may be the case that crush is incorrectly applying the 
      inductive hypothesis. In that case try replacing crush
      by 
        clear F; crush.
      where F is the name of the fixpoint. 
 *)

(* Exercise (25 min) : Use your btree definition to write a recursive function
   isEqual which takes two btrees with the same bounds and returns true
   if the trees are equal (have all the same keys in the same structure). 
*)


Require Import Ascii String.
Open Scope string_scope.

(* Regular Expression Matcher
   
   Index our regular expreesions by prediates over
   strings which describe what we are matching on. *)

(* ++ : concatination
   "" : Empty string
   String c s : prepend the character c on the 
                front of s (cons) *)

(*
Inductive regexp0 : (string -> Prop) -> Set :=
| Char0 : forall ch : ascii,
  regexp0 (fun s => s = String ch "")
| Concat0 : forall (P1 P2 : string -> Prop) 
           (r1 : regexp0 P1) (r2 : regexp0 P2),
  regexp0  (fun s => exists s1, exists s2, 
            s = s1 ++ s2 /\ P1 s1 /\ P2 s2).
*)

(* A large inductive type is a Coq inductive 
   type that has a constructor quantified over 
   something in Type

   Concat quantifies over (string -> Prop) : Type 

   Large inductive types lead to contradictions in Coq.
   Solution: place regexp in Type. *)

Section star.
  (* P represents the regular expression being star'd *)
  Variable P : string -> Prop.

  Inductive star : string -> Prop :=
  | Empty : star ""
  | Iter : forall s1 s2,
    P s1
    -> star s2
    -> star (s1 ++ s2).
End star.

Inductive regexp : (string -> Prop) -> Type :=
| Char : forall ch : ascii,
  regexp (fun s => s = String ch "")
| Concat : forall P1 P2 (r1 : regexp P1) (r2 : regexp P2),
  regexp (fun s => exists s1, exists s2, s = s1 ++ s2 /\ P1 s1 /\ P2 s2)
| Or : forall P1 P2 (r1 : regexp P1) (r2 : regexp P2),
  regexp (fun s => P1 s \/ P2 s)
| Star : forall P (r : regexp P),
  regexp (star P).

(* begin hide *)
Open Scope specif_scope.

Lemma length_emp : length "" <= 0.
  crush.
Qed.

Lemma append_emp : forall s, s = "" ++ s.
  crush.
Qed.

Ltac substring :=
  crush;
  repeat match goal with
           | [ |- context[match ?N with O => _ | S _ => _ end] ] => destruct N; crush
         end.

Lemma substring_le : forall s n m,
  length (substring n m s) <= m.
  induction s; substring.
Qed.

Lemma substring_all : forall s,
  substring 0 (length s) s = s.
  induction s; substring.
Qed.

Lemma substring_none : forall s n,
  substring n 0 s = "".
  induction s; substring.
Qed.

Hint Rewrite substring_all substring_none.

Lemma substring_split : forall s m,
  substring 0 m s ++ substring m (length s - m) s = s.
  induction s; substring.
Qed.

Lemma length_app1 : forall s1 s2,
  length s1 <= length (s1 ++ s2).
  induction s1; crush.
Qed.

Hint Resolve length_emp append_emp substring_le substring_split length_app1.

Lemma substring_app_fst : forall s2 s1 n,
  length s1 = n
  -> substring 0 n (s1 ++ s2) = s1.
  induction s1; crush.
Qed.

Lemma substring_app_snd : forall s2 s1 n,
  length s1 = n
  -> substring n (length (s1 ++ s2) - n) (s1 ++ s2) = s2.
  Hint Rewrite <- minus_n_O.

  induction s1; crush.
Qed.

Hint Rewrite substring_app_fst substring_app_snd using solve [trivial].
(* end hide *)


Section split.
  Variables P1 P2 : string -> Prop.
  Variable P1_dec : forall s, {P1 s} + {~ P1 s}.
  Variable P2_dec : forall s, {P2 s} + {~ P2 s}.

  (* The string we are matching *)
  Variable s : string.

  (* split' searches through possible ways of splitting 
     s into two pieces and checks P1 and P2 on each split. 

     It does a linear search, splitting at the index 
     n at iteration n. *)

  Locate "Reduce".

  Definition split' : forall n : nat, n <= length s -> 
    {exists s1, exists s2,
      length s1 <= n /\ s1 ++ s2 = s /\ P1 s1 /\ P2 s2}
    + {forall s1 s2, length s1 <= n -> 
      s1 ++ s2 = s -> ~ P1 s1 \/ ~ P2 s2}.

    refine (fix F (n : nat) : n <= length s -> 
      {exists s1, exists s2, 
        length s1 <= n /\ s1 ++ s2 = s /\ P1 s1 /\ P2 s2}
      + {forall s1 s2, length s1 <= n -> 
        s1 ++ s2 = s -> ~ P1 s1 \/ ~ P2 s2} :=

      match n with
        | O => fun _ => Reduce (P1_dec "" && P2_dec s)
        
        | S n' => fun _ => (P1_dec (substring 0 (S n') s)
        && P2_dec (substring (S n') (length s - S n') s))
          || F n' _

      end); clear F; crush; eauto 7;
    match goal with
      | [ _ : length ?S <= 0 |- _ ] => destruct S
      | [ _ : length ?S' <= S ?N |- _ ] =>
        destruct (eq_nat_dec (length S') (S N))
    end; crush.
  Defined.

     (*
        | S n' => fun _ => let n := S n' in
          (P1_dec (substring 0 n s)
            && P2_dec (substring n (length s - n) s))
          || F n' _
     *)


  Definition split : 
    {exists s1, exists s2, s = s1 ++ s2 /\ P1 s1 /\ P2 s2}
    + {forall s1 s2, s = s1 ++ s2 -> ~ P1 s1 \/ ~ P2 s2}.
    refine (Reduce (split' (n := length s) _)); crush; eauto.
  Defined.

End split.

Implicit Arguments split [P1 P2].

(* begin hide *)
Lemma app_empty_end : forall s, s ++ "" = s.
  induction s; crush.
Qed.

Hint Rewrite app_empty_end.

Lemma substring_self : forall s n,
  n <= 0
  -> substring n (length s - n) s = s.
  induction s; substring.
Qed.

Lemma substring_empty : forall s n m,
  m <= 0
  -> substring n m s = "".
  induction s; substring.
Qed.

Hint Rewrite substring_self substring_empty using omega.

Lemma substring_split' : forall s n m,
  substring n m s ++ substring (n + m) (length s - (n + m)) s
  = substring n (length s - n) s.
  Hint Rewrite substring_split.

  induction s; substring.
Qed.

Lemma substring_stack : forall s n2 m1 m2,
  m1 <= m2
  -> substring 0 m1 (substring n2 m2 s)
  = substring n2 m1 s.
  induction s; substring.
Qed.

Ltac substring' :=
  crush;
  repeat match goal with
           | [ |- context[match ?N with O => _ | S _ => _ end] ] => case_eq N; crush
         end.

Lemma substring_stack' : forall s n1 n2 m1 m2,
  n1 + m1 <= m2
  -> substring n1 m1 (substring n2 m2 s)
  = substring (n1 + n2) m1 s.
  induction s; substring';
    match goal with
      | [ |- substring ?N1 _ _ = substring ?N2 _ _ ] =>
        replace N1 with N2; crush
    end.
Qed.

Lemma substring_suffix : forall s n,
  n <= length s
  -> length (substring n (length s - n) s) = length s - n.
  induction s; substring.
Qed.

Lemma substring_suffix_emp' : forall s n m,
  substring n (S m) s = ""
  -> n >= length s.
  induction s; crush;
    match goal with
      | [ |- ?N >= _ ] => destruct N; crush
    end;
    match goal with
      [ |- S ?N >= S ?E ] => assert (N >= E); [ eauto | omega ]
    end.
Qed.

Lemma substring_suffix_emp : forall s n m,
  substring n m s = ""
  -> m > 0
  -> n >= length s.
  destruct m as [ | m]; [crush | intros; apply substring_suffix_emp' with m; assumption].
Qed.

Hint Rewrite substring_stack substring_stack' substring_suffix
  using omega.

Lemma minus_minus : forall n m1 m2,
  m1 + m2 <= n
  -> n - m1 - m2 = n - (m1 + m2).
  intros; omega.
Qed.

Lemma plus_n_Sm' : forall n m : nat, S (n + m) = m + S n.
  intros; omega.
Qed.

Hint Rewrite minus_minus using omega.
(* end hide *)

(* dec_star: searches through ways of splitting a string 
   for the kleene star *)

Section dec_star.
  Variable P : string -> Prop.
  Variable P_dec : forall s, {P s} + {~ P s}.

  (* begin hide *)
  Hint Constructors star.

  Lemma star_empty : forall s,
    length s = 0
    -> star P s.
    destruct s; crush.
  Qed.

  Lemma star_singleton : forall s, P s -> star P s.
    intros; rewrite <- (app_empty_end s); auto.
  Qed.

  Lemma star_app : forall s n m,
    P (substring n m s)
    -> star P (substring (n + m) (length s - (n + m)) s)
    -> star P (substring n (length s - n) s).
    induction n; substring;
      match goal with
        | [ H : P (substring ?N ?M ?S) |- _ ] =>
          solve [ rewrite <- (substring_split S M); auto
            | rewrite <- (substring_split' S N M); auto ]
      end.
  Qed.

  Hint Resolve star_empty star_singleton star_app.

  Variable s : string.

  Lemma star_inv : forall s,
    star P s
    -> s = ""
    \/ exists i, i < length s
      /\ P (substring 0 (S i) s)
      /\ star P (substring (S i) (length s - S i) s).
    Hint Extern 1 (exists i : nat, _) =>
      match goal with
        | [ H : P (String _ ?S) |- _ ] => exists (length S); crush
      end.

    induction 1; [
      crush
      | match goal with
          | [ _ : P ?S |- _ ] => destruct S; crush
        end
    ].
  Qed.    

  Lemma star_substring_inv : forall n,
    n <= length s
    -> star P (substring n (length s - n) s)
    -> substring n (length s - n) s = ""
    \/ exists l, l < length s - n
      /\ P (substring n (S l) s)
      /\ star P (substring (n + S l) (length s - (n + S l)) s).
    Hint Rewrite plus_n_Sm'.

    intros;
      match goal with
        | [ H : star _ _ |- _ ] => generalize (star_inv H); do 3 crush; eauto
      end.
  Qed.
  (* end hide *)

  (* dec_star'' implements a single iterations of
     star--it tries to find some prefix matching P 
     and checks if some P' holds on the remainder
     of the string *)

  Section dec_star''.
    Variable n : nat.

    Variable P' : string -> Prop.
    Variable P'_dec : forall n' : nat, n' > n
      -> {P' (substring n' (length s - n') s)}
      + {~ P' (substring n' (length s - n') s)}.

    Definition dec_star'' : forall l : nat,
      {exists l', S l' <= l
        /\ P (substring n (S l') s) 
        /\ P' (substring (n + S l') (length s - (n + S l')) s)}
      + {forall l', S l' <= l
        -> ~ P (substring n (S l') s)
        \/ ~ P' (substring (n + S l') (length s - (n + S l')) s)}.

      refine (fix F (l : nat) : {exists l', S l' <= l
        /\ P (substring n (S l') s) 
        /\ P' (substring (n + S l') (length s - (n + S l')) s)}
      + {forall l', S l' <= l
        -> ~ P (substring n (S l') s)
        \/ ~ P' (substring (n + S l') (length s - (n + S l')) s)} :=

      match l return {exists l', S l' <= l
        /\ P (substring n (S l') s) 
        /\ P' (substring (n + S l') (length s - (n + S l')) s)}
      + {forall l', S l' <= l
        -> ~ P (substring n (S l') s)
        \/ ~ P' (substring (n + S l') (length s - (n + S l')) s)} 
      with

        | O => _

        | S l' =>
          (P_dec (substring n (S l') s) && P'_dec (n' := n + S l') _)
          || F l'
      end); clear F; crush; eauto 7;
      match goal with
        | [ H : ?X <= S ?Y |- _ ] => destruct (eq_nat_dec X (S Y)); crush
      end.
    Defined.
  End dec_star''.

  (* begin hide *)
  Lemma star_length_contra : forall n,
    length s > n
    -> n >= length s
    -> False.
    crush.
  Qed.

  Lemma star_length_flip : forall n n',
    length s - n <= S n'
    -> length s > n
    -> length s - n > 0.
    crush.
  Qed.

  Hint Resolve star_length_contra star_length_flip substring_suffix_emp.
  (* end hide *)
  
  Definition dec_star' : forall n n' : nat, 
    length s - n' <= n -> 
    {star P (substring n' (length s - n') s)}
    + {~ star P (substring n' (length s - n') s)}.
    
    refine (fix F (n n' : nat) : length s - n' <= n ->
      {star P (substring n' (length s - n') s)}
      + {~ star P (substring n' (length s - n') s)} :=

      match n with
        | O => fun _ => Yes

        | S n'' => fun _ =>
          le_gt_dec (length s) n'
          || dec_star'' (n := n') (star P)
            (fun n0 _ => Reduce (F n'' n0 _)) (length s - n')

      end); clear F; crush; eauto;
    match goal with
      | [ H : star _ _ |- _ ] => apply star_substring_inv in H; crush; eauto
    end;
    match goal with
      | [ H1 : _ < _ - _, H2 : forall l' : nat, _ <= _ - _ -> _ |- _ ] =>
        generalize (H2 _ (lt_le_S _ _ H1)); tauto
    end.
  Defined.

  Definition dec_star : {star P s} + {~ star P s}.
    refine (Reduce (dec_star' (n := length s) 0 _)); 
    crush.
  Defined.
End dec_star.

(* begin hide *)
Lemma app_cong : forall x1 y1 x2 y2,
  x1 = x2
  -> y1 = y2
  -> x1 ++ y1 = x2 ++ y2.
  congruence.
Qed.

Hint Resolve app_cong.
(* end hide *)


Definition matches : forall P (r : regexp P) s, {P s} + {~ P s}.

  refine (fix F P (r : regexp P) s : {P s} + {~ P s} :=
    match r in regexp P0 return {P0 s} + {~P0 s} with
      | Char ch => string_dec s (String ch "")
      | Concat _ _ r1 r2 => Reduce (split (F _ r1) (F _ r2) s)
      | Or _ _ r1 r2 => F _ r1 s || F _ r2 s
      | Star _ r => dec_star _ _ _
    end); crush;
  match goal with
    | [ H : _ |- _ ] => generalize (H _ _ (eq_refl _))
  end; tauto.
Defined.

(* Exercise (15 min): Add a wildcard regular expression
   to the above example which matches any string consisting
   of a single character. Incorporate it into matches
   by means of a dec_wild function which checks if a 
   string is a single character. *)
   

(* begin hide *)
Example hi := Concat (Char "h"%char) (Char "i"%char).
Eval hnf in matches hi "hi".
Eval hnf in matches hi "bye".

Example a_b := Or (Char "a"%char) (Char "b"%char).
Eval hnf in matches a_b "".
Eval hnf in matches a_b "a".
Eval hnf in matches a_b "aa".
Eval hnf in matches a_b "b".
(* end hide *)

Example a_star := Star (Char "a"%char).
Eval hnf in matches a_star "".
Eval hnf in matches a_star "a".
Eval hnf in matches a_star "b".
Eval hnf in matches a_star "aa".

