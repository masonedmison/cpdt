(**Reasoning About Equality Proofs*)

Require Import Eqdep JMeq List.

Require Import CpdtTactics.

Set Implicit Arguments.

(** * The Definitional Equality *)

Definition pred' (x : nat) :=
  match x with
    | O => O
    | S n' => let y := n' in y 
  end.

Theorem reduce_me : pred' 1 = 0.

  cbv delta. (* Unfolding Global defs *)

  cbv beta. (* Simplify the application of a known function *)

  cbv iota. (* Simplifies single [match] terms *)

  cbv beta.

  cbv zeta. (* Replace let instruction into body *)

  reflexivity.
Qed.

(* Exercise (optional - 2 minutes) : use the reductions manually to prove the following Theorem *)

Theorem reduce_me' : plus 2 0 = 2.
Admitted.

(*End Exercise*)

Definition id (n : nat) := n.

Eval compute in fun x => id x. (* Here compute unfold id *)

Fixpoint id' (n : nat) := n.

Eval compute in fun x => id' x. (* But not here *)

Fixpoint addLists (ls1 ls2 : list nat) : list nat :=
  match ls1, ls2 with
    | n1 :: ls1' , n2 :: ls2' => n1 + n2 :: addLists ls1' ls2'
    | _, _ => nil
  end.

Eval compute in fun ls => addLists nil ls.

Eval compute in fun ls => addLists ls nil.

(* Version of [addLists] with [ls2] marked as 
recursive. *)

Fixpoint addLists' (ls1 ls2 : list nat) {struct ls2} : list nat :=
  match ls1, ls2 with
    | n1 :: ls1' , n2 :: ls2' => n1 + n2 :: addLists' ls1' ls2'
    | _, _ => nil
  end.

Eval compute in fun ls => addLists' ls nil.

CoInductive stream (A : Type) : Type :=
  | SCons : A -> stream A -> stream A.

Definition head (A:Type) (s : stream A) :=
  match s with
  | SCons a s' => a
  end.

CoFixpoint same (A : Type) (a : A) : stream A := SCons a (same a).

Eval simpl in (same 4).

Eval simpl in (head (same 4)).


(*
Coq's eq relation is also called propositional equality because it reifies 
definitional equality as something that may or not holds.
*)

Print eq.

(** * Proof Methods With The Standard eq Relation *)

Section fhlist.
  Variable A : Type.
  Variable B : A -> Type.

  Fixpoint fhlist (ls : list A) : Type :=
    match ls with
      | nil => unit
      | x :: ls' => B x * fhlist ls'
    end%type.

End fhlist.

Section fhapp_def.
  Variable A : Type.
  Variable B : A -> Type.
  Variable elm : A.

  Fixpoint fhapp (ls1 ls2 : list A)
    : fhlist B ls1 -> fhlist B ls2 -> fhlist B (ls1 ++ ls2) :=
    match ls1 with
      | nil => fun _ hls2 => hls2
      | _ :: _ => fun hls1 hls2 => (fst hls1, fhapp _ _ (snd hls1) hls2)
    end.

End fhapp_def.

Implicit Arguments fhapp [A B ls1 ls2].


Section eq_proofs.
  Variable A : Type.
  Variable B : A -> Type.
  Variable elm : A.

  Lemma lemma1 : forall x (pf : x = elm), O = match pf with eq_refl => O end.
    destruct pf; reflexivity.
  Qed.
  
  Print lemma1.
  
  (* Manual Proof *)
  Definition lemma1' (x : A) (pf : x = elm) :=
    match pf return (0 = match pf with
                           | eq_refl => 0
                         end) with
      | eq_refl => eq_refl 0 
    end.

 Check lemma1'.


  Lemma lemma2 : forall (x : A) (pf : x = x), O = match pf with eq_refl => O end.
    destruct pf; reflexivity.
  Qed.
  
  Print lemma2.

  (* Manual Proof *)
  Definition lemma2' :=
    fun (x : A) (pf : x = x) =>
      match pf return (0 = match pf with
                             | eq_refl => 0
                           end) with
        | eq_refl => eq_refl 0
      end.


  Lemma lemma3 (ls1 ls2 : list A) (hls1 : fhlist B ls1) (hls2 : fhlist B ls2) 
  (pf : ls1 ++ ls2 = ls1 ++ ls2): 
  fhapp hls1 hls2 = match pf with eq_refl => fhapp hls1 hls2 end.
    (*destruct pf.*)
  Abort.
  
  (* Proof object *)
  Definition lemma3' := 
    fun (ls1 ls2 : list A) (hls1 : fhlist B ls1) (hls2 : fhlist B ls2) 
      (pf : ls1 ++ ls2 = ls1 ++ ls2) =>
      match pf return (fhapp hls1 hls2 = match pf with
                                           | eq_refl => fhapp hls1 hls2
                                         end) with
        | eq_refl => eq_refl _
      end.

Check lemma3'.      
   
  Lemma lemma4 : forall (x : A) (pf : x = x), pf = eq_refl x.
    intros.
    (*simple destruct pf.*)
    (*destruct pf.*)

  Abort.
    
  (* Proof object *)
(*
  Definition lemma4' :=
    fun (x : A) (pf : x = x) =>
      match pf as pf' in (_ = x') return (pf' = eq_refl x') with
        | eq_refl => eq_refl _
      end.
*)


(* To prove this lemma, we must use something else... *)

  Lemma lemma4 : forall (x : A) (pf : x = x), pf = eq_refl x.
    intros; apply UIP_refl.
  Qed.

End eq_proofs.

  Check UIP_refl.
  
  Print Assumptions UIP_refl.

(* UIP_refl is proved using an axiom: eq_rect_eq *)

  Import Eq_rect_eq.

  Print eq_rect_eq.

  Eval compute in (forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
    x = eq_rect p Q x p h).



(* Exercise (25 minutes) : Axioms equivalence *) 

(* Here we proove the equivalence of 4 statements about dependent equality *)

Section equivalences.

Variable U : Type.

(* Streicher's K axiom *)
Print Streicher_K_.
(* Uniqueness of reflexive identity proofs *)
Print UIP_refl_.
(* Uniqueness of identity proofs *)
Print UIP_.
(* Invariance by substitution of reflexive equality proofs *)
Print Eq_rect_eq.
(* Injectivity of dependent equality*)
Print Eq_dep_eq.

Lemma eq_rect_eq_eq_dep_eq : Eq_rect_eq U -> Eq_dep_eq U.
  (*TODO*)
  Admitted.

Lemma eq_dep_eq__UIP : Eq_dep_eq U -> UIP_ U.
  (*TODO*)
  Admitted.

Lemma UIP__UIP_refl : UIP_ U -> UIP_refl_ U.
  (*TODO*)
  Admitted.

Lemma UIP_refl__Streicher_K : UIP_refl_ U -> Streicher_K_ U.
  (*TODO*)
  Admitted.

Lemma Streicher_K__eq_rect_eq : Streicher_K_ U -> Eq_rect_eq U.
  (*TODO*)
  Admitted.

End equivalences.

(*End Exercise*)




(** * Type-Casts in Theorem Statements *)

Section fhapp.
  Variable A : Type.
  Variable B : A -> Type.

  (** We might like to prove that [fhapp] is associative.**)

(*  
   Theorem fhapp_ass : forall ls1 ls2 ls3
    (hls1 : fhlist B ls1) (hls2 : fhlist B ls2) (hls3 : fhlist B ls3),
    fhapp hls1 (fhapp hls2 hls3) = fhapp (fhapp hls1 hls2) hls3.
*)

(* we must give coq a proof that those two types are equal *)

  Theorem fhapp_ass : forall ls1 ls2 ls3
    (pf : (ls1 ++ ls2) ++ ls3 = ls1 ++ (ls2 ++ ls3))
    (hls1 : fhlist B ls1) (hls2 : fhlist B ls2) (hls3 : fhlist B ls3),
    fhapp hls1 (fhapp hls2 hls3)
    = match pf in (_ = ls) return fhlist _ ls with
        | eq_refl => fhapp (fhapp hls1 hls2) hls3
      end.
    induction ls1; crush.
    rewrite (UIP_refl _ _ pf).
    reflexivity.
    rewrite (IHls1 _ _ H1).
    generalize pf H1.
    generalize (fhapp (fhapp b hls2) hls3).
    rewrite app_ass.
    (* Alternative:*)
    (*
    generalize pf H1.
    rewrite <- app_ass.
    *)
    intros.
    rewrite (UIP_refl _ _ pf0).
    rewrite (UIP_refl _ _ H2).
    reflexivity.
  Qed.
End fhapp.


(* Exercise 10 minutes - Inductive Heterogeneous lists *)
(* Prove the same theorem for inductive heterogeneous lists *)
Section hlist.

 Variable A : Type.
 Variable B : A -> Type.

 Inductive hlist : list A -> Type :=
   | HNil : hlist nil
   | HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).

End hlist.

Implicit Arguments HNil [A B].
Implicit Arguments HCons [A B x ls].

Section happ.

  Variable A : Type.
  Variable B : A -> Type.

  Fixpoint happ (ls1 ls2 : list A)  (hl1: hlist B ls1) (hl2 : hlist B ls2) : 
hlist B (ls1 ++ ls2) :=
    match hl1 in hlist _ l1 return hlist B (l1 ++ ls2) with
      | HNil => hl2
      | HCons _ _ x hl1' => HCons x (happ hl1' hl2)
    end.

  Theorem happ_ass : forall ls1 ls2 ls3 (hls1 : hlist B ls1) (hls2 : hlist B ls2)
    (hls3 : hlist B ls3)
    (pf : (ls1 ++ ls2) ++ ls3 = ls1 ++ (ls2 ++ ls3)),
    happ hls1 (happ hls2 hls3) 
    = match pf in (_ = ls) return hlist _ ls with
        | eq_refl => happ (happ hls1 hls2) hls3
      end.
    Admitted.
End happ.

Implicit Arguments happ [A B ls1 ls2].

(*End Exercise*)


(* Exercise : 45 minutes - unject_inverse *)
(* Our favorite length-indexed lists *)

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

  Fixpoint inject (ls : list A) : ilist (length ls) :=
    match ls with
      | nil => Nil
      | h :: t => Cons h (inject t)
    end.

  Fixpoint unject n (ls : ilist n) : list A :=
    match ls with
      | Nil => nil
      | Cons _ h t => h :: unject t
    end.

  (* 
  Jennifer proved that [unject (inject ls) = ls] and asked us to prove the inverse, 
that is [inject (unject ls) = ls]. However, stated like this, the theorem will not 
typecheck, just like fhapp_ass. Modify the statement like Adam did for fhapp_ass and 
prove it using the same proof technique.
  *)

End ilist. 

(* End Exercise *)




(** * Heterogeneous Equality *)

Print JMeq.
Print eq.

Infix "==" := JMeq (at level 70, no associativity).

Definition UIP_refl' (A : Type) (x : A) (pf : x = x) : pf == eq_refl x :=
  match pf return (pf == eq_refl _) with
    | eq_refl => JMeq_refl _
  end.

Lemma lemma5 : forall (A : Type) (x : A) (pf : x = x),
  O = match pf with eq_refl => O end.
  intros; rewrite (UIP_refl' pf); reflexivity.
Qed.

Check JMeq_eq. (* This is an axiom !*)

Section fhapp'.
  Variable A : Type.
  Variable B : A -> Type.

  Theorem fhapp_ass' : forall ls1 ls2 ls3 (hls1 : fhlist B ls1) (hls2 : fhlist B ls2)
    (hls3 : fhlist B ls3),
    fhapp hls1 (fhapp hls2 hls3) == fhapp (fhapp hls1 hls2) hls3.
    induction ls1; crush.
    generalize (fhapp b (fhapp hls2 hls3))
      (fhapp (fhapp b hls2) hls3)
      (IHls1 _ _ b hls2 hls3).
    rewrite app_ass.
    intros f f0 H; rewrite H; reflexivity.
  Qed.

End fhapp'. 


(* Exercise - 10 minutes - Inductive Heterogeneous lists #2 *)
(* Use the same technique to prove the following theorem *)
Section happ'.

  Variable A : Type.
  Variable B : A -> Type.

  Theorem happ_ass' : forall ls1 ls2 ls3 (hls1 : hlist B ls1) (hls2 : hlist B ls2)
    (hls3 : hlist B ls3),
    happ hls1 (happ hls2 hls3) == happ (happ hls1 hls2) hls3.
    Admitted.

End happ'.

(*End Exercise*)



(* Exercise (20 minutes): unject_inverse #2*)
(* Prove the following theorem using Adam's proof technique *)
Section ilist'.
  Variable A : Set.

  Theorem unject_inverse' : forall n (ls : ilist A n),
    ls == inject (unject ls).
  Admitted.

End ilist'.

(*End Exercise*)



Print Assumptions fhapp_ass'.

Lemma pair_cong : forall A1 A2 B1 B2 (x1 : A1) (x2 : A2) (y1 : B1) (y2 : B2),
  x1 == x2
  -> y1 == y2
  -> (x1, y1) == (x2, y2).
  intros until y2; intros Hx Hy; rewrite Hx; rewrite Hy; reflexivity.
Qed.

Hint Resolve pair_cong.

Section fhapp''.
  Variable A : Type.
  Variable B : A -> Type.

  Theorem fhapp_ass'' : forall ls1 ls2 ls3 (hls1 : fhlist B ls1) (hls2 : fhlist B ls2)
    (hls3 : fhlist B ls3),
    fhapp hls1 (fhapp hls2 hls3) == fhapp (fhapp hls1 hls2) hls3.
    induction ls1; crush.
  Qed.
End fhapp''.

Print Assumptions fhapp_ass''.

(* Lemma used when rewriting a '=' term *)
Check eq_ind_r.
Check eq_ind.

(* Lemma used when rewriting a '==' term *)
Check internal_JMeq_rew_r. 

Check JMeq_ind_r.

Theorem out_of_luck : forall n m : nat,
  n == m
  -> S n == S m.
  intros n m H.

(* We need to abstract n in order to apply JMeq_ind_r *)

  pattern n.

  apply JMeq_ind_r with (x := m). auto.


(*  However, we run into trouble trying to get the goal into a form compatible with
 [internal_JMeq_rew_r.] *)
  Undo 2.
(*pattern nat, n.*)

Abort.

Print internal_JMeq_rew_r.

Lemma pair_cong' : forall A1 A2 B1 B2 (x1 : A1) (x2 : A2) (y1 : B1) (y2 : B2),
  x1 == x2
  -> y1 == y2
  -> (x1, y1) == (x2, y2).
intros until y2; intros Hx Hy.
pattern A1, x1. (* Here we can abstract x1 _and_ its type *) 
apply internal_JMeq_rew_r with (B:=A2) (b:=x2).
pattern B1, y1. apply internal_JMeq_rew_r with (B:=B2) (b:=y2). (*etc...*) Abort.


(* Exercise (15 minutes) - Magic lemma ?


1.
In the previous exercise (unject_inverse #2), do you see when [rewrite] used [JM_eq] ?

Do you think it would be possible to come up with a lemma such as [pair_cong] to
help [rewrite] not to use this axiom ?
If yes, write this lemma, prove it, add it as a hint, and prove [unject_inverse''].
If not, explain what is the problem.

2.
Same questions with (Inductive Heterogeneous lists #2)
*)

(*End exercise*)


(** * Equivalence of Equality Axioms *)

(*  The axioms presented here are _logically_ equivalent.  *)

(* We use UIP_refl' to prove UIP_refl *)

Lemma UIP_refl'' : forall (A : Type) (x : A) (pf : x = x), pf = eq_refl x.
  intros; rewrite (UIP_refl' pf); reflexivity.
Qed.

(* We can define [JMeq] in a way that satisfies the same interface as the 
combination of the [JMeq] module's inductive definition and axiom. *)

Definition JMeq' (A : Type) (x : A) (B : Type) (y : B) : Prop :=
  exists pf : B = A, x = match pf with eq_refl => y end.

Infix "===" := JMeq' (at level 70, no associativity).

Theorem JMeq_refl' : forall (A : Type) (x : A), x === x.
  intros; unfold JMeq'; exists (eq_refl A); reflexivity.
Qed.

Theorem JMeq_eq' : forall (A : Type) (x y : A),
  x === y -> x = y.
  unfold JMeq'; intros.
  destruct H.
  rewrite H.
  rewrite (UIP_refl _ _ x0); reflexivity.
Qed.

(** * Equality of Functions *)

Require Import FunctionalExtensionality.
About functional_extensionality.

Theorem two_funs : (fun n => n) = (fun n => n + 0).
  apply functional_extensionality; crush.
Qed.

(* The same axiom can help us prove equality of types, where we need to "reason under 
quantifiers." *)

Theorem forall_eq : (forall x : nat, match x with
                                      | O => True
                                      | S _ => True
                                    end)
  = (forall _ : nat, True).

  change ((forall x : nat, (fun x => match x with
                                       | 0 => True
                                       | S _ => True
                                     end) x) = (nat -> True)).

  rewrite (functional_extensionality (fun x => match x with
                                                 | 0 => True
                                                 | S _ => True
                                               end) (fun _ => True));

  reflexivity || destruct x; constructor.

Qed.


(* Interestingly, there is another axiom about functional extensionality *)
About functional_extensionality_dep.

Theorem funct_ext : forall (A B : Type) (f g : A -> B),
 (forall x, f x = g x) -> f = g.
 intros;
 apply functional_extensionality_dep; assumption.
 Qed.



(* Exercise (5 minutes) - Two parameters functions *)

Theorem funct_ext_2param : forall (A B C : Type) (f g : A -> B -> C),
(forall (x : A) (y : B), f x y = g x y) -> f = g.
Admitted. 

(*End Exercise*)


(* Exercise - Optional - Open Challenge 
(Open in the sense that I couldn't do it, it might be easy :D) *)
(* Prove that quickSort and mergesort are equal (we defined them in Chapter 7) *)

(*End Exercise*)

(* 
If you are curious about axioms in coq, you might want to check 
http://coq.inria.fr/cocorico/CoqAndAxioms 

(Edited by Arthur Charguéraud, who sounds to be a smart French guy !)
*)

