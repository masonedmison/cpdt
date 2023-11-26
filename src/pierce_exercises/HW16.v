Add LoadPath "../src/".
Require Import List.
Require Import DepList CpdtTactics.

Set Implicit Arguments.
Open Scope type_scope.

Check 0.    (* : nat *)
Check nat.  (* : Set *)
Check Set.  (* : Type *)
Check Type. (* : Type *)

Set Printing Universes.
Check nat.  (* : nat *)
Check Set.  (* : Type  [Set + 1] *)
Check Type. (* : Type  [Top.5 + 1] *)







(** Predicativity *)

Check forall X : nat, fin X. (* : Set *)

Check forall X : Set, X.     (* : Type [max(Set, Set+1)] *)

Check forall X : Type, X.
  (*  forall X : Type [Top.6], X
      : Type [max(Top.6, (Top.6)+1)]   *)


(* The typing rule is

   G ⊢ T : Type(i)    i≤ k    G, x:T ⊢ U : Type(j)   j ≤ k
  --------------------------------------------------------
      G ⊢ ∀ x:T,U : Type(k)    

  http://coq.inria.fr/refman/Reference-Manual006.html#toc29 .
*)  


(* A forall type is _predicative_ if it does not
    quantify over itself. *)

Definition id : forall (T : Type), T->T
 := fun T t => t.

Check id 0.
Check id S.
Check id Set.
Check id Type.
(*
Check id id.
*)

(* For clarity we can define types with explicit levels. *)
Definition Type4 := Type.
Definition Type3 : Type4 := Type.
Definition Type2 : Type3 := Type.
Definition Type1 : Type2 := Type.
Definition Type0 : Type1 := Type.
















(** ** Inductive Definitions *)

(*
Inductive exp : Set -> Set :=
| Const : forall T : Set, T -> exp T
| Pair : forall T1 T2, exp T1 -> exp T2 -> exp (T1 * T2)
| Eq : forall T, exp T -> exp T -> exp bool.

 Error: Large non-propositional inductive types must be in Type.
*)

Inductive exp : Type -> Type :=
| Const : forall T, T -> exp T     (* T defaults to "Type" *)
| Pair : forall T1 T2, exp T1 -> exp T2 -> exp (T1 * T2)
| Eq : forall T, exp T -> exp T -> exp bool.

Check Const 0.
Check Pair (Const 0) (Const tt).
Check Eq (Const Set) (Const Type).
(*
Check Const exp.
  Error: universe inconsistency *)

Print exp. 
  (* The sort of the datatype is bigger than the sorts of all
     constructor arguments, similar to the rule for arrow types *)

(* What about the sort of the index of the datatype? *)
(* Print Universes. *)
(* We get a constraint from each application of exp in the definition. *)
(*
Print Sorted Universes.
*)


(* Exercise (3 min).
   Change the occurences of Type below into
     Type0, Type1, Type2, ...
   in some suitable way. *)
Module Exercise1.

Inductive exp : Type -> Type :=
| Const : forall (T : Type), T -> exp T
| Pair : forall (T1 T2 : Type), exp T1 -> exp T2 -> exp (T1 * T2)
| Eq : forall (T : Type), exp T -> exp T -> exp bool.

Check Eq (Const Set) (Const Type).

End Exercise1.





(* What about _parameters_ of inductive definitions? *)
Print prod.  (* max, not max+1. *)

Check (3, (4, 5)).


Inductive prod' : Type -> Type -> Type :=
| pair' : forall A B : Type, A -> B -> prod' A B.

(*
Check (pair' 3 (pair' 4 5)).
*)

(* Sometimes we can use parameters instead of indices 
   to make a type "fit" in Set. *)
Inductive exp1 : nat ->  Set :=
  | var1 : forall n, fin n -> exp1 n
  | app1 : forall n, exp1 n -> exp1 n -> exp1 n
  | abs1 : forall n, exp1 (S n) -> exp1 n.

Inductive exp2 (V : Set) : Set :=
  | var2 : V -> exp2 V
  | app2 : exp2 V -> exp2 V -> exp2 V
  | abs2 : exp2 (option V) -> exp2 V.


(* (fake) sort polymorphism. *)
Unset Printing Universes.

Inductive foo (A : Type) : Type :=
| Foo : A -> foo A.

Check foo nat.
Check foo Set.
Check foo True. 

(* The prod type from the standard library is sort-polymorphic. *)
Check (nat*nat).
Check (True*False).

Check (option nat).
Check (option False).  (* not Prop, because of allowable elimination sorts *)

(* One quirk with sort-polymorphism. *)
Inductive bar : Type := Bar : bar.
Check bar.
Check foo.
Print foo.













(*** Subsumption (subtyping for sorts) *)
Check Type1.
Check (Type1 : Type4).

(* also: *)
Check (fun (t:Type3) => t).
Check ((fun (t:Type3) => t)  : Type3 -> Type4).

(* ...but: *)
(* 
Check ((fun (t:Type3) => t)  : Type1 -> Type4).
Check ((nat,nat) : (Type3 * Type3)).
*)

(* We have both
     Set : Type1 : Type2 : ... 
     Set < Type1 < Type2 < ...

  From an intuitive set-theoretic point of view, 
     Set ∈ Type1 ∈ Type2 ∈ ... 
  and
     Set ⊆ Type1 ⊆ Type2 ⊆ ...
*)
    
















(**Baffling Messages about Inability to Unify *)

Theorem symmetry : forall A B : Type,
  A = B -> B = A.
  intros ? ? H; rewrite H; reflexivity.
Qed.

Theorem illustrative_but_silly_detour : unit = unit.
(*
  apply symmetry.
*)
Abort.

Theorem illustrative_but_silly_detour : (unit : Type) = unit.
  apply symmetry; reflexivity.
Qed.

Unset Printing All.

Theorem obviously_false : 
 exists n : nat, forall m : nat, n = m.
  eexists. intros m. 
  (* reflexivity. *)
  Show Existentials.
Abort.











(** * The [Prop] Universe *)


Check (2 = 2).

Check Prop.

Check (forall (A:Type) (a:A),  a=a).

(* The rule is

    G ⊢ T : s    s ∈  S    G ⊢ U : Prop
   ------------------------------------------------
    G ⊢ ∀ x:T,U : Prop

   Impredicative!
*)

Check forall P Q : Prop, P \/ Q -> Q \/ P.



(* Elimination restriction *)

Print sig.
(*
  Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> sig P
    *)

Print ex.
(*
  Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> ex P
*)

Definition projS A (P : A -> Prop) (x : sig P) : A :=
  match x with
    | exist v _ => v
  end.

(*
Definition projE A (P : A -> Prop) (x : ex P) : A :=
  match x with
    | ex_intro v _ => v
  end.
*)

(* Why? 
   - Extraction
   - Consistency *)



(* Impredicativity works for datatypes too. *)
Open Scope nat_scope.

Inductive expP : Type -> Prop :=
| ConstP : forall T, T -> expP T
| PairP : forall T1 T2, expP T1 -> expP T2 -> expP (T1 * T2)
| EqP : forall T, expP T -> expP T -> expP bool.


(* A more reasonable use. *)
Inductive eqPlus : forall T, T -> T -> Prop :=
| Base : forall T (x : T), eqPlus x x
| Func : forall dom ran (f1 f2 : dom -> ran),
  (forall x : dom, eqPlus (f1 x) (f2 x))
  -> eqPlus f1 f2.

Check (Base 0).

Check (Func (fun n => n) (fun n => 0 + n) (fun n => Base n)).

Check (Base (Base 1)).


(* Note that Coq has an -impredicative-set option. *)

(* The sort hierachy looks like

    Set 
        : Type0 : Type1 : ...
    Prop

    If you want to live in the future, there is: 
*)
(*
Require Import SetIsType.
*)


(* What's wrong with Type:Type anyway?

   The following is from the Coq-club thread
     "Simple demonstration that the type hierarchy is needed for consistency?"
     https://sympa.inria.fr/sympa/arc/coq-club/2012-05/msg00015.html

   *)

(* Sets a la Aczel  ("sets as trees") *)
Inductive V : Type := 
  V_const : forall {X:Type}, (X -> V) -> V.

(* Set membership *)
Inductive V_rel : V -> V -> Prop :=
  V_rel_def : forall {X:Type} (f:X -> V) (x:X), V_rel (f x) (V_const f).

Lemma V_rel_inv : forall y X (f:X -> V), V_rel y (V_const f) -> exists x, y = f x.
  intros y X f H. inversion H; eauto.
Qed.

(* E.g. *)
Definition EmptySet : V 
  := V_const (fun (e:False) => match e with end).
Definition PairSet (x y: V) 
  := V_const (fun (b:bool) => if b then x else y).
(*
Definition AllSets 
  := V_const (fun (v:V) => v). *)

(* The proper class of sets not containing themselves. *)
Definition RT : Type := {x:V | ~V_rel x x}.

Theorem Russell_paradox : False.
  (* Define the Russell set. This is the key step that causes universe inconsistency.
     If we defined this at top-level, it would already fail. *)
  set (russell := V_const (fun x:RT => proj1_sig x)).
     
  (* Show that the Russell set fails to contain itself. *)
  assert (Hrussell1 : ~V_rel russell russell).
    intro H. subst russell. 
    apply V_rel_inv in H. destruct H as [[x H] Hx].
    apply H. simpl in Hx. pattern x at 2. rewrite <- Hx.
    apply (@V_rel_def RT (@proj1_sig _ _) (exist _ x H)).

  (* Therefore, the Russell set contains itself. *)
  assert (Hrussell2 : V_rel russell russell).
    apply (@V_rel_def RT (@proj1_sig _ _) (exist _ russell Hrussell1)).

  (* Thus, contradiction. *)
  exact (Hrussell1 Hrussell2). (* Coq reports "Proof completed." *)

Show Proof. (* We've generated a complete proof term... *)
(*
Qed. Now the typechecking core discovers our mistake: Universe inconsistency. *)
Abort.




(* Exercise (20 min): Church encodings. *)
Section Exercise2. 

(* The classic example where you want impredicativity is
   to encode inductive types as functions.
   
   For instance, here is the classic representation of natural
   numbers as higher-order functions: *)

Definition iNat : Prop := forall (X:Prop), (X->X) -> X -> X.

Definition  zero : iNat
 := fun X f z => z.
Definition succ : iNat -> iNat 
 := fun n => fun X f z => f (n X f z).

(* e.g. the number 3 is represented as the function which 
   applies its argument three times. *) 
Eval compute in (succ (succ (succ zero))).


(* Write functions to add, multiply and exponentiate, and verify that
   they compute as expected: *)
Definition plus : iNat -> iNat -> iNat.
Admitted.

Theorem plus_spec : plus (succ (succ zero)) (succ (succ zero))
                    = (succ (succ (succ (succ zero)))).
Admitted.

Definition mult : iNat -> iNat -> iNat.
Admitted.

Theorem mult_spec : mult (succ (succ zero)) (succ (succ (succ zero)))
                    = succ (succ (succ (succ (succ (succ zero))))).
Admitted.

Definition expt : iNat -> iNat -> iNat.
Admitted.

Theorem expt_spec : expt (succ (succ zero)) (succ (succ (succ zero)))
                    = (succ (succ (succ (succ (succ (succ (succ (succ (succ zero))))))))).
Admitted.

(* Of course, we would also like to prove theorems about numbers.
   At as a basic example, discrimination of constructors.

   Either prove the following theorem, or explain why you cannot: *) 
Theorem iNat_discrim : forall n, succ n <> zero.
Admitted.

End Exercise2.

Module Exercise3.

(* In frustration with the impredicative encoding, we turn to 
   the following "impredicative encoding" (in Type rather than Prop). *)

Definition pNat := forall (X:Type), (X->X) -> X -> X.

Definition  zero : pNat
 := fun X f z => z.
Definition succ : pNat -> pNat 
 := fun n => fun X f z => f (n X f z).

(* Prove discrimination for this representation. 
   How many levels of Type does your proof use? *)

Theorem pNat_discrim : forall n, succ n <> zero.
Admitted. 
          
(* As an aside, this representation even accomodates (a slightly 
   complicated version of) proof by induction. For details, see 
   Alexander Miquel's thesis, pp282-288. 

   But, there are also drawbacks. *)

(* For each of plus, mult, and expt, either give a definition for
   pNat (e.g. using the same as before), or explain why you cannot. *)

Definition plus : pNat -> pNat -> pNat.
Admitted.

Theorem plus_spec : plus (succ (succ zero)) (succ (succ zero))
                    = (succ (succ (succ (succ zero)))).
Admitted.

Definition mult : pNat -> pNat -> pNat.
Admitted.

Theorem mult_spec : mult (succ (succ zero)) (succ (succ (succ zero)))
                    = succ (succ (succ (succ (succ (succ zero))))).
Admitted.

Definition expt : pNat -> pNat -> pNat.
Admitted.

Theorem expt_spec : expt (succ (succ zero)) (succ (succ (succ zero)))
                    = (succ (succ (succ (succ (succ (succ (succ (succ (succ zero))))))))).
Admitted.

End Exercise3.








(** * Axioms *)

(** Excluded Middle *)

Require Import Classical_Prop.
Print classic.

Axiom classic : forall P : Prop, P \/ ~ P.




(* Exercise (15 min)

   Using classic we can derive other familiar logic identities.
   Which of these require classic, and which are constructively valid? *)
Module Exercise4.
Theorem P_NNP : forall (P : Prop), P -> ~~P.
Admitted.

Theorem NNP_P : forall (P : Prop), ~~P -> P.
Admitted.

Theorem NAll_ExN : forall A (P : A->Prop), 
  (~forall x, P x) -> exists x:A, ~P x.
Admitted.

Theorem NEx_AllN : forall A (P : A->Prop),
  (~exists x:A, P x) -> (forall x, ~P x).
Admitted.
End Exercise4.

(* Presenting developments "axiomatically" *)

Parameter num : nat.
Axiom positive : num > 0.
Reset num.

Axiom not_classic : ~ forall P : Prop, P \/ ~ P.

Theorem uhoh : False.
  generalize classic not_classic; tauto.
Qed.

Theorem uhoh_again : 1 + 1 = 3.
  destruct uhoh.
Qed.

Reset not_classic.



Theorem t1 : forall P : Prop, P -> ~ ~ P.
  tauto.
Qed.
Print Assumptions t1.

Theorem t2 : forall P : Prop, ~ ~ P -> P.
  tauto.
Qed.
Print Assumptions t2. 


(* Classic is often provable for specific propositions. *)
Theorem nat_eq_dec : forall n m : nat, n = m \/ n <> m.
  induction n; destruct m; intuition; generalize (IHn m); intuition.
Qed.

Theorem t2' : forall n m : nat, ~ ~ (n = m) -> n = m.
  intros n m; destruct (nat_eq_dec n m); tauto.
Qed.
Print Assumptions t2'.















(* Proof Irrelevance *)

Require Import ProofIrrelevance.
Print proof_irrelevance.

Lemma zgtz : 0 > 0 -> False.
  crush.
Qed.

Definition pred_strong1 (n : nat) : n > 0 -> nat :=
  match n with
    | O => fun pf : 0 > 0 => match zgtz pf with end
    | S n' => fun _ => n'
  end.

(* pred_strong1 does not distingiush different proof arguments *)

Theorem pred_strong1_irrel : forall n (pf1 pf2 : n > 0), 
 pred_strong1 pf1 = pred_strong1 pf2.
  destruct n; crush.
Qed.

Theorem pred_strong1_irrel' : forall n (pf1 pf2 : n > 0), pred_strong1 pf1 = pred_strong1 pf2.
  intros. f_equal. apply proof_irrelevance.
Qed.






















(* Axioms about equality *)

Require Import Eqdep.
Import Eq_rect_eq.
Print eq_rect_eq.

Corollary UIP_refl : 
  forall A (x : A) (pf : x = x), pf = eq_refl x.
  intros; replace pf with (eq_rect x (eq x) (eq_refl x) x pf); [
    symmetry; apply eq_rect_eq
    | exact (match pf as pf' return match pf' in _ = y return x = y with
                                      | eq_refl => eq_refl x
                                    end = pf' with
               | eq_refl => eq_refl _
             end) ].
Qed.

Corollary UIP : forall A (x y : A) (pf1 pf2 : x = y), pf1 = pf2.
  intros; generalize pf1 pf2; subst; intros;
    match goal with
      | [ |- ?pf1 = ?pf2 ] => rewrite (UIP_refl pf1); rewrite (UIP_refl pf2); reflexivity
    end.
Qed. 





(* UIP is provable for types with decidable equality. *)
Require Import Eqdep_dec.
Require Import Arith.

Module NatDec : DecidableSet.
  Definition U := nat.
  Definition eq_dec := eq_nat_dec.
End NatDec.
Module DecidableEqDepSetNat  := DecidableEqDepSet(NatDec).
Check DecidableEqDepSetNat.UIP_refl.











(* Functional Extensionality *)

Require Import FunctionalExtensionality.

Check (@functional_extensionality)
 : forall (A B : Type) (f g : A -> B), 
     (forall x : A, f x = g x) -> f = g.

Check (@functional_extensionality_dep) 
 : forall (A : Type) (B : A -> Type) 
   (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g.






(* Propositional Extensionality *)
Axiom prop_extensionality : forall (P Q : Prop), 
  (P <-> Q) -> P = Q.

(* This (somewhat scarily) implies arbitrary fixpoints in Prop, 
     see Coq.Logic.ClassicalFacts. *)










Module Exercise5.
(*  Remember the type of regular expressions from chapter 8? *)
Require Import Ascii String.
Open Scope string_scope.

Inductive star (P :string -> Prop) : string -> Prop :=
  | StarEmpty : star P ""
  | StarIter : forall s1 s2,
    P s1
    -> star P s2
    -> star P (s1 ++ s2).

Inductive regexp : (string -> Prop) -> Type :=
| REmpty : regexp (fun s => False)
| RChar : forall ch : ascii,
  regexp (fun s => s = String ch "")
| RConcat : forall P1 P2 (r1 : regexp P1) (r2 : regexp P2),
  regexp (fun s => exists s1, exists s2, s = s1 ++ s2 /\ P1 s1 /\ P2 s2)
| ROr : forall P1 P2 (r1 : regexp P1) (r2 : regexp P2),
  regexp (fun s => P1 s \/ P2 s)
| RStar : forall P (r : regexp P),
  regexp (star P).

(* Exercise (10 min).
   Define (using axioms as appropriate) a regular expression
   of the following type (which states it matches exactly the
   empty string *)

Definition RNull : regexp (fun s => s = "").
Admitted.

Close Scope string_scope.
End Exercise5.






(** ** Axioms of Choice / Axioms of Description *)

Require Import ClassicalChoice.
Check choice
     : forall (A B : Type) (R : A -> B -> Prop),
       (forall x : A, exists y : B, R x y) ->
       exists f : A -> B, forall x : A, R x (f x).


Definition choice_Set 
  : forall (A B : Type) (R : A -> B -> Prop),
           (forall x : A, {y : B | R x y}) ->
             {f : A -> B | forall x : A, R x (f x)} 

:= fun A B R H => exist (fun f => forall x : A, R x (f x))
    (fun x => proj1_sig (H x)) (fun x => proj2_sig (H x)).

















Axiom constructive_definite_description :
  forall (A : Type) (P : A->Prop),
    (exists! x, P x) -> { x : A | P x }.


Axiom epsilon :
  forall (A : Type) (P : A->Prop), inhabited A ->
    { x : A | (exists x, P x) -> P x }.

Axiom computational_classic : 
  forall (P : Prop), {P} + {~P}.

Require Import ConstructiveEpsilon.
Check constructive_definite_description
     : forall (A : Set) (f : A -> nat) (g : nat -> A),
       (forall x : A, g (f x) = x) ->
       forall P : A -> Prop,
       (forall x : A, {P x} + {~ P x}) ->
       (exists! x : A, P x) -> {x : A | P x}. 

Print Assumptions constructive_definite_description.
(* Closed under the global context *)





Section Exercise6.
(* In set theory we often form a quotient set by an equivalence 
   relation. This does not work very well in plain Coq, but 
   assuming some axioms helps. *)

(* Suppose we have a nonempty type A and some equivalence relation on
it. *)

Variable A : Set.
Hypothesis A_inhabited : inhabited A.
Variable R : A -> A -> Prop.
Hypothesis R_refl : forall x, R x x.
Hypothesis R_sym : forall x y, R x y -> R y x.
Hypothesis R_trans : forall x y z, R x y -> R y z -> R x z.

(* Exercise (30 min) 

   Define a function repr, and prove that it picks out exactly one
   representative from each equivalence class of R.

   Hint: three axioms from earlier in the file may be useful here.
*)

Definition repr : A -> A.
Admitted.

Theorem repr_spec1 : forall x, R x (repr x).
Admitted.

Theorem repr_spec2 : forall x y, R x y <-> (repr x = repr y).
Admitted.

End Exercise6.










(** ** Axioms and Computation *)

Definition cast (A B : Set) (pf : A = B) (v : A) : B :=
  match pf with
    | eq_refl => v
  end.


Eval compute in (cast (eq_refl (nat -> nat)) (fun n => S n)) 12.

Theorem t3 :   (forall n : nat, fin (S n)) 
             = (forall n : nat, fin (n + 1)). 
  change ((forall n : nat, (fun n => fin (S n)) n) = (forall n : nat, (fun n => fin (n + 1)) n)).
  rewrite (functional_extensionality (fun n => fin (n + 1)) (fun n => fin (S n))); crush.
Qed.

Eval compute in (cast t3 (fun _ => First)) 12.

Reset t3.

Theorem t3 : (forall n : nat, fin (S n)) = (forall n : nat, fin (n + 1)). 
  change ((forall n : nat, (fun n => fin (S n)) n) = (forall n : nat, (fun n => fin (n + 1)) n));
    rewrite (functional_extensionality (fun n => fin (n + 1)) (fun n => fin (S n))); crush.
Defined. (* not Qed. *)

(* But, still no luck. *)
Eval compute in (cast t3 (fun _ => First)) 12.   

(* A better proof. *)
Lemma plus1 : forall n, S n = n + 1.
  induction n; simpl; intuition.
Defined.

Theorem t4 : forall n, fin (S n) = fin (n + 1).
  intro; f_equal; apply plus1.
Defined.

Eval compute in cast (t4 13) First.

Eval compute in 
  fun n:nat => cast (t4 n) First.


















(** ** Methods for Avoiding Axioms *)

(* Why avoid axioms? 
   Blocking reduction, clearer meaning, smaller TCB. *)


(* The dep_destruct tactic uses the JMeq_eq axiom. *)
Theorem fin_cases : forall n (f : fin (S n)), 
                       f = First \/ exists f', f = Next f'.
  intros; dep_destruct f; eauto.
Qed.
Print Assumptions fin_cases.


Lemma fin_cases_again' : forall n (f : fin n),
  match n return fin n -> Prop with
    | O => fun _ => False
    | S n' => fun f => f = First \/ exists f', f = Next f'
  end f.
  destruct f; eauto.
Qed.

Theorem fin_cases_again : forall n (f : fin (S n)),
                            f = First \/ exists f', f = Next f'.
  intros; exact (fin_cases_again' f).
Qed.
Print Assumptions fin_cases_again.

Definition finOut n (f : fin n) : match n return fin n -> Type with
                                    | O => fun _ => Empty_set
                                    | _ => fun f => {f' : _ | f = Next f'} + {f = First}
                                  end f
 :=
  match f with
    | First _ => inright _ (eq_refl _)
    | Next _ f' => inleft _ (exist _ f' (eq_refl _))
  end.











(* Another example *)

Inductive formula : list Type -> Type :=
| Inject : forall Ts, Prop -> formula Ts
| VarEq : forall T Ts, T -> formula (T :: Ts)
| Lift : forall T Ts, formula Ts -> formula (T :: Ts)
| Forall : forall T Ts, formula (T :: Ts) -> formula Ts
| And : forall Ts, formula Ts -> formula Ts -> formula Ts.


Inductive proof : formula nil -> Prop :=
| PInject : forall (P : Prop), P -> proof (Inject nil P)
| PAnd : forall p q, proof p -> proof q -> proof (And p q).

Theorem proj1 : forall p q, proof (And p q) -> proof p.
  destruct 1.  (* destruct does not work well for  nonvariable args *)

  Restart.
  Require Import Program.
  intros ? ? H; dependent destruction H; auto.
Qed.
Print Assumptions proj1.

(* The usual trick for the nonvariable arg problem. *)
Lemma proj1_again' : forall r, proof r
  -> forall p q, r = And p q -> proof p.
  destruct 1; crush.

  discriminate.   (* Discriminate still works. *)

  injection H1; intros. (* But injection is wonky. *)
  crush.
Qed.
Print Assumptions proj1_again'.

Lemma proj1_again'' : forall r, proof r
  -> match r with
       | And Ps p _ => match Ps return formula Ps -> Prop with
                         | nil => fun p => proof p
                         | _ => fun _ => True
                       end p
       | _ => True
     end.
  destruct 1; auto.
Qed.

Theorem proj1_again : forall p q, proof (And p q) -> proof p.
  intros ? ? H; exact (proj1_again'' H).
Qed.

Print Assumptions proj1_again.

















(* Avoiding axioms by making definitions compute *)


Section withTypes.
  (* Suppose we want to value environments for some PL *)
  Variable types : list Set.
  Variable values : hlist (fun x : Set => x) types.

  (* Given a valid index, we can look up the corresponding value. *)
  Variable natIndex : nat.
  Variable natIndex_ok : nth_error types natIndex = Some nat.


  Lemma nth_error_nil : forall A n x,
    nth_error (@nil A) n = Some x
    -> False.
    destruct n; simpl; unfold error; congruence.
  Defined.

  Implicit Arguments nth_error_nil [A n x].

  Lemma Some_inj : forall A (x y : A),
    Some x = Some y
    -> x = y.
    congruence.
  Defined.

  Fixpoint getNat (types' : list Set) (values' : hlist (fun x : Set => x) types')
    (natIndex : nat) : (nth_error types' natIndex = Some nat) -> nat :=
    match values' with
      | HNil => fun pf => match nth_error_nil pf with end
      | HCons t ts x values'' =>
        match natIndex return nth_error (t :: ts) natIndex = Some nat -> nat with
          | O => fun pf =>
            match Some_inj pf in _ = T return T with
              | eq_refl => x
            end
          | S natIndex' => getNat values'' natIndex'
        end
    end.
End withTypes.

(* For example, *)
Definition myTypes := unit :: nat :: bool :: nil.
Definition myValues : hlist (fun x : Set => x) myTypes :=
  tt ::: 3 ::: false ::: HNil.

Definition myNatIndex := 1.

Theorem myNatIndex_ok : nth_error myTypes myNatIndex = Some nat.
  reflexivity.
Defined.

Eval compute in getNat myValues myNatIndex myNatIndex_ok.

(* However: *)
Theorem getNat_is_reasonable : forall pf, getNat myValues myNatIndex pf = 3.
intros.
  compute.
Abort.



(* Let's change the representation of environments. *)
Fixpoint copies A (x : A) (n : nat) : list A :=
  match n with
    | O => nil
    | S n' => x :: copies x n'
  end.

Fixpoint update A (ls : list A) (n : nat) (x : A) : list A :=
  match ls with
    | nil => copies x n ++ x :: nil
    | y :: ls' => match n with
                    | O => x :: ls'
                    | S n' => y :: update ls' n' x
                  end
  end.

(** Now let us revisit the definition of [getNat]. *)
Section withTypes'.
  Variable types : list Set.
  Variable natIndex : nat.

  Definition types' := update types natIndex nat.
  Variable values : hlist (fun x : Set => x) types'.


  Fixpoint skipCopies (n : nat)
    : hlist (fun x : Set => x) (copies nat n ++ nat :: nil) -> nat :=
    match n with
      | O => fun vs => hhd vs
      | S n' => fun vs => skipCopies n' (htl vs)
    end.

  Fixpoint getNat' (types'' : list Set) (natIndex : nat)
    : hlist (fun x : Set => x) (update types'' natIndex nat) -> nat :=
    match types'' with
      | nil => skipCopies natIndex
      | t :: types0 =>
        match natIndex return hlist (fun x : Set => x)
          (update (t :: types0) natIndex nat) -> nat with
          | O => fun vs => hhd vs
          | S natIndex' => fun vs => getNat' types0 natIndex' (htl vs)
        end
    end.
End withTypes'.


(* No equality proof to get stuck on! *)

Check (getNat' myTypes myNatIndex).
Eval compute in (update myTypes myNatIndex nat).

Theorem getNat_is_reasonable : getNat' myTypes myNatIndex myValues = 3.
  reflexivity.
Qed.