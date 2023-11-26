(* Copyright (c) 2011-2012, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(** Note: Exercises are tagged with "Exercise". Since we already
    did first-order encodings a few weeks ago, all the exercises
    are in the PHOAS section. Don't hesitate to email if you
    have questions. *)

Require Import FunctionalExtensionality List.

Require Import CpdtTactics DepList.

Set Implicit Arguments.

Ltac ext := let x := fresh "x" in extensionality x.
Ltac crushf := crush; repeat (ext || f_equal; crush).

Section hmap.
  Variable A : Type.
  Variables B1 B2 B3 : A -> Type.

  Variable f1 : forall x, B1 x -> B2 x.
  Variable f2 : forall x, B2 x -> B3 x.

  Theorem hmap_hmap : forall ls (hl : hlist B1 ls), hmap f2 (hmap f1 hl) = hmap (fun i (x : B1 i) => f2 (f1 x)) hl.
    induction hl; crush.
  Qed.
End hmap.

Section Forall.
  Variable A : Type.
  Variable P : A -> Prop.

  Print In.

  Theorem Forall_In : forall ls, Forall P ls -> forall x, In x ls -> P x.
    induction 1; crush.
  Qed.

  Theorem Forall_In' : forall ls, (forall x, In x ls -> P x) -> Forall P ls.
    induction ls; crush.
  Qed.

  Variable P' : A -> Prop.

  Theorem Forall_weaken : forall ls, Forall P ls
    -> (forall x, P x -> P' x)
    -> Forall P' ls.
    induction 1; crush.
  Qed.
End Forall.

Inductive type : Type :=
| Nat : type
| Func : type -> type -> type.

Fixpoint typeDenote (t : type) : Type :=
  match t with
    | Nat => nat
    | Func t1 t2 => typeDenote t1 -> typeDenote t2
  end.

(** * Dependent de Bruijn Indices *)

Module FirstOrder.

  Inductive term : list type -> type -> Type :=
  | Var : forall G t, member t G -> term G t

  | Const : forall G, nat -> term G Nat
  | Plus : forall G, term G Nat -> term G Nat -> term G Nat

  | Abs : forall G dom ran, term (dom :: G) ran -> term G (Func dom ran)
  | App : forall G dom ran, term G (Func dom ran) -> term G dom -> term G ran

  | Let : forall G t1 t2, term G t1 -> term (t1 :: G) t2 -> term G t2.

  Implicit Arguments Const [G].

  (* \x. \y. x + y *)
  Example add : term nil (Func Nat (Func Nat Nat)) :=
    Abs (Abs (Plus (Var (HNext HFirst)) (Var HFirst))).

  (* (add 1) 2 *)
  Example three_the_hard_way : term nil Nat :=
    App (App add (Const 1)) (Const 2).

  Fixpoint termDenote G t (e : term G t) : hlist typeDenote G -> typeDenote t :=
    match e with
      | Var _ _ x => fun s => hget s x

      | Const _ n => fun _ => n
      | Plus _ e1 e2 => fun s => termDenote e1 s + termDenote e2 s

      | Abs _ _ _ e1 => fun s => fun x => termDenote e1 (x ::: s)
      | App _ _ _ e1 e2 => fun s => (termDenote e1 s) (termDenote e2 s)

      | Let _ _ _ e1 e2 => fun s => termDenote e2 (termDenote e1 s ::: s)
    end.

  Fixpoint ident G t (e : term G t) : term G t :=
    match e with
      | Var _ _ x => Var x

      | Const _ n => Const n
      | Plus _ e1 e2 => Plus (ident e1) (ident e2)

      | Abs _ _ _ e1 => Abs (ident e1)
      | App _ _ _ e1 e2 => App (ident e1) (ident e2)

      | Let _ _ _ e1 e2 => Let (ident e1) (ident e2)
    end.

  Theorem identSound : forall G t (e : term G t) s,
    termDenote (ident e) s = termDenote e s.
    induction e; crushf.
  Qed.

  Fixpoint cfold G t (e : term G t) : term G t :=
    match e with
      | Plus G e1 e2 =>
        let e1' := cfold e1 in
        let e2' := cfold e2 in
        let maybeOpt := match e1' return _ with
                          | Const _ n1 =>
                            match e2' return _ with
                              | Const _ n2 => Some (Const (n1 + n2))
                              | _ => None
                            end
                          | _ => None
                        end in
        match maybeOpt with
          | None => Plus e1' e2'
          | Some e' => e'
        end

      | Abs _ _ _ e1 => Abs (cfold e1)
      | App _ _ _ e1 e2 => App (cfold e1) (cfold e2)

      | Let _ _ _ e1 e2 => Let (cfold e1) (cfold e2)

      | e => e (* Var, Const *)
    end.

  Theorem cfoldSound : forall G t (e : term G t) s,
    termDenote (cfold e) s = termDenote e s.
    induction e; crushf;
      repeat (match goal with
                | [ |- context[match ?E with Var _ _ _ => _ | _ => _ end] ] =>
                  dep_destruct E
              end; crushf).
  Qed.

  (* Let Substitution *)
  (* Removes "[let x = e1 in e2]" by substituting [e1] for [x] in [e2]. *)

  (* Inserts t at the given index in G *)
  Fixpoint insertAt (t : type) (G : list type) (n : nat) {struct n} : list type :=
    match n with
      | O => t :: G
      | S n' => match G with
                  | nil => t :: G
                  | t' :: G' => t' :: insertAt t G' n'
                end
    end.

  (* Applies HNext if n "<=" x. *) 
  Fixpoint liftVar t G (x : member t G) t' n : member t (insertAt t' G n) :=
    match x with
      | HFirst G' => match n return member t (insertAt t' (t :: G') n) with
                       | O => HNext HFirst
                       | _ => HFirst
                     end
      | HNext t'' G' x' => match n return member t (insertAt t' (t'' :: G') n) with
                             | O => HNext (HNext x')
                             | S n' => HNext (liftVar x' t' n')
                           end
    end.

  Fixpoint lift' G t' n t (e : term G t) : term (insertAt t' G n) t :=
    match e with
      | Var _ _ x => Var (liftVar x t' n)

      | Const _ n => Const n
      | Plus _ e1 e2 => Plus (lift' t' n e1) (lift' t' n e2)

      | Abs _ _ _ e1 => Abs (lift' t' (S n) e1)
      | App _ _ _ e1 e2 => App (lift' t' n e1) (lift' t' n e2)

      | Let _ _ _ e1 e2 => Let (lift' t' n e1) (lift' t' (S n) e2)
    end.

  Definition lift G t' t (e : term G t) : term (t' :: G) t :=
    lift' t' O e.

  (* Example: [\y. x + y] *)
  Definition part_add : term (Nat :: nil) (Func Nat Nat) :=
    Abs (Plus (Var (HNext HFirst)) (Var HFirst)).

  (* closed *)
  Eval compute in lift Nat add.
  (* not closed *)
  Eval compute in lift Nat part_add.
  
  Definition ctxt1 : hlist typeDenote (Nat :: nil) :=
    @HCons _ _ Nat _ 3 HNil.

  Definition ctxt2 : hlist typeDenote (Nat :: Nat :: nil) :=
    @HCons _ _ Nat _ 0 ctxt1.

  Eval compute in termDenote part_add ctxt1.
  Eval compute in termDenote (lift Nat part_add) ctxt2.

  Fixpoint unlet G t (e : term G t) G' : hlist (term G') G -> term G' t :=
    match e with
      | Var _ _ x => fun s => hget s x

      | Const _ n => fun _ => Const n
      | Plus _ e1 e2 => fun s => Plus (unlet e1 s) (unlet e2 s)

      | Abs _ dom _ e1 => fun s => Abs (unlet e1 (Var HFirst ::: hmap (lift dom) s))
      | App _ _ _ e1 e2 => fun s => App (unlet e1 s) (unlet e2 s)

      | Let _ t1 _ e1 e2 => fun s => unlet e2 (unlet e1 s ::: s)
    end.

  Check hmap.

  (* Example: [let x := 2 in \y. x + y] *)
  Definition add_2 : term nil (Func Nat Nat) :=
    Let (Const 2) (Abs (Plus (Var (HNext HFirst)) (Var HFirst))).

  (* Example: [let y := 2 in x + y] *)
  Definition part_add_2 : term (Nat :: nil) Nat :=
    Let (Const 2) (Plus (Var (HNext HFirst)) (Var HFirst)).

  Definition ctxt3 : hlist (term (Nat :: nil)) (Nat :: nil) :=
    @HCons _ _ Nat _ (Const 1) HNil.
  
  Eval compute in unlet add_2 HNil.
  Eval compute in unlet part_add_2 ctxt3.

  Fixpoint insertAtS (t : type) (x : typeDenote t) (G : list type) (n : nat) {struct n}
    : hlist typeDenote G -> hlist typeDenote (insertAt t G n) :=
    match n with
      | O => fun s => x ::: s
      | S n' => match G return hlist typeDenote G
                               -> hlist typeDenote (insertAt t G (S n')) with
                  | nil => fun s => x ::: s
                  | t' :: G' => fun s => hhd s ::: insertAtS t x n' (htl s)
                end
    end.

  Implicit Arguments insertAtS [t G].

  Lemma liftVarSound : forall t' (x : typeDenote t') t G (m : member t G) s n,
    hget s m = hget (insertAtS x n s) (liftVar m t' n).
    induction m; destruct n; dep_destruct s; crushf.
  Qed.

  Hint Resolve liftVarSound.

  Lemma lift'Sound : forall G t' (x : typeDenote t') t (e : term G t) n s,
    termDenote e s = termDenote (lift' t' n e) (insertAtS x n s).
    induction e; crushf;
      repeat match goal with
               | [ IH : forall n s, _ = termDenote (lift' _ n ?E) _
                   |- context[lift' _ (S ?N) ?E] ] => specialize (IH (S N))
             end; crushf.
  Qed.

  Lemma liftSound : forall G t' (x : typeDenote t') t (e : term G t) s,
    termDenote (lift t' e) (x ::: s) = termDenote e s.
    unfold lift; intros; rewrite (lift'Sound _ x e O); trivial.
  Qed.

  Hint Rewrite hget_hmap hmap_hmap liftSound.

  Lemma unletSound' : forall G t (e : term G t) G' (s : hlist (term G') G) (s1 : hlist typeDenote G'),
    termDenote (unlet e s) s1
    = termDenote e (hmap (fun t' (e' : term G' t') => termDenote e' s1) s).
    induction e; crushf.
  Qed.

  Theorem unletSound : forall t (e : term nil t),
    termDenote (unlet e HNil) HNil = termDenote e HNil.
    intros; apply unletSound'.
  Qed.

End FirstOrder.

(** * Parametric Higher-Order Abstract Syntax *)

Module HigherOrder.

(*
  Inductive term : type -> Type :=
  | Const : nat -> term Nat
  | Plus : term Nat -> term Nat -> term Nat

  | Abs : forall dom ran, (term dom -> term ran) -> term (Func dom ran)
  | App : forall dom ran, term (Func dom ran) -> term dom -> term ran

  | Let : forall t1 t2, term t1 -> (term t1 -> term t2) -> term t2.
*)

(*
<<
Error: Non strictly positive occurrence of "term" in
 "forall dom ran : type, (term dom -> term ran) -> term (Func dom ran)".
>>
*)

  Module Loop.
    Section Omega.
      
      Variable Term : Type.
      Variable Abs : (Term -> Term) -> Term.
      
      Variable matchA : Term -> forall Q : Type, ((Term -> Term) -> Q) -> Q.
      
     (*
     matchA t Q h :=
     match t return Q with
     | Abs f => h f
     | ...
     end
     *)
      
      Definition app (f x : Term) : Term :=
        matchA f (fun h => h x).
      
      Definition Delta : Term :=
        Abs (fun x : Term => app x x).

      Definition Omega := app Delta Delta.
      
    End Omega.
  End Loop.

  (** Exercise

     The assignment is to add a variable-arity let binding [VLet] that
     generalizes the single binding in [Let] to an hlist of bindings,
     and then update the definitions and theorems to account for this.
     Some of the more redundant or pointless ones are optional. *)     
  
  Section var.
    Variable var : type -> Type.

    (* Exercise : Start by adding the [VLet] case to the definition. *)
    Inductive term : type -> Type :=
    | Var : forall t, var t -> term t

    | Const : nat -> term Nat
    | Plus : term Nat -> term Nat -> term Nat

    | Abs : forall dom ran, (var dom -> term ran) -> term (Func dom ran)
    | App : forall dom ran, term (Func dom ran) -> term dom -> term ran

    | Let : forall t1 t2, term t1 -> (var t1 -> term t2) -> term t2.
  End var.

  Implicit Arguments Var [var t].
  Implicit Arguments Const [var].
  Implicit Arguments Abs [var dom ran].
  
  (* If [VLet] is defined correctly, these should typecheck. *)
  (*
  Definition bindings var : hlist (term var) (Nat :: Func Nat Nat :: nil) :=
    Const 2 ::: Abs (fun v => Plus (Const 1) (Var v)) ::: HNil.

  Definition body var (bs : hlist var (Nat :: Func Nat Nat :: nil)) :=
    App (Var (hget bs (HNext HFirst))) (Var (hget bs HFirst)).

  (* [let (x := 2, f := fun v => v + 1) in f x] *)
  Definition three_the_vlet_way var := VLet (bindings var) (@body var).
  *)

  Check term_ind.

  (* You most likely ended up with a lousy induction principle, so let's
     make it better. *)

  (* This might useful for defining the induction principle. *)
  Inductive hAll A (B : A -> Type) (P : forall x, B x -> Prop)
    : forall ls, hlist B ls -> Prop :=
  | hAll_Nil : hAll P (@HNil A B)
  | hAll_HCons : forall (t : A) (x : B t) ls (h : hlist B ls),
      P t x -> hAll P h -> hAll P (HCons x h).

  Hint Constructors hAll.
  
  (* Exercise : Add an induction case for [VLet]. Don't bother proving
     the theorem, since it's somewhat orthogonal. Just leave it as
     Admitted. *)
  Theorem term_ind2
     : forall (var : type -> Type) (P : forall t : type, term var t -> Prop),
       (* Var *)
       (forall (t : type) (v : var t), P t (Var v)) ->
       (* Const *)
       (forall n : nat, P Nat (Const n)) ->
       (* Plus *)
       (forall t1 : term var Nat, P Nat t1 ->
         forall t2 : term var Nat, P Nat t2 -> P Nat (Plus t1 t2)) ->
       (* Abs *)
       (forall (dom ran : type) (f : var dom -> term var ran),
        (forall v : var dom, P ran (f v)) -> P (Func dom ran) (Abs f)) ->
       (* App *)
       (forall (dom ran : type) (t1 : term var (Func dom ran)),
        P (Func dom ran) t1 ->
        forall t2 : term var dom, P dom t2 -> P ran (App t1 t2)) ->
       (* Let *)
       (forall (t1 t2 : type) (tm : term var t1),
        P t1 tm ->
        forall f : var t1 -> term var t2,
        (forall v : var t1, P t2 (f v)) -> P t2 (Let tm f)) ->
       (* Add VLet case here *)

       forall (t : type) (tm : term var t), P t tm.
  Admitted.

  (* Closed terms can quantify over [var] *)
  Definition Term t := forall var, term var t.

  Example add : Term (Func Nat (Func Nat Nat)) := fun var =>
    Abs (fun x => Abs (fun y => Plus (Var x) (Var y))).

  Example three_the_hard_way : Term Nat := fun var =>
    App (App (add var) (Const 1)) (Const 2).

  (*
  Example three_the_really_hard_way : Term Nat := fun var =>
    three_the_vlet_way var.
  *)

  (* or... *)

  Example add' : Term (Func Nat (Func Nat Nat)) := fun _ =>
    Abs (fun x => Abs (fun y => Plus (Var x) (Var y))).

  Example three_the_hard_way' : Term Nat := fun _ =>
    App (App (add' _) (Const 1)) (Const 2).

  (** ** Functional Programming with PHOAS *)

  (* Exercise, Optional

     Add a [VLet] case for [countVars] and [pretty] below. If you
     don't do these exercises, you'll need to comment them out or
     use some default value.
  *)

  Fixpoint countVars t (e : term (fun _ => unit) t) : nat :=
    match e with
      | Var _ _ => 1

      | Const _ => 0
      | Plus e1 e2 => countVars e1 + countVars e2
      | Abs _ _ e1 => countVars (e1 tt)
      | App _ _ e1 e2 => countVars e1 + countVars e2

      | Let _ _ e1 e2 => countVars e1 + countVars (e2 tt)
    end.

  Definition CountVars t (E : Term t) := countVars (E (fun _ => unit)).

  Eval compute in CountVars three_the_hard_way.

  Require Import String.
  Open Scope string_scope.

  (* "pretty" *)
  Fixpoint pretty t (e : term (fun _ => string) t) (x : string) : string :=
    match e with
      | Var _ s => s

      | Const _ => "N" (* to avoid orthogonal details *)
      | Plus e1 e2 => "(" ++ pretty e1 x ++ " + " ++ pretty e2 x ++ ")"

      | Abs _ _ e1 => "(fun " ++ x ++ " => " ++ pretty (e1 x) (x ++ "'") ++ ")"
      | App _ _ e1 e2 => "(" ++ pretty e1 x ++ " " ++ pretty e2 x ++ ")"

      | Let _ _ e1 e2 => "(let " ++ x ++ " = " ++ pretty e1 x ++ " in "
        ++ pretty (e2 x) (x ++ "'") ++ ")"
    end.

  Definition Pretty t (E : Term t) := pretty (E (fun _ => string)) "x".

  Eval compute in Pretty three_the_hard_way.

  (** Exercise : Add the [VLet] case below. *)
  (* Hint: *) Check hmap.

  Fixpoint termDenote t (e : term typeDenote t) : typeDenote t :=
    match e with
      | Var _ v => v

      | Const n => n
      | Plus e1 e2 => termDenote e1 + termDenote e2

      | Abs _ _ e1 => fun x => termDenote (e1 x)
      | App _ _ e1 e2 => (termDenote e1) (termDenote e2)

      | Let _ _ e1 e2 => termDenote (e2 (termDenote e1))
    end.

  Definition TermDenote t (E : Term t) : typeDenote t :=
    termDenote (E typeDenote).
  
  Eval compute in TermDenote three_the_hard_way.
  (* Eval compute in TermDenote three_the_really_hard_way. *)

  (* Exercise: Add a case for [VLet] below. *)
  (* Hint: I needed to use hmap twice. *)
  Fixpoint squash var t (e : term (term var) t) : term var t :=
    match e with
      | Var _ e1 => e1

      | Const n => Const n
      | Plus e1 e2 => Plus (squash e1) (squash e2)

      | Abs _ _ e1 => Abs (fun x => squash (e1 (Var x)))
      | App _ _ e1 e2 => App (squash e1) (squash e2)

      | Let _ _ e1 e2 => Let (squash e1) (fun x => squash (e2 (Var x)))
    end.

  Definition add4 var : term (term var) (Func Nat Nat) :=
    Abs (fun v : term var Nat => Plus (Var (Const 4)) (Var v)).

  Eval compute in squash (add4 typeDenote).

  Definition Term1 (t1 t2 : type) := forall var, var t1 -> term var t2.

  (* Definition Term t := forall var, term var t. *)

  Definition Subst (t1 t2 : type) (E : Term1 t1 t2) (E' : Term t1) : Term t2 :=
    fun var => squash (E (term var) (E' var)).

  Eval compute in Subst (fun _ x => Plus (Var x) (Const 3)) three_the_hard_way.
  (* fun var => squash (Plus (Var (three_the_hard_way var)) (Const 3)) *)
  (* fun var => Plus (three_the_hard_way var) (Const 3) *)
  
  (** ** Verifying Program Transformations *)

  (* Exercise : Add the [VLet] case below. *)
  Fixpoint ident var t (e : term var t) : term var t :=
    match e with
      | Var _ x => Var x

      | Const n => Const n
      | Plus e1 e2 => Plus (ident e1) (ident e2)

      | Abs _ _ e1 => Abs (fun x => ident (e1 x))
      | App _ _ e1 e2 => App (ident e1) (ident e2)

      | Let _ _ e1 e2 => Let (ident e1) (fun x => ident (e2 x))
    end.

  Definition Ident t (E : Term t) : Term t := fun var =>
    ident (E var).

  (* A general lemma about [hmap] and [hAll], which may be useful.
     You may want to specialize it a bit before adding it to the
     hint database though. *)
  Theorem hmap_hAll : forall A B1 B2 ls (h : hlist B1 ls)
    (P : forall t, B1 t -> Prop)
    (f g : forall t : A, B1 t -> B2 t),
    (forall t x, P t x -> f t x = g t x) ->
    hAll P h ->
    hmap f h = hmap g h.
  Proof.
    intros; induction h; trivial;
      match goal with
        | [ H : hAll _ (_ ::: _) |- _ ] => dep_destruct H
      end; crush.
  Qed.
    
  Hint Rewrite hmap_hmap.

  (* Exercise : Prove soundness for the [ident] transformation. *)
  Lemma identSound : forall t (e : term typeDenote t),
    termDenote (ident e) = termDenote e.
    induction e using term_ind2; crushf.
  Qed.

  Theorem IdentSound : forall t (E : Term t),
    TermDenote (Ident E) = TermDenote E.
    intros; apply identSound.
  Qed.

  (* Exercise (Optional): Add a case for [VLet] below and prove it correct. *)
  Fixpoint cfold var t (e : term var t) : term var t :=
    match e with
      | Plus e1 e2 =>
        let e1' := cfold e1 in
        let e2' := cfold e2 in
          match e1', e2' with
            | Const n1, Const n2 => Const (n1 + n2)
            | _, _ => Plus e1' e2'
          end

      | Abs _ _ e1 => Abs (fun x => cfold (e1 x))
      | App _ _ e1 e2 => App (cfold e1) (cfold e2)

      | Let _ _ e1 e2 => Let (cfold e1) (fun x => cfold (e2 x))
      | e => e
    end.

  Definition Cfold t (E : Term t) : Term t := fun var =>
    cfold (E var).

  
  Lemma cfoldSound : forall t (e : term typeDenote t),
    termDenote (cfold e) = termDenote e.
    induction e using term_ind2; crushf;
      repeat (match goal with
                | [ |- context[match ?E with Var _ _ => _ | _ => _ end] ] =>
                  dep_destruct E
              end; crushf).
  Qed.

  Theorem CfoldSound : forall t (E : Term t),
    TermDenote (Cfold E) = TermDenote E.
    intros; apply cfoldSound.
  Qed.

  (* Exercise : Add a case for [VLet] below. Unlet should remove
     [VLet] as well as [Let]. *)
  Fixpoint unlet var t (e : term (term var) t) : term var t :=
    match e with
      | Var _ e1 => e1

      | Const n => Const n
      | Plus e1 e2 => Plus (unlet e1) (unlet e2)

      | Abs _ _ e1 => Abs (fun x => unlet (e1 (Var x)))
      | App _ _ e1 e2 => App (unlet e1) (unlet e2)

      | Let _ _ e1 e2 => unlet (e2 (unlet e1))
    end.

  Definition Unlet t (E : Term t) : Term t := fun var =>
    unlet (E (term var)).

  Eval compute in Unlet three_the_hard_way.

  (* [let x = 1 in let y = 2 in (add x) y] *)
  Definition three_a_harder_way : Term Nat := fun _ =>
    Let (Const 1) (fun x => Let (Const 2) (fun y => App (App (add _) (Var x)) (Var y))).

  Eval compute in Unlet three_a_harder_way.

  (* Exercise (Optional) : Extend [Wf] with a case for [VLet]. *)

  (* A proposition that holds for all pairs of corresponding elements in two
     heterogenous lists. It may be useful for the [VLet] case of [Wf]. *)
  Inductive hAll2 A (B1 : A -> Type) (B2 : A -> Type)
    (P : forall x, B1 x -> B2 x -> Prop)
    : forall ls, hlist B1 ls -> hlist B2 ls -> Prop :=
  | hAll2_Nil : hAll2 P HNil HNil
  | hAll2_Cons : forall x (y1 : B1 x) (y2 : B2 x) ls
    (h1 : hlist B1 ls) (h2 : hlist B2 ls),
    P x y1 y2 -> hAll2 P h1 h2 -> hAll2 P (HCons y1 h1) (HCons y2 h2).

  Section wf.
    Variables var1 var2 : type -> Type.

    Record varEntry := {
      Ty : type;
      First : var1 Ty;
      Second : var2 Ty
    }.

    (* Adds pairs of corresponding elements in each hlist to the list
       of var entries. It may also be useful.

       Optional Optional Exercise: Can we clean this definition up?
       I don't like the match inside the return, since we know [ts']
       cannot be [nil]. *)
    Fixpoint hvar_app (G : list varEntry) ts (h1 : hlist var1 ts)
      : hlist var2 ts -> list varEntry :=
      match h1 with
        | HNil => fun _ => G
        | HCons t _ x xs => fun h2 =>
          match h2 in hlist _ ts'
            return (match ts' with
                      | nil => var1 t ->
                        (hlist var2 nil -> list varEntry) -> list varEntry
                      | t' :: ts'' => var1 t' ->
                        (hlist var2 ts'' -> list varEntry) -> list varEntry
                    end) with
            | HNil => fun _ _ => G
            | HCons _ _ y ys =>
              fun x' f => {| First := x'; Second := y |} :: f ys
          end x (hvar_app G xs)
      end.

    Inductive wf : list varEntry -> forall t, term var1 t -> term var2 t -> Prop :=
    | WfVar : forall G t x x', In {| Ty := t; First := x; Second := x' |} G
      -> wf G (Var x) (Var x')

    | WfConst : forall G n, wf G (Const n) (Const n)

    | WfPlus : forall G e1 e2 e1' e2',
      wf G e1 e1'
      -> wf G e2 e2'
      -> wf G (Plus e1 e2) (Plus e1' e2')

    | WfAbs : forall G dom ran (e1 : var1 dom -> term var1 ran) e1',
      (forall x1 x2, wf ({| First := x1; Second := x2 |} :: G) (e1 x1) (e1' x2))
      -> wf G (Abs e1) (Abs e1')

    | WfApp : forall G dom ran (e1 : term var1 (Func dom ran)) (e2 : term var1 dom) e1' e2',
      wf G e1 e1'
      -> wf G e2 e2'
      -> wf G (App e1 e2) (App e1' e2')

    | WfLet : forall G t1 t2 e1 e1' (e2 : var1 t1 -> term var1 t2) e2', wf G e1 e1'
      -> (forall x1 x2, wf ({| First := x1; Second := x2 |} :: G) (e2 x1) (e2' x2))
      -> wf G (Let e1 e2) (Let e1' e2').
  End wf.

  Definition Wf t (E : Term t) := forall var1 var2, wf nil (E var1) (E var2).

  Theorem three_the_hard_way_Wf : Wf three_the_hard_way.
    red; intros; repeat match goal with
                          | [ |- wf _ _ _ ] => constructor; intros
                        end; intuition.
  Qed.

  Hint Extern 1 => match goal with
                     | [ H1 : Forall _ _, H2 : In _ _ |- _ ] => apply (Forall_In H1 _ H2)
                   end.

  (* Exercise (Optional) : Prove this lemma. You'll probably need to
     define another induction principle like you did for [term]. It
     looks rather unpleasant, actually. *)
  Lemma unletSound : forall G t (e1 : term _ t) e2,
    wf G e1 e2
    -> Forall (fun ve => termDenote (First ve) = Second ve) G
    -> termDenote (unlet e1) = termDenote e2.
    induction 1; crushf.
  Qed.

  Theorem UnletSound : forall t (E : Term t), Wf E
    -> TermDenote (Unlet E) = TermDenote E.
    intros; eapply unletSound; eauto.
  Qed.
  
  (** ** Establishing Term Well-Formedness *)

  Hint Constructors wf.
  Hint Extern 1 (In _ _) => simpl; tauto.
  Hint Extern 1 (Forall _ _) => eapply Forall_weaken; [ eassumption | simpl ].

  Lemma wf_monotone : forall var1 var2 G t (e1 : term var1 t) (e2 : term var2 t),
    wf G e1 e2
    -> forall G', Forall (fun x => In x G') G
      -> wf G' e1 e2.
    induction 1; crushf; auto 6.
  Qed.

  Hint Resolve wf_monotone Forall_In'.

  Hint Extern 1 (wf _ _ _) => progress simpl.

  Lemma unletWf : forall var1 var2 G t (e1 : term (term var1) t) (e2 : term (term var2) t),
    wf G e1 e2
    -> forall G', Forall (fun ve => wf G' (First ve) (Second ve)) G
      -> wf G' (unlet e1) (unlet e2).
    induction 1; crushf; eauto 9.
  Qed.

  Theorem UnletWf : forall t (E : Term t), Wf E
    -> Wf (Unlet E).
    red; intros; apply unletWf with nil; auto.
  Qed.


  (** ** A Few More Remarks *)

  Infix "-->" := Func (right associativity, at level 52).

  Notation "^" := Var.
  Notation "#" := Const.
  Infix "@" := App (left associativity, at level 50).
  Infix "@+" := Plus (left associativity, at level 50).
  Notation "\ x : t , e" := (Abs (dom := t) (fun x => e))
    (no associativity, at level 51, x at level 0).
  Notation "[ e ]" := (fun _ => e).

  Example Add : Term (Nat --> Nat --> Nat) :=
    [\x : Nat, \y : Nat, ^x @+ ^y].

  Example Three_the_hard_way : Term Nat :=
    [Add _ @ #1 @ #2].

  Eval compute in TermDenote Three_the_hard_way.

End HigherOrder.
