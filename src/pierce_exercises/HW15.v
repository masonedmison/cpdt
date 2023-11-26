(* All the exercises in the file are marked with the string "EXERCISE". *)
Require Import String List.
Require Import CpdtTactics DepList.
Set Implicit Arguments.

(***************************** Generic datatypes ******************************)

Record constructor : Type := Con {
  nonrecursive : Type;
  recursive : nat
}.

Inductive nlist :=
  | nnil  : nlist
  | ncons : nat -> nlist -> nlist.

Definition datatype := list constructor.

Definition Empty_set_dt       : datatype
  := nil.
Definition unit_dt            : datatype
  := Con unit 0 :: nil.
Definition bool_dt            : datatype
  := Con unit 0 :: Con unit 0 :: nil.
Definition nat_dt             : datatype
  := Con unit 0 :: Con unit 1 :: nil.
Definition list_dt (A: Type) : datatype
  := Con unit 0 :: Con A 1 :: nil.

Section tree.
  Variable A : Type.

  Inductive tree : Type :=
  | Leaf : A -> tree
  | Node : tree -> tree -> tree.
End tree.

Definition tree_dt (A : Type) : datatype
  := Con A 0 :: Con unit 2 :: nil.

(* EXERCISE: Write a generic datatype corresponding to the following `tree234`
   type. *)
Inductive tree234 (A : Type) : Type :=
  | Leaf0   : tree234 A
  | Leaf1   : A ->
              tree234 A
  | Leaf2   : A -> A ->
              tree234 A
  | Leaf3   : A -> A -> A ->
              tree234 A
  | Branch2 : A ->
              tree234 A -> tree234 A -> tree234 A
  | Branch3 : A -> A ->
              tree234 A -> tree234 A -> tree234 A ->
              tree234 A
  | Branch4 : A -> A -> A ->
              tree234 A -> tree234 A -> tree234 A -> tree234 A ->
              tree234 A.
Arguments Leaf0 [A].

Definition tree234_dt (A : Type) : datatype.
Admitted.

(**************************** Datatype denotations ****************************)

Section denote.
  Variable T : Type.
  Definition constructorDenote (c : constructor) :=
    nonrecursive c -> ilist T (recursive c) -> T.
  Definition datatypeDenote := hlist constructorDenote.
End denote.

Print hlist.
Check datatypeDenote.

Notation "[ ! , ! ~> x ]" :=
  ((fun _ _ => x) : constructorDenote _ (Con _ _)).
Notation "[ v , ! ~> x ]" :=
  ((fun v _ => x) : constructorDenote _ (Con _ _)).
Notation "[ ! , r ~> x ]" :=
  ((fun _ r => x) : constructorDenote _ (Con _ _)).
Notation "[ v , r ~> x ]" :=
  ((fun v r => x) : constructorDenote _ (Con _ _)).

Definition Empty_set_den
  : datatypeDenote Empty_set Empty_set_dt :=
  HNil.
Definition unit_den : datatypeDenote unit unit_dt :=
  [!, ! ~> tt] ::: HNil.
Definition bool_den : datatypeDenote bool bool_dt :=
  [!, ! ~> true] ::: [!, ! ~> false] ::: HNil.
Definition nat_den : datatypeDenote nat nat_dt :=
  [!, ! ~> O] ::: [!, r ~> S (hd r)] ::: HNil.
Definition list_den (A : Type)
  : datatypeDenote (list A) (list_dt A) :=
  [!, ! ~> nil] ::: [x, r ~> x :: hd r] ::: HNil.
Definition tree_den (A : Type)
  : datatypeDenote (tree A) (tree_dt A) :=
  [v, ! ~> Leaf v] :::
  [!, r ~> Node (hd r) (hd (tl r))] :::
  HNil.

Eval unfold datatypeDenote in datatypeDenote nat nat_dt.

(* EXERCISE: Write a denotation for the `tree234` type.  If you get odd type
   errors, try adding an explicit type parameter to the `Branch2` constructor
   (`@Branch2 A ...` or `Branch2 (A:=A) ...`). *)

(* Some useful tuple functions *)
Definition fst3 (A B C : Type) (triple : A * B * C) : A := fst (fst triple).
Definition snd3 (A B C : Type) (triple : A * B * C) : B := snd (fst triple).
Definition thd3 (A B C : Type) (triple : A * B * C) : C :=      snd triple.

Definition tree234_den (A : Type)
  : datatypeDenote (tree234 A) (tree234_dt A).
Admitted.

(******************************** Fixed points ********************************)

Definition fixDenote (T : Type) (dt : datatype) :=
  forall (R : Type), datatypeDenote R dt -> (T -> R).

Inductive nat' (R : Type) : Type :=
  | O' : nat' R
  | S' : R -> nat' R.

Inductive list' (A R : Type) : Type :=
  | nil'  : list' A R
  | cons' : A -> R -> list' A R.

Definition Empty_set_fix
  : fixDenote Empty_set Empty_set_dt :=
  fun R _ emp => match emp with end.

Definition unit_fix : fixDenote unit unit_dt :=
  fun R cases _ => (hhd cases) tt INil.

Definition bool_fix : fixDenote bool bool_dt :=
  fun R cases b => if b
    then (hhd cases) tt INil
    else (hhd (htl cases)) tt INil.

Definition nat_fix : fixDenote nat nat_dt :=
  fun R cases => fix F (n : nat) : R :=
    match n with
      | O => (hhd cases) tt INil
      | S n' => (hhd (htl cases)) tt (ICons (F n') INil)
    end.

Definition list_fix (A : Type)
  : fixDenote (list A) (list_dt A) :=
  fun R cases => fix F (ls : list A) : R :=
    match ls with
      | nil => (hhd cases) tt INil
      | x :: ls' =>
          (hhd (htl cases)) x (ICons (F ls') INil)
    end.

Definition tree_fix (A : Type) : fixDenote (tree A) (tree_dt A) :=
  fun R cases => fix F (t : tree A) : R :=
    match t with
      | Leaf x => (hhd cases) x INil
      | Node t1 t2 =>
          (hhd (htl cases))
            tt
            (ICons (F t1) (ICons (F t2) INil))
    end.

(* EXERCISE: Write a fixed point for recursion over the `tree234` type. *)

Definition tree234_fix (A : Type) : fixDenote (tree234 A) (tree234_dt A).
Admitted.

Fixpoint list_nat_sum (ls : list nat) :=
  match ls with
    | nil     => 0
    | x :: l' => x + list_nat_sum l'
  end.
Eval simpl in list_nat_sum (1::2::3::nil).

Definition list_nat_sum_den
  : datatypeDenote nat (list_dt nat) :=
  [!, ! ~> 0] ::: [x, r ~> x + hd r] ::: HNil.
Eval simpl in list_fix list_nat_sum_den (1::2::3::nil).

Definition list_map_den (A B : Type) (f : A -> B)
   : datatypeDenote (list B) (list_dt A) :=
       [!, ! ~> nil]         :::
       [x, r ~> f x :: hd r] :::
       HNil.
Definition map' (A B : Type) (f : A -> B)
  : list A -> list B :=
  list_fix (list_map_den f).
Eval compute in map'.
Eval compute in map.
Eval cbv beta iota delta -[plus] in list_fix list_nat_sum_den.

(* EXERCISE: Write a function `tree234_max` which computes the maximum natural
   number in a `tree234`; then, using `datatypeDenote`, write a
   `tree234_max_den` which does the same when paired with your `tree234_fix`
   from before.  Use `Eval cbv beta iota delta -[max] in ...` to see that the
   two are equivalent.  The maximum of an empty tree should be 0.  Note that Coq
   provides a `max : nat -> nat -> nat` function.  With some auxiliary
   definitions, your `tree234_max_den` should be reasonably clean. *)

Fixpoint tree234_max (t : tree234 nat) : nat.
Admitted.

Eval simpl in tree234_max Leaf0. (* => 0 *)
Eval simpl in tree234_max (Leaf3 3 5 2). (* => 5 *)
Eval simpl in tree234_max (Branch3 4 10
                            (Leaf2 6 8)
                            (Branch2 9
                              (Leaf1 17)
                              (Branch4 23 42 9
                                Leaf0
                                (Leaf1 30)
                                (Leaf2 0 1)
                                Leaf0))
                            (Leaf1 12)). (* => 42 *)

Definition tree234_max_den
  : datatypeDenote nat (tree234_dt nat).
Admitted.

Eval compute in tree234_fix tree234_max_den Leaf0. (* => 0 *)
Eval compute in tree234_fix tree234_max_den (Leaf3 3 5 2). (* => 5 *)
Eval compute in tree234_fix tree234_max_den (Branch3 4 10
                                              (Leaf2 6 8)
                                              (Branch2 9
                                                (Leaf1 17)
                                                (Branch4 23 42 9
                                                  Leaf0
                                                  (Leaf1 30)
                                                  (Leaf2 0 1)
                                                  Leaf0))
                                              (Leaf1 12)). (* => 42 *)
Eval cbv beta iota delta -[max] in tree234_fix tree234_max_den.

(***************************** Generic functions ******************************)

Check hmake.

Definition size T dt (fx : fixDenote T dt) : T -> nat :=
  fx nat (hmake (B := constructorDenote nat)
                (fun _ _ r => foldr plus 1 r)
                dt).
Eval compute in size Empty_set_fix.
Eval compute in size unit_fix.
Eval compute in size bool_fix.
Eval cbv beta iota delta -[plus] in size nat_fix.
Eval cbv beta iota delta -[plus] in
  fun A => size (@list_fix A).
Eval cbv beta iota delta -[plus] in
  fun A => size (@tree_fix A).

Eval compute in size (@tree_fix _)
                     (Node (Leaf true) (Node (Leaf false) (Leaf true))).

Record print_constructor (c : constructor) : Type := PI {
  printName : string;
  printNonrec : nonrecursive c -> string
}.
Notation "^" := (PI (Con _ _)).
Definition print_datatype := hlist print_constructor.
Local Open Scope string_scope.

Check hmap.

Definition print T dt
                 (pr : print_datatype dt)
                 (fx : fixDenote T dt) : T -> string :=
  fx string (hmap
    (B1 := print_constructor)
    (B2 := constructorDenote string)
    (fun _ pc x r => printName pc ++ "(" ++
                     printNonrec pc x ++
                     foldr (fun s acc =>
                             ", " ++ s ++ acc)
                           ")"
                          r)
    pr).

Eval compute in print HNil Empty_set_fix.
Eval compute in
  print (^ "tt" (fun _ => "") ::: HNil) unit_fix.
Eval compute in print (^ "true" (fun _ => "")
  ::: ^ "false" (fun _ => "")
  ::: HNil) bool_fix.

Definition print_nat := print (^ "O" (fun _ => "")
  ::: ^ "S" (fun _ => "")
  ::: HNil) nat_fix.
Eval cbv beta iota delta -[append] in print_nat.
Eval simpl in print_nat 0.
Eval simpl in print_nat 1.
Eval simpl in print_nat 2.

Eval cbv beta iota delta -[append] in
  fun A (pr : A -> string) =>
    print (^ "nil" (fun _ => "")
    ::: ^ "cons" pr
    ::: HNil) (@list_fix A).

Eval cbv beta iota delta -[append] in
  fun A (pr : A -> string) =>
    print (^ "Leaf" pr
    ::: ^ "Node" (fun _ => "")
    ::: HNil) (@tree_fix A).

Definition print_list :=   fun A (pr : A -> string) =>
    print (^ "nil" (fun _ => "")
    ::: ^ "cons" pr
    ::: HNil) (@list_fix A).

Eval compute in print_list (fun x => x) ("a" :: "b" :: "c" :: nil).

Definition map T dt (dd : datatypeDenote T dt)
                    (fx : fixDenote T dt)
                    (f : T -> T)
  : T -> T :=
  fx T (hmap (B1 := constructorDenote T)
             (B2 := constructorDenote T)
             (fun _ c x r => f (c x r))
             dd).

Eval compute in map Empty_set_den Empty_set_fix.
Eval compute in map unit_den unit_fix.
Eval compute in map bool_den bool_fix.
Eval compute in map nat_den nat_fix.
Eval compute in fun A => map (list_den A) (@list_fix A).
Eval compute in fun A => map (tree_den A) (@tree_fix A).
Definition map_nat := map nat_den nat_fix.
Eval simpl in map_nat S 0.
Eval simpl in map_nat S 1.
Eval simpl in map_nat S 2.
Eval simpl in map_nat (fun _ => 0) 10.

(* EXERCISE: Write a generic "measure" function, much like the generic printing
   function, that returns a natural number which is the sum of the measure of
   every non-recursive value.  You'll need to maintain the information on how to
   measure the non-recursive components (a function of type `A -> nat`). *)

(* Use this to represent measurement functions, à la `^` above. *)
Notation "[ x >-> n ]" := (fun x => n).

Definition measure T dt
                   (md : unit (* You'll want a better type here *))
                   (fx : fixDenote T dt) : T -> nat.
Admitted.

(* Uncomment these once you've gotten the types right. *)
(*
Eval compute in measure HNil Empty_set_fix.
Eval compute in measure ([_ >-> 0] ::: HNil)               unit_fix.
Eval compute in measure ([_ >-> 1] ::: [_ >-> 0] ::: HNil) bool_fix.
Eval cbv beta iota delta -[plus] in
  measure ([_ >-> 0] ::: [_ >-> 1] ::: HNil) nat_fix.
Eval cbv beta iota delta -[plus] in
  fun A ms => measure ([_ >-> 0] ::: [a >-> ms a] ::: HNil) (@list_fix A).
Eval cbv beta iota delta -[plus] in
  fun A ms => measure ([a >-> ms a] ::: [_ >-> 0] ::: HNil) (@tree_fix A).
*)

(******************************** Correctness *********************************)

Section ok.
  Variable T : Type.
  Variable dt : datatype.

  Variable dd : datatypeDenote T dt.
  Variable fx : fixDenote T dt.

  Definition datatypeDenoteOk :=
    forall P : T -> Prop,
      (forall c (m : member c dt)
                (x : nonrecursive c)
                (r : ilist T (recursive c)),
        (forall i : fin (recursive c), P (get r i))
        -> P ((hget dd m) x r))
      -> forall v, P v.

  Definition fixDenoteOk :=
    forall (R : Type) (cases : datatypeDenote R dt)
      c (m : member c dt)
      (x : nonrecursive c) (r : ilist T (recursive c)),
      fx cases ((hget dd m) x r)
      = (hget cases m) x (imap (fx cases) r).
End ok.

(* EXERCISE: Prove that `datatypeDenoteOk` and `fixDenoteOk` hold for
   `Empty_set`, `unit`, `bool`, `nat`, and `list`.  If you want, you can extend
   it to `tree` and `tree234` in the same way, but you'll probably want to
   figure out some sort of automation in that case (it's mechanical but messy; I
   don't have an automated version).  Some of my proofs used `dep_destruct`, so
   remember that that exists. *)
   
Theorem Empty_set_dt_ok : datatypeDenoteOk Empty_set_den.
Admitted.

Theorem unit_dt_ok : datatypeDenoteOk unit_den.
Admitted.

Theorem bool_dt_ok : datatypeDenoteOk bool_den.
Admitted.

Theorem nat_dt_ok : datatypeDenoteOk nat_den.
Admitted.

Theorem list_dt_ok : forall A, datatypeDenoteOk (list_den A).
Admitted.

(* Optional *)
(*
Theorem tree_dt_ok : forall A, datatypeDenoteOk (tree_den A).
Admitted.
*)

(* Optional *)
(*
Theorem tree234_dt_ok : forall A, datatypeDenoteOk (tree234_den A).
Admitted.
*)

Theorem Empty_set_fix_ok : fixDenoteOk Empty_set_den Empty_set_fix.
Admitted.

Theorem unit_fix_ok : fixDenoteOk unit_den unit_fix.
Admitted.

Theorem bool_fix_ok : fixDenoteOk bool_den bool_fix.
Admitted.

Theorem nat_fix_ok : fixDenoteOk nat_den nat_fix.
Admitted.

Theorem list_fix_ok : forall A, fixDenoteOk (list_den A) (@list_fix A).
Admitted.

(* Optional *)
(*
Theorem tree_fix_ok : forall A, fixDenoteOk (tree_den A) (@tree_fix A).
Admitted.
*)

(* Optional *)
(*
Theorem tree234_fix_ok : forall A, fixDenoteOk (tree234_den A) (@tree234_fix A).
Admitted.
*)

Lemma foldr_plus : forall n (ils : ilist nat n),
  foldr plus 1 ils > 0.
Proof.
  induction ils; crush.
Qed.

Theorem size_positive : forall T dt
  (dd : datatypeDenote T dt)  (fx : fixDenote T dt)
  (dok : datatypeDenoteOk dd) (fok : fixDenoteOk dd fx)
  (v : T),
  size fx v > 0.
Proof.
  unfold size. intros.
  pattern v.
  apply dok. intros. crush.
  rewrite hget_hmake.
  apply foldr_plus.
Restart.
  Hint Rewrite hget_hmake.
  Hint Resolve foldr_plus.
  unfold size; intros; pattern v; apply dok; crush.
Qed.

Theorem map_id : forall T dt
  (dd  : datatypeDenote T dt) (fx : fixDenote T dt)
  (dok : datatypeDenoteOk dd) (fok : fixDenoteOk dd fx)
  (v : T),
  map dd fx (fun x => x) v = v.
Proof.
  Hint Rewrite hget_hmap.

  unfold map. intros. pattern v.
  apply dok. crush.
  remember (fun (x : constructor) (c : constructorDenote T x)
              (x0 : nonrecursive x) (r : ilist T (recursive x)) => 
            c x0 r) as FN.
  f_equal.
  induction r.
  crush.
  simpl.
  f_equal.
  apply (H First).
  apply IHr. intros.
  apply (H (Next i)).
Restart.
  Hint Rewrite hget_hmap.

  unfold map; intros; pattern v; apply dok; crush.
  f_equal.
  induction r; crush.

  f_equal.
  apply (H First).
  apply IHr; crush.
  apply (H (Next i)).
Qed.
