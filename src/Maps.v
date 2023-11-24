From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.

Set Implicit Arguments.
Set Asymmetric Patterns.

(* A mapping from naturals to booleans 
 * used particularly within the Subset exercises *)
Definition bool_map := nat -> bool.

Definition empty_map : bool_map := fun _ => false.

Definition map_update n b m : bool_map := fun k =>
  if k =? n then b
  else m k.

Declare Scope bool_map_scope.

Notation "k '!->' v ';' m" := (map_update k v m) 
                              (at level 75, right associativity) : bool_map_scope.

Definition pbool_map := nat -> option bool.

Definition pempty_map : pbool_map := fun _ => None.

Definition pmap_update n b m : pbool_map := fun k =>
  if k =? n then Some b
  else m k.

Notation "k '|->' v ; m" := (pmap_update k v m)
                            (at level 75, right associativity): bool_map_scope.
