Require Import List.

Require Import Cpdt.CpdtTactics.

Require Extraction.

Set Implicit Arguments.
Set Asymmetric Patterns.

Module Ex1.
Inductive Foo : Set :=
  | Bar
  | Baz.

End Ex1.