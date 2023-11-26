Require Import Arith Bool List.
Require Import CpdtTactics MoreSpecif.
Require Import MoreDep.
Set Implicit Arguments.

(* CPDT Chapter 8-More Dependent Types
   Exercises by Jennifer Paykin
*)

Section unject_inverse.
(* Exercise:
   In chapter 10 we defined length-indexed lists. The function 
     inject : forall A (ls : list A), ilist A (length ls)
   takes regular lists and sends them to the corresponding
   length-indexed list, and 
     unject : forall A n, ilist A n -> list A
   takes length-indexed lists and sends them to regular Coq lists.
 
   Adam proved
     inject_inverse : forall A (ls : list A), unject (inject ls) = ls
   We also want to prove the opposite, that
     forall A n (ls : ilist A n), inject (unject ls) = ls
   This theorem is not well-typed, however--ls is an ilist of length n
   and inject (unject ls) is an ilist of length (length (unject ls))!

   Define an equivalence relation ilist_eq on ilists and prove that
   is is in fact an equivalence relation (reflexivity, symmetry, transitivity).
   Then prove
     unject_inverse : forall A n (ls : ilist A n), ilist_eq (inject (unject ls)) ls
*)

End unject_inverse.

Section smallest.
(* Exercise:
   Define a proposition smallest which holds on a nat x and a
   red-black tree t if x occurs in t and is the smallest element in t.
   Follow the structure of the present_insert proofs in Chapter 10 to show
   that x is the smallest element in insert x t if and only if
   either (1) z = x and x is a lower bound on t or
   (2) z <= x and z is the smallest element in t.

   The definition of smallest makes a big difference on how
   easy the correctness proof is! Follow the example set by
   present: define smallest using Fixpoint and prove
   that smallest is correct on the balance functions (like present_balance1),
   on ins (like present_ins), and on insert (like present_insert_Red).

   Alternatively, define smallest in terms of present and
   a lower bound proposition--construct all
   the intermediate proofs for lower bounds and then the 
   correctness of smallest follows.
*)

End smallest.

Section bin_search_tree.
(* Exercise: The one invariant that rbtrees don't take 
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
   an entry is present in a tree and prove that
   y is present in (insert x t) iff y=x or y is present in t.
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



(* Exercise: Use the convoy pattern and your btree definition to 
   write a fixpoint recursive function 
     isEqual : forall m n (t1 t2: btree m n), bool
   which takes two btrees with the same bounds and returns true
   if the trees are equal (have all the same keys in the same structure). 
   
   It may be helpful to define functions which trivially expand
   the bounds of the tree (push the lower bound lower and the higher bound
   higher). These helper functions can have type 
     sinkBound : forall m n (t : btree m n) p (L:p<=m), btree p n
   and
     raiseBound : forall m n (t : btree m n) p (L:n<=p), btree m p
   respectively.
*)
End bin_search_tree.


