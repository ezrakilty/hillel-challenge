Require Import Arith.
Require Import List.

Require Import Omega.

Require Import listkit.

Parameter char : Set.

Definition leftpad c n (s : list char) :=
  repeat c (n - length s) ++ s.

(** Proving the three correctness conditions separately. *)

Lemma c1 :
  forall c n s,
    length (leftpad c n s) = max n (length s).
Proof.
 unfold leftpad.
 intros.
 autorewrite with list_lemmas.
 destruct (le_lt_dec n (length s)).
  rewrite max_r; omega.
 rewrite max_l; omega.
Qed.

Lemma c2 :
  forall s c n,
    allEq _ (take _ (n - length s) (leftpad c n s)) c.
Proof.
 unfold leftpad.
 unfold allEq.
 intros.
 autorewrite with list_lemmas.
  apply listall_repeat.
 autorewrite with list_lemmas; auto.
Qed.

Lemma c3 :
  forall n c s,
    drop _ (n - length s) (leftpad c n s) = s.
Proof.
 unfold leftpad.
 intros.
 autorewrite with list_lemmas;
   autorewrite with list_lemmas; auto.
Qed.

(** Proving all three correctness conditions at once. *)
Lemma correctness:
  forall c n s,
    length (leftpad c n s) = max n (length s) /\
    allEq _ (take _ (n - length s) (leftpad c n s)) c /\
    drop _ (n - length s) (leftpad c n s) = s.
Proof.
 unfold leftpad.
 firstorder (autorewrite with list_lemmas; auto).
    destruct (le_lt_dec n (length s)).
     rewrite max_r; try omega.
    rewrite max_l; omega.
   apply listall_repeat.
  firstorder (autorewrite with list_lemmas; auto).
 firstorder (autorewrite with list_lemmas; auto).
Qed.
