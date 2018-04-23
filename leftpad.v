Require Import Arith.
Require Import List.

Require Import Omega.

Fixpoint listall A P (xs:list A) :=
  match xs with
      nil => True
    | (x::xs) => P x /\ listall _ P xs
  end.

Definition allEq A xs y := listall A (fun x => x = y) xs.

Fixpoint take A n (xs : list A) :=
  match xs with
      nil => nil
    | (x::xs) =>
      match n with
          0 => nil
        | S n => x :: take _ n xs
      end
  end.

Lemma take_repeat:
  forall A n c,
    take A n (repeat c n) = repeat c n.
Proof.
 induction n.
  simpl.
  auto.
 simpl.
 intro c.
 rewrite IHn.
 auto.
Qed.

Lemma take_app:
  forall A n (xs ys : list A),
  n <= length xs ->
  take A n (xs ++ ys) = take A n xs.
Proof.
 induction n.
  intros.
  simpl.
  destruct xs; destruct ys; auto.
 intros.
 simpl.
 destruct xs.
  simpl.
  destruct ys.
   auto.
  simpl in H.
  exfalso; omega.
 simpl.
 rewrite IHn.
  auto.
 simpl in H.
 omega.
Qed.

Lemma listall_repeat :
  forall A c n,
    listall A (fun x => x = c) (repeat c n).
Proof.
 induction n; simpl.
  auto.
 split; auto.
Qed.

Fixpoint drop A n (xs : list A) :=
  match n with
      0 => xs
    | S n =>
      match xs with
          nil => nil
        | (x::xs) =>
          drop _ n xs
      end
  end.

Lemma drop_app:
  forall A n (xs ys : list A),
    n = length xs ->
    drop A n (xs ++ ys) = ys.
Proof.
 induction n.
  intros.
  simpl.
  destruct xs; auto.
  simpl in *.
  discriminate.
 intros.
 destruct xs; simpl in *.
  discriminate.
 rewrite IHn; auto.
Qed.

Hint Rewrite take_repeat take_app drop_app app_length repeat_length : list_lemmas.

Parameter char : Set.

Definition leftpad c n (s : list char) :=
  repeat c (n - length s) ++ s.

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
