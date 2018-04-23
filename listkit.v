Require Import Arith.
Require Import List.
Require Import Omega.

(** All elements of a list have a property. *)
Fixpoint listall A P (xs:list A) :=
  match xs with
      nil => True
    | (x::xs) => P x /\ listall _ P xs
  end.

(** All elements of a list have the same (given) value. *)
Definition allEq A xs y := listall A (fun x => x = y) xs.

(** Return the first n elements of a list. *)
Fixpoint take A n (xs : list A) :=
  match xs with
      nil => nil
    | (x::xs) =>
      match n with
          0 => nil
        | S n => x :: take _ n xs
      end
  end.

(** After conjuring up n copies of an element, taking n of them is a no-op. *)
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

(** Taking n elements of a concatentation, when n is less than the
    length of the first concatenand, gives just n elements of that concatenand. *)
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

(** If we conjure copies of a value, all the elements of the list are equal to that value. *)
Lemma listall_repeat :
  forall A c n,
    listall A (fun x => x = c) (repeat c n).
Proof.
 induction n; simpl.
  auto.
 split; auto.
Qed.

(** Return what follows after the first n elements of a list. *)
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

(** Dropping the first n elements of a concatenation, when n is the
    length of the first concatenand, gives just the second concatenand. *)
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
