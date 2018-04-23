(* method Unique(a: seq<int>) returns (b: seq<int>) *)
(*   ensures forall k :: 0 <= k < |a| ==> a[k] in b *)
(*   ensures forall i, j :: 0 <= i < j < |b| ==> b[i] != b[j] *)

Definition HasEqDec A := forall (x y : A), {x = y} + {~ x = y}.

Require Import List.

Fixpoint Unique A (eq : HasEqDec A) (xs : list A) : list A :=
  match xs with
      nil => nil
    | x::xs =>
      let xs' := Unique _ eq xs in
      if in_dec eq x xs' then
        xs'
      else
        x::xs'
  end.

Lemma c1:
  forall A (eq : HasEqDec A) (x:A) xs, In x xs -> In x (Unique _ eq xs).
Proof.
 induction xs; intros; inversion H; simpl;
  destruct (in_dec eq a (Unique A eq xs)); simpl; subst; eauto.
Qed.

Fixpoint tails A (xs : list A) :=
  xs ::
     match xs with
      nil => nil
       | (x::xs) => tails _ xs
      end.

Lemma c2:
  forall A (eq : HasEqDec A) (x:A) xs,
    forall y ys,
    In (y::ys) (tails _ (Unique A eq xs)) ->
    ~ In y ys.
Proof.
 induction xs; simpl; intros.
  inversion H as [H0 | H0].
   inversion H0.
  inversion H0.
 destruct (in_dec eq a (Unique A eq xs)).
  auto.
 simpl in H.
 inversion H.
  inversion H0.
  subst.
  auto.
 auto using IHxs.
Qed.