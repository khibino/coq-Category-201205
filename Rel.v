Add LoadPath "megacz-coq-categories/build".

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Unicode.Utf8.

Require Import Categories_ch1_3.


Definition Rel : Type -> Type -> Type
  := fun a b : Type => a -> b -> Prop.

Definition rel_id : ∀ a : Type, Rel a a
  := (fun a : Type => @eq a).

Definition rel_comp : ∀ a b c : Type, Rel a b -> Rel b c -> Rel a c
  := fun a b c r1 r2 x y => exists z, r1 x z /\ r2 z y.


Definition rel_eqv : ∀ a b : Type, Rel a b -> Rel a b -> Prop
  := fun a b r1 r2 => ∀ x y, r1 x y <-> r2 x y.


Theorem relation_category : Category Type Rel.
Proof.
  apply (@Build_Category Type Rel rel_id rel_comp rel_eqv).
  intros.
  apply Build_Equivalence.
  intro.
  unfold rel_eqv.
  intros.
  reflexivity.

  intro.
  unfold rel_eqv.
  intros.
  symmetry.
  auto.

  intro.
  unfold rel_eqv.
  intros.
  transitivity (y x0 y0).
  auto.
  auto.

  intros.
  constructor.
  unfold rel_comp.

  intros [z [??]].
  exists z.
  rewrite <- (H x1 z).
  rewrite <- (H0 z y1).
  auto.

  unfold rel_comp.
  intros [z [??]].
  exists z.
  rewrite (H x1 z).
  rewrite (H0 z y1).
  auto.

  unfold rel_id.
  unfold rel_comp.
  unfold rel_eqv.
  intros.
  split.
  intros.
  destruct H.
  destruct H.
  rewrite H.
  auto.

  intros.
  exists x.
  auto.

  intros.
  unfold rel_id.
  unfold rel_comp.
  unfold rel_eqv.
  intros.
  split.
  intro.
  destruct H.
  destruct H.
  rewrite <- H0.
  auto.

  intro.
  exists y.
  auto.

  intros.
  unfold rel_comp.
  unfold rel_eqv.
  intros.
  split.
  intro.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  exists x1.
  split.
  auto.

  exists x0.
  auto.

  intro.
  destruct H.
  destruct H.
  destruct H0.
  destruct H0.
  exists x1.
  split.
  exists x0.
  auto.
  auto.
Defined.

(*
Definition rel_comp : forall a b c : Type, Rel a b -> Rel b c -> Rel a c.
Proof.
  intros.
  intro.
  intro.
  refine (exists b' : b, _ /\ _).
  exact (X X1 b').
  exact (X0 b' X2).
Defined.
*)
