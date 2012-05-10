Add LoadPath "megacz-coq-categories/build".

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Unicode.Utf8.

Require Import Categories_ch1_3.


Definition Map : Type -> Type -> Type
  := fun a b : Type => a -> b.

Definition map_id : ∀ a : Type, Map a a
  := (fun a : Type => (fun x => x)).

Definition map_comp : ∀ a b c : Type, Map a b -> Map b c -> Map a c
  := fun a b c r1 r2 x => r2 (r1 x).


Definition map_eqv : forall a b : Type, Map a b -> Map a b -> Prop
  := fun a b r1 r2 => forall x, r1 x = r2 x.


Theorem sets_category : Category Type Map.
Proof.
  apply (@Build_Category Type Map map_id map_comp map_eqv).
  intros.
  apply Build_Equivalence.
  intro.
  unfold map_eqv.
  intros.
  reflexivity.

  intro.
  unfold map_eqv.
  intros.
  symmetry.
  auto.
  
  intro.
  unfold map_eqv.
  intros.
  transitivity (y x0).
  auto.
  auto.

  intros.
  unfold Proper.
  unfold respectful.
  unfold map_eqv.
  unfold map_comp.
  intros.
  congruence.

  unfold map_id.
  unfold map_comp.
  unfold map_eqv.
  intros.
  reflexivity.

  unfold map_id.
  unfold map_comp.
  unfold map_eqv.
  intros.
  reflexivity.

  unfold map_comp.
  unfold map_eqv.
  intros.
  reflexivity.
Defined.

Require Import Rel.
Require Import Functors_ch1_4.

Definition sets_fobj : sets_category -> relation_category
  := fun s => s.

Definition sets_fmor :
  forall a b : sets_category,
    (a ~~{sets_category}~~> b) -> ((sets_fobj a) ~~{relation_category}~~> (sets_fobj b))
  := fun (a b : sets_category) (f : a ~> b) x y => f x = y.

Theorem sets_functor : Functor sets_category relation_category sets_fobj.
Proof.
  apply (Build_Functor _ _ _ _ _ _ sets_fobj sets_fmor).
  intros.
  unfold sets_fmor.
  red.
  simpl.
  unfold rel_eqv.
  intros.
  rewrite (H x).
  tauto.

  intros.
  red.
  simpl.
  unfold rel_eqv, sets_fmor, map_id, rel_id, sets_fobj.
  tauto.

  intros.
  unfold sets_fmor.
  red.
  simpl.
  unfold rel_eqv, sets_fmor, map_id, rel_id, sets_fobj.
  intros.
  unfold rel_comp, map_comp.
  split.
  intros.
  destruct H.
  destruct H.
  congruence.
  intros.
  exists (f x).
  tauto.
Defined.
