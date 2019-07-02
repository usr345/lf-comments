Set Warnings "-notation-overridden,-parsing".
Require Import List.
Import ListNotations.
Require Import PeanoNat.
(* Import Nat. *)
Local Open Scope nat_scope.

Inductive nostutter {X:Type} : list X -> Prop :=
| ns_nil : nostutter []
| ns_one : forall (x : X), nostutter [x]
| ns_cons: forall (x : X) (h : X) (t : list X), nostutter (h::t) -> x <> h -> nostutter (x::h::t).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
  repeat constructor; apply Nat.eqb_neq; auto.
Qed.

Example test_nostutter_1_1: nostutter [3;1;4;1;5;6].
Proof.
  constructor; try (apply Nat.eqb_neq).
Abort.

Example test_nostutter_1_2: nostutter [3;1;4;1;5;6].
Proof.
  (* [3;1;4;1;5;6] *)
  constructor.
  2: {apply Nat.eqb_neq. trivial. }
  (* [1;4;1;5;6] *)
  constructor.
  2: {apply Nat.eqb_neq. simpl. reflexivity. }
  (* [4;1;5;6] *)
  constructor.
  2: {apply Nat.eqb_neq. auto. }
  (* [1;5;6] *)
  constructor.
  2: {apply Nat.eqb_neq. auto. }
  (* [5;6] *)
  constructor.
  2: {apply Nat.eqb_neq. auto. }
  (* [6], ns_one applied*)
  constructor.
Qed.

(* do tactical *)
Example test_nostutter_1_3: nostutter [3;1;4;1;5;6].
Proof.
  do 5 (constructor 3; [ | apply Nat.eqb_neq; auto ]).
  constructor.
Qed.

Example test_nostutter_1_4: nostutter [3;1;4;1;5;6].
Proof.
  do 5 (constructor 3; [ | auto using Nat.eqb_neq ]).
  constructor.
Qed.

Example test_nostutter_1_5: nostutter [3;1;4;1;5;6].
Proof.
  do 5 (constructor 3; auto using Nat.eqb_neq).
  constructor.
Qed.

Hint Constructors nostutter.
Example test_nostutter_1_6: nostutter [3;1;4;1;5;6].
Proof.
  auto 6 using Nat.eqb_neq.
Qed.

Example test_nostutter_1_7: nostutter [3;1;4;1;5;6].
Proof.
  auto 6.
Qed.

(* test_nostutter_4 *)

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof.
  intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
         end.
  contradiction.
Qed.



(* unfold not in H5. *)
(* specialize (H5 eq_refl). *)
(* subst tactic *)

Lemma equality_commutes:
  forall (a: bool) (b: bool), a = b -> b = a.
Proof.
  intros.
  subst a.
  reflexivity.
Qed.

Example test_nostutter_4_3commands: not (nostutter [3;1;1;4]).
Proof.
  intro.
  inversion H.
  clear H.
  subst.
Abort.

Example test_nostutter_manual: not (nostutter [3;1;1;4]).
Proof.
  intro.
  inversion_clear H.
  inversion_clear H0.
  unfold not in H2.
  specialize (H2 eq_refl).
  apply H2.
Qed.

Example test_nostutter_4_clear: not (nostutter [3;1;1;4]).
Proof.
  intro.
  repeat match goal with
    H: nostutter _ |- _ => inversion_clear H
         end.
  contradiction.
Qed.
