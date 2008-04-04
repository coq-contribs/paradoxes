(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(****************************************************************************)
(*                                                                          *)
(*                                Coq V6.3                                  *)
(*                                                                          *)
(*                 A choice axiom that entails excluded middle              *)
(*                                                                          *)
(* Following ideas of Diaconescu, Goodman, Myhill and Lacas.                *)
(*                                                                          *)
(*                             Benjamin Werner                              *)
(*                                                                          *)
(*                                  1997                                    *)
(****************************************************************************)



Section TTDiaconescu.


(* Definition of what is an equivalence relation *)

Definition EquivRel (A : Set) (R : A -> A -> Prop) :=
  (forall x : A, R x x) /\
  (forall x y : A, R x y -> R y x) /\
  (forall x y z : A, R x y -> R y z -> R x z).


(* The axiom of choice *)

Definition Tchoice :=
  forall (A : Set) (R : A -> A -> Prop),
  EquivRel A R ->
  ex
    (fun f : A -> A =>
     (forall x : A, R x (f x)) /\ (forall x y : A, R x y -> f x = f y)).


Hypothesis TTCA : Tchoice.



(* The proposition to be decided  *)

Hypothesis P : Prop.


(* The relation R *)

Inductive rel : bool -> bool -> Prop :=
  | rrefl : forall b : bool, rel b b
  | rel2 : forall b c : bool, P -> rel b c.

Hint Resolve rrefl rel2.

(* R is an equivalence relation *)
Lemma rel_trans : forall x y z : bool, rel x y -> rel y z -> rel x z.
intros x y z h1; inversion h1; auto.
Qed.

Lemma rel_sym : forall x y : bool, rel x y -> rel y x.
intros x y h; inversion h; auto.
Qed.

Hint Resolve rel_sym rel_trans.


Lemma rel_equiv : EquivRel bool rel.
split; auto; split; intros; eauto.
Qed.



(* equality is decidable over booleans -- of course  *)
Lemma eq_bool_dec : forall a b : bool, a = b \/ a <> b.
simple induction a; simple induction b; auto; try (right; discriminate).
Qed.



(* The proof of the excluded middle  *)
Theorem EM : P \/ ~ P.

(* first we exhibit the choice function f *)
elim (TTCA bool rel rel_equiv).
intros f; simple induction 1; intros hf1 hf2.

(* the actual "decision": compare (f true) and (f false) *)
elim (eq_bool_dec (f true) (f false)); intros h.

(* case where P is true *)
cut (rel true false).
intros hr; inversion hr; auto.
apply rel_trans with (f true); auto.

rewrite h.
apply rel_sym; auto.

(* case where P is false *)
right; unfold not in |- *; intros p.
apply h.
apply hf2.
auto.

Qed.


End TTDiaconescu.



(* We obtain the closed term   EM : Tchoice->(P:Prop)P\/~P        *)



(************************************************************)
(* A variant, using another formulation of the choice axiom *)
(************************************************************)


Inductive EXType (A : Type) (P : A -> Prop) : Prop :=
    EXi : forall a : A, P a -> EXType A P.


Section TTDiaconescu2.


(* The axiom of choice *)

Definition Tchoice2 :=
  forall (A : Set) (R : A -> A -> Prop),
  EquivRel A R ->
  EXType (A -> Prop)
    (fun P : A -> Prop =>
     (forall x : A, ex (fun y : A => R x y /\ P y)) /\
     (forall x y : A, R x y -> P x -> P y -> x = y)).


Hypothesis TTAC2 : Tchoice2.

Hypothesis P : Prop.


Definition rel' := rel P.

Hint Resolve rel2.

Lemma EM2 : P \/ ~ P.
elim (TTAC2 bool rel' (rel_equiv P)).
intro Q; simple induction 1; intros hQ1 hQ2.
elim (hQ1 true); intros w_true; simple induction 1; intros ht1 ht2.
elim (hQ1 false); intros w_false; simple induction 1; intros hf1 hf2.
elim (eq_bool_dec w_true w_false); intro e.
left; cut (rel' true false).
intro hr; inversion hr; auto.
unfold rel' in |- *; apply rel_trans with w_true; auto.
apply rel_sym; rewrite e; auto.
right; unfold not in |- *; intro p; apply e; auto.
apply hQ2; auto.
unfold rel' in |- *; auto.
Qed.

End TTDiaconescu2. 