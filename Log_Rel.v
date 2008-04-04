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
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                                Log_Rel.v                                 *)
(****************************************************************************)


Lemma cut : forall A B : Prop, A -> (A -> B) -> B.
auto.
Qed.

(* First, some general definition about relations *)

Inductive equiv (A B : Prop) : Prop :=
    equiv_intro : (A -> B) -> (B -> A) -> equiv A B.

Section relation.

Definition Rel (A : Type) := A -> A -> Prop.

Definition sym (A : Type) (R : Rel A) := forall x y : A, R x y -> R y x.

Definition trans (A : Type) (R : Rel A) :=
  forall x y z : A, R x y -> R y z -> R x z.

Definition inclus (A : Type) (R S : Rel A) := forall x y : A, R x y -> S x y.

End relation.

Inductive per (A : Type) (R : Rel A) : Prop :=
    per_intro : sym A R -> trans A R -> per A R.

(* equiv is a partial equivalence relation over Prop *)

Lemma per_equiv : per Prop equiv.
apply per_intro.
(*    subgoal   (sym Prop equiv) *)
unfold sym in |- *; intros x y h.
(*    h : (equiv x y)
      y : Prop
      x : Prop
      subgoal (equiv y x) *)
elim h; intros f1 f2.
(*    f2 : y->x
      f1 : x->y
      subgoal (equiv y x) *)
apply equiv_intro.
(*    subgoal  y->x *)
exact f2.
(*    Solves subgoal. Next subgoal:
      x->y *)
exact f1.
(*    Solves subgoal. Next subgoal:
      (trans Prop equiv) *)
unfold trans in |- *; intros x y z h1 h2.
(*    h2 : (equiv y z)
      h1 : (equiv x y)
      z : Prop
      y : Prop
      x : Prop
      subgoal (equiv x z) *)
elim h2; elim h1; intros f1 f2 f3 f4.
(*    f4 : z->y
      f3 : y->z
      f2 : y->x
      f1 : x->y
      subgoal (equiv x z) *)
apply equiv_intro; intro a.
(*    a : x
      subgoal z *)
exact (f3 (f1 a)).
(*    Solves subgoal. Next subgoal:
      x *)
exact (f2 (f4 a)).
(*    Solves subgoal. *)
Qed.

Section logical_relation.

Definition exp (A : Type) (R : Rel A) (B : Type) (S : Rel B) :
  Rel (A -> B) := fun f g : A -> B => forall x y : A, R x y -> S (f x) (g y).

Definition power (A : Type) (R : Rel A) : Rel (A -> Prop) :=
  exp A R Prop equiv.

End logical_relation.

