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
(*                                Log_Rel1.v                                *)
(****************************************************************************)

(* We derive the proof-irrelevance principle from the excluded middle *)

Variable Bool : Prop.

Variable T : Bool -> Prop.

Variable I : Prop -> Bool.

Variable E1 : forall x : Prop, x -> T (I x).

Variable E2 : forall x : Prop, T (I x) -> x.

(* First, some general definition about relations *)

Inductive equiv (A B : Prop) : Prop :=
    equiv_intro : (A -> B) -> (B -> A) -> equiv A B.

Section Relation.

Definition Rel (A : Prop) := A -> A -> Prop.

Definition sym (A : Prop) (R : Rel A) := forall x y : A, R x y -> R y x.

Definition trans (A : Prop) (R : Rel A) :=
  forall x y z : A, R x y -> R y z -> R x z.

Definition inclus (A : Prop) (R S : Rel A) := forall x y : A, R x y -> S x y.

End Relation.

Inductive per (A : Prop) (R : Rel A) : Prop :=
    per_intro : sym A R -> trans A R -> per A R.

Definition Eq (x y : Bool) := equiv (T x) (T y).

(* Eq is a partial equivalence relation over Bool *)
Lemma per_Eq : per Bool Log_Rel1.Eq.
unfold Log_Rel1.Eq in |- *; apply per_intro.
(* 1: (sym Bool [x:Bool][y:Bool](equiv (T x) (T y))) *)
unfold sym in |- *.
simple induction 1; intros; apply equiv_intro; trivial.
(* 2: (trans Bool [x:Bool][y:Bool](equiv (T x) (T y))) *)
unfold trans in |- *.
simple induction 2.
elim H.
intros; apply equiv_intro; auto.
Qed.

Section logical_relation.

Definition exp (A : Prop) (R : Rel A) (B : Prop) (S : Rel B) :
  Rel (A -> B) := fun f g : A -> B => forall x y : A, R x y -> S (f x) (g y).

Definition power (A : Prop) (R : Rel A) : Rel (A -> Bool) :=
  exp A R Bool Log_Rel1.Eq.

End logical_relation.
