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


(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                 Coq V6.3                                 *)
(*                               January 1998                               *)
(*                                                                          *)
(****************************************************************************)
(*                                 Logics.v                                 *)
(****************************************************************************)

(* Some properties about relations on objects in Type *)

  Inductive ACC (A : Type) (R : A -> A -> Prop) : A -> Prop :=
      ACC_intro :
        forall x : A, (forall y : A, R y x -> ACC A R y) -> ACC A R x.

  Lemma ACC_nonreflexive :
   forall (A : Type) (R : A -> A -> Prop) (x : A),
   ACC A R x -> R x x -> False.
simple induction 1; intros.
exact (H1 x0 H2 H2).
Qed.

  Definition WF (A : Type) (R : A -> A -> Prop) := forall x : A, ACC A R x.


Section Inverse_Image.

  Variables (A B : Type) (R : B -> B -> Prop) (f : A -> B).

  Definition Rof (x y : A) : Prop := R (f x) (f y).

  Remark ACC_lemma :
   forall y : B, ACC B R y -> forall x : A, y = f x -> ACC A Rof x.
    simple induction 1; intros.
    constructor; intros.
    apply (H1 (f y0)); trivial.
    elim H2 using eq_ind_r; trivial.
    Qed.

  Lemma ACC_inverse_image : forall x : A, ACC B R (f x) -> ACC A Rof x.
    intros; apply (ACC_lemma (f x)); trivial.
    Qed.

  Lemma WF_inverse_image : WF B R -> WF A Rof.
    red in |- *; intros; apply ACC_inverse_image; auto.
    Qed.

End Inverse_Image.