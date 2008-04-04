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
(*                            Projet LogiCal                                *)
(*                                                                          *)
(*                     INRIA                        LRI-CNRS                *)
(*              Rocquencourt                        Orsay                   *)
(*                                                                          *)
(*                              May 29th 2002                               *)
(*                                                                          *)
(****************************************************************************)
(*                            Hurkens_set.v                                 *)
(****************************************************************************)

(** This is Hurkens paradox [Hurkens] in system U-, adapted by Herman
    Geuvers [Geuvers] to show the inconsistency in the pure calculus of
    constructions of a retract from Prop into a small type. This file
    focus on the case of a retract into a small type in impredicative
    Set. As a consequence, Excluded Middle in Set is inconsistent with
    the impredicativity of Set.


    References:

    - [Hurkens] A. J. Hurkens, "A simplification of Girard's paradox",
      Proceedings of the 2nd international conference Typed Lambda-Calculi
      and Applications (TLCA'95), 1995.

    - [Geuvers] "Inconsistency of Classical Logic in Type Theory", 2001
      (see www.cs.kun.nl/~herman/note.ps.gz).
*)

(** We show that Hurkens paradox still hold for a retract from the
    negative fragment of Prop only, into bool:Set *)

Section Hurkens_set_neg.

Variable p2b : Prop -> bool.
Variable b2p : bool -> Prop.
Definition dn (A : Prop) := (A -> False) -> False.
Hypothesis p2p1 : forall A : Prop, dn (b2p (p2b A)) -> dn A.
Hypothesis p2p2 : forall A : Prop, A -> b2p (p2b A).

Definition V := forall A : Set, ((A -> bool) -> A -> bool) -> A -> bool.
Definition U := V -> bool.
Definition sb (z : V) : V := fun A r a => r (z A r) a.
Definition le (i : U -> bool) (x : U) : bool :=
  x (fun A r a => i (fun v => sb v A r a)).
Definition induct (i : U -> bool) : Prop :=
  forall x : U, b2p (le i x) -> dn (b2p (i x)).
Definition WF : U := fun z => p2b (induct (z U le)).
Definition I (x : U) : Prop :=
  (forall i : U -> bool, b2p (le i x) -> dn (b2p (i (fun v => sb v U le x)))) ->
  False.

Lemma Omega : forall i : U -> bool, induct i -> dn (b2p (i WF)).
intros i y.
apply y.
unfold le, WF, induct in |- *.
apply p2p2.
intros x H0.
apply y.
exact H0.
Qed.

Lemma lemma : induct (fun u => p2b (I u)).
unfold induct in |- *.
intros x p.
intro H; apply H.
apply (p2p2 (I x)).
intro q.
apply (p2p1 (I (fun v : V => sb v U le x)) (q (fun u => p2b (I u)) p)).
intro H'; apply H'.
intro i.
apply q with (i := fun y => i (fun v : V => sb v U le y)).
Qed.

Lemma lemma2 : (forall i : U -> bool, induct i -> dn (b2p (i WF))) -> False.
intro x.
apply (p2p1 (I WF) (x (fun u => p2b (I u)) lemma)).
intro H; apply H.
intros i H0.
apply (x (fun y => i (fun v => sb v U le y))).
assert (H1 : dn (induct (fun y : U => i (fun v : V => sb v U le y)))).
assert (H0' : dn (b2p (le i WF))).
  intro H1; apply H1; exact H0.
apply (p2p1 _ H0').
intros y H2 H3.
apply H1.
intro H4.
unfold induct in H4.
unfold dn in H4.
apply (H4 y H2 H3).
Qed.

Theorem Hurkens_set_neg : False.
exact (lemma2 Omega).
Qed.

End Hurkens_set_neg.

Section EM_set_neg_inconsistency.

Variable EM_set_neg : forall A : Prop, {~ A} + {~ ~ A}.

Definition p2b (A : Prop) :=
  if EM_set_neg A then false else true.
Definition b2p (b : bool) := b = true.

Lemma p2p1 : forall A : Prop, ~ ~ b2p (p2b A) -> ~ ~ A.
Proof.
intro A.
unfold p2b in |- *.
destruct (EM_set_neg A) as [_| Ha].
  unfold b2p in |- *; intros H Hna; apply H; discriminate.
  tauto.
Qed.

Lemma p2p2 : forall A : Prop, A -> b2p (p2b A).
Proof.
intro A.
unfold p2b in |- *.
destruct (EM_set_neg A) as [Hna| _].
  intro Ha; elim (Hna Ha).
  intro; unfold b2p in |- *; reflexivity.
Qed.

Theorem not_EM_set_neg : False.
Proof.
apply Hurkens_set_neg with p2b b2p.
apply p2p1.
apply p2p2.
Qed.

End EM_set_neg_inconsistency.

Section EM_set_inconsistency.

Variable EM_set_neg : forall A : Prop, {A} + {~ A}.

Theorem not_EM_set : False.
Proof.
apply not_EM_set_neg.
intro A; apply EM_set_neg.
Qed.

End EM_set_inconsistency.
