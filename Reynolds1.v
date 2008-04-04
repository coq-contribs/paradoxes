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
(*                               Reynolds1.v                                *)
(****************************************************************************)

Require Import Log_Rel1.

(* Reynolds operator *)

Definition PHI (A : Prop) := (A -> Bool) -> Bool.

(* we extend this map functorialy *)

Definition phi (A B : Prop) (f : A -> B) (z : PHI A) : 
  PHI B := fun u : B -> Bool => z (fun x : A => u (f x)).

(* preinitial PHI-algebra. We need the axiom (Prop,Prop) *)

Definition A0 := forall A : Prop, (PHI A -> A) -> A.

Definition iter_A0 (X : Prop) (f : PHI X -> X) (u : A0) := u X f.

Definition intro (z : PHI A0) : A0 :=
  fun (A : Prop) (f : PHI A -> A) => f (phi A0 A (iter_A0 A f) z).

(* Extension of PHI to relations. We can thus consider PHI as a functor
   on sets, that are types with a relations *)

Definition phi2 (A : Prop) (R : Rel A) : Rel (PHI A) :=
  power (A -> Bool) (power A R).

(* Partial equivalence relation defined on A0, so that the set A0,E0
   is an initial PHI-algebra in the category of sets *)

Definition teta : A0 -> PHI A0 := iter_A0 (PHI A0) (phi (PHI A0) A0 intro).

Definition E0 : Rel A0 :=
  fun x1 x2 : A0 =>
  forall E : Rel A0,
  per A0 E ->
  (forall z1 z2 : PHI A0, phi2 A0 E z1 z2 -> E (intro z1) (intro z2)) ->
  (forall x1 x2 : A0, E x1 x2 -> E x1 (intro (teta x2))) -> E x1 x2.

Definition F0 : Rel (A0 -> Bool) := power A0 E0.

Definition G0 : Rel (PHI A0) := power (A0 -> Bool) F0.

(* the goal of what follows is to show that the set A0,E0 is in one-to-one
   correspondance with the set (PHI A0),(phi2 A0 E0), via intro,teta.
   From this, we deduce a contradiction via Cantor-Russell's argument *)

Theorem sym_E0 : sym A0 E0.
Proof.
unfold sym in |- *; intros x y h1.
unfold E0 in |- *; intros E h2 h3 h4.
elim h2.
unfold sym in |- *; intros h5 h6.
apply h5.
apply (h1 E).
exact h2.
exact h3.
exact h4.
Qed.

Theorem trans_E0 : trans A0 E0.
Proof.
unfold trans in |- *; intros x y z h1 h2.
unfold E0 in |- *; intros E h3 h4 h5.
elim h3.
unfold sym, trans in |- *; intros h6 h7.
apply h7 with y.
apply (h1 E); auto.
apply (h2 E); auto.
Qed.

Theorem per_E0 : per A0 E0.
Proof.
apply per_intro.
exact sym_E0.
exact trans_E0.
Qed.

(* intro is a map from (PHI A0),(phi2 A0 E0) to A0,E0 *)
Theorem lemma1 : forall z1 z2 : PHI A0, G0 z1 z2 -> E0 (intro z1) (intro z2).
Proof.
unfold E0 in |- *; intros z1 x2 h1 E h2 h3 h4.
apply h3; hnf in |- *; intros x y h5.
apply h1; hnf in |- *; intros x0 y0 h6.
apply h5.
apply (h6 E); auto.
Qed.

Theorem per_F0 : per (A0 -> Bool) F0.
Proof.
unfold F0 in |- *.
unfold power in |- *.
elim per_E0; intros h1 h2.
elim per_Eq; intros h3 h4.
apply per_intro.
unfold sym in |- *; intros x y h5.
unfold exp in |- *; intros x0 y0 h6.
apply h3.
apply h5.
apply h1.
exact h6.
unfold trans in |- *; intros x y z h5 h6.
unfold exp in |- *; intros x0 y0 h7.
eapply h4.
instantiate ( 1 := y y0) in |- *.
eapply h5.
exact h7.
apply h6.
eapply h2.
instantiate ( 1 := x0) in |- *.
apply h1.
exact h7.
exact h7.
Qed.

Theorem per_G0 : per (PHI A0) G0.
Proof.
unfold G0 in |- *.
unfold power in |- *.
elim per_F0; intros h1 h2.
elim per_Eq; intros h3 h4.
apply per_intro.
unfold sym in |- *; intros x y h5.
unfold exp in |- *; intros x0 y0 h6.
apply h3.
apply h5.
apply h1; auto.
unfold trans in |- *; intros x y z h5 h6.
unfold exp in |- *; intros x0 y0 h7.
eapply h4.
instantiate ( 1 := y y0) in |- *.
apply h5.
exact h7.
apply h6.
eapply h2.
instantiate ( 1 := x0) in |- *.
apply h1.
exact h7.
exact h7.
Qed.

Theorem id_intro_teta :
 forall x1 x2 : A0, E0 x1 x2 -> E0 x1 (intro (teta x2)).
Proof.
intros x1 x2 h1; unfold E0 in |- *; intros E h2 h3 h4.
apply h4.
apply (h1 E); auto.
Qed.

Theorem id_teta_intro :
 forall z1 z2 : PHI A0, G0 z1 z2 -> G0 z1 (teta (intro z2)).
Proof.
intros z1 z2 h1; hnf in |- *; intros x y h2.
change (Log_Rel1.Eq (z1 x) (z2 (fun x : A0 => y (intro (teta x))))) in |- *.
apply h1; unfold F0, power, exp in |- *; intros x0 y0 h3.
apply h2.
apply id_intro_teta; auto.
Qed.

Theorem lemma_teta : forall x1 x2 : A0, E0 x1 x2 -> G0 (teta x1) (teta x2).
Proof.
intros x1 x2 h1.
change ((fun u v : A0 => G0 (teta u) (teta v)) x1 x2) in |- *.
apply h1.
elim per_G0.
intros h2 h3.
apply per_intro.
unfold sym in |- *.
intros x y h4.
apply h2.
exact h4.
unfold trans in |- *; intros x y z h4 h5.
eapply h3.
instantiate ( 1 := teta y) in |- *.
exact h4.
exact h5.
intros z1 z2 h2; hnf in |- *; intros x y h3.
change
  (Log_Rel1.Eq (z1 (fun u : A0 => x (intro (teta u))))
     (z2 (fun u : A0 => y (intro (teta u))))) in |- *.
apply h2; unfold power, exp in |- *; intros x0 y0 h4.
apply h3.
apply lemma1; auto.
intros x3 x4 h2; apply id_teta_intro; auto.
Qed.

Definition f0 (x y : A0 -> Bool) := I (F0 x y).

Definition psi (u : A0 -> Bool) : A0 := intro (f0 u).

Definition inter (C : PHI A0) (x : A0) : Bool :=
  I (forall P : A0 -> Bool, F0 P P -> T (C P) -> T (P x)).

Definition INTER (C : PHI A0) (x : A0) : Prop :=
  forall P : A0 -> Bool, F0 P P -> T (C P) -> T (P x).

Theorem lemma_inter :
 forall z1 z2 : PHI A0, G0 z1 z2 -> F0 (inter z1) (inter z2).
Proof.
intros z1 z2 H; hnf in |- *; intros x y H0.
unfold Log_Rel1.Eq in |- *.
apply equiv_intro; intro H1.

unfold inter in |- *.
apply E1; intros P H2 H3.
cut (Log_Rel1.Eq (P x) (P y)).
unfold Log_Rel1.Eq in |- *; intro H4.
elim H4; intros H5 H6.
apply H5.
cut (forall P : A0 -> Bool, F0 P P -> T (z1 P) -> T (P x)).
intro H7; apply H7.
exact H2.
cut (Log_Rel1.Eq (z1 P) (z2 P)).
unfold Log_Rel1.Eq in |- *; intro H8.
elim H8; intros H9 H10.
exact (H10 H3).
apply H.
exact H2.
apply E2.
apply H1.
apply H2.
exact H0.

unfold inter in |- *.
apply E1; intros P H2 H3.
cut (Log_Rel1.Eq (P x) (P y)).
unfold Log_Rel1.Eq in |- *; intro H4.
elim H4; intros H5 H6.
apply H6.
cut (forall P : A0 -> Bool, F0 P P -> T (z2 P) -> T (P y)).
intro H7; apply H7.
exact H2.
cut (Log_Rel1.Eq (z1 P) (z2 P)).
unfold Log_Rel1.Eq in |- *; intro H8.
elim H8; intros H9 H10.
exact (H9 H3).
apply H.
exact H2.
apply E2.
apply H1.
apply H2.
exact H0.
Qed.

(* we follow Cantor-Russell's paradox *)

Definition khi (x : A0) : A0 -> Bool := inter (teta x).

Section paradox.

Variable p : Prop.

Definition u0 (x : A0) : Bool := I (T (khi x x) -> p).

Definition x0 : A0 := psi u0.

Theorem lemma4 : E0 x0 x0.
Proof.
unfold x0 in |- *.
unfold psi in |- *.
apply lemma1; hnf in |- *; intros x y H.
elim per_F0; intros H0 H1.
unfold f0, Log_Rel1.Eq in |- *.
apply equiv_intro; intro H2.
apply E1.
eapply H1.
instantiate ( 1 := x) in |- *.
apply E2.
exact H2.
exact H.
apply E1.
eapply H1.
instantiate ( 1 := y) in |- *.
apply E2.
exact H2.
apply H0.
exact H.
Qed.

Theorem lemma3 : F0 u0 u0.
Proof.
hnf in |- *; intros x y H.
cut (F0 (khi x) (khi y)).
unfold khi in |- *; intro H0.
cut (Log_Rel1.Eq (khi x x) (khi y y)).
unfold Log_Rel1.Eq in |- *; intro H1.
elim H1; intros H2 H3.
unfold u0 in |- *.
apply equiv_intro; intro H4.
apply E1; intro H5.
apply (E2 (T (khi x x) -> p) H4).
exact (H3 H5).
apply E1; intro H5.
apply (E2 (T (khi y y) -> p) H4).
exact (H2 H5).
unfold khi in |- *; apply H0.
exact H.
unfold khi in |- *.
apply lemma_inter.
apply lemma_teta; auto.
Qed.

Theorem lemma5 : F0 u0 (khi x0).
Proof.
unfold x0, psi in |- *.
unfold khi in |- *.
cut (per (A0 -> Bool) F0).
intro H; elim H; intros H0 H1.
eapply H1; try instantiate ( 1 := inter (f0 u0)) in |- *.
hnf in |- *; intros x y H2.
unfold Log_Rel1.Eq in |- *.
apply equiv_intro; intro H3.

unfold inter in |- *.
apply E1; intros P H4 H5.
cut (Log_Rel1.Eq (u0 x) (P y)).
unfold Log_Rel1.Eq in |- *; intro H6.
elim H6; intros H7 H8.
exact (H7 H3).
cut (F0 u0 P).
intro H6; apply H6; auto.
apply E2; auto.

cut (F0 u0 u0).
intro H4.
cut (Log_Rel1.Eq (u0 x) (u0 y)).
unfold Log_Rel1.Eq in |- *; intro H5.
elim H5; intros H6 H7.
apply H7.
cut (INTER (f0 u0) y).
intro H8; apply H8.
exact H4.
exact (E1 (F0 u0 u0) H4).
apply E2; apply H3.
apply H4.
exact H2.
exact lemma3.

apply lemma_inter.
hnf in |- *; intros x y H2.
cut (G0 (f0 u0) (teta (intro (f0 u0)))).
intro H3; apply H3.
exact H2.
apply id_teta_intro.
hnf in |- *; intros x' y0 H3.
unfold Log_Rel1.Eq in |- *.
apply equiv_intro; intro H4.

unfold f0 in |- *.
apply E1.
eapply H1; try instantiate ( 1 := x') in |- *.
apply E2; auto.
exact H3.
unfold f0 in |- *.
apply E1.
eapply H1; try instantiate ( 1 := y0) in |- *.
apply E2; auto.
apply H0; auto.
apply per_F0.

Qed.

Theorem lemma6 : Log_Rel1.Eq (u0 x0) (khi x0 x0).
Proof.
apply lemma5.
exact lemma4.
Qed.

Theorem lemma7 : T (u0 x0).
Proof.
unfold u0 in |- *.
apply E1; intro H.
cut (Log_Rel1.Eq (u0 x0) (khi x0 x0)).
unfold Log_Rel1.Eq in |- *; intro H0.
elim H0; intros H1 H2.
cut (T (u0 x0)).
intro H3.
exact (E2 (T (khi x0 x0) -> p) H3 H).
exact (H2 H).
apply lemma6.
Qed.

Theorem Reynolds : p.
Proof.
cut (Log_Rel1.Eq (u0 x0) (khi x0 x0)).
unfold Log_Rel1.Eq in |- *; intro H.
apply (E2 (T (khi x0 x0) -> p) lemma7).
elim H; intros H0 H1.
exact (H0 lemma7).
exact lemma6.
Qed.

End paradox.