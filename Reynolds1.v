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

(** This proves that the axioms defined in Log_Rel1.v are contradictory.
    This specializes the refutation by Reynolds of set semantics for System F:
    John Reynolds. Polymorphism is not set-theoretic.
    [Research Report] RR-0296, INRIA. 1984. inria-00076261
    https://hal.inria.fr/inria-00076261/document

    Here System F is replaced by Coq's universe Prop. This makes sense because
    Prop is impredicative like System F, and Prop can interpret all of System F's
    syntax. For example the forall type alpha in System F is replaced by
    forall alpha:Prop. In his article, Reynolds writes B for Bool, and it is
    an unspecified system F type with at least 2 different terms. We do have
    those terms here: I True and I False. If it helps understanding, we may
    specialize this proof for Bool := forall s:Prop, s -> s -> s, the booleans
    of system F. *)

Require Import Log_Rel1.


(* Definition of the Reynolds functor PHI (written T in Reynolds' article). *)
Definition PHI (A : Prop) := (A -> Bool) -> Bool.
Definition phi {A B : Prop} (f : A -> B) (z : PHI A) : PHI B :=
  fun u : B -> Bool => z (fun x : A => u (f x)).

Lemma phi_id : forall (A : Prop), phi (fun (x:A) => x) = (fun y => y).
Proof. reflexivity. Qed.

Lemma phi_compose : forall (A B C : Prop) (f : A -> B) (g : B -> C) (x : PHI A),
    (phi g) (phi f x) = phi (fun y => g (f y)) x.
Proof. reflexivity. Qed.

(** Definition of the preinitial PHI-algebra A0 (written W in Reynolds' article).
    The algebra is given by A0_cons : PHI A0 -> A0 (written H in Reynolds' article),
    and preinitial means there is a morphism A0_ind (written rho in Reynolds' article)
    from A0 to any other PHI-algebra f. In other words A0 is the inductive type
    Inductive A0 : Prop := A0_cons : PHI A0 -> A0
    and A0_ind is its induction principle.

    We remark that the definition of A0 is impredicative, as allowed by Prop
    (or System F). If we used Type instead of Prop, A0 would live in a higher
    universe than the quantified variable A. *)
Definition A0 : Prop := forall A : Prop, (PHI A -> A) -> A.
Definition A0_ind {X : Prop} (f : PHI X -> X) (u : A0) : X := u _ f.
Definition A0_cons (z : PHI A0) : A0 :=
  fun (A : Prop) (f : PHI A -> A) => f (phi (A0_ind f) z).

Lemma A0_morph_alg : forall {X : Prop} (f : PHI X -> X) (u : PHI A0),
    A0_ind f (A0_cons u) = f (phi (A0_ind f) u).
Proof. reflexivity. Qed.

(** By Lambek's theorem, A0_cons : PHI A0 -> A0 is an isomorphism in the category Prop
    (or System F). In other words, A0 is the least fixed point of functor PHI.
    The inverse morphism A0_match is obtained by considering the algebra
    phi A0_cons : PHI (PHI A0) -> PHI A0,
    and taking the induction morphism from A0 to it.

    Again we remark that the definition of A0_match is impredicative. If we used Type
    instead of Prop, we could still define A0 in higher universes, but Coq would
    refuse A0_match, arguing that the subtype constrains cannot be resolved.

    There is a caveat however. The above would be correct if the morphism from A0 to
    another PHI-algebra, written A0_ind, would be unique. This is the difference
    between preinitial and initial algebras. As in Reynolds' article, we must refine
    A0 to get a true initial algebra. *)
Definition A0_match : A0 -> PHI A0 := A0_ind (phi A0_cons).

(** So far we haven't used the contradictory axiom T. A0, A0_cons and A0_match
    are definable terms of System F. Intuitively this is because the morphisms
    of System F are restricted to be computable lambda-terms. These fewer morphisms
    make A0_cons,A0_match a type isomorphism between A0 and PHI A0.

    We will now trigger a contradiction by moving from the category Prop (or System F)
    to the category of sets. The idea of assigning sets to types, in a way compatible
    with beta reduction, is called denotational semantics. This is what Reynolds
    refuted for system F, only assuming the general translation rules that a semantics
    satisfies. Here we will use the contradictory axiom T to explicitly give the
    (contradictory) set semantics. Our set denotation of A0 is simply a partial
    equivalence relation E0 on A0, which turns A0 into a setoid. In other words,
    our set denotation of A0 is a quotient of A0. A0_cons and A0_match induce quotient
    maps that are truly inverse from each other. In the quotient, all morphisms
    from A0 to any other PHI-algera are equalized, which turns the preinitial algebra
    into an initial algebra.

    Here is a synthesis of our set semantics, for all objects involved in the
    contradiction
    ----------------------------------------
    System F     | Set denotation     
    ----------------------------------------
    Bool         | (Bool, Eq)
    A0           | (A0, E0)
    A -> B       | (A -> B, exp R S)
    A -> Bool    | (A -> Bool, power R)
    PHI A        | (PHI A, power (power R))
    t : A : Prop | t
    A0_cons      | A0_cons
    A0_match     | A0_match

    Proof terms t are denoted by themselves, but in the quotient they may become
    equalized to other terms, or erased when irreflexive.

    First we alias the denotation of PHI A by phi2, and check that PHI extends
    to a functor on sets. *)
Definition phi2 {A : Prop} (R : Rel A) : Rel (PHI A) := power (power R).

(* phi sends a set-function to a set-function
   (which means a function that respects the equality relations). *)
Lemma phi_set_func : forall (A B : Prop) (R : Rel A) (S : Rel B) (f : A -> B),
    (forall x y:A, R x y -> S (f x) (f y))
    -> forall s t : PHI A,
      phi2 R s t -> phi2 S (phi f s) (phi f t).
Proof.
  intros. intros x y H1. unfold power, exp in H1.
  apply H0. intros a b H2. apply H1, H, H2.
Qed.

(** Definition of the partial equivalence relation E0 on A0, so that A0_cons and
    A0_match are inverse set-functions between (A0, E0) and (PHI A0, phi2 E0).
    This makes the set (A0, E0) an initial PHI-algebra in the category of sets.
    E0 is the intersection of all partial equivalence relations E on A0 such that
    A0_cons is a set-function and such that A0_match is the inverse of A0_cons. E0 is
    therefore the smallest such relation, so that the quotient by E0 modifies A0
    the least. We alias the relation phi2 E0 by G0. *)
Definition E0 (x1 x2 : A0) : Prop :=
  forall E : Rel A0,
  per E ->
  (* Assume A0_cons is a set-function that respects relation E.
     This hypothesis prevents E from being empty. *)
  (forall z1 z2 : PHI A0, phi2 E z1 z2 -> E (A0_cons z1) (A0_cons z2)) ->
  (* Assume u and A0_cons (A0_match u) are E-equal, for all (reflexive) elements
     u of the quotient (A,E). *)
  (forall u : A0, E u u -> E u (A0_cons (A0_match u))) ->
  E x1 x2.
Definition F0 : Rel (A0 -> Bool) := power E0. (* Equality on subsets of (A0,E0) *)
Definition G0 : Rel (PHI A0) := power F0.

Lemma G0_phi2 : G0 = phi2 E0.
Proof. reflexivity. Qed.

(** What follows proves that the definition of relation E0 fulfills its goal.
    A0_cons is a set-function (PHI A0, phi2 E0) -> (A0, E0) and A0_match is its
    inverse set-function. In other words, the set (A0, E0) is a fixed point
    of the set-functor PHI (and it is an initial algebra, the smallest such
    fixed point).

    First we show that E0 is a partial equivalence, necessary to define a set.
    Recall that irreflexive elements are allowed in partial equivalences: they
    are considered erased in the quotient (A0, E0). *)

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

Theorem per_E0 : per E0.
Proof.
exact (per_intro _ sym_E0 trans_E0).
Qed.

(* A0_cons : PHI A0 -> A0 is a set-function, it respects the equality relation E0.
   In other words, A0_cons is a PHI-algebra in the category of sets. *)
Theorem lemma1 : forall z1 z2 : PHI A0, G0 z1 z2 -> E0 (A0_cons z1) (A0_cons z2).
Proof.
unfold E0 in |- *; intros z1 x2 h1 E h2 h3 h4.
apply h3; hnf in |- *; intros x y h5.
apply h1; hnf in |- *; intros x0 y0 h6.
apply h5.
apply (h6 E); auto.
Qed.

Theorem per_F0 : per F0.
Proof.
apply power_per, per_E0.
Qed.

Theorem per_G0 : per G0.
Proof.
apply power_per, per_F0.
Qed.

(* Now the inversion theorems. First that A0_match is the right inverse of A0_cons. *)
Theorem id_A0_cons_match :
  forall x : A0, E0 x x -> E0 x (A0_cons (A0_match x)).
Proof.
intros x xrefl E h1 h2 h3.
apply h3.
apply (xrefl E); auto.
Qed.

(* Then A0_match is the left inverse of A0_cons. *)
Theorem id_A0_match_cons :
  forall z : PHI A0, G0 z z -> G0 z (A0_match (A0_cons z)).
Proof.
intros z zrefl x y F0xy.
apply zrefl. intros x0 y0 h3.
apply F0xy.
change (E0 x0 (A0_cons (A0_match y0))).
destruct per_E0 as [sym_E0 trans_E0].
apply (trans_E0 _ y0 _ h3).
apply id_A0_cons_match.
apply (trans_E0 _ x0).
apply sym_E0, h3.
exact h3.
Qed.

(* A0_match : A0 -> PHI A0 is a set-function, it respects the equality relation E0. *)
Theorem A0_match_set_func : forall x1 x2 : A0, E0 x1 x2 -> G0 (A0_match x1) (A0_match x2).
Proof.
intros x1 x2 h1.
change ((fun u v : A0 => G0 (A0_match u) (A0_match v)) x1 x2) in |- *.
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
instantiate (1 := A0_match y) in |- *.
exact h4.
exact h5.
intros z1 z2 h2; hnf in |- *; intros x y h3.
change
  (Log_Rel1.Eq (z1 (fun u : A0 => x (A0_cons (A0_match u))))
     (z2 (fun u : A0 => y (A0_cons (A0_match u))))) in |- *.
apply h2; unfold power, exp in |- *; intros x0 y0 h4.
apply h3.
apply lemma1; auto.
intros x3 x4 h2.
apply id_A0_match_cons, x4.
Qed.

(** We now have an initial PHI-algebra in the category of sets, i.e. a bijection
    between sets (A0, E0) and (PHI A0, phi2 E0). This leads to a contradiction,
    because Cantor's theorem now applies and tells that the powerset of (A0, E0)
    is strictly bigger than (A0, E0). (PHI A0, phi2 E0) is the powerset of the
    powerset of (A0, E0), hence even bigger.

    The cardinal would already be increased by fun (A:Prop) => A -> Bool, which is
    simpler than PHI. However this is not a functor, because it does not apply
    covariantly to functions. 

    We first define intersection. An x : PHI A0 is in the powerset of the powerset
    of A0, which means x is included in the powerset of A0, x is a set of subsets
    of A0. Therefore x can be intersected into a subset of A0. The intersection
    predicate asserts that x:A0 is in the intersection of C:PHI A0. *)
Definition INTER (C : PHI A0) (x : A0) : Prop :=
  forall P : A0 -> Bool, F0 P P -> T (C P) -> T (P x).
Definition inter (C : PHI A0) (x : A0) : Bool :=
  I (INTER C x).

(* inter : PHI A0 -> (A0 -> Bool) is a set-function, it respects equality relations.
   By composition, inter turns the bijection A0_match : A0 ~-> PHI A0 into a
   surjection A0 ->> (A0 -> Bool), written khi below, which directly violates
   Cantor's theorem about powersets. *)
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

Definition f0 (x y : A0 -> Bool) : Bool := I (F0 x y).

Definition psi (u : A0 -> Bool) : A0 := A0_cons (f0 u).

Definition khi (x : A0) : A0 -> Bool := inter (A0_match x).

(** khi is surjective, and so reaches the subset u0 := { x : A0 | x \notin khi x }.
    x0 is the element mapped to u0, i.e. khi x0 = u0. Theorem lemma7 : T (u0 x0)
    will prove that x0 \in u0. This is a contradiction because that means
    x0 \notin khi x0, which in turn implies x0 \notin u0. *)
Definition u0 (x : A0) : Bool := I (T (khi x x) -> False).
Definition x0 : A0 := psi u0.

(* x0 is reflexive for E0, which means x0 is in the set (A0, E0). *)
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

(* u0 is reflexive for F0, which means u0 is in the subset of (A0, E0). *)
Theorem lemma3 : F0 u0 u0.
Proof.
intros x y H.
cut (F0 (khi x) (khi y)).
unfold khi in |- *; intro H0.
cut (Log_Rel1.Eq (khi x x) (khi y y)).
unfold Log_Rel1.Eq in |- *; intro H1.
elim H1; intros H2 H3.
unfold u0 in |- *.
apply equiv_intro; intro H4.
apply E1; intro H5.
apply (E2 (T (khi x x) -> False) H4).
exact (H3 H5).
apply E1; intro H5.
apply (E2 (T (khi y y) -> False) H4).
exact (H2 H5).
unfold khi in |- *; apply H0.
exact H.
unfold khi in |- *.
apply lemma_inter.
apply A0_match_set_func; auto.
Qed.

(* Now we prove khi x0 = u0. *)
Theorem lemma5 : F0 u0 (khi x0).
Proof.
unfold x0, psi in |- *.
unfold khi in |- *.
cut (per F0).
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
cut (G0 (f0 u0) (A0_match (A0_cons (f0 u0)))).
intro H3; apply H3.
exact H2.
apply id_A0_match_cons.
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

Theorem lemma7 : T (u0 x0).
Proof.
unfold u0 in |- *.
apply E1; intro H.
cut (Log_Rel1.Eq (u0 x0) (khi x0 x0)).
unfold Log_Rel1.Eq in |- *; intro H0.
elim H0; intros H1 H2.
cut (T (u0 x0)).
intro H3.
exact (E2 (T (khi x0 x0) -> False) H3 H).
exact (H2 H).
apply lemma5.
exact lemma4.
Qed.

Theorem Reynolds : False.
Proof.
(* lemma7 unfolds to T (I (T (khi x0 x0) -> False)), remove prefix T I. *)
apply (E2 (T (khi x0 x0) -> False) lemma7).
(* We are left to prove T (khi x0 x0), which is equivalent to lemma7. *) 
cut (T (u0 x0)).
apply lemma5, lemma4.
exact lemma7.
Qed.
