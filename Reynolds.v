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

(** We show that Prop does not inject into a proposition Heyt. More precisely,
    we refute hypothesis Iinject below. Intuitively, this is justified by the
    proof-irrelevant semantics of Coq, because Prop has at least 2 elements
    (True and False), whereas Heyt:Prop has at most 1 element. As a simple
    corollary, we will show that the excluded middle principle implies proof
    irrelevance.

    This specializes the refutation by Reynolds of set semantics for System F:
    John Reynolds. Polymorphism is not set-theoretic.
    [Research Report] RR-0296, INRIA. 1984. inria-00076261
    https://hal.inria.fr/inria-00076261/document

    Here System F is replaced by Coq's universe Prop. This makes sense because
    Prop is impredicative like System F, and Prop can interpret all of System F's
    syntax. For example the forall type alpha in System F is replaced by
    forall alpha:Prop. In his article, Reynolds writes B for Heyt, and it is
    an unspecified system F type with at least 2 different terms. We do have
    those terms here: I True and I False. Our Heyt has a structure of complete
    Heyting algebra, hence does generalize the booleans of System F. *)

Require Import Log_Rel.

Section PropRetract.

Variable Heyt : Prop.
Variable I : Prop -> Heyt. (* the injection of Prop into a proposition Heyt *)
Hypothesis Iinject : forall (P Q : Prop), I P = I Q -> (P <-> Q).

(* The injection I has a left inverse T (aka a retract). *)
Definition T (b : Heyt) : Prop := exists P:Prop, P /\ b = I P.
Lemma E1 : forall x : Prop, x -> T (I x).
Proof using Type.
  intros x H. unfold T. exists x. split. exact H. reflexivity.
Qed.
Lemma E2 : forall x : Prop, T (I x) -> x.
Proof using Iinject.
  intros x [Q [H H0]].
  apply (Iinject _ _ H0), H.
Qed.

(** The injection I equips Heyt with a structure of complete Heyting algebra that
    we define here. It is simply the injection of Prop's Heyting algebra. We can
    therefore interpret X -> Heyt as the type of subtypes of X, a.k.a. the powerset
    of X. We will later use this structure to take the intersection of a family of
    subsets. We define Heyt_Le as the injection of Prop's implication in Heyt, and
    that is a preorder on Heyt (reflexive and transitive). We define Heyt_Eq as
    the symmetrization of preorder Heyt_Le, which is an equivalence relation on
    Heyt. Functions I and T become a bijection between the setoids (Prop, <->)
    and (Heyt, Heyt_Eq). *)
Definition Heyt_Le (x y : Heyt) : Prop := (T x) -> (T y).
Definition Heyt_Eq (x y : Heyt) : Prop := (T x) <-> (T y).

(* All elements of Heyt outside the image of I are false in the quotient. *)
Lemma Heyt_out : forall x : Heyt, (forall P:Prop, x <> I P) -> Heyt_Eq x (I False).
Proof.
  intros x xout. split.
  - intros [P [H Tx]]. exfalso. exact (xout P Tx).
  - intros Tx. exfalso. apply E2 in Tx. contradiction.
Qed.

(* Eq is a partial equivalence relation over Heyt. *)
Lemma per_Eq : per Heyt_Eq.
Proof using Type.
apply per_intro.
- intros x y. unfold Heyt_Eq. intro H. split; apply H.
- intros x y z. unfold Heyt_Eq. intros H H0.
  split; intro H1. apply H0, H, H1. apply H, H0, H1.
Qed.

(* Eq is actually a full equivalence. *)
Lemma refl_Eq : forall b:Heyt, Heyt_Eq b b.
Proof using Type.
  intro b. split; intros; assumption.
Qed.

(** power R is mostly used on a setoid (A,R), where R is a partial equivalence
    relation. Then, power R is the extensional equality on the powerset
    of A: two subsets of A are equal iff they have the same elements. *)
Definition power {A : Prop} (R : Rel A) : Rel (A -> Heyt) :=
  exp R Heyt_Eq.

Lemma power_per : forall (A : Prop) (R : Rel A),
    per R
    -> per (power R).
Proof using Type.
  intros A R H.
  apply exp_per.
  exact H.
  exact per_Eq.
Qed.


(* Definition of the Reynolds functor PHI (written T in Reynolds' article). *)
Definition PHI (A : Prop) := (A -> Heyt) -> Heyt.
Definition phi {A B : Prop} (f : A -> B) (z : PHI A) : PHI B :=
  fun u : B -> Heyt => z (fun x : A => u (f x)).

Lemma phi_id : forall (A : Prop), phi (fun (x:A) => x) = (fun y => y).
Proof using Type. reflexivity. Qed.

Lemma phi_compose : forall (A B C : Prop) (f : A -> B) (g : B -> C) (x : PHI A),
    (phi g) (phi f x) = phi (fun y => g (f y)) x.
Proof using Type. reflexivity. Qed.

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
Proof using Type. reflexivity. Qed.

(** By Lambek's theorem, A0_cons : PHI A0 -> A0 is an isomorphism in the category Prop
    (or System F). In other words, A0 is the least fixed point of functor PHI.
    The inverse morphism A0_match is obtained by considering the algebra
    phi A0_cons : PHI (PHI A0) -> PHI A0,
    and taking the induction morphism from A0 to it.

    Again we remark that the definition of A0_match is impredicative. If we used Type
    instead of Prop, we could still define A0 in higher universes, but Coq would
    refuse A0_match, arguing that the subtype constrains cannot be resolved. *)
Definition A0_match : A0 -> PHI A0 := A0_ind (phi A0_cons).

(** There is a caveat however. The above would be correct if the morphism from A0 to
    another PHI-algebra, written A0_ind, would be unique. This is the difference
    between preinitial and initial algebras. As in Reynolds' article, we will refine
    A0 to get a true initial algebra. We do so by moving from the category Prop
    (or System F) to the category of sets. The idea of assigning sets to types,
    in a way compatible with beta reduction, is called denotational semantics.
    This is what Reynolds discussed in his paper, only assuming the general
    translation rules that a semantics satisfies. Here we will explicitly give the
    set semantics. Our set denotation of A0 is simply a partial equivalence relation
    E0 on A0, which turns A0 into a setoid. In other words, our set denotation of A0
    is a quotient of A0. A0_cons and A0_match induce quotient maps that are truly
    inverse from each other. In the quotient, all morphisms from A0 to any other
    PHI-algera are equalized, which turns the preinitial algebra into an initial
    algebra.

    Here is a synthesis of our set semantics, for all objects involved in our
    final refutation of Iinject
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
Proof using Type.
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
Definition F0 : Rel (A0 -> Heyt) := power E0. (* Equality on subsets of (A0,E0) *)
Definition G0 : Rel (PHI A0) := power F0.

Lemma G0_phi2 : G0 = phi2 E0.
Proof using Type. reflexivity. Qed.

(** What follows proves that the definition of relation E0 fulfills its goal.
    A0_cons is a set-function (PHI A0, phi2 E0) -> (A0, E0) and A0_match is its
    inverse set-function. In other words, the set (A0, E0) is a fixed point
    of the set-functor PHI (and it is an initial algebra, the smallest such
    fixed point).

    First we show that E0 is a partial equivalence, necessary to define a set.
    Recall that irreflexive elements are allowed in partial equivalences: they
    are considered erased in the quotient (A0, E0). *)

Theorem sym_E0 : sym A0 E0.
Proof using Type.
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
Proof using Type.
unfold trans in |- *; intros x y z h1 h2.
unfold E0 in |- *; intros E h3 h4 h5.
elim h3.
unfold sym, trans in |- *; intros h6 h7.
apply h7 with y.
apply (h1 E); auto.
apply (h2 E); auto.
Qed.

Theorem per_E0 : per E0.
Proof using Type.
exact (per_intro _ sym_E0 trans_E0).
Qed.

(* A0_cons : PHI A0 -> A0 is a set-function, it respects the equality relation E0.
   In other words, A0_cons is a PHI-algebra in the category of sets. *)
Theorem A0_cons_set_func : forall z1 z2 : PHI A0,
    G0 z1 z2 -> E0 (A0_cons z1) (A0_cons z2).
Proof using Type.
unfold E0 in |- *; intros z1 x2 h1 E h2 h3 h4.
apply h3; hnf in |- *; intros x y h5.
apply h1; hnf in |- *; intros x0 y0 h6.
apply h5.
apply (h6 E); auto.
Qed.

Theorem per_F0 : per F0.
Proof using Type.
apply power_per, per_E0.
Qed.

Theorem per_G0 : per G0.
Proof using Type.
apply power_per, per_F0.
Qed.

(* Now the inversion theorems. First that A0_match is the right inverse of A0_cons. *)
Theorem id_A0_cons_match :
  forall x : A0, E0 x x -> E0 x (A0_cons (A0_match x)).
Proof using Type.
intros x xrefl E h1 h2 h3.
apply h3.
apply (xrefl E); auto.
Qed.

(* Then A0_match is the left inverse of A0_cons. *)
Theorem id_A0_match_cons :
  forall z : PHI A0, G0 z z -> G0 z (A0_match (A0_cons z)).
Proof using Type.
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
Theorem A0_match_set_func : forall a b : A0,
    E0 a b -> G0 (A0_match a) (A0_match b).
Proof using Type.
intros a b aeqb.
(* E0 is an intersection of relations E,
   we simply show that the goal is one of those relations. *)
pose (fun u v : A0 => G0 (A0_match u) (A0_match v)) as E.
apply (aeqb E).
- (* E is a per *)
  destruct per_G0 as [G0sym G0trans].
  apply per_intro.
  intros x y h4.
  apply G0sym.
  exact h4.
  intros x y z h4 h5.
  apply (G0trans _ (A0_match y)).
  exact h4.
  exact h5.
- (* A0_cons respects E *)
  intros z1 z2 z1eqz2 x y xeqy.
  apply (z1eqz2 (fun u : A0 => x (A0_cons (A0_match u)))
                (fun u : A0 => y (A0_cons (A0_match u)))).
  intros x0 y0 x0eqy0.
  apply xeqy.
  apply A0_cons_set_func. exact x0eqy0.
- (* u and A0_cons (A0_match u) are E-equal *)
  intros u urefl h2.
  exact (id_A0_match_cons (A0_match u) urefl h2).
Qed.

(** We now have an initial PHI-algebra in the category of sets, i.e. a bijection
    between sets (A0, E0) and (PHI A0, phi2 E0).

    So far we haven't used the contradictory hypothesis Iinject. And the above
    bijection is indeed valid, if (Bool, Eq) and (A0, E0) are singleton sets.
    This corresponds to the proof-irrelevant semantics of Coq: all proofs of any
    proposition are equal. But now we assume Iinject, and use it to prove that
    the set (Bool, Eq) has at least 2 different elements. Then the set 
    (A0 -> Bool, F0) becomes bigger than the powerset of (A0, E0), and the
    set (PHI A0, phi2 E0) is even bigger. This leads to a contradiction, because
    Cantor's theorem tells that the powerset of (A0, E0) is strictly bigger than
    (A0, E0).

    The cardinal would already be increased by fun (A:Prop) => A -> Bool, which is
    simpler than PHI. However this is not a functor, because it does not apply
    covariantly to functions. *)
Lemma TrueNeqFalse : ~Heyt_Eq (I True) (I False).
Proof using Iinject.
  unfold Heyt_Eq, T.
  intros [H _]. destruct H as [P [Pprf H]].
  exists True. split. trivial. reflexivity.
  apply (Iinject _ _ H), Pprf.
Qed.

(** Cantor's theorem needs a surjection A0 ->> (A0 -> Heyt), which we must get
    from the bijection A0_match : A0 ~-> PHI A0. By composition this reduces to
    finding a surjection PHI A0 ->> (A0 -> Heyt). We will define it as a retraction
    of the singleton injection (A0 -> Heyt) -> PHI A0. Several such retractions
    exists, for example intersection or union of subsets, in the sense of the
    complete Heyting algebra Heyt. We choose intersection, where we only consider
    reflexive subsets P, as expected of a quotient by a per. The intersect predicate
    asserts that x:A0 is in this restricted intersection of C:PHI A0. *)
Definition singleton : (A0 -> Heyt) -> PHI A0 :=
  fun (x y : A0 -> Heyt) => I (F0 x y). 
Definition intersect (C : PHI A0) (x : A0) : Heyt :=
  I (forall P : A0 -> Heyt, F0 P P -> T (C P) -> T (P x)).


(* intersect : PHI A0 -> (A0 -> Bool) is a set-function, it respects equality
   relations. By composition, inter turns the bijection A0_match : A0 ~-> PHI A0
   into a surjection A0 ->> (A0 -> Bool), written khi below, which directly violates
   Cantor's theorem about powersets. *)
Lemma lemma_inter :
  forall (z1 z2 : PHI A0) (x y : A0),
    G0 z1 z2
    -> E0 x y
    -> T (intersect z1 x)
    -> T (intersect z2 y).
Proof using Iinject.
intros z1 z2 x y z1eqz2 xeqy.
unfold intersect. intro H1.
apply E1; intros P H2 H3.
cut (Heyt_Eq (P x) (P y)).
unfold Heyt_Eq in |- *; intro H4.
elim H4; intros H5 H6.
apply H5.
cut (forall P : A0 -> Heyt, F0 P P -> T (z1 P) -> T (P x)).
intro H7; apply H7.
exact H2.
cut (Heyt_Eq (z1 P) (z2 P)).
unfold Heyt_Eq in |- *; intro H8.
elim H8; intros H9 H10.
exact (H10 H3).
apply z1eqz2.
exact H2.
apply E2.
apply H1.
apply H2.
exact xeqy.
Qed.

Theorem inter_set_func :
  forall z1 z2 : PHI A0, G0 z1 z2 -> F0 (intersect z1) (intersect z2).
Proof using Iinject.
intros z1 z2 z1eqz2 x y xeqy.
split; intro H1.
exact (lemma_inter z1 z2 x y z1eqz2 xeqy H1).
apply (lemma_inter z2 z1 y x).
destruct per_G0. apply H, z1eqz2.
destruct per_E0. apply H, xeqy.
exact H1.
Qed.

(* Proof that intersect is surjective *)
Lemma id_intersect_singleton : forall (P : A0 -> Heyt),
    F0 P P -> F0 (intersect (singleton P)) P.
Proof using Iinject.
  intros P Prefl x y xeqy.
  unfold intersect, singleton.
  destruct per_Eq as [Eqsym Eqtrans].
  apply (Eqtrans _ (P x)).
  2: apply Prefl, xeqy.
  split.
  - intro H. apply E2 in H.
    exact (H P Prefl (E1 _ Prefl)).
  - intro H. apply E1. intros Q H0 H1.
    apply E2 in H1.
    assert (E0 x x) as H2.
    { destruct per_E0. apply (H3 _ y).
      exact xeqy. apply H2, xeqy. }
    apply (H1 _ _ H2), H.
Qed. 

Theorem singleton_set_func :
  forall z1 z2 : A0 -> Heyt, F0 z1 z2 -> G0 (singleton z1) (singleton z2).
Proof using Iinject.
  intros z1 z2 z1eqz2 x y xeqy.
  unfold singleton, Heyt_Eq.
  destruct per_F0 as [F0sym F0trans].
  split.
  - intros. apply E1. apply E2 in H.
    apply (F0trans _ z1).
    apply F0sym, z1eqz2.
    apply (F0trans _ x).
    exact H. exact xeqy.
  - intros. apply E1. apply E2 in H.
    apply (F0trans _ z2).
    exact z1eqz2.
    apply (F0trans _ y).
    exact H. apply F0sym. exact xeqy.
Qed.
 
Definition psi (u : A0 -> Heyt) : A0 := A0_cons (singleton u).
Definition khi (x : A0) : A0 -> Heyt := intersect (A0_match x).

(* Proof that khi is surjective, as a composition of surjections. *)
Lemma id_khi_psi : forall (P : A0 -> Heyt),
    F0 P P -> F0 (khi (psi P)) P.
Proof using Iinject.
  intros P H. unfold khi, psi.
  destruct per_F0 as [F0sym F0trans].
  apply (F0trans _ (intersect (singleton P))).
  2: apply id_intersect_singleton, H.
  apply inter_set_func.
  destruct per_G0 as [G0sym G0trans].
  apply G0sym.
  apply id_A0_match_cons.
  apply singleton_set_func, H.
Qed.

(* A generalization of Cantor's theorem to an arbitrary set Heyt. *)
Lemma Lawvere_fixpoint : forall f : Heyt -> Heyt,
    let q := (fun a:A0 => f (khi a a)) in
    F0 q q ->
    let p := psi q in
    Heyt_Eq (f (khi p p)) (khi p p).
Proof using Iinject.
  intros f q qrefl p.
  destruct per_Eq as [Eqsym Eqtrans].
  change (f (khi p p)) with (q p).
  unfold p.
  assert (E0 (psi q) (psi q)).
  { unfold psi. apply A0_cons_set_func.
    apply singleton_set_func. exact qrefl. }
  apply Eqsym.
  exact (id_khi_psi q qrefl _ _ H).
Qed.

(* Then the negation of Heyting algebra Heyt has a fixed point u0,
   which is a contradiction. *)
Definition u0 (x : A0) : Heyt := I (T (khi x x) -> False).

(* u0 is reflexive for F0, which means u0 is in the subset of (A0, E0). *)
Theorem lemma3 : F0 u0 u0.
Proof using Iinject.
intros x y H.
cut (F0 (khi x) (khi y)).
unfold khi in |- *; intro H0.
cut (Heyt_Eq (khi x x) (khi y y)).
unfold Heyt_Eq in |- *; intro H1.
elim H1; intros H2 H3.
unfold u0 in |- *.
split; intro H4.
apply E1; intro H5.
apply (E2 (T (khi x x) -> False) H4).
exact (H3 H5).
apply E1; intro H5.
apply (E2 (T (khi y y) -> False) H4).
exact (H2 H5).
unfold khi in |- *; apply H0.
exact H.
unfold khi in |- *.
apply inter_set_func.
apply A0_match_set_func; auto.
Qed.

Lemma Reynolds : False.
Proof using Iinject.
  assert (forall h:Heyt, ~Heyt_Eq (I(~T h)) h) as negnofix.
  { intros h [H H0].
    assert (T h). apply H, E1. intro abs.
    specialize (H0 abs). apply E2 in H0. contradiction.
    specialize (H0 H1). apply E2 in H0. contradiction. }
  pose proof (Lawvere_fixpoint (fun h:Heyt => I(~T h)) lemma3) as negfix.
  pose (psi (fun a : A0 => (fun h : Heyt => I (~ T h)) (khi a a))) as p.
  specialize (negnofix (khi p p)). contradiction.
Qed.

End PropRetract.


(** Excluded middle implies proof irrelevance.
    Unfortunately we cannot use the Reynolds contradiction to derive proof
    irrelevance without assuming the excluded middle, because constructively
    it is consistent (and anti-classical) that (nat -> 2) -> 2 is in bijection
    with nat. *)
Lemma EM_PI : (forall P:Prop, P \/ ~P) -> forall (Q:Prop) (a b : Q), a = b.
Proof.
  intros EM Q a b.
  (* By excluded middle, we refute the negation. *)
  destruct (EM (a = b)) as [aeqb | aneqb].
  exact aeqb. exfalso.
  (* Now we have assumed a and b are different, and that plus EM allow to define
     an injection I : Prop->Q, which violates Reynolds. *)
  pose (fun P:Prop => if EM P then a else b) as I.
  apply (Reynolds Q I). intros.
  unfold I in H.
  destruct (EM P), (EM Q0).
  - split; intros; assumption.
  - exfalso. contradict aneqb. exact H.
  - exfalso. contradict aneqb. symmetry. exact H.
  - split; intros; contradiction.
Qed.
