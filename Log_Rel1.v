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

(** We derive the proof-irrelevance principle from the excluded middle.
    More precisely, the following 5 axioms are contradictory
    (cf. proof of contradiction in file Reynolds1.v).
    Axiom I represents the excluded middle principle: any proposition
    is either true or false. Assuming I, T cannot exist, because it would
    extract computational information from proofs. The refutation of T
    stands for the proof-irrelevance principle. *)

Parameter Bool : Prop.

Parameter T : Bool -> Prop.

Parameter I : Prop -> Bool.

Parameter E1 : forall x : Prop, x -> T (I x).

Parameter E2 : forall x : Prop, T (I x) -> x.

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

(** A setoid is a type A equipped with an equivalence relation R, which is interpreted
    as equality on A. In other words, it is the quotient of a type A by an equivalence
    relation R. Here we consider a slight generalization of equivalence relations,
    called partial equivalence relations, where reflexivity is omitted. A quotient
    by an equivalence merges related elements, in addition a quotient by a per erases
    irreflexive elements. *) 
Inductive per {A : Prop} (R : Rel A) : Prop :=
    per_intro : sym A R -> trans A R -> per R.

Definition Eq (x y : Bool) := equiv (T x) (T y).

(* Eq is a partial equivalence relation over Bool.
   It is even an equivalence actually. *)
Lemma per_Eq : per Log_Rel1.Eq.
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

(** exp R S is mostly used on setoids (A,R),(B,S) where R and S are partial
    equivalence relations. Then, exp R S is the extensional equality for functions
    in A -> B: for all equal inputs, the functions produce equal outputs.
    The erasure of irreflexive elements for exp R S is very elegant:
    it means we only consider functions f : A -> B that respect relations R,S,
    as expected for the quotients (A,R) and (B,S). *)
Definition exp {A B : Prop} (R : Rel A) (S : Rel B) (f g : A -> B) : Prop :=
  forall x y : A, R x y -> S (f x) (g y).

(** power R is mostly used on a setoid (A,R), where R is a partial equivalence
    relation. Then, power R is the extensional equality on the powerset
    of A: two subsets of A are equal iff they have the same elements. *)
Definition power {A : Prop} (R : Rel A) : Rel (A -> Bool) :=
  exp R Log_Rel1.Eq.

Lemma exp_per : forall (A B : Prop) (R : Rel A) (S : Rel B),
    per R
    -> per S
    -> per (exp R S).
Proof.
  unfold exp.
  intros A B R S [symR transR] [symS transS].
  apply per_intro.
  - (* symmetry *)
    intros x y H0 s t H1.
    apply symS, H0, symR, H1.
  - (* transitivity *)
    intros x y z H H0 s t H1.
    apply (transS _ (y t)).
    apply H, H1.
    apply H0.
    apply (transR _ s).
    apply symR, H1.
    exact H1.
Qed.

Lemma power_per : forall (A : Prop) (R : Rel A),
    per R
    -> per (power R).
Proof.
  intros A R H.
  apply exp_per.
  exact H.
  exact per_Eq.
Qed.

Lemma per_empty : forall A:Prop, per (fun (x y : A) => False).
Proof.
  intro A. split.
  intros x y H. exact H.
  intros x y z H. contradiction.
Qed.

(* The power set of the empty set is a singleton. *)
Lemma power_empty : forall (A:Prop) (f g : A -> Bool), 
    power (fun _ _ => False) f g.
Proof.
  intros A f g x y H. contradiction.
Qed.

End logical_relation.
