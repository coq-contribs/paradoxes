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
(*                                                                          *)
(*                An exercise about paradoxes in system U-                  *)
(*                                                                          *)
(*                                 Coq V8.0                                 *)
(*                               August 2004                                *)
(*                                                                          *)
(****************************************************************************)
(*                             BuraliForti_ex.v                             *)
(*                (adapted from BuraliForti.v by H. Herbelin)               *)
(****************************************************************************)

(** The motivations for the following adaptation of Burali-Forti paradox in
    BuraliForti.v are

  - to provide a proof of Burali-Forti paradox directly applicable to
    system U-,

  - to show, as an exercise, that it is enough to take a minimal
    universal system of notations (as described in Coquand [Coquand])
    encoding only relations, assuming that the encoding is injective
    wrt morphisms preserving the diagonal, as follows:

    Variable   A0  : Type.
    Variable   i0  : (A0->A0->Prop)->A0.

    Definition morphism (R S:A0->A0->Prop) (f:A0->A0) :=
      forall x y:A0, R x y -> S (f x) (f y).

    Definition preserve_strictness (R:A0->A0->Prop) (f:A0->B0) :=
      forall x y:A0, x<>y -> R x y -> f x <> f y.

    Hypothesis inj : forall R1 R2:A0->A0->Prop, i0 R1 = i0 R2 
      -> exists2 f:A0->A0, morphism R1 R2 f & preserve_strictness R1 f).

  Basically, Burali-Forti can be derived by encoding into A0 the pair
of a relation and its domain. As done in Howe's formalization within
the NuPrl system of the Burali-Forti paradox in system U [Howe], the
domain can be characterized by a predicate rather than by a type (as
done in file BuraliForti.v). As a side consequence, the paradox is
derivable within system U- (without requiring the power of full system
U as in Girard [Girard]): the universal system of notation A0 has not
to encode types and relations but just predicates and relations
(i.e. i0 can be given the type (A0->Prop)->(A0->A0->Prop)->A0 and
quantification of types over statements are no longer necessary).

  The basic idea to contract the domain and the relation into a single
relation (hence to only require i0:(A0->A0->Prop)->Prop) is to encode
the domain of the relation in its diagonal. This is possible because
the relation considered in Burali-Forti paradox are well-founded,
hence strict. See the definitions of "strict", "dom" and "define_on"
hereafter. The counterpart is that the morphisms considered between 
relations must act independently on and outside the diagonal.

  References:

  [Coquand] T. Coquand, "An Analysis of Girard's Paradox",
  In: Symposium on Logic in Computer Science (LICS '86), Cambridge, MA, 1986.

  [Girard] J.-Y. Girard. "Une extension de l'interprétation de Gödel à
  l'analyse, et son application à l'élimination des coupures dans
  l'analyse et la théorie des types", In: Proceedings of the 2nd
  Scandinavian Logic Symposium, North Holland, 1971.

  [Howe] D.J. Howe, "The Computational Behaviour of Girard's Paradox."
  Proceedings of the 2nd Symposium on Logic in Computer Science (LICS '87),
  Ithaca, 1987.
*)

  Inductive ACC (A : Type) (R : A -> A -> Prop) : A -> Prop :=
      ACC_intro :
        forall x : A, (forall y : A, R y x -> ACC A R y) -> ACC A R x.

  Lemma ACC_irrefl :
   forall (A : Type) (R : A -> A -> Prop) (x : A),
   ACC A R x -> R x x -> False.
simple induction 1; intros.
exact (H1 x0 H2 H2).
Qed.

  Definition WF (A : Type) (R : A -> A -> Prop) := forall x : A, ACC A R x.

  Definition morphism (A : Type) (R : A -> A -> Prop) 
    (B : Type) (S : B -> B -> Prop) (f : A -> B) :=
    forall x y : A, R x y -> S (f x) (f y).

  Definition preserve_strictness (A : Type) (R : A -> A -> Prop) 
    (B : Type) (f : A -> B) := forall x y : A, x <> y -> R x y -> f x <> f y.

(** Remark: the paradox is written in Type, but also works in Prop or Set. *)

Section Burali_Forti_Paradox.

  (** The hypothesis of the paradox:
      assumes there exists an universal system of notations, i.e:
      - A type A0
      - An injection i0 from relations on A0 into A0
      - The proof that i0 is injective modulo diagonal-preserving morphism
   *)

  Variable A0 : Type.                (* Type_i *)
  Variable i0 : (A0 -> A0 -> Prop) -> A0.  (* X: Type_j *)

  Hypothesis
    inj :
      forall R1 R2 : A0 -> A0 -> Prop,
      i0 R1 = i0 R2 ->
      exists2 f : A0 -> A0,
        morphism A0 R1 A0 R2 f & preserve_strictness A0 R1 A0 f.

  (** Extracting the dom and the strict relation of a large relation *)
  Definition dom (R : A0 -> A0 -> Prop) (x : A0) := R x x.
  Definition strict (R : A0 -> A0 -> Prop) (x y : A0) := x <> y /\ R x y.
  Definition define_on (P : A0 -> Prop) (R : A0 -> A0 -> Prop) 
    (x y : A0) := R x y \/ x = y /\ P y.

  (* Embedding of x in y: x and y are images of 2 well founded relations
     R1 and R2, the ordinal of R1 being strictly greater than that of R2.
   *)
  Record emb (x y : A0) : Prop := 
    {R1 : A0 -> A0 -> Prop;
     eqx : x = i0 R1;
     R2 : A0 -> A0 -> Prop;
     eqy : y = i0 R2;
     W2 : WF A0 (strict R2);
     f : A0 -> A0;
     fmorph : morphism A0 R1 A0 R2 f;
     fstrict : preserve_strictness A0 R1 A0 f;
     maj : A0;
     majd : dom R2 maj;
     majf : forall z : A0, dom R1 z -> strict R2 (f z) maj}.

  Lemma emb_trans : forall x y z : A0, emb x y -> emb y z -> emb x z.
intros.
case H; intros.
case H0; unfold dom in |- *; intros.
generalize eqx0; clear eqx0.
elim eqy using eq_ind_r; intro.
case (inj _ _ eqx0); intros.
exists R1 R3 (fun x : A0 => f0 (x0 (f x))) maj0; trivial.
red in |- *; auto.
red in |- *; auto.
intros; apply majf0; auto.
Defined.

  Lemma ACC_emb :
   forall (R : A0 -> A0 -> Prop) (x : A0),
   ACC A0 (strict R) x ->
   forall (S : A0 -> A0 -> Prop) (f : A0 -> A0),
   morphism A0 S A0 R f ->
   preserve_strictness A0 S A0 f ->
   (forall y : A0, dom S y -> strict R (f y) x) -> ACC A0 emb (i0 S).
unfold dom in |- *; simple induction 1; intros.
constructor; intros.
case H5; intros.
elim eqx using eq_ind_r.
case (inj R2 S).
apply sym_eq; assumption.

intros.
apply H1 with (y := f (x1 maj)) (f := fun x : A0 => f (x1 (f0 x)));
 try red in |- *; auto.
destruct (H4 (x1 maj)); auto.
intros; case (majf y0); intros; auto.
Defined.

  (* The embedding relation is well founded *)
  Lemma WF_emb : WF A0 emb.
constructor; intros.
case H; intros.
elim eqx using eq_ind_r.
apply ACC_emb with (R := R2) (x := maj) (f := f); trivial.
Defined.

  Lemma emb_irrefl : forall x y : A0, emb x y -> x <> y.
intros x y H H0; apply ACC_irrefl with A0 emb x.
apply WF_emb.
pattern x at 2 in |- *; rewrite H0.
assumption.
Defined.

  (** Encoding a relation defined everywhere *)
  Definition large_emb := define_on (fun _ => True) emb.

  (* The embedding relation is well founded *)
  Lemma WF_emb_strict : WF A0 (strict large_emb).
intro x.
pattern x in |- *; elim WF_emb; intros.
constructor; intros.
apply H0.
destruct H1 as (H1, [H2| (H2, _)]).
trivial.
case (H1 H2).
Defined.

  (* The following definition enforces Type_j >= Type_i *)
  Definition Omega : A0 := i0 large_emb.

Section Subsets.

  Variable a : A0.

  (* We restrict the embedding to the elements of A0 smaller than a
     w.r.t embedding. The Record is in Type, but it is possible to avoid
     such structure. *)

  Definition restrict := define_on (fun c => emb c a) emb.

  (* F is its image through i0 *)
  Definition F : A0 := i0 restrict.

  (* F is embedded in Omega:
     - the witness projection is a morphism
     - a is an upper bound because emb_wit proves that witness is
       smaller than a.
   *)
  Lemma F_emb_Omega : emb F Omega.
exists restrict large_emb (fun x : A0 => x) a; trivial.
exact WF_emb_strict.
red in |- *; red in |- *. unfold restrict, define_on in |- *; tauto.
red in |- *; trivial.
red in |- *; red in |- *; red in |- *; tauto.
intros. destruct H as [H| (_, H)]; trivial. 
elim (emb_irrefl z z); trivial.
split.
apply emb_irrefl; trivial.
red in |- *; red in |- *; tauto.
Defined.

  Lemma emb_morph :
   forall f : A0 -> A0,
   morphism A0 emb A0 emb f -> forall x : A0, ~ emb (f x) x.
intros.
red in H.
pattern x in |- *; elim WF_emb; intros.
intro; apply (H1 (f x0)); trivial.
apply H; trivial.
Qed.

  Lemma F_Omega_neq : F <> Omega.
unfold F, Omega in |- *.
intro H. symmetry  in H.
case (inj _ _ H); intros.
clear H.
red in H0, H1.
unfold restrict in H0.
assert (Hx : morphism A0 emb A0 emb x).
red in |- *; intros.
unfold large_emb, define_on in H0, H1.
destruct (H0 x0 y) as [| (H3, _)]; try tauto.
assert (H4 := emb_irrefl _ _ H).
elim (H1 x0 y); try tauto.
cut (emb (x a) a).
apply (emb_morph _ Hx).
unfold large_emb, define_on in H0.
case (H0 a a); intros; try tauto.
elim (emb_irrefl (x a) (x a)); trivial.
Defined.

  Lemma F_emb_strict_Omega : strict large_emb F Omega.
split.
apply F_Omega_neq.
left.
apply F_emb_Omega.
Defined.

End Subsets.

  Lemma WF_restrict : forall a : A0, WF A0 (strict (restrict a)).
red in |- *; intros.
pattern x in |- *.
elim WF_emb; intros.
constructor; intros.
apply H0.
destruct H1 as (H2, [H3| (H3, _)]).
trivial.
elim (H2 H3).
Defined.

  Lemma morphism_restrict :
   forall x y : A0,
   emb x y -> morphism A0 (restrict x) A0 (restrict y) (fun x => x).
red in |- *; intros.
destruct H0 as [H0| (H0, H1)].
left; trivial.
right; split; trivial.
apply emb_trans with (y := x); trivial.
Defined.

  (* F is a morphism: a < b => F(a) < F(b)
      - the morphism from F(a) to F(b) is fsub above
      - the upper bound is a, which is in F(b) since a < b
   *)
  Lemma F_morphism : morphism A0 large_emb A0 large_emb F.
red in |- *; intros.
case H; intros.
left.
exists (restrict x) (restrict y) (fun x : A0 => x) x; trivial.

apply WF_restrict.
apply morphism_restrict; trivial.
red in |- *; trivial. 
red in |- *; right; split; trivial. 

intros. destruct H1 as [H1| (_, H1)].
elim (emb_irrefl z z); trivial.
split.
apply emb_irrefl; trivial.
left; trivial.

case H0; intros.
right; split; trivial.
rewrite H1; trivial.
Defined.

  Lemma F_preserve_strictness : preserve_strictness A0 large_emb A0 F.
red in |- *.
intros x y H H0 H1.
unfold F in H1. symmetry  in H1.
case (inj _ _ H1); intros.
red in H2.
red in H3.
case H0; intros; try tauto.
assert (Hx : morphism A0 emb A0 emb x0). red in |- *; intros.
destruct (H2 x1 y0) as [H6| (H6, H7)]; trivial.
left; trivial.
elim (H3 x1 y0); trivial.
apply emb_irrefl; trivial.
left; trivial.

cut (emb (x0 x) x).
apply (emb_morph _ Hx).
case (H2 x x); unfold restrict, define_on, strict in |- *; intros; try tauto.
elim (emb_irrefl (x0 x) (x0 x)); trivial.
Defined.

  (* Omega is embedded in itself:
     - F is a morphism
     - Omega is an upper bound of the image of F
   *)
  Lemma Omega_refl : emb Omega Omega.
exists large_emb large_emb F Omega; trivial.

exact WF_emb_strict.
exact F_morphism.
exact F_preserve_strictness.

right; tauto.

intros; apply F_emb_strict_Omega; trivial.
Defined.

  (* The paradox is that Omega cannot be embedded in itself, since
     the embedding relation is well founded, hence irreflexive.
   *)
  Theorem Burali_Forti : False.
apply (emb_irrefl Omega Omega Omega_refl).
trivial.
Defined.

End Burali_Forti_Paradox.


  (* The following type seems to satisfy the hypothesis of the paradox.
     But it does not!
   *)
  Record A0 : Type :=  (* Type_i' *)
    i {X0 : Type; R0 : X0 -> X0 -> Prop}. (* X0: Type_j' *)

  (* Note: this proof uses a large elimination of A0. *)
  Lemma inj :
   forall (X1 X2 : Type) (R1 : X1 -> X1 -> Prop) (R2 : X2 -> X2 -> Prop),
   i X1 R1 = i X2 R2 ->
   exists2 f : X1 -> X2,
     morphism X1 R1 X2 R2 f & preserve_strictness X1 R1 X2 f.
intros.
change
  match i X1 R1, i X2 R2 with
  | i x1 r1, i x2 r2 =>
      exists2 f : _, morphism x1 r1 x2 r2 f & preserve_strictness x1 r1 x2 f
  end in |- *.
case H; simpl in |- *.
exists (fun x : X1 => x).
red in |- *; trivial.
red in |- *; trivial.
Defined.

(* The following command raises 'Error: Universe Inconsistency'.
   To allow large elimination of A0, i0 must not be a large constructor.
   Hence, the constraint Type_j' < Type_i' is added, which is incompatible
   with the constraint j >= i in the paradox.

  Definition i0 := (i A0).

  Definition Paradox: False := (Burali_Forti A0 (i A0) (inj A0 A0)).
*)
