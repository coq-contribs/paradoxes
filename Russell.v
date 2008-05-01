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


(***********************************************************************)
(** This is a simplification of Alexandre Miquel's encoding of          *)
(** Russell's paradox in system U and U-.                               *)
(** Extraction yields a looping combinator                              *)
(***********************************************************************)
(** Formalized by Hugo Herbelin, 2001                                   *)
(***********************************************************************)
(**
   Reference:

   - [Miquel] A. Miquel, "Le Calcul des Constructions Implicites",
     thèse de doctorat de l'université Paris7, 2001.
*)

(** The basic idea is to encode sets by pointed graphs over a given
universe U, a pointed graph being a relation expressing on the
universe U the subset ordering structure of a set from a given
root. 

  E.g., the following relation on U, starting from point a denotes the
set {{empty},empty} (= 2 in set theory).

                   a
                  / \
                 b   c
                 |
                 d

  Notice that the same relation, considered from c or d denotes the
empty set. From b it denotes the singleton {empty}.

  Pointed graphs are considered up to bissimulation. E.g, the relation

                   a
                  /\
                 b  |
                  \ |
                   c

considered from a has the same underlying structure as the previous
set and hence denotes the same set {{empty},empty}.
*)

(**
   In order to get a shorter proof, then a shorter extracted program,
   the following simplifications have been performed:

   - Inlining of the definitions of elt, eqv, ELT.
   - Encodings of there is and or by means of for all, implication and False.
   - Removal of extra double negations.
   - Replacement of EQV by an EMB order, the only equivalence used in both
     way in the proof is the equivalence between (A,a) and (elt,i(A,a)).
   - Replacement of arbitrary elements in u by out as much as possible.
   - Replacement of elt in FOLD by just a link in some set B.
*)

Inductive False : Set :=.
Inductive True : Set :=
    I : True.

(** As shown in Coquand ("An Analysis of Girard Paradox", LICS'86), we
  can define in system U- a type (let's call it U also) which is a
  "universal system of notations" for pointed graphs, that is U:Type
  comes with an injection i from pointed graphs on U into U itself *)

(** Definitions of U, i and out typable in U but not in CIC
Definition Type1 := Type.
Definition U := (forall U:Type1, (U->U->Set)->U->Set)->Set : Type1.
Definition i (A:U->U->Set) (a:U) : U := fun H => H U A a.
Definition out : U := fun _ => False.
*)

Parameter U : Type.
Parameter i : (U -> U -> Set) -> U -> U.
Parameter out : U.

Definition eq (u v : U) := forall P : U -> Set, P u -> P v.
Infix "=" := eq (at level 70, no associativity) : type_scope.

Lemma refl_eq : forall u : U, u = u.
Proof fun _ _ x => x.

Notation Sim := (U -> U -> Set).
Notation Graph := Sim.

(** The property [gemb A B R] expresses that R is an embedding of graph
    A into graph B

                    R
                a ------ b
                |        |
             A  |          B  
                |    R   |
                a' - - - b'
*)

Definition gemb (A B R : Graph) :=
  forall a a' b : U,
  A a' a -> R a b -> (forall b' : U, R a' b' -> B b' b -> False) -> False.

Notation "A <= B [ R ]" := (gemb A B R)
  (at level 70, B at level 8, no associativity).

(** [EMB A a B b] means there a simulation between (A,a) and (B,b) as
    pointed graphs; [NOTEMB] is its contrary *)

Definition NOTEMB (A : Graph) (a : U) (B : Graph) (b : U) :=
  forall R : Graph, A <= B [R] -> R a b -> False.

Definition EMB (A : Graph) (a : U) (B : Graph) (b : U) :=
  NOTEMB A a B b -> False.

Notation "( A , a )  <= ( B , b )" := (EMB A a B b) (at level 0).

(** Basic lemmas on [gemb] and [EMB] *)

Lemma eq_gemb : forall A : Graph, A <= A [eq].
Proof
  fun A a a' a0 Ha'a Heq H => H a' (refl_eq a') (Heq (fun a => A a' a) Ha'a).

Lemma refl_EMB : forall (A : Graph) (a : U), (A, a) <= (A, a).
Proof fun A a H => H eq (eq_gemb A) (refl_eq a).

(** At some time, we need to compose 4 embeddings *)
(** [comp4 R S T V] denotes the composed embedding *)

Definition comp4 (R S T V : Graph) (x y : U) :=
  (forall z1 z2 z3 : U, R x z1 -> S z1 z2 -> T z2 z3 -> V z3 y -> False) ->
  False.

Lemma comp4_top :
 forall (R S T V : Graph) (a b c d e : U),
 R a b -> S b c -> T c d -> V d e -> comp4 R S T V a e.
Proof fun R S T V a b c d e Hab Hbc Hcd Hde H => H b c d Hab Hbc Hcd Hde.

Lemma comp4_gemb :
 forall A B C D R S T V : Graph,
 A <= B [R] ->
 B <= C [S] -> C <= D [T] -> D <= A [V] -> A <= A [comp4 R S T V].
Proof
  fun A B C D R S T V HsubAB HsubBC HsubCD HsubDA a a' a0 Ha'a Haa0 H =>
  Haa0
    (fun b c d Hab Hbc Hcd Hda0 =>
     HsubAB a a' b Ha'a Hab
       (fun b' Ha'b' Hb'b =>
        HsubBC b b' c Hb'b Hbc
          (fun c' Hb'c' Hc'c =>
           HsubCD c c' d Hc'c Hcd
             (fun d' Hc'd' Hd'd =>
              HsubDA d d' a0 Hd'd Hda0
                (fun a0' Hd'a0' Ha0'a0 =>
                 H a0' (fun H' => H' b' c' d' Ha'b' Hb'c' Hc'd' Hd'a0')
                   Ha0'a0))))).

(** [comp2 R S] denotes the composition of R and S *)

Definition comp2 (R S : Graph) (x y : U) :=
  (forall z : U, R x z -> S z y -> False) -> False.

Infix "o" := comp2 (at level 30, right associativity).

Lemma comp2_top :
 forall (R S : Graph) (a b c : U), R a b -> S b c -> (R o S) a c.
Proof fun R S a b c Hab Hbc H => H b Hab Hbc.

Lemma comp2_gemb :
 forall A B C R S : Graph, A <= B [R] -> B <= C [S] -> A <= C [R o S].
Proof
  fun A B C R S HsubAB HsubBC a a' c Ha'a Hac H =>
  Hac
    (fun b Hab Hbc =>
     HsubAB a a' b Ha'a Hab
       (fun b' Ha'b' Hb'b =>
        HsubBC b b' c Hb'b Hbc
          (fun c' Hb'c' Hc'c => H c' (fun H' => H' b' Ha'b' Hb'c') Hc'c))).

(** [out_spec] provable in U but not provable in CIC

Lemma out_spec : forall (A:Graph) (a:U), i A a = out -> False.
Proof fun A a H => H (fun u => u (fun X A a => True) I).
*)

Axiom out_spec : forall (A : Graph) (a : U), i A a = out -> False.

(** Abstraction of EMB over the universes as a step towards
    proving injectivity of I which cannot be done in CIC *)

Definition GEMB (X : Type) (A : X -> X -> Set) (a : X) 
  (Y : Type) (B : Y -> Y -> Set) (b : Y) :=
  (forall R : X -> Y -> Set,
   (forall (a a' : X) (b : Y),
    A a' a -> R a b -> (forall b' : Y, R a' b' -> B b' b -> False) -> False) ->
   R a b -> False) -> False.

(** [inj] provable in U but not in CIC
Lemma inj : forall (A B:Graph) (a b:U), (i A a)=(i B b) -> (A,a)<=(B,b).
Proof fun A B a b H =>
      (H (fun u:U => u (fun (Z:Type) (C:Z->Z->Prop) (c:Z) => GEMB U A a Z C c))
         (refl_EMB A a)).
*)

Axiom inj : forall (A B : Graph) (a b : U), i A a = i B b -> (A, a) <= (B, b).

Definition P0 (A : Graph) := forall a' : U, A a' out -> NOTEMB A out A a'.

Definition FOLDP0 (u v : U) :=
  (forall (B : Graph) (b b' : U), u = i B b' -> i B b = v -> B b' b -> False) ->
  (forall A : Graph, i A out = u -> v = out -> P0 A -> False) -> False.

Lemma injr : P0 FOLDP0 -> FOLDP0 (i FOLDP0 out) out.
Proof fun H _ H1 => H1 FOLDP0 (refl_eq (i FOLDP0 out)) (refl_eq out) H.

(** Reification from (A,a) into (FOLDP0,i(A,a)) *)

(** There is a bissimulation, that is a relation (REIFY A a) which
    satisfies gemb in both way and relates a and i(A,a) *)

Definition REIFY_sim (A : Graph) (a0 a u : U) :=
  (forall (B : Graph) (b : U),
   i B b = u -> forall R : Graph, A <= B [R] -> R a b -> False) -> False.

Definition REIFY_sim_rev (A : Graph) (a0 u a : U) :=
  (forall (B : Graph) (b : U),
   u = i B b -> forall R : Graph, B <= A [R] -> R b a -> False) -> False.

Lemma REIFY_gemb : forall (A : Graph) (a : U), A <= FOLDP0 [REIFY_sim A a].
Proof
  fun A0 a0 a a' u Ha'a HREIFYau H =>
  HREIFYau
    (fun B b Heq R Rsub Rtop =>
     Rsub a a' b Ha'a Rtop
       (fun b' HRa'b' Hb'b =>
        H (i B b') (fun H0 => H0 B b' (refl_eq (i B b')) R Rsub HRa'b')
          (fun Hl Hr => Hl B b b' (refl_eq (i B b')) Heq Hb'b))).

Lemma REIFY_gemb_rev :
 forall (A : Graph) (a : U), FOLDP0 <= A [REIFY_sim_rev A a].
Proof.
red in |- *; intros A0 a0 u u' a Hu'u HREIFYua H.
apply HREIFYua.
intros B b Heq R Rsub Rtop.
apply (Heq (fun u => FOLDP0 u' u) Hu'u).
2: intros C H1 H2 H3; apply out_spec with (A := B) (a := b); exact H2.
intros B0 b0 b0' Hequ' Hequb0 Hb0'b0. 
apply (inj _ _ _ _ Hequb0).
red in |- *; intros R' R'sub R'top.
(* We have 
               a  <=  b  <=  b0
                             |
                             b0'
                  |       |
             in A | in B  | in B0
                  |       |
*)
(* We successively find b' then a' s.t.

               a  <=  b  <=  b0
               |      |      |
               a' <=  b' <=  b0'
                  |       |
             in A | in B  | in B0
                  |       |
*)
apply (R'sub b0 b0' b Hb0'b0 R'top).
intros b' R'b0'b' Hb'b.
apply (Rsub b b' a Hb'b Rtop).
intros a' Rb'a' Ha'a.
apply
 (Hequ'
    (fun u' => forall b' : U, REIFY_sim_rev A0 a0 u' b' -> A0 b' a -> False)
    H a').
(* We prove (REIFY_sim_rev A0 a0 u' a') *)
red in |- *; intro H'.
apply
 (H' B0 b0' (refl_eq (i B0 b0')) (R' o R)
    (comp2_gemb B0 B A0 R' R R'sub Rsub)
    (comp2_top R' R b0' b' a' R'b0'b' Rb'a')).
exact Ha'a.
Qed.

Lemma REIFY_top : forall A : Graph, REIFY_sim A out out (i A out).
Proof
  fun (A : Graph) H =>
  H A out (refl_eq (i A out)) eq (eq_gemb A) (refl_eq out).

Lemma REIFY_top_rev : forall (A : Graph) (a : U), REIFY_sim_rev A a (i A a) a.
Proof
  fun (A : Graph) (a : U) H =>
  H A a (refl_eq (i A a)) eq (eq_gemb A) (refl_eq a).

(** Used in extraction to trace the infinite loop *)
Parameter f : forall A : Set, (A -> False) -> A -> False.

Lemma p : P0 FOLDP0 -> False.
Proof
  fun H =>
  H (i FOLDP0 out) (injr H) (REIFY_sim FOLDP0 out) 
    (REIFY_gemb FOLDP0 out) (REIFY_top FOLDP0).

Lemma q : P0 FOLDP0.
Proof.
(* We assume there is some a s.t. "a FOLDP0 out" and "out EMB a" *)
(* i.e.
               out => a
                |
                a
*)
unfold P0, NOTEMB in |- *; intros a Hle Remb Remb_sub.
apply (f (Remb out a)). (* ... to trace the execution *)
intro Remb_top.
(* We apply the definition of "a FOLDP0 out" *)
apply Hle.
  (* Absurd case of FOLDP0, impossible because v==out *)
  unfold NOTEMB in |- *.
  intros B b b' H H0 H1.
  apply out_spec with (A := B) (a := b). exact H0.
(* From FOLDP0, we get B s.t. a==i(B,out) and P0(B) *)
(* "a' FOLDP0 a" and "a EMB a'" *)
intros B Heq H HP0.
(* By projecting "a FOLDP0 out" along "out EMB a" *)
(* we get B s.t. a==i(B,out) and P0(B) *)
(* i.e.
               out => a
                |     |
    i(B,out) == a  => a'
*)
apply (Remb_sub out a a Hle Remb_top).
apply (Heq (fun a => forall b' : U, Remb a b' -> FOLDP0 b' a -> False)).
intros a' Remb_top_aa' Hle'.
(* Since, we have (FOLDP0 a' i(B,out)), we get B0, b, b' s.t.

                                      out => a
                                       |     |
       b0  <=  i(B0,b0) == i(B,out) == a  => a'
       |                               |
       b0' <=    i(B0,b0')     ==      a'
            |
      in B0 |    i n    F O L D  P 0
            |
*)
apply Hle'.
2: intros C H1 H2 H3; apply out_spec with (A := B) (a := out); exact H2.
intros B0 b0 b0' Heqa' HeqB Hleb0.
apply (inj _ _ _ _ HeqB).
intros RB0B RBOB_sub RB0B_top_b0out.
(* Since i(B0,b0) == i(B,out), we get i(B0,b0) <= i(B,out) and then get
   b' below out in B

                                              out => a
           RB0B                                |     |
        out <=  b0  <= i(B0,b0) == i(B,out) == a  => a'
         |      |                              |
         b' <=  b0' <=   i(B0,b0')    ==       a'
             |       |
        in B | in B0 |    i n    F O L D  P 0
             |       |
*)
apply (RBOB_sub b0 b0' out Hleb0 RB0B_top_b0out).
intros b' RB0B_top_b0'b' Hleb'.
(* We get the contradiction, since out does not contain itself wrt B *)
unfold P0, NOTEMB in HP0.
(* That (B,out) => (B,b') comes from 

          REIFY          Remb          REIFY_rev      RB0B
   (B,out)  => (FOLDP0,a) ==> (FOLDP0,a') ==> (B0,b0') ==> (B,b')
*)
apply
 (HP0 b' Hleb' (comp4 (REIFY_sim B out) Remb (REIFY_sim_rev B0 b0') RB0B)).
apply
 (comp4_gemb B FOLDP0 FOLDP0 B0 (REIFY_sim B out) Remb 
    (REIFY_sim_rev B0 b0') RB0B (REIFY_gemb B out) Remb_sub
    (REIFY_gemb_rev B0 b0') RBOB_sub).
apply
 (comp4_top (REIFY_sim B out) Remb (REIFY_sim_rev B0 b0') RB0B out 
    (i B out) (i B0 b0') b0' b' (REIFY_top B)
    (Heqa' (fun a' => Remb (i B out) a') Remb_top_aa') 
    (REIFY_top_rev B0 b0') RB0B_top_b0'b').
Qed.

Theorem Russell : False.
Proof p q.

Extract Constant U => "Out | I of u".
Extract Constant out => "Out".
Extract Constant i => "fun x -> I x".

Extract Constant inj => "fun a b (h:eq) -> Obj.magic h __ (refl_EMB a)".
Extract Constant out_spec => "fun _ _ -> failwith ""Impossible""".

(** To trace the recursive loop *)
Extract Constant f => "fun x -> print_char '.'; flush stdout; x".

Extraction "russell.ml" refl_EMB Russell.
