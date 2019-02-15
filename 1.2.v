Require Import List.
Import ListNotations.

(* no need to differentiate between Alphabet.
   machanism of automata does not depend on what the alphabet is,
   but on how to treat them. *)

Definition Str := list nat.
Definition concat := @app nat.
Definition reverse := @rev nat.

Definition str_sample : Str := [1;1;0;1;0;0;1;0].
Compute length str_sample.
Compute concat str_sample str_sample.
Compute length (concat str_sample str_sample).
Compute reverse str_sample.


Definition empty_str := @nil nat.

Example empty_str_length_0 : length empty_str = 0.
Proof. simpl. reflexivity. Qed.

Lemma empty_str_concat_idl : forall w : Str, concat empty_str w = w.
Proof. reflexivity. Qed.

Lemma empty_str_concat_idr : forall w : Str, concat w empty_str = w.
Proof.
  induction w.
  - reflexivity.
  - simpl. rewrite IHw. reflexivity.
Qed.

Inductive SubStr : Str -> Str -> Prop :=
| prefix : forall w v, (exists u, w = concat v u) -> SubStr w v
| suffix : forall w v, (exists u, w = concat u v) -> SubStr w v.

Lemma empty_substr : forall w : Str, SubStr w empty_str.
Proof.
  intros. apply prefix.
  exists w. reflexivity.
Qed.

(* app_length does induction part for us ;) *)
Lemma length_distribute : forall w v : Str,
  length (concat w v) = length w + length v.
Proof.
  intros. apply app_length.
Qed.


Fixpoint replicate {A : Type} (n : nat) (l : list A) :=
  match n with
  | O => []
  | S m => l ++ replicate m l
  end.

Definition times := @replicate nat.

Lemma time_0_emtpy : forall w : Str, times 0 w = empty_str.
Proof. reflexivity. Qed.


(* it's hard to reason on infinite set represented as in coq's standard library.
   intead, use boolean function representation.. *)
Definition Lang := Str -> Prop.

Fixpoint list2lang (strs : list Str) (w : Str) : Prop :=
  match strs with
  | [] => False
  | s :: trs => s = w \/ list2lang trs w
  end.

Definition lang_sample : Lang := list2lang [[0]; [0;0]; [0;0;1]].

Example lang_sample_match0 : ~ lang_sample nil.
Proof.
  unfold not, lang_sample. simpl. intro H. destruct H.
  inversion H. destruct H. inversion H. inversion H.
  destruct H. inversion H. inversion H0. destruct H. inversion H. exact H.
Qed.

Example lang_sample_match1 : lang_sample [0;0].
Proof.
  unfold lang_sample. simpl.
  right. left. reflexivity.
Qed.

Definition lang_an (c : nat) : Lang :=
  fun w => exists n, times n [c] = w.

Example lang_an_match0 : forall c, lang_an c empty_str.
Proof.
  unfold lang_an.
  exists 0.
  reflexivity.
Qed.

Example lang_an_match1 : forall c, lang_an c [c;c;c;c].
Proof.
  unfold lang_an.
  exists 4.
  reflexivity.
Qed.

Definition lang_anbn (c1 c2 : nat) : Lang :=
  fun (w : Str) => exists n, concat (times n [c1]) (times n [c2]) = w.

Example lang_anbn_match0 : forall c1 c2, lang_anbn c1 c2 empty_str.
Proof.
  intros. unfold lang_anbn.
  exists 0. reflexivity.
Qed.

Example lang_anbn_match1 : lang_anbn 0 1 [0;0;0;0;1;1;1;1].
Proof. exists 4. reflexivity. Qed.

Lemma times_length : forall (c : nat) (w : Str),
  length (times c w) = c * length w.
Proof.
  intros. induction c; simpl; try reflexivity.
  unfold times. simpl. rewrite app_length.
  apply f_equal2_plus; try reflexivity.
  apply IHc.
Qed.

Require Import Even.

Lemma double_even : forall n, even (n + n).
Proof.
  induction n.
  - simpl. apply even_O.
  - rewrite <- plus_n_Sm. simpl.
    apply even_S. apply odd_S. exact IHn.
Qed.

Lemma lang_anbn_even_length : forall c1 c2 w,
  lang_anbn c1 c2 w -> even (length w).
Proof.
  intros. unfold lang_anbn in H.
  destruct H as [n H]. rewrite <- H.
  rewrite app_length.
  rewrite (times_length n [c1]). rewrite (times_length n [c2]).
  simpl. apply double_even.
Qed.

Example lang_anbn_nomat1 : ~ lang_anbn 0 1 [0;0;0;0;1;1;1].
Proof.
  unfold not. intros H.
  pose (H0 := lang_anbn_even_length 0 1 [0;0;0;0;1;1;1]).
  apply H0 in H. simpl in H.
  inversion H; inversion H2; inversion H4; inversion H6;
  inversion H8; inversion H10; inversion H12; inversion H14.
Qed.


(* Σ* *)
Definition lang_full : Lang := Basics.const True.

(* Σ+ *)
Definition lang_fill : Lang :=
  fun (w : Str) => w <> empty_str.

Example lang_fill_no_nil : ~ lang_fill empty_str.
Proof.
  intro H. unfold lang_fill in H.
  unfold not in H. apply H. reflexivity.
Qed.

Inductive Sublang (l1 l2: Lang) : Prop :=
  include : (forall w : Str, l1 w -> l2 w) -> Sublang l1 l2.

Lemma lang_full_whole : forall l : Lang, Sublang l lang_full.
Proof.
  intro l. apply include.
  intros w H. exact I.
Qed.


(* complement language *)
Definition complang (l : Lang) : Lang :=
  fun (w : Str) => ~ l w.

Definition revlang (l : Lang) : Lang :=
  fun (w : Str) => l (reverse w).

Definition catlang (l1 l2 : Lang) : Lang :=
  fun (w : Str) => exists u v, l1 u /\ l2 v /\ concat u v = w.

Fixpoint timeslang (n : nat) (l : Lang) (w : Str) :=
  match n with
  | O   => w = empty_str
  | S n => exists u v, concat u v = w /\ l u /\ timeslang n l v
  end.

Definition eq_lang (l1 l2 : Lang) := forall w, l1 w <-> l2 w.


Example timeslang_0 : forall l : Lang, eq_lang (timeslang 0 l) (list2lang [empty_str]).
Proof.
  intro l. split.
  - destruct w as [ | h t]; simpl.
    + intro H. left. reflexivity.
    + intro contra. inversion contra.
  - simpl. intro H. destruct H as [H0 | F].
    + exact (eq_sym H0).
    + exfalso. exact F.
Qed.


Definition unionlang (l1 l2 : Lang) : Lang :=
  fun (w : Str) => l1 w \/ l2 w.

Definition star_closure (l : Lang) : Lang :=
  fun (w : Str) => exists n, timeslang n l w.

Definition positive_closure (l : Lang) : Lang:=
  fun (w : Str) => exists n, timeslang (S n) l w.

Definition lang_anbnambm (c1 c2 : nat) : Lang :=
  fun (w : Str) => exists n m, concat
    (concat (times n [c1]) (times n [c2]))
    (concat (times m [c1]) (times m [c2])) = w.

Definition cat_empty_r : forall w : Str, concat w empty_str = w := @app_nil_r nat.
Definition cat_empty_l : forall w : Str, concat empty_str w = w := @app_nil_l nat.

Example anbnambm_anbn2 : forall c1 c2,
  eq_lang (lang_anbnambm c1 c2) (timeslang 2 (lang_anbn c1 c2)).
Proof.
  intros c1 c2. split.
  - intros [n [m H]].
    exists (concat (times n [c1]) (times n [c2])).
    exists (concat (times m [c1]) (times m [c2])).
    split; try (exact H).
    split; try (exists n; reflexivity).

    exists (concat (times m [c1]) (times m [c2])).
    exists empty_str.
    split; try (rewrite cat_empty_r; reflexivity).
    split; try (exists m; reflexivity).

    unfold timeslang. reflexivity.

  - intro H. destruct H as [u1 [v1 [H1 [H2 H3]]]].
    destruct H3 as [u2 [v2 [Y1 [Y2 Y3]]]].
    destruct H2 as [n1 H2]. destruct Y2 as [n2 Y2].

    unfold timeslang in Y3. rewrite Y3 in Y1.
    rewrite cat_empty_r in Y1. rewrite <- Y1 in H1.
    rewrite <- H1.

    exists n1, n2. rewrite <- H2. rewrite <- Y2.
    reflexivity.
Qed.

(* Grammer
     V : variables
     T : termianl symbols
     S : start variable
     P : production rules

   variables ans terminal symbols should be able to treated together.
   start variable is always 0.
   production rule replaces symbol with symbols.
*)

Inductive symbol : Type :=
  | terminal : nat -> symbol
  | variable : nat -> symbol.

(* SententialForm *)
Definition sform : Type := list symbol.

(* returns list of possible substitutions of given symbol *)
Definition production := nat -> list sform.

Definition derive (p : production) (sf : sform) : list sform. Admitted.

Definition grammar2lang (p : production) : lang. Admitted.
(*  fun (w : Str) => derive?? p [variable 0)] ??? *)

Definition grammar_sample : production :=
  fun (v : nat) =>
    match v with
    | 0 => [[terminal 0; variable 0; terminal 1]; nil]
    | _ => [[variable v]]
    end.

Example grammar_sample_anbn : eq_lang (grammar2lang grammar_sample) (lang_anbn 0 1).
Admitted.

anbnb (c1 c2 : nat) (n : nat) :=
  fun (w : Str) := (times n [c1]) (time (S n) [c2]).
