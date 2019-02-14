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
Definition Lang := Str -> bool.

Local Open Scope bool_scope.


Fixpoint eqb_str (s1 s2 : Str) : bool :=
  match s1, s2 with
  | [],     [] => true
  | _ :: _, [] => false
  | [], _ :: _ => false
  | h1 :: t1, h2 :: t2 => Nat.eqb h1 h2 && eqb_str t1 t2
  end.

Fixpoint list2lang (strs : list Str) (w : Str) : bool :=
  match strs with
  | [] => false
  | s :: trs => eqb_str s w || list2lang trs w
  end.

Definition lang_sample : Lang := list2lang [[0]; [0;0]; [0;0;1]].

Example lang_sample_match0 : lang_sample nil = false.
Proof. reflexivity. Qed.

Example lang_sample_match1 : lang_sample [0;0] = true.
Proof. reflexivity. Qed.


Definition lang_an (c : nat) : Lang :=
  fix f (w : Str) :=
    match w with
    | [] => true
    | x :: v => Nat.eqb x c && f v
    end.

Example an_lang_match0 : forall c, lang_an c empty_str = true.
Proof. reflexivity. Qed.

Example an_lang_match1 : lang_an 0 [0;0;0;0] = true.
Proof. reflexivity. Qed.


Definition anbn_lang : Lang :=
  fun (w : Str) =>
    let n2 := (length w) in
    if Nat.odd n2 then
      false
    else
      let n := Nat.div2 n2 in
      lang_an 0 (firstn n w) && lang_an 1(skipn n w).

Example anbn_lang_match0 : anbn_lang nil = true.
Proof. reflexivity. Qed.

Example anbn_lang_match1 : anbn_lang [0;0;0;0;1;1;1;1] = true.
Proof. reflexivity. Qed.

Example anbn_lang_nomat1 : anbn_lang [0;0;0;0;1;1;1] = false.
Proof. reflexivity. Qed.


(* Σ* *)
Definition lang_full : Lang := Basics.const true.

(* Σ+ *)
Definition lang_fill : Lang :=
  fun (w : Str) => negb (eqb_str nil w).

Example lang_fill_no_nil : lang_fill empty_str = false.
Proof. reflexivity. Qed.

Inductive Sublang (l1 l2: Lang) : Prop :=
  include : (forall w : Str, l1 w = true -> l2 w = true) -> Sublang l1 l2.

Lemma lang_full_whole : forall l : Lang, Sublang l lang_full.
Proof.
  intro l. apply include.
  intros w H. reflexivity.
Qed.


(* complement language *)
Definition complang (l : Lang) : Lang :=
  fun (w : Str) => negb (l w).

Definition revlang (l : Lang) : Lang :=
  fun (w : Str) => l (reverse w).

Definition catlang (l1 l2 : Lang) : Lang. Admitted.

Definition timeslang (n : nat) (l : Lang) : Lang. Admitted.

Example timeslang_0 : forall l : Lang, timeslang 0 l = list2lang [nil]. Admitted.

Definition unionlang (l1 l2 : Lang) : Lang :=
  fun (w : Str) => l1 w || l2 w.

Definition star_closure (l : Lang) : Lang. Admitted.
Definition positive_closure (l : Lang) : Lang. Admitted.
