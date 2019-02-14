Require Import List.
Import ListNotations.

Inductive Alphabet {A : Type} : list A -> Type :=
  alphabet : forall (l : list A), Alphabet l.

Definition bin_alphabet := alphabet [0;1].

(* String.length overwrites List.length...
Require Import String.
Local Open Scope string_scope.

Definition en_alpha := alphabet [
  "a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"; "m";
  "n"; "o"; "p"; "q"; "r"; "s"; "t"; "u"; "v"; "w"; "x"; "y"; "z"].
*)

Definition Str {A : Type} {l : list A} (ab : Alphabet l) := list A.

Definition binstr_sample : Str bin_alphabet :=
  [1;1;0;1;0;0;1;0].

Compute length binstr_sample.

Definition concat {A : Type} {l : list A} {ab : Alphabet l} (w v : Str ab) := app w v.

Compute concat binstr_sample binstr_sample.
Compute length (concat binstr_sample binstr_sample).

Definition reverse {A : Type} {l : list A} {ab : Alphabet l} (w : Str ab) := rev w.

Compute reverse binstr_sample.

Definition empty_str {A : Type} := @nil A.

Example empty_str_length_0 : forall A:Type, @length A empty_str = 0.
Proof.
  intro A. simpl. reflexivity.
Qed.

Lemma empty_str_concat_idl : forall (A : Type) (l : list A) (ab : Alphabet l),
  forall w : Str ab, @concat A l ab empty_str w = w.
Proof. reflexivity. Qed.
Lemma empty_str_concat_idr : forall (A : Type) (l : list A) (ab : Alphabet l),
  forall w : Str ab, @concat A l ab w empty_str = w.
Proof. 
  intros. induction w.
  - reflexivity.
  - simpl. rewrite IHw. reflexivity.
Qed.

Inductive SubStr {A : Type} {l : list A} {ab : Alphabet l}
  : Str ab -> Str ab -> Prop :=
| prefix : forall w v, (exists u, w = concat v u) -> SubStr w v
| suffix : forall w v, (exists u, w = concat u v) -> SubStr w v.

Lemma empty_substr : forall (A : Type) (l : list A) (ab : Alphabet l),
  forall w : Str ab, SubStr w empty_str.
Proof.
  intros. apply prefix.
  exists w. reflexivity.
Qed.

Lemma length_distribute : forall (A : Type) (l : list A) (ab : Alphabet l),
  forall w v : Str ab, length (concat w v) = length w + length v.
Proof.
  intros. apply app_length.
Qed.
(* app_length does induction proof for us ;) *)

Search (forall A, nat -> list A -> list A).

Fixpoint replicate {A : Type} (n : nat) (l : list A) :=
  match n with
  | O => []
  | S m => l ++ replicate m l
  end.

Definition times {A : Type} {l : list A} {ab : Alphabet l}
  (n : nat) (w : Str ab) := replicate n w.

Lemma time_0_emtpy : forall (A : Type) (l : list A) (ab : Alphabet l),
  forall w : Str ab, times 0 w = empty_str.
Proof. reflexivity. Qed.

Definition Lang {A : Type} {l : list A} (ab : Alphabet l)
  := Str ab -> bool.

Local Open Scope bool_scope.

Definition an_lang (c : nat) : Lang bin_alphabet :=
  fix f (w : Str bin_alphabet) :=
    match w with
    | [] => true
    | x :: v => Nat.eqb x c && f v
    end.

Example an_lang_match0 : forall c, an_lang c empty_str = true.
Proof. reflexivity. Qed.

Example an_lang_match1 : an_lang 0 [0;0;0;0] = true.
Proof. reflexivity. Qed.

Check Nat.divmod.
Locate "x * y".
Check prod.
Search (forall A, nat -> list A -> list A).
Check Nat.even.

Definition anbn_lang : Lang bin_alphabet :=
  fun (w : Str bin_alphabet) =>
    let n2 := (length w) in
    if Nat.odd n2 then
      false
    else
      let n := Nat.div2 n2 in
      an_lang 0 (firstn n w) && an_lang 1(skipn n w).

Example anbn_lang_match0 : anbn_lang nil = true.
Proof. reflexivity. Qed.

Example anbn_lang_match1 : anbn_lang [0;0;0;0;1;1;1;1] = true.
Proof. reflexivity. Qed.

Example anbn_lang_nomat1 : anbn_lang [0;0;0;0;1;1;1] = false.
Proof. reflexivity. Qed.

(* it's hard to reason on infinite set represented as in coq's standard library.
   intead, use boolean function representation.. *)
(* Σ* *)
Definition lang_full {A : Type} {l : list A} {ab : Alphabet l}
  : (Lang ab) := Basics.const true.

(* Σ+ *)
Definition lang_fill {A : Type} {l : list A} {ab : Alphabet l}
  : (Lang ab) :=
  fun (w : Str ab) => negb (Nat.eqb 0 (length w)).

Example lang_fill_no_nil : forall (A : Type) (l : list A) (ab : Alphabet l),
  @lang_fill A l ab [] = false.
Proof. reflexivity. Qed.

Inductive Sublang {A : Type} {l : list A} {ab : Alphabet l}
  (l1 l2: Lang ab) : Prop :=
  include : forall w : Str ab, l1 w = true -> l2 w = true -> Sublang l1 l2.
