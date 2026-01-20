(* Используемая версия Rocq -- 9.1.
  Более низкие версии могут не скомплировать файл из-за
  использования автоматических тактик eexists и lia,
  которые стали работать лучше начиная с версии 9.0. *)

From Stdlib Require Import Arith Lia List Unicode.Utf8.
Import ListNotations.
(* Решим слегка обобщённую версию,
  чтобы удобно абстрагировать детали и использовать библиотечные теоремы для списков.
  Дан (односвязнный) список элементов некоторого типа A
  и (разрешимый) предикат P на этом типе.
  Выделить ближайший слева максимальный подсписок элементов,
  удовлетворяющих предикату P.
  Ясна, что исходная задача решается,
  если взять в качестве A тип символов Char,
  а в качетсве P -- предикат "быть цифрой". *)

Section MaximalSublist.

Context {A : Type} (P : A → bool).

(* Будем считать, что "эффективность" программы,
  упомянутая в условии, означает асимптотическую эффективность,
  а не написание на "эффективном" языке программирования (например, C).
  Приведём пример решения в Rocq. *)

Fixpoint max_sublist_aux (l acc : list A) : list A :=
  match l with
  | [] => acc
  | a :: l =>
    if P a then max_sublist_aux l (a :: acc)
    else
      let acc' := max_sublist_aux l [] in
      if length acc <? length acc'
      then acc'
      else acc
  end.

Definition max_sublist (l : list A) : list A :=
  rev (max_sublist_aux l []).

(* Данная программа работает за время,
  линейное от длинны входного массива
  (в предположении, что предикат P вычислим за константное время).
  Действительно, время работы функции max_sublist_aux
  пропорционально сумарному времени работы всех сравнений <?.
  Так как все подсписки acc' не пересекаются,
  то сумарное время работы линейно от суммы длин l и acc.
  Разворот списка в функции max_sublist также работает за линейное время. *)
  
(* Вероятно, более "эффективным" можно было бы считать решение,
  использующее хвостовую рекурсию: *)

Fixpoint max_sublist_aux' (l x y: list A) : list A :=
  let long a b := if length b <? length a then a else b in
  match l with
  | [] => long x y
  | a :: l =>
    if P a
    then max_sublist_aux' l (a :: x) y
    else max_sublist_aux' l [] (long x y)
  end.

(* Однако доказывать корректность такой функции ещё менее удобно,
  чем для изначального варианта.
  Поэтому остановимся на первой версии. *)

(* Перейд`м к спецификации.
  Для этого нам потребуется понятие подсписка,
  которое отсутсвует в стандартной библиотеке. *)

Definition sublist {A : Type} (i j : nat) (l : list A) : list A :=
  skipn i (firstn j l).

Definition max_sublist_spec (f : list A → list A) :=
  ∀ (l : list A),
  Forall (λ x, P x = true) (f l) ∧ (* -- все элементы удовлтворяют предикату P *)
  ∃ i j, 0 ≤ i ∧ i ≤ j ∧ j ≤ length l ∧
    f l = sublist i j l ∧ (* -- возращается подсписок *)
    ∀ i' j', 0 ≤ i' ∧ i' ≤ j' ∧ j' ≤ length l ∧ Forall (λ x, P x = true) (sublist i' j' l) →
      length (sublist i' j' l) ≤ length (f l) ∧ (* -- он максимальный *)
      (length (sublist i' j' l) = length (f l) → i ≤ i'). (* -- он ближайший слева из максимальных*)

(* Далее доказываются несколько лемм о поведении функции max_sublist_aux.
  Доказательство корректности основной функции max_sublist
  приведено в теореме max_subslit_correct ниже на строках 189--225. *)

Lemma sub_0_le : ∀ (m n : nat), m ≤ n → m - n = 0.
Proof. apply Nat.sub_0_le. Qed.

Lemma max_sublist_aux_sublist :  
  ∀ (l acc : list A),
  Forall (λ x, P x = true) acc →
  ∃ i j, 0 ≤ i ∧ i ≤ j ∧ j ≤ length (rev l ++ acc) ∧
    max_sublist_aux l acc = sublist i j (rev l ++ acc) ∧
    ∀ i' j', 0 ≤ i' ∧ i' ≤ j' ∧ j' ≤ length (rev l ++ acc) ∧
      Forall (λ x, P x = true) (sublist i' j' (rev l ++ acc)) →
      (j - i = j' - i' → j' ≤ j).
Proof with (now try lia).
  unfold sublist.
  induction l as [|? l IH]; intros acc ?; simpl.
  1: do 2 eexists; repeat split; try rewrite firstn_all, skipn_0...
  destruct (P _) eqn: ?.
  1: rewrite <- app_assoc; apply IH, Forall_cons...
  destruct (_ <? _) eqn: Hlen.
  2: {
    do 2 eexists; repeat split.
    4: rewrite firstn_all, skipn_app, skipn_all, Nat.sub_diag...
    all: repeat rewrite length_app... }
  rewrite <- app_assoc; simpl.
  destruct (IH [] (Forall_nil _))
    as (i & j & ? & ? & ? & Hxij & Hij); clear IH.
  exists i, j.
  rewrite app_nil_r in *.
  do 4 try split.
  1,2,3: try rewrite length_app...
  1: rewrite firstn_app, sub_0_le, firstn_0, app_nil_r...
  intros x y (? & ? & Hy & Hxy) ?.
  destruct
    (le_gt_dec x (length (rev l))),
    (le_gt_dec y (length (rev l))).
  * apply Hij with x; repeat split.
    all: try rewrite firstn_app, sub_0_le, firstn_0, app_nil_r in Hxy...
  * rewrite firstn_app, firstn_all2, skipn_app, sub_0_le, skipn_0 in Hxy by lia.
    apply Forall_app in Hxy as [_ H'].
    destruct (y - length (rev l)) eqn:?.
    1: lia.
    rewrite firstn_cons in H'.
    inversion H'; congruence.
  * lia.
  * rewrite length_app in Hy; simpl in Hy.
    apply Nat.ltb_lt in Hlen.
    rewrite Hxij, length_skipn, length_firstn in Hlen...
Qed.

Lemma max_sublist_aux_correct :
  ∀ (l acc : list A), Forall (λ x, P x = true) acc →
    Forall (λ x, P x = true) (max_sublist_aux l acc).
Proof.
  induction l; intros; simpl.
  1: easy.
  destruct (P _) eqn:?; try destruct (_ <? _).
  all: auto using Forall_cons.
Qed.

Lemma max_sublist_aux_maximal :
  ∀ (l acc : list A), Forall (λ x, P x = true) acc →
    ∀ i j,  Forall (λ x, P x = true) (sublist i j (rev l ++ acc)) →
    length (sublist i j (rev l ++ acc)) ≤ length (max_sublist_aux l acc).
Proof with (now try simpl; try lia).
  unfold sublist.
  induction l as [|? l' IH]; intros acc ? i j Hij; simpl in *.
  1: rewrite length_skipn, length_firstn...
  rewrite <- app_assoc in *; simpl in *.
  destruct (P _) eqn: ?.
  1: auto using Forall_cons.
  rewrite firstn_app in *.
  replace (length (if _ <? _ then _ else _))
    with (Nat.max (length acc) (length (max_sublist_aux l' []))).
  2: {
    destruct (_ <? _) eqn: E.
    + apply Nat.ltb_lt in E...
    + apply Nat.ltb_ge in E... }
  destruct (le_gt_dec j (length (rev l'))).
  - set (IH' := IH []).
    rewrite sub_0_le, firstn_0, app_nil_r in * by lia.
    eapply Nat.le_trans; try apply IH'...
  - rewrite firstn_all2, skipn_app in * by lia.
    destruct (le_gt_dec i (length (rev l'))).
    + rewrite sub_0_le, skipn_0 in * by lia.
      apply Forall_app in Hij as [_ Hij].
      destruct (_ - _) eqn: ?.
      1: lia.
      rewrite firstn_cons in Hij.
      inversion Hij; congruence.
    + rewrite skipn_all2, app_nil_l, length_skipn, length_firstn...
Qed.

Lemma rev_sublist :
  ∀ (l : list A) (i j : nat), 0 ≤ i ∧ i ≤ j ∧ j ≤ length l →
    sublist i j (rev l) = rev (sublist (length l - j) (length l - i) l).
Proof.
  intros * [? ?]; unfold sublist in *.
  rewrite firstn_rev, skipn_rev, skipn_firstn_comm, length_skipn.
  do 2 f_equal; lia.
Qed.

(* Основная теорема о корректности функции max_sublist. *)
Theorem max_sublist_correct : max_sublist_spec max_sublist.
Proof.
  intros l.
  unfold max_sublist.
  split.
  1: now apply Forall_rev, max_sublist_aux_correct.
  destruct (max_sublist_aux_sublist l []) as (i & j & ? & ? & ? & Hxij & H); simpl in *.
  1: easy.
  rewrite app_nil_r, length_rev in *.
  do 2 eexists; do 4 try split.
  4: now rewrite Hxij, rev_sublist, rev_involutive.
  1,2,3: lia.
  intros i' j' (? & ? & ?).
  split.
  - replace (sublist i' j' l) with (rev (sublist (length l - j') (length l - i') (rev l ++ []))).
    1: rewrite length_rev; apply max_sublist_aux_maximal.
    1: easy.
    all: rewrite app_nil_r, rev_sublist by lia.
    all: replace (_ - (_ - _)) with i' by lia.
    all: replace (_ - (_ - _)) with j' by lia.
    + now apply Forall_rev.
    + now rewrite rev_involutive.
  - intros H'.
    enough (length l - i' <= j) by lia.
    apply H with (length l - j').
    do 4 try split.
    1,2,3: lia.
    + rewrite rev_sublist by lia.
      replace (_ - (_ - _)) with i' by lia.
      replace (_ - (_ - _)) with j' by lia.
      now apply Forall_rev.
    + rewrite Hxij, rev_sublist, length_rev in H' by lia.
      unfold sublist in H'.
      do 2 rewrite length_skipn in H'.
      do 2 rewrite length_firstn in H'.
      lia.
Qed.

End MaximalSublist.


From Stdlib Require Import String.

(* Вернёмся к исходной задаче о максимальной построке из десятичных цифр. *)
Section MaximalSubstring.

(* В этом случае предикат P = is_disgit. *)
Definition is_digit (b : Byte.byte) : bool :=
  match b with
  | Byte.x30
  | Byte.x31
  | Byte.x32
  | Byte.x33
  | Byte.x34
  | Byte.x35
  | Byte.x36
  | Byte.x37
  | Byte.x38
  | Byte.x39 => true
  | _        => false
  end.

(* Строка в Rocq -- это не совсем список
  (она задаётся отдельным индуктивным типом, полностью повторяющим тип списка),
  поэтому приходится использовать переводы в список байтов и обратно.
  Они работают за линейное время. *)
Definition max_substring (s : string) :=
  string_of_list_byte (max_sublist is_digit (list_byte_of_string s)).

Compute (max_substring "=123 456+89").
(* = "123" *)

(* Пример со строкой длины 10000*)
Definition s := "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"%string.
Compute (length s).
Compute (max_substring s).

End MaximalSubstring.
