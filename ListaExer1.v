(** * Métodos Formais Lista de Exercícios 1 *)

From LF Require Export Induction.

(** Prove usando Coq que $\Sigma_{i=0}^{n}i = (n^2 + n)/2$ ([sum_n]). 
    No desenvolvimento desse exercício serão necessárias algumas definições 
    feitas nos módulos [Basics.v] e [Induction.v] são elas: [plus_n_O], 
    [plus_assoc], [plus_comm], [mult_comm] e [mult_S]. *)

(** A função somatório de números naturais de 0 até $n$ pode ser implementada 
    como: *)

Fixpoint sum (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n + sum n'
  end.

(** Com objetivo de simplificar as provas a função [div2] implementa a 
    divisão por 2. *) 

Fixpoint div2 (n:nat) : nat :=
  match n with
  | O => O
  | S O => O 
  | S (S n') => S (div2 n')  
end.  


Theorem plus_n_1 : forall (n : nat),
  n + 1 = S (n).
Proof. 
  intro n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. 
Qed.

Theorem plus_n_Sm : forall (n m:nat),
  n + S m = S (n + m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_2_n_plus : forall (n : nat),
  n + n = 2 * n.
Proof.
  intro n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- plus_n_O. reflexivity.
Qed.

Theorem mult2_div2 : forall n : nat,
  n = div2 (2 * n).
Proof.
  intro n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> plus_n_Sm. rewrite <- plus_n_O.
    rewrite -> mult_2_n_plus. rewrite <- IHn'. reflexivity.
Qed.

Theorem div2_mult2_plus: forall (n m : nat),
  n + div2 m = div2 (2 * n + m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite <- plus_assoc. simpl.
  rewrite -> plus_n_Sm. rewrite <- plus_assoc. reflexivity.
Qed.
  
Theorem mult_Sn_m : forall (n m : nat),
  S n * m = m + n * m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> plus_assoc. reflexivity.
Qed.

Theorem sum_Sn : forall n : nat,
  sum (S n) = S n + sum n.
Proof.
  intro n. induction n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem sum_n : forall n : nat,
  sum n = div2 (n * (n + 1)).
Proof.
  intro n. induction n.
  - simpl. reflexivity.
  (*- rewrite -> mult_Sn_m. rewrite -> plus_n_Sm. rewrite <- plus_n_O.
  rewrite -> mult_comm. rewrite <- mult_nm. rewrite -> mult_comm. 
  rewrite -> mult_nm. rewrite sum_Sn. rewrite IHn. rewrite -> plus_n_1.
  rewrite -> mult_comm. rewrite -> mult_Sn_m. rewrite -> div2_mult2_plus.
  rewrite <- *)
  - rewrite plus_n_1. rewrite mult_nm. rewrite mult_Sn_m. rewrite sum_Sn.
    assert(H: n * S n = S n * n). { simpl. rewrite <- mult_n_Sm. rewrite plus_comm. reflexivity. } 
    rewrite H. rewrite mult_Sn_m. rewrite plus_assoc. rewrite mult_2_n_plus. rewrite <- plus_n_1.
    rewrite <- div2_mult2_plus. rewrite IHn. rewrite <- mult_nm. rewrite plus_n_1. 
    reflexivity.
   Qed.

  