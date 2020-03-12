(* Lista de Exercícios 4 
   Nome: Guilherme Utiama
         Peter Brendel 
*)


(* A relação menor ou igual pode ser definida por outro tipo indutivo *)

Inductive le' : nat -> nat -> Prop :=
  | le_0' m : le' 0 m
  | le_S' n m (H : le' n m) : le' (S n) (S m).
(*Prove os segi=uintes teoremas: *)

  

Lemma n_le'_m__Sn_le'_Sm : forall a b, le' a b -> le' (S a) (S b).
Proof.
  intros. apply le_S'. apply H.
Qed.  

Lemma le'_n_n : forall a, le' a a.
Proof.
  intros. induction a. apply le_0'. apply le_S'. apply IHa.
Qed.


Lemma le'_n_Sm : forall a b, le' a b -> le' a (S b). 
Proof.
  intros. generalize dependent b. induction a.
  - intros. apply le_0'.
  - intros. induction b.
    + inversion H.
    + apply le_S'. apply IHa. inversion H. apply H2.
Qed.

(* Prove que as duas definiçoes da relação menor ou igual
   são equivalentes: *)

Theorem le_le' : forall a b, le a b <-> le' a b.
Proof. (*
  intros a b. split. 
  - generalize dependent b. intros. induction b. apply le_00'.
    + inversion H. apply le_S'. apply le_n'. apply le_SS'. apply IHb. apply H2.
  - generalize dependent a. intros. induction b.
    + inversion H. apply le_n. apply le_0. apply le_n.
    + apply le_S. apply IHb. inversion H.
      *)
  split.
  - intros. generalize dependent a. induction b.
    + intros. inversion H. apply le_0'.
    + intros. destruct a.
      * apply le_0'. 
      * apply le_S'. apply IHb. Search le. apply le_S_n in H. apply H.
  - generalize dependent a. induction b.
    + intros. inversion H. apply le_0_n.
    + intros. induction a.
      * apply le_0_n.
      * Search le. apply le_n_S. apply IHb. inversion H. apply H2.
Qed.