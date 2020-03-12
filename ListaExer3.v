(*Nome: Guilherme Utiama e Peter Brendel

*)

From LF Require Export Logic.


Theorem dist_exists_and : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
  split.
  - intros. destruct H. exists x. apply proj1 in H. apply H.
  -  destruct H. exists x. apply and_commut in H. apply proj1 in H. apply H.
Qed.

Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros. split.
  - intros. induction l.
    + right. apply H.
    + simpl. simpl in H. destruct H.
      * left. left. apply H.
      * apply or_assoc. right. apply IHl. apply H.
  - intros. induction l.
    + destruct H. induction l'.
      * apply H.
      * simpl. simpl in IHl'. right. apply IHl'.
      * simpl. apply H.
    + simpl. simpl in H. destruct H. destruct H.
      * left. apply H.
      * right. apply IHl. left. apply H.
      * right. apply IHl. right. apply H.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | (h :: t) => P h /\ All P t 
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros. split. intros.
  - induction l as [| x y].
    + simpl. reflexivity.
    + simpl. split.
      * apply H. simpl. left. reflexivity.
      * apply IHy. intros. apply H. simpl. right. apply H0.
  - induction l as [|x y]. intros.
    + inversion H0. 
    + intros. simpl in H0. simpl in H. destruct H0 as [h' | a']. destruct H as [ah' ha']. 
        rewrite <- h'. apply ah'.
      * apply IHy. destruct H as [ariel tiama]. apply tiama. apply a'. 
Qed.
    
(* Um problema com a definição da função que retorna o reverso de 
   uma lista [rev] é sua complexidade de tempo quadrática devido as
   sucessivas chamadas a função de concatenação [app].
   Essa execução pode ser melhorada com a seguinte definição: *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].
  
  

(* Provar que essa definição é equivalente a de [rev]: *)

Fixpoint auxxx {T} (l a : list T) : list T :=
  match l with
  | [] => a
  | x :: l => auxxx l (x :: a)
  end.


Lemma aux : forall T (l l1 : list T), auxxx l l1 = rev l ++ l1.
Proof.
  intros T l. induction l.
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite IHl. rewrite <- app_assoc.  reflexivity.
Qed.


Lemma tr_rev_correct : forall (X:Type) (l:list X), tr_rev l = rev l.
Proof.
  intros. unfold tr_rev. unfold rev_append. rewrite aux. unfold rev. apply app_nil_r.
Qed.