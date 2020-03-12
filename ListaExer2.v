From LF Require Export Tactics.

Check map.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
map f l. (*fold (fun x xs => (f x) :: xs) l [].*)

Example test_fold_map : fold_map (mult 2) [1; 2; 3] = [2; 4; 6].
Proof. reflexivity.
Qed. 

Theorem fold_map_correct : forall X Y (f: X -> Y) (l: list X),
  fold_map f l = map f l.
Proof. 
  intros. induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intro n. induction n.
  - simpl. intros m. destruct m.
    + reflexivity.
    + simpl. intros que. discriminate que.
  - intros m. destruct m.
    + intros que. discriminate que.
    + intros que. injection que as q. rewrite <- plus_n_Sm in q.
      rewrite <- plus_n_Sm in q. injection q as qu.
      apply IHn in qu. rewrite qu. reflexivity.
Qed.

(*https://github.com/michaelgwelch/coq/blob/master/Poly.v*)
Theorem combine_split' : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [|h t IH1].
  - intros l1 l2 H. simpl in H.  injection H as H1 H2. rewrite <- H1.
    rewrite <- H2. simpl. reflexivity.
  -  intros. inversion H. .
    

Theorem split_combine' : forall X Y (l1 : list X) (l2 : list Y) (l : list (X*Y)),
  length l1 = length l2 -> combine l1 l2 = l -> split l = (l1, l2).
Proof.
  intros X Y l1 l2 l. generalize dependent l1. generalize dependent l2.
  induction l as [| h t IHl].
  - intros l1 l2 H1 H2. destruct l1 as [| h1 t1].
    + simpl. 