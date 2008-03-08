(*
 * Reflecting first-order proofs
 * Copyright (C) 2004-2005 Pierre CORBINEAU
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU Library General Public License version 2 for more details
 * (enclosed in the file LGPL).
 *)

(* $Id$ *)

Unset Boxed Definitions.

Require Export List.
Require Export BinPos.

Open Scope positive_scope.

Ltac clean := try (simpl; congruence). 
Ltac caseq t := generalize (refl_equal t); pattern t at -1; case t.

Functional Scheme Pcompare_ind := Induction for Pcompare Sort Prop.


Lemma Gt_Eq_Gt : forall p q cmp,
       (p ?= q) Eq = Gt -> (p ?= q) cmp = Gt.
apply (Pcompare_ind (fun p q cmp _ => (p ?= q) Eq = Gt -> (p ?= q) cmp = Gt));
simpl;auto;congruence.
Qed.

Lemma Gt_Lt_Gt : forall p q cmp,
       (p ?= q) Lt = Gt -> (p ?= q) cmp = Gt.
apply (Pcompare_ind (fun p q cmp _ => (p ?= q) Lt = Gt -> (p ?= q) cmp = Gt));
simpl;auto;congruence.
Qed.

Lemma Gt_Psucc_Eq: forall p q,
  (p ?= Psucc q) Gt = Gt -> (p ?= q) Eq = Gt.
intros p q;generalize p;clear p;induction q;destruct p;simpl;auto;try congruence.
intro;apply Gt_Eq_Gt;auto.
apply Gt_Lt_Gt.
Qed.

Lemma Eq_Psucc_Gt: forall p q,
  (p ?= Psucc q) Eq = Eq -> (p ?= q) Eq = Gt.
intros p q;generalize p;clear p;induction q;destruct p;simpl;auto;try congruence.
intro H;elim (Pcompare_not_Eq p (Psucc q));tauto.
intro H;apply Gt_Eq_Gt;auto.
intro H;rewrite Pcompare_Eq_eq with p q;auto.
generalize q;clear q IHq p H;induction q;simpl;auto.
intro H;elim (Pcompare_not_Eq p q);tauto.
Qed.

Lemma Gt_Psucc_Gt : forall n p cmp cmp0,
 (n?=p) cmp = Gt -> (Psucc n?=p) cmp0 = Gt.
induction n;intros [ | p | p];simpl;try congruence.
intros; apply IHn with cmp;trivial.
intros; apply IHn with Gt;trivial.
intros;apply Gt_Lt_Gt;trivial.
intros [ | | ] _ H.
apply Gt_Eq_Gt;trivial.
apply Gt_Lt_Gt;trivial.
trivial.
Qed.

Lemma Gt_Psucc: forall p q,
       (p ?= Psucc q) Eq = Gt -> (p ?= q) Eq = Gt.
intros p q;generalize p;clear p;induction q;destruct p;simpl;auto;try congruence.
apply Gt_Psucc_Eq.
intro;apply Gt_Eq_Gt;apply IHq;auto.
apply Gt_Eq_Gt.
apply Gt_Lt_Gt.
Qed.

Lemma Psucc_Gt : forall p,
       (Psucc p ?= p) Eq = Gt.
induction p;simpl.
apply Gt_Eq_Gt;auto.
generalize p;clear p IHp.
induction p;simpl;auto.
reflexivity.
Qed.

Lemma Pcompare_Gt_Lt_rev: forall p q,
(p ?= q) Eq = Gt -> (q ?= p) Eq = Lt .
intros p q H; change ((q ?= p) (CompOpp Eq) = Lt).
rewrite <- (Pcompare_antisym p q Eq).
rewrite H;reflexivity.
Qed.

Fixpoint pos_eq (m n:positive) {struct m} :bool :=
match m, n with
  xI mm, xI nn => pos_eq mm nn
| xO mm, xO nn => pos_eq mm nn
| xH, xH => true
| _, _ => false
end. 

Theorem pos_eq_refl : forall m n, pos_eq m n = true -> m = n.
fix 1.
intros [mm|mm|] [nn|nn|];simpl;congruence ||
(intros;apply f_equal with positive;auto).
Defined.

Theorem refl_pos_eq : forall m, pos_eq m m = true.
induction m;simpl;auto.
Qed.

Definition pos_eq_dec (m n:positive) :{m=n}+{m<>n} .
fix 1;intros [mm|mm|] [nn|nn|];try (right;congruence).
case (pos_eq_dec mm nn).
intro e;left;apply (f_equal xI e).
intro ne;right;congruence.
case (pos_eq_dec mm nn).
intro e;left;apply (f_equal xO e).
intro ne;right;congruence.
left;reflexivity.
Defined.

Theorem pos_eq_dec_refl : forall m, pos_eq_dec m m = left (refl_equal m) .
fix 1;intros [mm|mm|].
simpl; rewrite  pos_eq_dec_refl; reflexivity.
simpl; rewrite  pos_eq_dec_refl; reflexivity.
reflexivity.
Qed.

Theorem pos_eq_dec_ex : forall m n,
 pos_eq m n =true -> exists h:m=n,
 pos_eq_dec m n = left h.
fix 1;intros [mm|mm|] [nn|nn|];try (simpl;congruence).
simpl;intro e.
elim (pos_eq_dec_ex _ _ e).
intros x ex; rewrite ex. 
exists (f_equal xI x).
reflexivity.
simpl;intro e.
elim (pos_eq_dec_ex _ _ e).
intros x ex; rewrite ex. 
exists (f_equal xO x).
reflexivity.
simpl.
exists (refl_equal xH).
reflexivity.
Qed.

Fixpoint nat_eq (m n:nat) {struct m}: bool:=
match m, n with 
O,O => true
| S mm,S nn => nat_eq mm nn
| _,_ => false
end.

Theorem nat_eq_refl : forall m n, nat_eq m n = true -> m = n.
fix 1;intros [|mm] [|nn];try (simpl;congruence).
intros;apply f_equal with nat;auto.
Defined.

Theorem refl_nat_eq : forall n, nat_eq n n = true.
fix 1;intros [|nn];simpl;trivial.
Defined.

Section with_A.

Variables A:Set.

Fixpoint Lget (n:nat) (l:list A) {struct l}:option A :=
match l with nil => None
| x::q => 
match n with O => Some x
| S m => Lget m q
end end .

Lemma Lget_app : forall (a:A) l i,
Lget i (l ++ a :: nil) = if nat_eq i (length l) then Some a else Lget i l.
induction l;simpl Lget;simpl length.
intros [ | i];simpl;reflexivity.
intros [ | i];simpl.
reflexivity.
auto.
Qed.

Lemma Lget_app_Some : forall l delta i (a: A), 
Lget i l = Some a ->
Lget i (l ++ delta) = Some a.
induction l;destruct i;simpl;try congruence;auto.
Qed.

Fixpoint pos_length (l:list A) (p:positive) {struct l} : positive :=
match l with
  nil => p
| _::l' => Psucc (pos_length l' p)
end. 

Lemma pos_length_app : forall (l:list A) a p, 
pos_length (l ++ a:: nil) p = Psucc (pos_length l p).
induction l.
reflexivity.
simpl.
intros a0 p;rewrite (IHl a0 p);reflexivity.
Qed.

Lemma pos_length_Psucc : forall (l:list A) p, 
Psucc (pos_length l p) = pos_length l (Psucc p).
induction l.
reflexivity.
simpl.
intro p;rewrite (IHl p);reflexivity.
Qed.

Lemma list_app_split : forall (l: list A),
{ a: A & {l':list A | l = l' ++ a :: nil}} + {l=nil}.
induction l.
right;auto.
left;elim IHl.
intros [ a' [l' h] ];split with a';split with (a::l').
simpl;congruence.
split with a; split with (@nil A).
simpl;congruence.
Qed.

Lemma list_app_rec : forall (P: list A -> Prop),
P nil -> (forall a l, P l -> P (l ++ (a::nil))) -> forall l,P l.
intros P Pnil Pcons.
pose (Q:=fun l => P (rev l)).
assert (HQnil : Q nil). 
assumption.
assert (HQcons :forall a l,Q l -> Q (a::l)). 
unfold Q;simpl.
auto.
assert (HQ:forall l,Q l).
apply list_ind;auto.
intro l; replace l with (rev (rev l)). 
apply HQ. 
apply rev_involutive. 
Qed. 

End with_A.

Implicit Arguments Lget [A].
Implicit Arguments pos_length [A].

Section with_AB.

Variables A B:Set.

Lemma map_app : forall (f:A -> B) l m, 
List.map  f (l ++ m) = List.map  f  l ++ List.map  f  m.
induction l.
reflexivity.
simpl.
intro m ; apply f_equal with (list B);apply IHl.
Qed.

Lemma length_map : forall (f:A -> B) l, 
length (List.map  f l) = length l.
induction l.
reflexivity.
simpl; apply f_equal with nat;apply IHl.
Qed.

Lemma Lget_map : forall (f:A -> B) i l, 
Lget i (List.map f l) = 
match Lget i l with Some a => 
Some (f a) | None => None end.
induction i;intros [ | x l ] ;trivial.
simpl;auto.
Qed.

End with_AB.

Section Store.

Variable A:Type.

Inductive Poption : Type:=
  PSome : A -> Poption
| PNone : Poption.

Inductive Tree : Type :=
   Tempty : Tree
 | Branch0 : Tree -> Tree -> Tree
 | Branch1 : A -> Tree -> Tree -> Tree.
        
Fixpoint Tget (p:positive) (T:Tree) {struct p} : Poption := 
  match T with
    Tempty => PNone
  | Branch0 T1 T2 =>
    match p with
      xI pp => Tget pp T2
    | xO pp => Tget pp T1
    | xH => PNone
    end
  | Branch1 a T1 T2 =>
    match p with
      xI pp => Tget pp T2
    | xO pp => Tget pp T1
    | xH => PSome a
    end
end.

Fixpoint Tadd (p:positive) (a:A) (T:Tree) {struct p}: Tree := 
 match T with
   | Tempty =>
       match p with
       | xI pp => Branch0 Tempty (Tadd pp a Tempty)
       | xO pp => Branch0 (Tadd pp a Tempty) Tempty
       | xH => Branch1 a Tempty Tempty
       end
   | Branch0 T1 T2 =>
       match p with
       | xI pp => Branch0 T1 (Tadd pp a T2)
       | xO pp => Branch0 (Tadd pp a T1) T2
       | xH => Branch1 a T1 T2
       end
   | Branch1 b T1 T2 =>
       match p with
       | xI pp => Branch1 b T1 (Tadd pp a T2)
       | xO pp => Branch1 b (Tadd pp a T1) T2
       | xH => Branch1 a T1 T2
       end
   end.

Definition mkBranch0 (T1 T2:Tree) :=
  match T1,T2 with
    Tempty ,Tempty => Tempty
  | _,_ => Branch0 T1 T2
  end.
  
Fixpoint Tremove (p:positive) (T:Tree) {struct p}: Tree :=
   match T with
      | Tempty => Tempty
      | Branch0 T1 T2 => 
        match p with
        | xI pp => mkBranch0 T1 (Tremove pp T2)                  
        | xO pp => mkBranch0 (Tremove pp T1) T2
        | xH => T
        end
      | Branch1 b T1 T2 =>
        match p with
        | xI pp => Branch1 b T1 (Tremove pp T2)
        | xO pp => Branch1 b (Tremove pp T1) T2
        | xH => mkBranch0 T1 T2
        end
      end.
                                                                                                                        
 
Theorem Tget_Tempty: forall (p : positive), Tget p (Tempty) = PNone.
destruct p;reflexivity.
Qed.

Theorem Tget_Tadd: forall i j a T,
       Tget i (Tadd j a T) =
       match (i ?= j) Eq with
         Eq => PSome a
       | Lt => Tget i T
       | Gt => Tget i T
       end.
intros i j.
caseq ((i ?= j) Eq).
intro H;rewrite (Pcompare_Eq_eq _ _ H);intros a;clear i H.
induction j;destruct T;simpl;try (apply IHj);congruence.
generalize i;clear i;induction j;destruct T;simpl in H|-*;
destruct i;simpl;try rewrite (IHj _ H);try (destruct i;simpl;congruence);reflexivity|| congruence.
generalize i;clear i;induction j;destruct T;simpl in H|-*;
destruct i;simpl;try rewrite (IHj _ H);try (destruct i;simpl;congruence);reflexivity|| congruence.
Qed.

Record Store : Type :=  
mkStore  {index:positive;contents:Tree}.

Definition empty := mkStore xH Tempty.

Definition push a  S :=
mkStore (Psucc (index S)) (Tadd (index S) a (contents S)).

Definition get i S := Tget i (contents S).

Lemma get_empty : forall i, get i empty = PNone.
intro i; case i; unfold empty,get; simpl;reflexivity.
Qed.

Inductive Full : Store -> Type:=
    F_empty : Full empty
  | F_push : forall a S, Full S -> Full (push a S).

Theorem get_Full_Gt : forall S, Full S ->
       forall i, (i ?= index S) Eq = Gt -> get i S = PNone.
intros S W;induction W.
unfold empty,index,get,contents;intros;apply Tget_Tempty.
unfold index,get,push;simpl contents.
intros i e;rewrite Tget_Tadd.
rewrite (Gt_Psucc _ _ e). 
unfold get in IHW.
apply IHW;apply Gt_Psucc;assumption.
Qed.

Theorem get_Full_Eq : forall S, Full S -> get (index S) S = PNone.
intros [index0 contents0] F.
case F.
unfold empty,index,get,contents;intros;apply Tget_Tempty.
unfold index,get,push;simpl contents.
intros a S.
rewrite Tget_Tadd.
rewrite Psucc_Gt.
intro W.
change (get (Psucc (index S)) S =PNone).
apply get_Full_Gt; auto.
apply Psucc_Gt.
Qed.

Theorem get_push_Full : 
  forall i a S, Full S -> 
  get i (push a S) =
  match (i ?= index S) Eq with
    Eq => PSome a
  | Lt => get i S
  | Gt => PNone
end.
intros i a S F.
caseq ((i ?= index S) Eq).
intro e;rewrite (Pcompare_Eq_eq _ _ e).
destruct S;unfold get,push,index;simpl contents;rewrite Tget_Tadd.
rewrite Pcompare_refl;reflexivity.
intros;destruct S;unfold get,push,index;simpl contents;rewrite Tget_Tadd.
simpl index in H;rewrite H;reflexivity.
intro H;generalize H;clear H.
unfold get,push;simpl index;simpl contents.
rewrite Tget_Tadd;intro e;rewrite e.
change (get i S=PNone).
apply get_Full_Gt;auto.
Qed.

Lemma Full_push_compat : forall i a S, Full S ->
forall x, get i S = PSome x -> 
 get i (push a S) = PSome x.
intros i a S F x H. 
caseq ((i ?= index S) Eq);intro test.
rewrite (Pcompare_Eq_eq _ _ test) in H.
rewrite (get_Full_Eq _ F) in H;congruence.
rewrite <- H.
rewrite (get_push_Full i a).
rewrite test;reflexivity.
assumption.
rewrite (get_Full_Gt _ F) in H;congruence.
Qed.

Lemma Full_index_one_empty : forall S, Full S -> index S = 1 -> S=empty. 
intros [ind cont] F one; inversion F.
reflexivity.
simpl index in one;assert (h:=Psucc_not_one (index S)).
congruence.
Qed.

Lemma push_not_empty: forall a S, (push a S) <> empty.
intros a [ind cont];unfold push,empty.
simpl;intro H;injection H; intros _ ; apply Psucc_not_one.
Qed. 

Lemma Full_inv: forall (F:Full empty), 
(existT _  empty F) = (existT _ empty F_empty).
assert (H:
 (forall s,
 forall F : Full s,
 s = empty ->
 existT Full s F = existT Full empty F_empty)).
intros s F.
case F.
reflexivity.
intros a S f ne.
elim (push_not_empty  _ _ ne).
auto.
 Qed.

Fixpoint In (x:A) (S:Store) (F:Full S) {struct F}: Prop :=
match F with
F_empty => False
| F_push a SS FF => x=a \/ In x SS FF
end.

Lemma get_In : forall (x:A) (S:Store) (F:Full S) i , 
get i S = PSome x -> In x S F.
induction F.
intro i;rewrite get_empty; congruence.
intro i;rewrite get_push_Full;trivial.
caseq ((i ?= index S) Eq);simpl.
left;congruence.
right;eauto.
congruence.
Qed.
End Store.

Implicit Arguments PNone [A].
Implicit Arguments PSome [A].

Implicit Arguments Tempty [A].
Implicit Arguments Branch0 [A].
Implicit Arguments Branch1 [A].

Implicit Arguments Tget [A].
Implicit Arguments Tadd [A].

Implicit Arguments Tget_Tempty [A].
Implicit Arguments Tget_Tadd [A].

Implicit Arguments mkStore [A].
Implicit Arguments index [A].
Implicit Arguments contents [A].

Implicit Arguments empty [A].
Implicit Arguments get [A].
Implicit Arguments push [A].

Implicit Arguments get_empty [A].
Implicit Arguments get_push_Full [A].

Implicit Arguments Full [A].
Implicit Arguments F_empty [A].
Implicit Arguments F_push [A].
Implicit Arguments In [A].

Section Store_equiv.
Variable A:Set.
Variable a_eq: A  -> A -> bool.
Variable AEq: A -> A -> Prop.

Variable a_eq_refl : forall a a', a_eq a a' = true -> AEq a  a'.
Variable refl_a_eq : forall a, a_eq a a = true. 

Fixpoint equiv (l:list A) (idx:positive) (S:Store A) {struct l} :bool :=
match l with
 nil => pos_eq (index S) idx 
| a :: l0 => 
  match (get idx S) with
   PNone => false
|  PSome a' => if  a_eq a a'  then equiv l0 (Psucc idx) S else false
end end.

Inductive Equiv : list A -> forall S:Store A , Full S -> Prop := 
  Equiv_nil : Equiv nil empty F_empty
| Equiv_cons : forall l S F a a',
   Equiv l S F ->  
   AEq a a' ->
   Equiv (l ++ a :: nil) (push a' S) (F_push _ _ F).

Lemma Equiv_pos_length_index: forall l S F, 
Equiv l S F -> pos_length l 1 = index S.
intros l S F E.
induction E.
reflexivity.
rewrite pos_length_app.
simpl;congruence.
Qed.

Lemma equiv_inv :  forall l p a a' S (F:Full S),
equiv (l ++ a :: nil) p (push a' S) = true -> 
(equiv l p S = true /\ AEq a a' ). 
induction l.
simpl.
intros p a a' S F;subst.
rewrite get_push_Full;auto.
caseq ((p ?= index S) Eq);clean.
caseq (a_eq a a');clean.
intros ea e ep;
generalize (a_eq_refl _ _ ea) (Psucc_inj _ _ (pos_eq_refl _ _ ep)). 
intros;subst;split;try apply refl_pos_eq;trivial.
case (get p S);clean.
intro h;case (a_eq a h);clean.
intros e ep;
generalize (Psucc_inj _ _ (pos_eq_refl _ _ ep)). 
intro;subst;rewrite Pcompare_refl in e;congruence.
simpl;intros p b b' S F.
rewrite (get_push_Full p b' S F).
caseq ((p ?= index S) Eq);clean.

intro e;assert  (ee:=Pcompare_Eq_eq _ _ e);subst. 
case (a_eq a b');clean.
case l;simpl.
rewrite get_push_Full;auto.
rewrite Psucc_Gt;clean.
rewrite get_push_Full;auto.
rewrite Psucc_Gt;clean.
case (get p S);clean.
intro h;case (a_eq a h);clean.
auto.
Qed.

Lemma equiv_Equiv : forall l S F, 
  equiv l xH S = true -> Equiv l S F. 
intros l S F;generalize l;clear l;induction F.
destruct l;simpl.
left.
congruence.
intro l;elim (list_app_split A l).
intros [ a0 [l0 e]];subst.
intro H;assert (HH := equiv_inv l0 1 a0 a S F H).
elim HH;intros HH1 HH2;subst.
constructor 2;auto.
intros e h;rewrite e in h;unfold push,equiv in h;simpl in h.
elim (Psucc_not_one _(pos_eq_refl _ _ h)).
Qed.



Record WF_store : Type :=
mkWF {WS: Store A; WF: Full WS}.

Fixpoint WF_store_of_list (l : list A) (WF:WF_store) {struct l} :  WF_store :=
match l  with 
 nil => WF
| a :: l0 => 
  let (S,F) := WF in
  WF_store_of_list l0 (mkWF (push a S) (F_push a S F))
end.

Definition mkenv lhyps := WF_store_of_list lhyps (mkWF empty F_empty).
    
Lemma mkenv_app :forall l a S F,
  mkenv l = mkWF S F -> 
  mkenv (l ++ a :: nil) = mkWF (push a S) (F_push a S F).
unfold mkenv.
intros l a;generalize (@empty A) (@F_empty A).
induction l.
simpl; intros s f S F e.
change 
(let (SS,FF) := mkWF s f in
mkWF (push a SS) (F_push a SS FF) = mkWF (push a S) (F_push a S F)).
rewrite e;reflexivity.
simpl;intros;auto.
Qed.

Lemma mkenv_Equiv :
	forall l: list A,
	let (ctx,F) := mkenv l in
	Equiv l ctx F.
intro;pattern l;apply list_app_rec. 
simpl;left.
intros a l'.
caseq (mkenv l').
intros s f e; assert (e':=mkenv_app _ a _ _ e).
rewrite e'.
right;auto.
Qed.

End Store_equiv.

Section Map. 

Variables A B:Set.

Variable f: A -> B.

Fixpoint Tmap (T: Tree A) : Tree B :=
match T with
Tempty => Tempty
| Branch0 t1 t2 => Branch0 (Tmap t1) (Tmap t2)
| Branch1 a t1 t2 => Branch1 (f a) (Tmap t1) (Tmap t2)
end.

Lemma Tget_Tmap: forall T i, 
Tget i (Tmap T)= match Tget i T with PNone => PNone 
| PSome a => PSome (f a) end.
fix 1;intros [|T1 T2|a T1 T2] [ii|ii|];simpl;try congruence;auto.
Qed.

Lemma Tmap_Tadd: forall i a T,
Tmap (Tadd i a T) = Tadd i (f a) (Tmap T).
fix 1;intros [ii|ii|] a [|T1 T2|b T1 T2];try congruence 0;simpl;
(apply f_equal with (Tree B) || simpl;apply f_equal2 with (Tree B)(Tree B)|| idtac);auto;
change (Tmap (Tadd ii a Tempty) = Tadd ii (f a) (Tmap Tempty));auto.
Qed.

Definition map (S:Store A) : Store B :=
mkStore (index S) (Tmap (contents S)).

Lemma get_map: forall i S, 
get i (map S)= match get i S with PNone => PNone 
| PSome a => PSome (f a) end.
intros i [ind T];unfold get,map,contents,index;apply Tget_Tmap.
Qed.

Lemma map_push: forall a S, 
map (push a S) = push (f a) (map S).
intros a [i T];unfold push,map,contents,index.
intros;rewrite Tmap_Tadd;reflexivity.
Qed.

Theorem Full_map : forall S, Full S -> Full (map S).
intros S F. 
induction F.
exact F_empty.
rewrite map_push;constructor 2;assumption.
Qed.

End Map.

Implicit Arguments Tmap [A B].
Implicit Arguments map [A B].
Implicit Arguments Full_map [A B f].

Notation "hyps \ A" := (push A hyps) (at level 72,left associativity).
