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

Require Import Main.

Module Parity.
Local Parameter N:Set.
Local Parameter S:N -> N .
Local Parameters even odd: N -> Prop.

Goal 
(forall x, even x -> odd (S x)) ->
(forall x, odd x -> even (S x)) ->
(forall x, even x -> even (S (S x))).

pose (Denv := empty \ N).
pose (Tenv := empty \ mkF Denv (1::nil) 1 S).
pose (Penv := empty \ mkP Denv (1::nil) odd \ mkP Denv (1::nil) even).

pose (goal := (!!1, Atom 2 [ #0 ]  =>> Atom 2 [App  1  [ App 1  [ #0 ] ]])).
pose (hyp2 := (!!1, Atom 1 [ #0 ] =>> Atom 2 [App 1 [ #0 ]])). 
pose (hyp1 := (!!1, Atom 2 [ #0 ] =>> Atom 1 [App 1 [ #0 ]])).

pose (prf := (* Proof Denv Tenv Penv *)
 (I_Forall ( I_Arrow 
 (E_Forall 1 (! 1) (E_Forall 2 (App 1 [! 1]) 
 (E_Arrow 3 4 (E_Arrow 6 5 (Ax 7)))))))).

refine (Reflect Denv Tenv Penv prf nil
           (hyp1 :: hyp2 :: nil ) goal _) .
reflexivity.
Qed.

End Parity.

Module Equality.

Local Parameter S:Set.

Goal 
forall x y : S , x = y -> y = x.

pose (Denv := empty \ S).
pose (goal0 := 
   (!!1, !! 1, Equal 1 (# 1) (# 0) =>> Equal 1 (# 0) (# 1))).
pose (prf0 := (* Proof Denv empty empty *)
 (I_Forall ( I_Forall (I_Arrow 
 (E_Equal_in_concl 1 fore (In_Eq Not_here Here) 
  I_Equal))))). 
 
refine (Reflect Denv empty empty prf0 nil nil goal0 _) .
reflexivity.
Qed.

Goal 
forall x y z : S , x = y /\ y = z -> x = z.

pose (Denv := empty \ S).

pose (goal1 := (!!1, !! 1, !!1, 
Equal 1 (#2) (#1) //\\
Equal 1 (# 1) (# 0) =>> 
Equal 1 (# 2) (# 0))).

pose (prf1 := (*Proof Denv empty empty *)
 (I_Forall ( I_Forall ( I_Forall ( I_Arrow ( E_And 1
 (E_Equal_in_concl 2 fore (In_Eq Here Not_here) 
 (Ax 3)))))))). 

refine (Reflect Denv empty empty prf1 nil nil goal1 _).
reflexivity.
Qed.

End Equality.

Module Group_theory.

Local Parameter G :Set.
Local Parameter op: G -> G -> G.
Local Parameter e :G.

Local Axiom assoc: forall x y z, op (op x y) z= op x (op y z).
Local Axiom neutral: forall x, op e x = x.
Local Axiom inverse: forall x,exists y, op y x = e.  

Goal forall x y, op x y = e -> op y x = e.

pose (Denv := (empty \ G)).
pose (Tenv := (empty \ 
mkF Denv (1::1::nil) 1 op \ 
mkF Denv nil 1 e )). 

pose (Hyp1 := !!1,!!1,!!1,
Equal 1 (App 1  [ App 1 [#2 ;#1] ; #0 ])
(App 1 [#2 ; App 1 [#1 ;#0]])). 
pose (Hyp2 := !!1,
Equal 1 (App 1  [& 2 ; #0]) (#0)).
pose (Hyp3 := !!1,??1,
Equal 1 (App 1  [ #0 ;#1] ) (& 2)).
pose (goal := !!1 , !! 1,
Arrow (Equal 1 (App 1  [ #1 ;#0] ) (& 2)) 
(Equal 1 (App 1  [ #0 ;#1] ) (& 2))).

pose (prf := (*Proof Denv Tenv empty*)
                   (I_Forall (I_Forall (I_Arrow
                   (E_Forall 3 (!1)
                   (E_Exists 5 
                   (E_Equal_in_concl 6 back 
                     (In_Eq Not_here Here)
                   (E_Forall 2 (!1)
                   (E_Equal_in_concl 7 back 
                     (In_Eq Not_here (In_args 
                     (More_occ Not_here (More_occ Here No_occ))))
                   (E_Forall 2 (App 1 [!2;!1]) 
                   (E_Equal_in_concl 8 back
                     (In_Eq Here Not_here) 
                   (E_Equal_in_concl 4 back
                     (In_Eq Not_here (In_args (More_occ Not_here 
                     (More_occ (In_args (More_occ Here No_occ)) No_occ))))
                   (E_Equal_in_concl 6 back
                     (In_Eq (In_args (More_occ Here No_occ)) Not_here)
                   (E_Forall 1 (!3) 
                   (E_Forall 9 (!1)
                   (E_Forall 10 (App 1 [!2; !1])
                   (E_Forall 1 (!1) 
                   (E_Forall 12 (!2)
                   (E_Forall 13 (!1)
                   (E_Equal_in_concl 11 fore (In_Eq Here Not_here)
                   (E_Equal_in_concl 14 fore 
                     (In_Eq Not_here (In_args (More_occ Not_here 
                     (More_occ Here No_occ)))) 
                     I_Equal
))))))))))))))))))))).

refine (Reflect Denv Tenv empty prf nil
(Hyp1::Hyp2::Hyp3::nil) goal _ assoc neutral inverse).
reflexivity.
Qed.

End Group_theory.
(*
Section Refined.

Goal forall b, ~(b=true /\ b=false).

pose (Denv := (empty \ bool)).
pose (Tenv := (empty \ mkF Denv nil 1 true \ mkF Denv nil 1 false)).

pose (goal := 
   !! 1, ( Equal 1 (#0) (&1) //\\ Equal 1 (#0) (&2) ) =>> Absurd).


pose (prf := fun H => Proof Denv Tenv empty
  (I_Forall (I_Arrow (E_And 1 
  (E_Equal_in_hyp 3 2 fore (In_Eq Here Not_here) 
  (Meta (1:: nil) 
     ( Equal 1 (!1) (&1) //\\ Equal 1 (!1) (&2) ::
       Equal 1 (!1) (&1) ::
       Equal 1 (!1) (&2) ::
       Equal 1 (&1) (&2) :: nil) # H)))))).

refine ((fun H => Reflect Denv Tenv empty (prf H) nil nil goal) _).
Show.
compute in *|-*.
Show.
congruence.
Qed.

End Refined.
*)
