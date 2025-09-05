From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra zmodp.
Require Import utils.
Import GroupScope Order.TTheory GRing.Theory Num.Theory GRing.Zmodule  Num.NumDomain.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(** ** Generak functions.                                                  *)
(****************************************************************************)


(* Added this definition, apparently removed from library *)
Definition prod_curry (A B C: Type) (f: A -> B -> C)  (p: A * B)
   := let (p1,p2) := p in f p1 p2.

(******************************************************************************)
(** **  Z Module convenience.                                                          *)
(******************************************************************************)
Section Z_Modules.


Variables (R : zmodType).
Implicit Types x y : R.

(** Functionality (must exist somewhere !!)*)
Fact add_eval z x y: (x = y -> (z + x = z + y)%R).
Proof.
  by move=> H; rewrite H.
Qed.

Fact func_eval (f: R -> R) (x y: R): (x = y ) -> ( f x = f y).
Proof.
  by move=> H; rewrite H.
Qed.

(* The involutive character of - oppr is simply expressed here*)
Lemma opprI x y : (- - x  = x )%R.
Proof.
by apply/eqP; rewrite eqr_oppLR.
Qed.

(** Use of morphism, and iteration.
*)
Fact oppM:  morphism_2 (fun x => GRing.opp x) (fun x y => GRing.add x y)
                (fun x y => GRing.add x y).
Proof. by apply opprD. Qed.

Fact oppM3 x y z: (- (x + y + z))%R = (- x -y - z)%R.
Proof.
by rewrite 2!oppM.
Qed.

Fact oppM4 w x y z: (- (w + x + y + z))%R = (- w - x -y - z)%R.
Proof.
by rewrite 3!oppM.
Qed.

(** Facilitate use of divisibility criterion *)
Fact modz_dvd: forall m d, (d %| m = (m %% d == 0))%Z.
Proof.
move => m d. 
by rewrite (sameP dvdz_mod0P eqP).
Qed.

(* Some addition rewrites can be awkward!*)
Fact addrC2: forall x y z, (x + y + z)%R = (x + z + y)%R.
Proof.
by move => x y z; rewrite addrC  [Z in (_ = Z + _)%R ]addrC   -addrA. 
Qed.

(** Following are a series of expression trees in which +/- simplification
    is sought.
    Numerous possible cases with opp and positionning in expression tree *)
Fact addr_opp2: forall x y z, (x - y + z)%R = (x + (z - y))%R.
Proof.
by move => x y z; rewrite -addrA  -GRing.opprB //=; 
  congr (GRing.add _ _); rewrite opprB addrC.
Qed.

Fact addr_opp2b: forall x y, (-x + y + x)%R = y.
Proof.
by move => x y; rewrite addrC addrA addrN add0r.  
Qed.

Fact addr_opp2c: forall x y, (x + y - y)%R = x.
Proof.
by move => x y; rewrite -addrA addrN  addr0.  
Qed.

Fact addr_opp2d: forall x y, ( - x + y - y)%R = (- x)%R.
Proof. by move => x y; apply addr_opp2c.
Qed.

Fact addr_opp2e: forall x y, (x + y - x)%R = y.
Proof.
 by move => x y; have := addr_opp2b (-x)%R; rewrite opprK => ->. 
Qed.

(** "Simplification rules, facilitate handling awkward expr. trees"*)

Fact addrK_N1 [V : zmodType] (x y : V): (- x + y + x)%R  = y .
Proof.
by rewrite -addrA addrC -addrA addrN addr0.
Qed.

Fact addrK_N2 z x y : (- x + y - z + x)%R  = (y - z)%R .
Proof.
rewrite -addrA addrC   [RHS]addrC. rewrite addrA.  
by have -> : (-z + x -x)%R = (-z)%R by rewrite -addrA addrN addr0. 
Qed.

(* Cannot use addrK_N2 with x = - x' because the - - x' does not get used when
   pattern checking. *)
Fact addrK_N2o z x y : ( x + y - z - x)%R  = (y - z)%R .
Proof.
rewrite -addrA addrC   [RHS]addrC. rewrite addrA.  
by have -> : (-z - x + x)%R = (-z)%R by  rewrite -addrA  addNr addr0.
Qed.

Fact addrK_N2oc z x y : ( y + x - z - x)%R  = (y - z)%R .
Proof.
rewrite -!addrA.
by have ->: (x + (- z - x))%R = (- z)%R by
  rewrite addrC -addrA addNr addr0. 
Qed.

Fact addrK_N3  z x y : (x + (y + (- x +  z)))%R  = (y + z)%R .
Proof.
by rewrite 2!addrA addrC  addr_opp2e addrC.
Qed.


Fact addrK_N3o  z x y : (- x + (y +  x +  z))%R  = (y + z)%R .
Proof.
by rewrite 2!addrA  addrC addr_opp2b addrC.
Qed.

Fact addrK_N3o'  z x y : (- x + (y +  (x +  z)))%R  = (y + z)%R .
Proof.
by rewrite 2!addrA  addrC addr_opp2b addrC.
Qed.

Fact addrK_N1X  z x y : (-x -y + (x + z))%R = (z - y)%R.
Proof.
by rewrite !addrA   addrC addrK_N1. 
Qed.

Fact addrK_N1X'  z x y : (-x -y + x + z)%R = (z - y)%R.
Proof.
by rewrite    addrC addrK_N1. 
Qed.

Fact addrK_N2X  z x y w : (-x -y + (x + z + w))%R = (z - y + w)%R.
Proof.
by rewrite !addrA addrC addrK_N1X' addrC. 
Qed.

End Z_Modules.

Section Nat_Z_convenience.

(* TBD: already in cone.v MOVE IN COMMON PLACE*)
Section Order.
Local Open Scope order_scope.
Local Open Scope ring_scope.

Variable (R : numDomainType).

Lemma ltler  (x y : R): (x <= y) = (x == y)  || (x < y).
Proof. by rewrite le_eqVlt eq_sym. Qed.

Lemma ltler_I (x y:R): (x < y) -> (x <=y ).
Proof. by  rewrite le_eqVlt => H; apply/orP; right. Qed.

(** Really, just repackagings of lerD2r/lerD2r monotony lemma
    Note: many more results in algebra.ssrnum and algebra.ssralg
*)
Lemma addger (x y z :R): (x <= y) = ( x + z <= y + z ).
Proof. by rewrite lerD2r.
Qed.

Lemma subger (x y z :R): (x <= y) = ( x - z <= y - z ).
Proof. by rewrite lerD2r.
Qed.

Lemma lerXoppl (x y :R): (x <= y) = ( 0 <= - x + y ).
Proof.
 by rewrite -(addNr x)  addrC [X in (_ = (_ <= X))]addrC lerD2r.
Qed.

Lemma lerXoppr (x y :R): (x <= y) = ( 0 <= y - x ).
Proof.
 by rewrite (subger _ _ x) addrC addNr. 
Qed.

Lemma mulger {r y z :R}: (0 < r) ->   (y <= z)  = (y * r <= z * r ).
Proof.
move =>H; apply: Logic.eq_sym (ler_pM2r H y z). 
Qed.

Lemma mulgel {r y z :R}: (0 < r) ->   (y <= z)%R  = ( r * y  <= r * z  ).
Proof.
 by move =>H; rewrite 2!mulrC (mulger H) mulrC; replace (z * r)%R with (r * z)%R;
  last by apply:mulrC. 
Qed.


Lemma mulwger (r y z :R): (0 <= r) 
        ->( (y <= z) || (r == 0) = ((r * y)  <= (r * z) )).
Proof. 
move => H; rewrite ltler in H; case/orP : H => H; 
      first by  rewrite -(eqP H) !mul0r [X in _ = X]ltler  eq_refl Bool.orb_true_r.
      rewrite orbC; rewrite (mulger (r:=r) H)  mulrC;
       replace (z * r)%R with (r * z)%R; last by apply:mulrC.
       rewrite (negPf (lt0r_neq0 H)) //= .
Qed.

(* missing or not found ?*)
Lemma ltz_abs : forall  (x:R), x < 0 -> 0 < `|x|%R. 
Proof.
move => x; move/ltr0_neq0 => H. 
have :=(normr_ge0 x); rewrite (le0r `|x|%R) normr_eq0.
by case H': (x == 0) =>//=; rewrite H' in H. 
Qed.


(* Facilitate use of intervals *)
Lemma itv_sepr: forall (a b x: R), a <= x <= b -> 0 <= x - a <= b - a.
Proof.
move => a b x H.
elim : (andP H) => H1 H2.
by apply/andP; split; [rewrite -lerXoppr | rewrite -subger].
Qed.

Lemma itv_sepl: forall (a b x: R), a <= x <= b -> 0 <= b - x  <= b - a.
Proof.
move => a b x H.
elim : (andP H) => H1 H2.
apply/andP; split.
  by rewrite -lerXoppr.
  rewrite lerBlDl addrC -(subrKA 0) add0r oppr0 addr0 -addrA 
          -{1}(add0r b) [X in (_ <= X )%R]addrC -addger
          -lerBlDl opprI; last by  apply: a. by rewrite  add0r.
Qed.

End Order.
End Nat_Z_convenience.


Section Num_Domain.

Variables (R : numDomainType).
Implicit Types x y : R.

Fact mulr_oppK: forall x y, (- ( (- x) * y))%R = (x * y)%R.
Proof.
by move => x y; rewrite -mulN1r -[X in (-1 * (X * _))%R]mulN1r
   -mulrA mulrA mulrNN mul1r mul1r.
Qed.

End  Num_Domain.

Section Int_Domain.
Local Open Scope ring_scope.

Implicit Types x y : int.

Fact leq_modz: forall (m d: int), (0 < d) -> (0 <= m) ->  (m %% d <= m)%Z.
Proof.
move => m d Hd ; rewrite -(@divz_ge0 m _ Hd) (mulger Hd) mul0r.
have:= divz_eq m d; move/eqP; rewrite - subr_eq => H; rewrite -(eqP H).  
by rewrite lerBrDl addr0 . 
Qed.

Lemma eqz_modDlX p m n d : (p + m == n %[mod d])%Z = (p == n - m  %[mod d])%Z.
Proof.
rewrite -{1}[m]addr0 -{1}[n]addr0. 
have -> : 0 = (- m + m)%Z by rewrite addNr.
by rewrite 3!addrA eqz_modDr -addrA addrN addr0.
Qed.

Lemma eqz_modDrX p m n d : (p + m == n %[mod d])%Z = (m == n - p  %[mod d])%Z.
Proof.
rewrite -{1}[m]addr0 -{1}[n]addr0. 
have -> : 0 = (- p + p)%Z by rewrite addNr.
replace (n + ( - p + p))%Z with (p +( n - p)). 
by rewrite eqz_modDl addNr addr0.
by rewrite addrC addrA.  
Qed.


End Int_Domain.

(******************************************************************************)
(** ** Simplifications in fields                                           *)
(******************************************************************************)

Section R_RealField.

Variables (R : realFieldType).
Implicit Types x y : R.


Lemma mulf_divA (x1 y x2:R)  : (x1  * (x2 / y) = (x1 * x2) / y)%R.
Proof.
rewrite -(divr1 x1)  (mulf_div x1 1 x2 y) (divr1 x1) mul1r //=.
Qed.

Lemma mulf_divB (x1 y x2:R)  : ((x1 / y) * x2 = (x1 * x2) / y)%R.
Proof.
by rewrite -{2}(divr1 y) -mulf_div  invr1 divr1.
Qed.

End R_RealField.



