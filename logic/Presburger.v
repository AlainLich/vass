From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra zmodp.
Require Import utils algebra_ext bigop_ext matrix_ext.
Import GroupScope Order.TTheory GRing.Theory Num.Theory GRing.Zmodule  Num.NumDomain.

(******************************************************************************)
(** * Presburger arithmetic                                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(** ** convenience.                                                               *)
(******************************************************************************)
Section Bool_convenience.

Fact orb_true_true:forall a b, b == true -> a||b.
Proof. by move => a b H; rewrite (eqP H); exact: orbT. Qed.

End Bool_convenience.

Section Nat_convenience.

Lemma   eq_orgt0: forall n:nat, (n == 0) || (0 < n).
Proof. by case. Qed.

End Nat_convenience.

Section Nat_Z_convenience.

Fact divnzN (x:nat) (y:int): 
          eq (divz (Posz x) (Num.norm y))
             (Posz (divn x (absz y))).
Proof.
case: y => // y; rewrite /divz // -abszE !absz_nat//;
   first by case Hpy: y => //=;  rewrite /sgz //= mul1r.
by rewrite /sgz //= mul1r. 
Qed.

End Nat_Z_convenience.

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

(** ** Quantifier free Presburger formula and negation free normal forms *)

Section QFLIA.

Variable (dim : nat).

Inductive QFLIA_af :=
  | QFLIA_leq       of int & 'cV[int]_dim
  | QFLIA_divisible of nat & int & 'cV[int]_dim.

Inductive QFLIA_formula :=
  | QFLIA_neg       of QFLIA_formula
  | QFLIA_and       of QFLIA_formula & QFLIA_formula
  | QFLIA_or        of QFLIA_formula & QFLIA_formula
  | QFLIA_aformula  of QFLIA_af.

Coercion QFLIA_aformula : QFLIA_af >-> QFLIA_formula.

Definition eq_QFLIA_af (f1 f2 : QFLIA_af) :=
  match f1, f2 with
    | QFLIA_leq nl tl, QFLIA_leq nr tr => (nl == nr) && (tl == tr)
    | QFLIA_divisible ml nl tl, QFLIA_divisible mr nr tr =>
      [&& (ml == mr), (nl == nr) & (tl == tr)]
    | _, _ => false
  end.

Lemma eq_QFLIA_afP : Equality.axiom eq_QFLIA_af.
Proof.
move=> f1 f2; apply: (iffP idP) => [| <-].
- by case: f1 f2 => [| ml] nl tl [nr tr //= /andP | mr nr tr //= /and3P] [];
    do ! move/eqP=> ->.
- by case: f1 => [| m] n t /=; rewrite !eqxx.
Qed.

HB.instance Definition _ := @hasDecEq.Build _ _ eq_QFLIA_afP.

Fixpoint eq_QFLIA_formula (f1 f2 : QFLIA_formula) :=
  match f1, f2 with
  | QFLIA_neg f1', QFLIA_neg f2' => eq_QFLIA_formula f1' f2'
  | QFLIA_and f1l f1r, QFLIA_and f2l f2r =>
    eq_QFLIA_formula f1l f2l && eq_QFLIA_formula f1r f2r
  | QFLIA_or f1l f1r, QFLIA_or f2l f2r =>
    eq_QFLIA_formula f1l f2l && eq_QFLIA_formula f1r f2r
  | QFLIA_aformula f1', QFLIA_aformula f2' => f1' == f2'
  | _, _ => false
  end.

Lemma eq_QFLIA_formulaP : Equality.axiom eq_QFLIA_formula.
Proof.
move=> f1 f2; apply: (iffP idP) => [| <-].
- by elim: f1 f2 =>
    [f1 IHf1 | f1l IHf1l f1r IHf1r | f1l IHf1l f1r IHf1r | f1]
    [//= f2 /IHf1 -> | //= f2l f2r /andP [] /IHf1l -> /IHf1r -> |
     //= f2l f2r /andP [] /IHf1l -> /IHf1r -> | //= f2 /eqP ->].
- by elim: f1 => //= fl -> fr ->.
Qed.

HB.instance Definition _ := @hasDecEq.Build _ _  eq_QFLIA_formulaP.

Definition QFLIA_interpret_af (I : 'cV[int]_dim) (f : QFLIA_af) : bool :=
  match f with
    | QFLIA_leq n t => (0 <= n + (t^T *m I) 0 0)%R
    | QFLIA_divisible m n t => (m.+1 %| (n + (t^T *m I) 0 0)%R)%Z
  end.

Fixpoint QFLIA_interpret_formula
         (I : 'cV[int]_dim) (f : QFLIA_formula) : bool :=
  match f with
    | QFLIA_neg f => ~~ QFLIA_interpret_formula I f
    | QFLIA_and f f' =>
      QFLIA_interpret_formula I f && QFLIA_interpret_formula I f'
    | QFLIA_or f f' =>
      QFLIA_interpret_formula I f || QFLIA_interpret_formula I f'
    | QFLIA_aformula f => QFLIA_interpret_af I f
  end.

Definition QFLIA_top : QFLIA_af := QFLIA_leq 0 0.

Lemma QFLIA_top_true (I : 'cV_dim) : QFLIA_interpret_af I QFLIA_top.
Proof. by rewrite /= trmx0 mul0mx mxE addr0. Qed.

Definition QFLIA_bot : QFLIA_af := QFLIA_leq (- 1) 0.

Lemma QFLIA_bot_false (I : 'cV_dim) : QFLIA_interpret_af I QFLIA_bot = false.
Proof. by rewrite /= trmx0 mul0mx mxE addr0. Qed.

Definition QFLIA_conj (fs : seq QFLIA_formula) := foldr QFLIA_and QFLIA_top fs.

Definition QFLIA_disj (fs : seq QFLIA_formula) := foldr QFLIA_or QFLIA_bot fs.

Lemma QFLIA_conj_all fs (I : 'cV_dim) :
  QFLIA_interpret_formula I (QFLIA_conj fs) =
  all (QFLIA_interpret_formula I) fs.
Proof. elim: fs => [| f fs /= -> //]; exact: QFLIA_top_true. Qed.

Lemma QFLIA_disj_has fs (I : 'cV_dim) :
  QFLIA_interpret_formula I (QFLIA_disj fs) =
  has (QFLIA_interpret_formula I) fs.
Proof. elim: fs => [| f fs /= -> //]; exact: QFLIA_bot_false. Qed.

Fixpoint QFLIA_NF (f : QFLIA_formula) b1 b2 : seq (seq QFLIA_af) :=
  match f with
    | QFLIA_neg f' => QFLIA_NF f' (~~ b1) (~~ b2)
    | QFLIA_and f1 f2 =>
      if b1
      then QFLIA_NF f1 b1 b2 ++ QFLIA_NF f2 b1 b2
      else [seq fs1 ++ fs2 | fs1 <- QFLIA_NF f1 b1 b2, fs2 <- QFLIA_NF f2 b1 b2]
    | QFLIA_or f1 f2 =>
      if b1
      then [seq fs1 ++ fs2 | fs1 <- QFLIA_NF f1 b1 b2, fs2 <- QFLIA_NF f2 b1 b2]
      else QFLIA_NF f1 b1 b2 ++ QFLIA_NF f2 b1 b2
    | QFLIA_aformula f' =>
      if b2
      then
        match f' with
          | QFLIA_leq n t => [:: [:: QFLIA_leq (- n - 1) (- t)]]
          | QFLIA_divisible m n t =>
            let fs := [seq QFLIA_divisible m (n + i%:R) t | i <- iota 1 m] in
            if b1 then [seq [:: f] | f <- fs] else [:: fs]
        end
      else [:: [:: f']]
  end.

Definition QFLIA_DNF f := QFLIA_NF f false false.
Definition QFLIA_CNF f := QFLIA_NF f true false.

Lemma QFLIA_NF_correctness' b1 b2 I (f : QFLIA_formula) :
  QFLIA_interpret_formula I f =
  \big[(if b1 then andb else orb)/b1]_(fs <- QFLIA_NF f b1 b2)
    \big[(if b1 then orb else andb)/ ~~ b1]_(af <- fs)
      (b2 (+) QFLIA_interpret_af I af).
Proof.
elim: f b1 b2 => //=.
- move=> f IH b1 b2.
  by rewrite (IH (~~ b1) (~~ b2)); case: b1 => //=;
    do ! (rewrite big_has big_all -all_predC; apply/eq_in_all => afs _ /=) ||
         (rewrite big_has big_all -has_predC; apply/eq_in_has => af _ /=);
    rewrite addNb negbK.
- move=> f1 IH1 f2 IH2 [] b2; first by rewrite big_cat /= -IH1 -IH2.
  rewrite (IH1 false b2) (IH2 false b2) big_distrlr big_allpairs_dep.
  by apply/eq_bigr => i _; apply/eq_bigr => j _; rewrite big_cat.
- move=> f1 IH1 f2 IH2 [] b2 /=; last by rewrite big_cat /= -IH1 -IH2.
  rewrite (IH1 true b2) (IH2 true b2) big_distrlr big_allpairs_dep /=.
  by apply/eq_bigr => i _; apply/eq_bigr => j _; rewrite big_cat.
- move=> q b1 []; last by case: b1; rewrite !big_cons !big_nil !andbT !orbF.
  case: q => [| m] n t /=; 
    first by rewrite !big_cons !big_nil /= linearN mulNmx  -opprD /= ;
          case : b1 =>//=; rewrite orbF andbT oppmxE opprD -oppM3 -lerNr -real_ltNge 
                                  //=  oppr0 [(n + 1)%R]addrC -addrA  ltz1D.

  suff Hdvdz x : (m.+1 %| x)%Z =
                 ~~ has (fun i => m.+1 %| (i%:Z + x)%R)%Z (iota 1 m)
    by rewrite Hdvdz -all_predC -big_all; case: b1 => /=;
       rewrite ?(big_cons, big_nil, big_map, orbF); apply/eq_bigr => i _;
       rewrite ?(big_cons, big_nil, big_map, orbF) /= addrCA addrA natz.
  apply/esym/hasPn; case: ifP => [| H0] H /=; last (apply/notF; rewrite -{}H0).
  + move=> i; rewrite mem_iota add1n ltnS => /andP [H0 H1].
    apply/dvdz_mod0P; rewrite -modzDmr (dvdz_mod0P H) addr0 modz_small.
    * by case: i H0 H1.
    * by rewrite lez_nat ltz_nat ltnS H1.
  + move: {H} (H `|(m.+1%:Z - (x %% m.+1)%Z)%R|).
    have H: ((x %% m.+1)%Z < m.+1)%R by rewrite ltz_pmod.
    rewrite mem_iota absz_gt0 subr_eq0 neq_lt H orbT /= add1n ltnS.
    move: (ltW H); rewrite -lez_nat ler_def abszE => /eqP ->.

    rewrite lerBDl intS lerD2r -intS.
    move/implyP; rewrite implybN -ltNge -(addr0 1%R) ltz1D => /implyP H0.
    apply/dvdz_mod0P/eqP; rewrite eq_le modz_ge0 // {}H0 //; apply/dvdz_mod0P.
    by rewrite -addrA modzDl addrC {1}(divz_eq x m.+1) -addrA modzMDl subrr.
Qed.    


Lemma QFLIA_NF_correctness b1 I (f : QFLIA_formula) :
  QFLIA_interpret_formula I f =
  (if b1 then all else has)
    ((if b1 then has else all) (QFLIA_interpret_af I))
    (QFLIA_NF f b1 false).
Proof.
rewrite (QFLIA_NF_correctness'  b1 false I f).
elim: (QFLIA_NF _ _ _); first by rewrite big_nil; case: b1 => //.
by case: b1 => fs fss IH; rewrite /= big_cons IH; [congr andb | congr orb];
  (elim: fs; first by rewrite big_nil); move=> af fs IH';
  rewrite big_cons /=; [congr orb | congr andb].
Qed.

End QFLIA.

Arguments QFLIA_top {dim}.
Arguments QFLIA_bot {dim}.

(* Presburger formula and its interpretation *)

Inductive LIA_formula (dim : nat) :=
  | f_all    of LIA_formula (1 + dim)
  | f_exists of LIA_formula (1 + dim)
  | f_neg    of LIA_formula dim
  | f_and    of LIA_formula dim & LIA_formula dim
  | f_or     of LIA_formula dim & LIA_formula dim
  | f_leq    of int & 'cV[int]_dim.

Fixpoint interpret_formula dim (f : LIA_formula dim) : 'cV[int]_dim -> Prop :=
  match f with
    | f_all f => fun I => forall n, interpret_formula f (col_mx (const_mx n) I)
    | f_exists f =>
      fun I => exists n, interpret_formula f (col_mx (const_mx n) I)
    | f_neg f => fun I => ~ interpret_formula f I
    | f_and f f' => fun I => interpret_formula f I /\ interpret_formula f' I
    | f_or f f' => fun I => interpret_formula f I \/ interpret_formula f' I
    | f_leq n t => fun I => (0 <= n + (t^T *m I) 0 0)%R
  end.

(* Quantifier elimination *)

Lemma modz_dvdm (m n d : int) : (d %| m)%Z -> ((n %% m)%Z = n %[mod d])%Z.
Proof.
by case/dvdzP => x ->; rewrite {2}(divz_eq n (x * d)) mulrA modzMDl.
Qed.

Lemma ler_mod m d : (0 <= m -> 0 < d -> (m %% d)%Z <= m)%R.
Proof.
by move=> H H0; rewrite {2}(divz_eq m d) lerDr;
  apply: mulr_ge0; [rewrite divz_ge0 | exact: ltW].
Qed.

Lemma dvdzE' (d m : int) : (d %| m)%Z = (m %% d == 0)%Z.
Proof. by case: dvdz_mod0P => /eqP // H; apply/eqP. Qed.

Section QE_principle.

Variables (dim : nat)
          (fs_leq : seq (int * 'cV[int]_(1 + dim)))
          (fs_mod : seq (nat * int * 'cV[int]_(1 + dim))).

Definition prod_coef :=
  (\prod_(f <- fs_leq | f.2 0%R 0%R != 0) `|f.2 0%R 0%R|%Z *
   \prod_(f <- fs_mod | f.2 0%R 0%R != 0) `|f.2 0%R 0%R|%Z)%N.

Definition fs_leq0 :=
  pmap (fun f : int * 'cV[int]_(1 + dim) =>
          if f.2 0%R 0%R == 0 then Some (f.1, dsubmx f.2) else None)
       fs_leq.

Definition fs_leq1 (b : bool) : seq (int * 'cV[int]_dim) :=
  pmap (fun f : int * 'cV[int]_(1 + dim) =>
          if (if b then f.2 0 0 <= 0 else 0 <= f.2 0 0)%R
          then None
          else let c := (- (prod_coef %/ f.2 ord0 ord0)%Z)%R in
               Some (c * f.1, c *: dsubmx f.2)%R)
       fs_leq.

Definition fs_mod0 : seq (nat * int * 'cV[int]_dim) :=
  [seq (f.1.1, f.1.2, dsubmx f.2) |
   f : nat * int * 'cV[int]_(1 + dim) <- fs_mod & (f.2 0 0 == 0)%R].

Definition fs_mod1 : seq (nat * int * 'cV[int]_dim) :=
  (prod_coef.-1, 0, 0)%R ::
  [seq let c : int := (prod_coef%:Z %/ (f.2 0 0)%R)%Z in
       ((f.1.1.+1 * `|c|)%N.-1, f.1.2 * c, c *: dsubmx f.2)%R |
   f : nat * int * 'cV[int]_(1 + dim) <- fs_mod & (f.2 0 0 != 0)%R].

Definition prod_mod := (\prod_(f <- fs_mod1) f.1.1.+1)%N.

Definition exists_conj_elim_mod (x0 : int) (t : 'cV_dim) : QFLIA_formula dim :=
  QFLIA_conj
    [seq QFLIA_aformula
         (QFLIA_divisible fm.1.1 (fm.1.2 + x0) (fm.2 + t))
    | fm <- fs_mod1].

Definition exists_conj_elim' : QFLIA_formula dim :=
  QFLIA_and
  (QFLIA_conj
     ([seq QFLIA_aformula (QFLIA_leq f.1 f.2) | f <- fs_leq0] ++
      [seq QFLIA_aformula (QFLIA_divisible f.1.1 f.1.2 f.2)  | f <- fs_mod0]))
  (if nilp (fs_leq1 false) || nilp (fs_leq1 true)
   then QFLIA_disj
          [seq exists_conj_elim_mod i 0 | i : nat <- iota 0 prod_mod]
   else QFLIA_conj
          [seq QFLIA_disj
               [seq QFLIA_and
                    (QFLIA_leq (fl.1 - fr.1 - i%:Z) (fl.2 - fr.2))
                    (exists_conj_elim_mod (fr.1 + i) fr.2)
               | i : nat <- iota 0 prod_mod]
          | fl <- fs_leq1 false, fr <- fs_leq1 true]).

Lemma prod_coef_gt0 : 0 < prod_coef.
Proof.
by rewrite muln_gt0; apply/andP; split;
  apply/prodn_cond_gt0 => i H; rewrite absz_gt0.
Qed.

Lemma prod_coef_cml f :
  f \in fs_leq -> (f.2 0 0 == 0)%R || (f.2 0%R 0%R %| prod_coef%:Z)%Z.
Proof.
rewrite -(negbK (_ == _)) -implybE /prod_coef => H; apply/implyP => H0.
rewrite (big_rem _ H) /= H0 !PoszM -mulrA; apply: dvdz_mulr.
by rewrite dvdzE absz_id dvdnn.
Qed.

Lemma prod_coef_cmm f :
  f \in fs_mod -> (f.2 0 0 == 0)%R || (f.2 0%R 0%R %| prod_coef%:Z)%Z.
Proof.
rewrite -(negbK (_ == _)) -implybE /prod_coef => H; apply/implyP => H0.
rewrite (big_rem _ H) /= H0 !PoszM mulrCA; apply: dvdz_mulr.
by rewrite dvdzE absz_id dvdnn.
Qed.

Lemma prod_mod_cm f : f \in fs_mod1 -> (f.1.1.+1 %| prod_mod%:Z)%Z.
Proof.
move=> Hf.
rewrite /prod_mod (perm_big _ (perm_to_rem Hf)) /= big_cons PoszM mulrC.
exact: dvdz_mull.
Qed.

Lemma fs_leq_correct x I :
  all (QFLIA_interpret_af (col_mx (const_mx x) I))
      [seq QFLIA_leq f.1 f.2 | f <- fs_leq] =
  [&& all (QFLIA_interpret_af I) [seq QFLIA_leq f.1 f.2 | f <- fs_leq0],
   all (fun f => prod_coef%:Z * x <= f.1 + (f.2^T *m I) 0 0)%R
       (fs_leq1 false) &
   all (fun f => f.1 + (f.2^T *m I) 0 0 <= prod_coef%:Z * x)%R
       (fs_leq1 true)].
Proof.
rewrite /fs_leq0 /fs_leq1 !(all_pmap, all_map) -!all_predI.
apply/eq_in_all => -[/= n t] Hf.
rewrite -(vsubmxK t) tr_col_mx (mxE col_mx_key);
  case: splitP => // j _;
  rewrite ord1 {j} vsubmxK mul_row_col 2!mxE big_ord1 3!mxE lshift0.

by (case: (ltrgtP (t 0 0) 0)%R (prod_coef_cml Hf);
      last by move=> -> _ /=; rewrite mul0r add0r andbT);
  rewrite dvdz_eq => /= H /eqP H0;
  rewrite ?andbT linearZ /= -scalemxAl (mxE scalemx_key) -mulrDr
          -1?[RHS](ler_nM2l H) -1?[RHS](ler_pM2l H) mulrA mulrN
          [X in (- X)%R](mulrC (t _ _)) H0 mulNr -mulrN mulrCA ler_pM2l
          ?ltz_nat ?prod_coef_gt0 // -(subr_ge0 (- _)%R) opprK (addrCA n).
Qed.


Lemma fs_mod_correct x I :
  all (QFLIA_interpret_af (col_mx (const_mx x) I))
      [seq QFLIA_divisible f.1.1 f.1.2 f.2 | f <- fs_mod] =
  all (QFLIA_interpret_af I)
      [seq QFLIA_divisible f.1.1 f.1.2 f.2 | f <- fs_mod0] &&
  all (fun f : nat * int * 'cV[int]_dim =>
       f.1.1.+1 %|
                (f.1.2 + prod_coef%:Z * x + (f.2^T *m I) 0 0)%R)%Z
      fs_mod1.
Proof.
rewrite /fs_mod0 /fs_mod1 /= !(all_pmap, all_filter, all_map)
        prednK ?prod_coef_gt0 //
        add0r trmx0 mul0mx mxE addr0 dvdz_mulr ?dvdzz //= -all_predI.
apply/eq_in_all => /= -[[d n] t] Hf /=.
rewrite -{1}(vsubmxK t) tr_col_mx mul_row_col 2!mxE big_ord1 3!mxE lshift0.
case: (altP (t 0%R 0%R =P 0%R)) => H /=;
  first by rewrite andbT H mul0r add0r.
move: (prod_coef_cmm Hf) prod_coef_gt0.
rewrite (negbTE H) /= => /dvdzP [prod_coef' H0] /lt0n_neq0.
rewrite -eqz_nat H0 mulzK // mulf_eq0 (negbTE H) /= orbF => H1.
by rewrite prednK ?ltz_nat ?muln_gt0 /= ?absz_gt0 //
           linearZ /= -scalemxAl (mxE scalemx_key) -mulrA (mulrC n) -!mulrDr
           [RHS]dvdzE PoszM abszM /(`|Posz `|_| |) -abszM -dvdzE
           (mulrC _%:Z%Z) dvdz_mul2l // addrA.
Qed.

(* int_Ring removed from mathcomp ( when?), adding a definition for 
   documentation purpose*)
Definition int_Ring:= int.

Lemma exists_conj_elim_mod_correct (x : int) t (I : 'cV_dim) :
  QFLIA_interpret_formula I (exists_conj_elim_mod x t) =
  all (fun f : nat *  int_Ring  * 'cV_dim =>
         (f.1.1.+1 %| (f.1.2 + x + ((f.2 + t)^T *m I) 0 0)%R)%Z)
      fs_mod1.
Proof. rewrite QFLIA_conj_all all_map; exact/eq_in_all. Qed.

Lemma exists_conj_elimP I :
  reflect
    (exists x,
        all (QFLIA_interpret_af (col_mx (const_mx x) I))
            ([seq QFLIA_leq f.1 f.2 | f <- fs_leq] ++
             [seq QFLIA_divisible f.1.1 f.1.2 f.2 | f <- fs_mod]))
    (QFLIA_interpret_formula I exists_conj_elim').
Proof.

set bs := fun fl => [seq (true, f.1 + (f.2^T *m I) 0 0)%R | f <- fs_leq1 fl].
set P := fun x => all
  (fun f => f.1.1.+1 %| (f.1.2 + x + (f.2^T *m I) 0 0)%R)%Z fs_mod1.
have H_prodm : (0 < prod_mod%:Z)%R by rewrite ltz_nat prodn_gt0.
have H_periodm x : P (prod_mod%:Z + x)%R = P x by
  apply/eq_in_all => /= f Hf; rewrite !dvdzE'; congr eq_op; apply/eqP;
  rewrite eqz_mod_dvd addrCA -2!(addrA prod_mod%:Z%Z) subrr addr0;
  exact: prod_mod_cm.
move: (periodic_qe_principle
         (int_archi H_prodm) H_periodm (bs true) (bs false)).
set F1 := exists x : int, _.
set F2 := exists x : int, _.
have: F1 <->
      all (QFLIA_interpret_af I)
        ([seq (QFLIA_leq f.1 f.2) | f <- fs_leq0] ++
         [seq (QFLIA_divisible f.1.1 f.1.2 f.2)  | f <- fs_mod0])
      /\ F2
  by subst F1 F2 bs P; split;
    [case=> x H; split; last exists (prod_coef%:Z * x)%R; move: H |
     case=> H0 [x' H];
     (have/dvdzP [x]: (prod_coef %| x')%Z
        by move/and3P: H => [_ _] /= /andP [H _]; move: H;
           rewrite add0r trmx0 mul0mx mxE addr0; congr dvdz;
           move: prod_coef_gt0; case: prod_coef);
     rewrite mulrC => Hx'; subst x'; exists x; move: H0 H];
  rewrite !all_cat fs_leq_correct fs_mod_correct;
  [by move=> /andP [] /and3P [] -> _ _ /andP [] |
   move=> /andP [] /and3P [_ H H0] /andP [_ H1] |
   move=> /andP [-> ->] /and3P [H H0 H1]; rewrite !andTb -andbA];
  move/and3P: (And3 H0 H H1); congr [&& _, _ & _];
  rewrite ?all_map; apply/eq_in_all => f Hf //=; rewrite mulrCA mulrA.
move=> H H0.
move: {H H0} (iff_trans H (and_iff_compat_l _ H0)) => H1.
apply: (equivP _ (iff_sym H1)) => {H1}; subst F1 F2.
rewrite /exists_conj_elim' /= QFLIA_conj_all !all_cat !all_map.
Opaque fs_leq0 fs_leq1 fs_mod0 fs_mod1.
apply/(iffP andP) => -[H0 H]; (split; first apply: H0);
  move: {H0} H; rewrite /bs /nilp !size_map -!/(nilp _) orbC; case: ifP => _.
- rewrite QFLIA_disj_has has_map => /hasP [i].
  rewrite mem_iota /= add0n exists_conj_elim_mod_correct /= => H H0. 
  by exists i; apply/allP => /= f /(allP H0) /=; rewrite addr0.
- rewrite QFLIA_conj_all => /all_allpairsP /= H lb ub.
  move=> /mapP [/= j Hj -> {lb}] /mapP [/= i Hi -> {ub}].
  move: (H i j Hi Hj); rewrite QFLIA_disj_has has_map => /hasP [/= k].
  rewrite mem_iota /= add0n exists_conj_elim_mod_correct => H0 /andP [H1 H2].
  exists (j.1 + (j.2^T *m I) 0 0 + k)%R; move: H1.
  rewrite -{1}(addr0 (j.1 + _)%R) lerD2l /=
          linearD linearN mulmxDl mulNmx mxE mxE  addrA
          2!(addrAC _ (- k%:Z)%R)  (addrAC _ (- j.1)%R) -2!addrA.
  rewrite  oppmxE  -2!opprD addrA subr_ge0 => -> /=.
  apply/allP => /= f; move/(allP H2); congr dvdz.
  by rewrite linearD /= mulmxDl mxE (addrAC j.1) !addrA addrAC.

- case=> x Hx; rewrite QFLIA_disj_has has_map; apply/hasP.
  exists `|x %% prod_mod|%Z => /=.
  + rewrite mem_iota /= add0n -ltz_nat gez0_abs; first exact: ltz_pmod.
    apply: modz_ge0; rewrite eqz_nat; exact: lt0n_neq0.
  + rewrite exists_conj_elim_mod_correct gez0_abs;
      last by apply: modz_ge0; rewrite eqz_nat; exact: lt0n_neq0.
    apply/allP => /= f Hf; move: (allP Hx _ Hf).
    rewrite addr0 !dvdzE'; congr eq_op; apply/eqP.
    rewrite eqz_mod_dvd !(addrC f.1.2) -!(addrA _ f.1.2)
            opprD addrA (addrAC x)  -addrA.
            
    rewrite -oppM -addrC  -addrA.
    set F2:= (Z in ( - _   + ( _ +Z) )%R).
    rewrite -/F2 addrC oppM3 opprI; last by [].
    rewrite addrC [Z in ( _ + (_ Z) )%R]addrC oppM -addrA addrC. 

    set xpm:= ((x %/ prod_mod)%Z * prod_mod)%R.
    have ->: (- x + xpm + (- f.1.2 - F2 + (F2 + x)) + f.1.2)%R = xpm;
     first by rewrite addrC  addrA addrC addrA 
         -2![(Z in ( Z + _)%R)]addrA [(Z in ( (_ + Z) + _)%R)]addrA
        [(- F2 + (F2 + _))%R]addrA addNr add0r  
        [(Z in (- _ + (Z ))%R)]addrC
        [(- _ + _)%R]addrA  addNr add0r
        addrA addrN add0r. 
    by rewrite /xpm mulrC; apply: dvdz_mulr; apply prod_mod_cm.

- move=> H; rewrite QFLIA_conj_all; apply/all_allpairsP => /= i j Hi Hj.
  case: {H} (H _ _ (map_f _ Hj) (map_f _ Hi)) => x /and3P [/= H H0 H1].
  rewrite QFLIA_disj_has has_map; apply/hasP.
  exists `|(x - (j.1 + (j.2^T *m I) 0%R 0%R))%R %% prod_mod|%Z;
    last (rewrite /= gez0_abs ?modz_ge0 // ?eqz_nat ?lt0n_neq0 //;
          apply/andP; split=> /=).
  + by rewrite mem_iota /= add0n -ltz_nat gez0_abs ?ltz_pmod //;
       apply: modz_ge0; rewrite eqz_nat; exact: lt0n_neq0.    
  + rewrite linearD linearN /= mulmxDl mulNmx mxE mxE.
    rewrite addrA 3!(addrAC _ (- _)%R) -2!addrA -!opprD. 
     rewrite oppM.

    set Z1:= (Z in (((_ - Z)%R %% _))%Z).
    set I2:= ((i.2^T *m I) 0 0)%R in H0 * .
    set J2:= ((j.2^T *m I) 0 0)%R in H *.
    set JJ:= ((- (j.2^T *m I)) 0 0)%R.
    have Z1J2: Z1 = (j.1 +  J2)%R. (* could have avoided this!!*)
      - rewrite /Z1 /J2. congr (_ + _)%R.
        by rewrite mxE.

    rewrite addrA.  
    have Hrew:  (i.1 + (- ((x - Z1) %% prod_mod)%Z - j.1) + I2 + JJ)%R
              = (i.1 + I2 - (j.1 + J2) - (((x - Z1) %% prod_mod)%Z))%R.
    -   apply subr0_eq; symmetry; rewrite !opprD !opprI //=. 
        set J2B:= (Z in ( _ + (_ + ((_ + (_  - Z)) + _)))%R).
        have -> : JJ = (- J2B)%R by rewrite /JJ /J2B 2!mxE.
        rewrite -/J2B.
        have <- : J2 = J2B by rewrite /J2 /J2B mxE.
        set TPM:= (((x + (- j.1 - J2)) %/ prod_mod)%Z * prod_mod)%R.
        set TL1:= (Z in ((Z + _) + _)%R).
        set TR1:= (Z in ( _ + (Z + _))%R).
        set TR2:= (Z in ( _ + (_ + Z))%R).
        rewrite addrC 2!addrA -[(_ + TL1)%R]addrA.
        have E1: (TR2+TL1)%R = (i.1  - j.1 )%R. 
            rewrite /TR2 /TL1.
            rewrite addrC addrA .  
            have ->:  (- x + (j.1 + J2) + TPM - j.1)%R = (- x + J2 + TPM)%R.
              rewrite -2!addrA. 
              have -> : (j.1 + J2 + (TPM - j.1))%R = (J2 + TPM)%R.
              rewrite addrC addrA addrC; congr (_ + _)%R. 
                + by rewrite -addrA addNr addr0.
                + by rewrite addrA.
            
            rewrite addrC;
            set TR4:= (i.1 + _ + _)%R;
            have -> :  TR4 = (i.1  - j.1 + TPM )%R; last by rewrite addrA addrK_N1.
            rewrite /TR4 addrA;
            set TR5:= (- x + _ + _)%R;
            set TR6:= (x - _ - _)%R;
            rewrite addr_opp2 -addrA; congr (_ + _)%R;
            rewrite  /TR6 addrA /TR5 addrC addrA  addrK_N3o.

            by rewrite addrA addr_opp2b.
              
      rewrite E1 /TR1.  
        set ZZ:=(Z in (_ = (Z + _) + _)%R).
        have -> : ZZ = (- I2 +  J2)%R.
          * rewrite /ZZ -2!addrA addrC -addrA /TR2 /TL1.
            replace (i.1 - j.1 - i.1)%R with (- j.1)%R.
            rewrite -addrA.
            by have ->: (j.1 + J2 - j.1)%R = J2 by rewrite addrC addrA addNr add0r.
            by rewrite -addrA addrC -addrA  addNr  addr0.
            
        by rewrite addrC [(-_ + _ + _)%R] addrC [(_ + (- _ + _))%R]addrA
            addrN add0r addNr.   

    rewrite Hrew Z1J2.
    
    have Hiv': (j.1 + J2 <= x <= i.1 + I2)%R by apply/andP; split. 
    case/andP : (itv_sepr Hiv') => Hiv1 Hiv2 .
    have Hmaj:=  ltz_pmod (x - (j.1 + J2))%R H_prodm . 
    rewrite subr_ge0.
    have Hlmod:= leq_modz H_prodm Hiv1. 
    by exact:le_trans Hlmod Hiv2. 
  
  +  rewrite exists_conj_elim_mod_correct;
      apply/allP => /= f Hf; move: (allP H1 _ Hf);
      rewrite !dvdzE'; congr eq_op; apply/eqP.
    rewrite addrAC linearD /= mulmxDl mxE addrA.

    set I2:= ((i.2^T *m I) 0 0)%R in H0 * .
    set J2:= ((j.2^T *m I) 0 0)%R in H *.
    set F2:=  ((f.2^T *m I) 0 0)%R.
    set F2':=  (Z in ( ( ((_ + Z) + _) %% _ )%Z == _)).
    have <-: F2 = F2' by rewrite /F2 /F2' mxE. clear F2'.
    set FJ2:= (Z in ( _ == ( ( _ + Z ) %% _ )%Z)).
    have -> : FJ2%R = (F2 + J2)%R by rewrite /F2 /J2 /FJ2 mxE. clear FJ2. 
    rewrite eqz_modDrX. rewrite 2!addrA.
    have ->: (f.1.2 + j.1 + (x - (j.1 + J2)))%R =   (f.1.2 + x -  J2)%R.
      by rewrite addrA addrC -addrA addrC addrA oppM addrA addrC
       -[(_ + _ + _ -_)%R]addrA [Z in ( _ +  j.1 + Z )%R]addrC -addrA addrC
        [(_ + (- _ + _))%R]addrA addrN add0r.

    set TMod :=(((x - (j.1 + J2)) %/ prod_mod)%Z * prod_mod)%R.
    have -> :  (f.1.2 + x - J2 - TMod + F2 + J2 - (f.1.2 + F2))%R = 
            (x -TMod )%R.

    set TR1:= (Z in  ((Z  )  + _ = _)%R).
    have -> : TR1 =  (f.1.2 + x - TMod + F2)%R
        by rewrite /TR1 -!addrA; apply add_eval;
           rewrite [(F2+J2)%R]addrC  addrK_N3o'.
    by rewrite addrC oppM -![(_ + _ - _ + _)%R]addrA  addrK_N2X addrC !addrA
       [RHS]addrC -!addrA -addr_opp2  addrN add0r.
     
    rewrite -eqz_modDrX -[Z in (_ == Z %[mod _])%Z]add0r  eqz_modDr 
            /TMod eqz_mod_dvd subr0. 
    exact :(dvdz_mull _ ( prod_mod_cm Hf)).
  Transparent fs_leq0 fs_leq1 fs_mod0 fs_mod1.
Qed.    

End QE_principle.

Definition exists_conj_elim dim (ls : seq (QFLIA_af dim.+1)) :
  QFLIA_formula dim :=
  exists_conj_elim'
    (pmap (fun l => match l with
                    | QFLIA_leq n t => Some (n, t)
                    | _ => None end) ls)
    (pmap (fun l => match l with
                    | QFLIA_divisible m n t => Some (m, n, t)
                    | _ => None end) ls).

Definition exists_DNF_elim dim (lss : seq (seq (QFLIA_af dim.+1))) :
  QFLIA_formula dim :=
  QFLIA_disj [seq exists_conj_elim ls | ls <- lss].

Lemma exists_DNF_elimP dim I (lss : seq (seq (QFLIA_af (1 + dim)))) :
  reflect (exists x,
             has (all (QFLIA_interpret_af (col_mx (const_mx x) I))) lss)
          (QFLIA_interpret_formula I (exists_DNF_elim lss)).
Proof.
rewrite /exists_DNF_elim QFLIA_disj_has; apply/(iffP hasP).
- case=> /= ls' /mapP [] /= ls H -> {ls'} /exists_conj_elimP [] x.
  rewrite all_cat !all_map !all_pmap -all_predI => H0.
  exists x; apply/hasP => /=; exists ls => //.
  by apply/allP => -[? ?|? ? ?] /(allP H0); rewrite //= andbT.
- case=> x /hasP [] /= ls H H0.
  exists (exists_conj_elim ls); first exact: map_f.
  apply/exists_conj_elimP; exists x.
  by rewrite all_cat !all_map !all_pmap -all_predI;
     apply/allP => l /(allP H0);
     case: l => //= n t; rewrite andbT.
Qed.

Fixpoint Presburger_algorithm dim (f : LIA_formula dim) : QFLIA_formula dim :=
  match f with
    | f_all f' =>
      QFLIA_neg
        (exists_DNF_elim (QFLIA_DNF (QFLIA_neg (Presburger_algorithm f'))))
    | f_exists f' =>
      exists_DNF_elim (QFLIA_DNF (Presburger_algorithm f'))
    | f_neg f' => QFLIA_neg (Presburger_algorithm f')
    | f_and f1 f2 =>
      QFLIA_and (Presburger_algorithm f1) (Presburger_algorithm f2)
    | f_or f1 f2 =>
      QFLIA_or (Presburger_algorithm f1) (Presburger_algorithm f2)
    | f_leq n t =>
      QFLIA_aformula (QFLIA_leq n t)
  end.

Lemma Presburger_algorithmP dim I (f : LIA_formula dim) :
  reflect (interpret_formula f I)
          (QFLIA_interpret_formula I (Presburger_algorithm f)).
Proof.
elim/LIA_formula_rect: dim / f I => /= dim.
- move=> f IH I; apply/(iffP idP).
  + move/exists_DNF_elimP => H x; apply/IH/negP => /negP.
    rewrite [~~_](QFLIA_NF_correctness false (col_mx (const_mx x) I)
                                       (QFLIA_neg (Presburger_algorithm f))).
    by move=> ?; apply: H; exists x.
  + move=> H; apply/negP => /exists_DNF_elimP [x].
    rewrite -[has _ _](QFLIA_NF_correctness
                         false (col_mx (const_mx x) I)
                         (QFLIA_neg (Presburger_algorithm f))).
    move=> /= /negP; apply; exact/IH.
- by move=> f IH I; apply/(iffP (exists_DNF_elimP _ _));
     move=> [x H]; exists x; move: H;
     rewrite /QFLIA_DNF -(QFLIA_NF_correctness false) => /IH.
- by move=> f IH I; apply/(iffP idP); move/IH.
- by move=> f1 IH1 f2 IH2 I; apply/(iffP andP); case=> /IH1 H /IH2 H0.
- move=> f1 IH1 f2 IH2 I; apply/(iffP orP)=> -[/IH1|/IH2]; tauto.
- move=> ? ? ?; exact/idP.
Qed.
