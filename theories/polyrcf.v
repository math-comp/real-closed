(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp
Require Import bigop order ssralg poly polydiv ssrnum zmodp.
From mathcomp
Require Import polyorder path interval ssrint.
Require Import table.

(****************************************************************************)
(* This files contains basic (and unformatted) theory for polynomials       *)
(* over a realclosed fields. From the IVT (contained in the rcfType         *)
(* structure), we derive Rolle's Theorem, the Mean Value Theorem, a root    *)
(* isolation procedure and the notion of neighborhood.                      *)
(*                                                                          *)
(*    sgp_minfty p == the sign of p in -oo                                  *)
(*    sgp_pinfty p == the sign of p in +oo                                  *)
(*  cauchy_bound p == the cauchy bound of p                                 *)
(*                    (this strictly bounds the norm of roots of p)         *)
(*     roots p a b == the ordered list of roots of p in  `[a, b]            *)
(*                    defaults to [::] when p == 0                          *)
(*        rootsR p == the ordered list of all roots of p, ([::] if p == 0). *)
(* next_root p x b == the smallest root of p contained in `[x, maxn x b]    *)
(*                    if p has no root on `[x, maxn x b], we pick maxn x b. *)
(* prev_root p x a == the smallest root of p contained in `[minn x a, x]    *)
(*                    if p has no root on `[minn x a, x], we pick minn x a. *)
(*   neighpr p a b := `]a, next_root p a b[.                                *)
(*                 == an open interval of the form `]a, x[, with x <= b     *)
(*                    in which p has no root.                               *)
(*   neighpl p a b := `]prev_root p a b, b[.                                *)
(*                 == an open interval of the form `]x, b[, with a <= x     *)
(*                    in which p has no root.                               *)
(*   sgp_right p a == the sign of p on the right of a.                      *)
(****************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory Num.Def Pdiv.Idomain.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope nat_scope.
Local Open Scope ring_scope.

Local Notation noroot p := (forall x, ~~ root p x).
Local Notation mid x y := ((x + y) / 2%:R).

(*************)
(* Intervals *)
(*************)
Section Intervals.
Variable R : numDomainType.

Definition convex (P : {pred R}) :=
  {in P &, forall x y, {subset `[x, y] <= P}}.

Lemma convex_interval (i : interval R) : convex (mem i).
Proof.
move=> x y xi yi z; apply: subitvP=> /=.
by case: i xi yi => [[[] ?|] [[] ?|]] /=; do ?move/itvP->.
Qed.

Lemma itvE3 (x y z : R) :
  (z \in `]x, y[ = (x <  z <  y)) *
  (z \in `[x, y[ = (x <= z <  y)) *
  (z \in `]x, y] = (x <  z <= y)) *
  (z \in `[x, y] = (x <= z <= y)).
Proof. by do !split; rewrite !inE//=. Qed.

Lemma itvE2 (x y : R) :
  (y \in `]x, +oo[ = (x <  y)) *
  (y \in `[x, +oo[ = (x <= y)) *
  (y \in `]-oo, x[ = (y <  x)) *
  (y \in `]-oo, x] = (x >= y)).
Proof. by do !split; rewrite !inE//= ?andbT. Qed.

Definition itvE := (itvE3, itvE2).

End Intervals.

(*************************************************************)
(* Definitions and properties for polynomials in a ringType. *)
(*************************************************************)
Section PolyRing.

Variable R : ringType.
Implicit Types (p q : {poly R}) (c : R).

Lemma lead_coef_MXaddC p c :
  lead_coef (p * 'X + c%:P) = if p == 0 then c else lead_coef p.
Proof.
have [->|p_neq0] := eqVneq; first by rewrite mul0r add0r lead_coefC.
rewrite lead_coefDl ?lead_coefMX// size_proper_mul; last first.
  by rewrite lead_coefX mulr1 lead_coef_eq0.
rewrite size_polyX size_polyC addn2 ltnS.
by rewrite (leq_trans (leq_b1 _)) ?size_poly_gt0.
Qed.

End PolyRing.

(******************************************************************)
(* Definitions and properties for polynomials in a numDomainType. *)
(******************************************************************)
Section PolyNumDomain.

Variable R : numDomainType.
Implicit Types (p q : {poly R}).

Definition sgp_pinfty (p : {poly R}) := sgr (lead_coef p).
Definition sgp_minfty (p : {poly R}) :=
  sgr ((-1) ^+ (size p).-1 * (lead_coef p)).

End PolyNumDomain.

(******************************************************************)
(* Definitions and properties for polynomials in a realFieldType. *)
(******************************************************************)
Section PolyRealField.

Variable R : realFieldType.
Implicit Types (p q : {poly R}).

Section SgpInfty.

Lemma sgp_pinfty_sym p : sgp_pinfty (p \Po -'X) = sgp_minfty p.
Proof.
rewrite /sgp_pinfty /sgp_minfty lead_coef_comp ?size_opp ?size_polyX //.
by rewrite lead_coef_opp lead_coefX mulrC.
Qed.

Lemma poly_pinfty_gt_lc p : lead_coef p > 0 ->
  exists A, forall x, x >= A -> p.[x] >= lead_coef p.
Proof.
elim/poly_ind: p => [|q c IHq]; first by rewrite lead_coef0 ltxx.
rewrite lead_coef_MXaddC; have [->|q_neq0] := eqVneq q 0.
  by rewrite mul0r add0r => c_gt0; exists 0 => x _; rewrite hornerC.
move=> lq_gt0; have [y Hy] := IHq lq_gt0.
pose z := 1 + (lead_coef q) ^-1 * `|c|; exists (maxr y z) => x.
have z_gt0 : 0 < z by rewrite ltr_spaddl ?ltr01 ?mulr_ge0 ?invr_ge0 // ltW.
rewrite !hornerE le_maxl => /andP[/Hy Hq Hc].
apply: le_trans (_ : lead_coef q * z + c <= _); last first.
  rewrite ler_add2r (le_trans (_ : _ <= q.[x] * z))// ?ler_pmul2r//.
  by rewrite ler_pmul2l // (lt_le_trans _ Hq).
rewrite mulrDr mulr1 -addrA ler_addl mulVKf ?gt_eqF //.
by rewrite -[c]opprK subr_ge0 normrN ler_norm.
Qed.

(* :REMARK: not necessary here ! *)
(* use near                      *)
Lemma poly_lim_infty p m :
    lead_coef p > 0 -> (size p > 1)%N ->
  exists n, forall x, x >= n -> p.[x] >= m.
Proof.
elim/poly_ind: p => [|q c _]; first by rewrite lead_coef0 ltxx.
rewrite lead_coef_MXaddC size_MXaddC.
case: eqVneq => [-> /gt_eqF->|q_neq0 lq_gt0 _]/=; first by rewrite size_poly0.
have [A q_ge] := poly_pinfty_gt_lc lq_gt0.
exists (maxr 0 (maxr A ((lead_coef q)^-1 * (m - c)))) => x.
rewrite !le_maxl => /and3P[x_ge0 x_geA].
rewrite ler_pdivr_mull// ?hornerE => xq_ge.
by rewrite -ler_subl_addr (le_trans xq_ge)// ?ler_wpmul2r// q_ge.
Qed.

End SgpInfty.

Section CauchyBound.


Definition cauchy_bound (p : {poly R}) :=
  1 + `|lead_coef p|^-1 * \sum_(i < size p) `|p`_i|.

(* Could be a sharp bound *)
Lemma cauchy_boundP (p : {poly R}) x :
  p != 0 -> p.[x] = 0 -> `| x | < cauchy_bound p.
Proof.
move=> np0 rpx; rewrite ltr_spaddl ?ltr01 //.
have sp_gt0 : (size p > 0)%N by rewrite size_poly_gt0.
have lcn0 : `|lead_coef p| != 0 by rewrite normr_eq0 lead_coef_eq0.
have lcp : `|lead_coef p| > 0 by rewrite lt_def lcn0 /=.
have [x_le1|x_gt1] := leP `|x| 1.
  rewrite (le_trans x_le1) // ler_pdivl_mull // mulr1.
  by rewrite polySpred// big_ord_recr/= ler_addr sumr_ge0.
have x_gt0 : `|x| > 0 by rewrite (lt_trans ltr01).
have [sp_le1|sp_gt1] := leqP (size p) 1.
  by move: rpx np0; rewrite [p]size1_polyC// hornerC polyC_eq0 => /eqP->.
rewrite ler_pdivl_mull//.
pose n := (size p).-1; have n_gt0 : (n > 0)%N by rewrite /n -subn1 subn_gt0.
have : `|p`_n| * `|x| ^+ n <= \sum_(i < n) `|p`_i * x ^+ i|.
  rewrite (le_trans _ (ler_norm_sum _ _ _))//.
  have := rpx; rewrite horner_coef polySpred// !big_ord_recr/=.
  by move=> /(canRL (@addrK _ _))->; rewrite sub0r normrN normrM normrX.
rewrite -[n in _ ^+ n]prednK// exprS mulrA.
rewrite -[X in _ X -> _]ler_pdivl_mulr ?exprn_gt0// => /le_trans->//.
rewrite polySpred// big_ord_recr/= ler_paddr// mulr_suml ler_sum => //i _.
rewrite normrM normrX ler_pdivr_mulr ?exprn_gt0// ler_pmul ?exprn_ge0//.
by rewrite ler_weexpn2l// 1?ltW// -ltnS prednK//.
Qed.

Lemma root_in_cauchy_bound (p : {poly R}) : p != 0 ->
  {subset root p <= `](- cauchy_bound p), (cauchy_bound p)[ }.
Proof. by move=> p_neq0 x /eqP /(cauchy_boundP p_neq0); rewrite ltr_norml. Qed.

Definition root_cauchy_boundP (p : {poly R}) pN0 x (rpx : root p x) :=
 itvP (root_in_cauchy_bound pN0 rpx).

Lemma le_cauchy_bound p : p != 0 -> {in `]-oo, (- cauchy_bound p)], noroot p}.
Proof.
move=> p_neq0 x; rewrite inE /= leNgt; apply: contra => /rootP.
by move=> /(cauchy_boundP p_neq0) /ltr_normlP []; rewrite ltr_oppl.
Qed.
Hint Resolve le_cauchy_bound.

Lemma ge_cauchy_bound p : p != 0 -> {in `[cauchy_bound p, +oo[, noroot p}.
Proof.
move=> p_neq0 x; rewrite inE andbT /= leNgt; apply: contra => /rootP.
by move=> /(cauchy_boundP p_neq0) /ltr_normlP []; rewrite ltr_oppl.
Qed.
Hint Resolve ge_cauchy_bound.

Lemma cauchy_bound_gt0 p : cauchy_bound p > 0.
Proof.
rewrite ltr_spaddl ?ltr01 ?mulr_ge0 ?invr_ge0 ?normr_ge0 //.
by rewrite sumr_ge0 // => i; rewrite normr_ge0.
Qed.
Hint Resolve cauchy_bound_gt0.

Lemma cauchy_bound_ge0 p : cauchy_bound p >= 0.
Proof. by rewrite ltW. Qed.
Hint Resolve cauchy_bound_ge0.

Lemma cauchy_bound_neq0 p : cauchy_bound p != 0.
Proof. by rewrite gt_eqF. Qed.
Hint Resolve cauchy_bound_neq0.

End CauchyBound.

End PolyRealField.
Hint Resolve le_cauchy_bound ge_cauchy_bound cauchy_bound_gt0 cauchy_bound_ge0.
Hint Resolve cauchy_bound_neq0.

(************************************************************)
(* Definitions and properties for polynomials in a rcfType. *)
(************************************************************)
Section PolyRCF.

Variable R : rcfType.

Section Prelim.

Implicit Types a b c : R.
Implicit Types x y z t : R.
Implicit Types p q r : {poly R}.

Section FixedSegment.

Variables (a b : R).
Variable (p : {poly R}).

(* we restate poly_ivt in a nicer way. Perhaps the def of PolyRCF should *)
(* be moved in this file, juste above this section                       *)
Definition poly_ivtW := poly_ivt.

Lemma poly_ivtP : a <= b -> p.[a] * p.[b] <= 0 ->
   exists2 x, x \in `[a, b] & root p x.
Proof.
move=> le_ab sgp; have []//= := @poly_ivt _ (p.[b] *: p) a b.
  by rewrite !hornerZ sqr_ge0 mulrC sgp.
move=> x axb; have [|?] := boolP (root p b); last by rewrite rootZ //; exists x.
by move=> rpb; exists b; rewrite // inE/= lexx andbT.
Qed.

Definition iroot :=
  if (a <= b) && (p.[a] * p.[b] <= 0) =P true isn't ReflectT pp then a
  else projT1 (sig2W (poly_ivtP (proj1 (andP pp)) (proj2 (andP pp)))).

Definition some_iroot := if root p iroot then Some iroot else None.

Variable (le_ab : a <= b).

Lemma irootK : root p iroot = (p.[a] * p.[b] <= 0).
Proof.
rewrite /iroot; case: eqP => [ab_pab|].
  by case: sig2W => //= x _ ->; case/andP: ab_pab => _ ->.
rewrite le_ab/= /root => /negP; case: eqP => // [->|_/negPf->//].
by rewrite mul0r lexx.
Qed.

Lemma iroot_inf : ~~ root p iroot -> iroot = a.
Proof.
rewrite irootK /iroot => Npab.
have : ~~ ((a <= b) && (p.[a] * p.[b] <= 0)) by rewrite negb_and Npab orbT.
by case: eqP => //= pab; rewrite {1}pab.
Qed.

Lemma iroot_in : iroot \in `[a, b].
Proof.
rewrite /iroot; case: eqP => ?; rewrite ?inE/= ?lexx ?le_ab//.
by case: sig2W.
Qed.

Lemma horner_iroot : p.[a] * p.[b] <= 0 -> p.[iroot] = 0.
Proof. by rewrite -irootK => /eqP. Qed.

Lemma iroot_inW : p.[a] * p.[b] < 0 -> iroot \in `]a, b[.
Proof.
rewrite lt_neqAle => /andP[pabN0 /horner_iroot] pi0.
have := iroot_in; rewrite !inE/= !lt_neqAle/=.
move=> /andP [-> ->]; rewrite !andbT eq_sym -negb_or.
by apply: contraNN pabN0 => /orP[] /eqP<-; rewrite pi0 (mul0r, mulr0) eqxx.
Qed.

Lemma le_iroot : a <= iroot. Proof. by rewrite (itvP iroot_in). Qed.
Lemma ge_iroot : iroot <= b. Proof. by rewrite (itvP iroot_in). Qed.

Lemma lt_iroot : p.[a] * p.[b] < 0 -> a < iroot.
Proof. by move=> /iroot_inW/itvP->. Qed.

Lemma gt_iroot : p.[a] * p.[b] < 0 -> iroot < b.
Proof. by move=> /iroot_inW/itvP->. Qed.

Lemma root_ivtW : p.[a] * p.[b] < 0 -> root p (iroot).
Proof. by rewrite irootK => /ltW. Qed.

Lemma hornerWiroot : p.[a] * p.[b] < 0 -> p.[iroot] = 0.
Proof. by move=> /root_ivtW/eqP. Qed.

Lemma poly_ivtPW : p.[a] * p.[b] < 0 -> exists2 x, x \in `]a, b[ & root p x.
Proof. by move=> pab; exists iroot; rewrite ?irootK ?ltW// iroot_inW. Qed.

Lemma some_irootE : some_iroot = if root p iroot then Some iroot else None.
Proof. by []. Qed.

Lemma some_eq_iroot x : some x = some_iroot <-> x = iroot /\ root p x.
Proof.
by rewrite some_irootE; split; case: ifP => rp; do 1?move=> [->]; rewrite ?rp.
Qed.

Lemma none_eq_iroot x : None = some_iroot <-> a = iroot /\ ~~ root p a.
Proof.
rewrite some_irootE; split; case: ifP => // nrp.
  by rewrite -?iroot_inf ?nrp.
by move=> [->]; rewrite nrp.
Qed.

End FixedSegment.

Lemma mulr_gt0_sg x y : x * y != 0 -> (x * y > 0) = (sgr x == sgr y).
Proof.
by rewrite !sgrEz (inj_eq intr_inj) -sgz_eq0 -sgz_gt0 sgzM; do 2!case: sgzP.
Qed.

Lemma mulr_ge0_sg x y : x * y != 0 -> (x * y >= 0) = (sgr x == sgr y).
Proof.
by rewrite !sgrEz (inj_eq intr_inj) -sgz_eq0 -sgz_ge0 sgzM; do 2!case: sgzP.
Qed.

Lemma mulr_lt0_sg x y : x * y != 0 -> (x * y < 0) = (sgr x != sgr y).
Proof.
by rewrite !sgrEz (inj_eq intr_inj) -sgz_eq0 -sgz_lt0 sgzM; do 2!case: sgzP.
Qed.

Lemma mulr_le0_sg x y : x * y != 0 -> (x * y <= 0) = (sgr x != sgr y).
Proof.
by rewrite !sgrEz (inj_eq intr_inj) -sgz_eq0 -sgz_le0 sgzM; do 2!case: sgzP.
Qed.

Lemma polyrN0_itv (i : interval R) (p : {poly R}) : {in i, noroot p} ->
  {in i &, forall y x : R, sgr p.[x] = sgr p.[y]}.
Proof.
move=> hi y x hy hx; wlog xy: x y hx hy / x <= y => [hwlog|].
  by case/orP: (le_total x y)=> xy; [|symmetry]; apply: hwlog.
apply/eqP; rewrite -mulr_gt0_sg ?mulf_neq0 ?hi//.
by rewrite ltNge -irootK// hi// (convex_interval hx hy)// iroot_in.
Qed.

Lemma nth_root x n : x > 0 -> { y | y > 0 & y ^+ (n.+1) = x }.
Proof.
move=> x_gt0; pose p := ('X ^+ n.+1 - x%:P); apply/sig2_eqW.
have xS_ge1: x + 1 >= 1 by rewrite ler_paddl// ltW.
have [] := @poly_ivtPW 0 (x + 1) p; first by rewrite (le_trans ler01).
  rewrite !(hornerE, horner_exp) expr0n /= sub0r nmulr_rlt0 ?oppr_lt0//.
  by rewrite subr_gt0 (lt_le_trans _ (ler_eexpr _ _)) // ltr_spaddr ?ltr01.
move=> c; rewrite !inE/= => /andP[c_gt0 _ rpc]; exists c => //.
by move: rpc; rewrite rootE !(hornerE, horner_exp) subr_eq0 => /eqP.
Qed.

Lemma poly_ltsp_roots p (rs : seq R) :
  (size rs >= size p)%N -> uniq rs -> all (root p) rs -> p = 0.
Proof.
move=> hrs urs rrs; apply/eqP; apply: contraLR hrs=> np0.
by rewrite -ltnNge; apply: max_poly_roots.
Qed.

Theorem poly_rolle a b p :
  a < b -> p.[a] = p.[b] -> {c | c \in `]a, b[ & p^`().[c] = 0}.
Proof.
gen have rolle_weak : a b p / a < b -> p.[a] = 0 -> p.[b] = 0 ->
   {c | (c \in `]a, b[) & (p^`().[c] == 0) || (p.[c] == 0)}.
  move=> lab pa0 pb0; have leab := ltW lab; apply/sig2W.
  have [->|p_neq0] := eqVneq p 0.
    by exists (mid a b); rewrite ?mid_in_itv// derivC horner0 eqxx.
  have [n [p' p'a0 hp]] := multiplicity_XsubC p a; rewrite p_neq0 /= in p'a0.
  case: n hp pa0 p_neq0 pb0 p'a0 => [ | n -> _ p0 pb0 p'a0].
    by rewrite {1}expr0 mulr1 rootE=> ->; move/eqP->.
  have [m [q qb0 hp']] := multiplicity_XsubC p' b.
  rewrite (contraNneq _ p'a0) /= in qb0 => [|->]; last exact: root0.
  case: m hp' pb0 p0 p'a0 qb0=> [|m].
    rewrite {1}expr0 mulr1=> ->; move/eqP.
    rewrite !(hornerE, horner_exp, mulf_eq0).
    by rewrite !expf_eq0 !subr_eq0 !(gt_eqF lab) !andbF !orbF !rootE=> ->.
  move=> -> _ p0 p'a0 qb0; case: (sgrP (q.[a] * q.[b])); first 2 last.
  - case/(poly_ivtPW leab)=> c c_in /eqP qc0; exists c => //.
    by rewrite !hornerM qc0 !mul0r eqxx orbT.
  - move/eqP; rewrite mulf_eq0 (rootPf qb0) orbF; move/eqP=> qa0.
    by move: p'a0; rewrite ?rootM rootE qa0 eqxx.
  move=> hspq; rewrite !derivCE /= !mul1r mulrDl !pmulrn.
  set xan := (('X - a%:P) ^+ n); set xbm := (('X - b%:P) ^+ m).
  have ->: ('X - a%:P) ^+ n.+1 = ('X - a%:P) * xan by rewrite exprS.
  have ->: ('X - b%:P) ^+ m.+1 = ('X - b%:P) * xbm by rewrite exprS.
  rewrite -mulrzl -[_ *~ n.+1]mulrzl.
  have fac : forall x y z : {poly R}, x * (y * xbm) * (z * xan)
    = (y * z * x) * (xbm * xan).
    by move=> x y z; rewrite mulrCA !mulrA [_ * y]mulrC mulrA.
  rewrite !fac -!mulrDl; set r := _ + _ + _.
  have [|c c_in] := @poly_ivtPW a b (sgr q.[b] *: r) leab.
    rewrite !hornerZ mulrACA -expr2 sqr_sg (rootPf qb0) mul1r.
    rewrite !(subrr, mul0r, mulr0, addr0, add0r, hornerC, hornerXsubC,
      hornerD, hornerN, hornerM, hornerMn) [_ * _%:R]mulrC.
    rewrite mulrACA pmulr_llt0 // mulrACA pmulr_rlt0 ?mulr_gt0 ?ltr0n //.
    by rewrite -opprB mulNr oppr_lt0 mulr_gt0 ?subr_gt0.
  rewrite rootE hornerZ mulf_eq0 sgr_cp0 (rootPf qb0) orFb => rc0.
  by exists c => //; rewrite !hornerM !mulf_eq0 rc0.
move=> lab pab; wlog pb0 : p pab / p.[b] = 0 => [hwlog|].
  case: (hwlog (p - p.[b]%:P)); rewrite ?hornerE ?pab ?subrr //.
  by move=> c acb; rewrite derivE derivC subr0=> hc; exists c.
move: pab; rewrite pb0=> pa0.
have: (forall rs : seq R, {subset rs <= `]a, b[} ->
    (size p <= size rs)%N -> uniq rs -> all (root p) rs -> p = 0).
  by move=> rs hrs; apply: poly_ltsp_roots.
elim: (size p) a b lab pa0 pb0=> [|n ihn] a b lab pa0 pb0 max_roots.
  rewrite (@max_roots [::]) //=.
  by exists (mid a b); rewrite ?mid_in_itv // derivE horner0.
case: (@rolle_weak a b p); rewrite // ?pa0 ?pb0 //=.
move=> c hc; case: (altP (_ =P 0))=> //= p'c0 pc0; first by exists c.
suff: { d : R | d \in `]a, c[ & (p^`()).[d] = 0 }.
  case=> [d hd] p'd0; exists d=> //.
  by apply: subitvPr hd; rewrite //= (itvP hc).
apply: ihn=> //; [by rewrite (itvP hc)|exact/eqP|].
move=> rs hrs srs urs rrs; apply: (max_roots (c :: rs))=> //=; last exact/andP.
  move=> x; rewrite in_cons; case/predU1P=> hx; first by rewrite hx.
  have: x \in `]a, c[ by apply: hrs.
  by apply: subitvPr; rewrite /= (itvP hc).
by rewrite urs andbT; apply/negP => /hrs; rewrite bound_in_itv.
Qed.

Theorem poly_mvt a b p : a < b ->
  exists2 c, c \in `]a, b[ & p.[b] - p.[a] = p^`().[c] * (b - a).
Proof.
pose q := (p.[b] - p.[a])%:P * ('X - a%:P) - (b - a)%:P * (p - p.[a]%:P).
move=> lt_ab; have [//||c le_acb q'x0] := @poly_rolle a b q.
  by rewrite /q !hornerE !(subrr,mulr0) mulrC subrr.
exists c=> //; move: q'x0; rewrite /q !derivE !(mul0r,add0r,subr0,mulr1).
by move/eqP; rewrite !hornerE mulrC subr_eq0; move/eqP.
Qed.

Lemma poly_lipshitz p a b :
  { k | k >= 1 & {in `[a, b] &, forall x y, `|p.[y] - p.[x]| <= k * `|y - x| }}.
Proof.
have [ub p_le] := @poly_itv_bound _ p^`() a b; exists (1 + `|ub|).
  by rewrite ler_addl.
move=> x y xi yi; wlog lt_xy : x y xi yi / x < y => [hw|].
  set d := `|y - _|; have [/hw->//|xy|xy//] := ltrgtP x y; last first.
    by rewrite /d xy !subrr normr0 mulr0.
  by rewrite /d (distrC y) (distrC p.[y]) hw.
have [c ci ->] := poly_mvt p lt_xy.
rewrite normrM ler_pmul2r ?p_le // ?normr_gt0 ?subr_eq0 ?gt_eqF//.
rewrite ler_paddl // (le_trans _ (ler_norm _)) // p_le //.
by have: c \in `[a, b] by apply: subitvP ci; rewrite /= ?(itvP xi, itvP yi).
Qed.

Lemma poly_cont x p e : e > 0 ->
  { d | d > 0 & forall y, `|y - x| < d -> `|p.[y] - p.[x]| < e }.
Proof.
move=> e_gt0; have [k k_ge1 kP] := poly_lipshitz p (x - e) (x + e).
have k_gt0 : k > 0 by rewrite (lt_le_trans ltr01).
exists (e / k) => [|y]; first by rewrite mulr_gt0 ?invr_gt0.
have [y_small|y_big] := lerP `|y - x| e.
  rewrite ltr_pdivl_mulr // mulrC; apply/le_lt_trans/kP => //;
  by rewrite -![_ \in _]ler_distl ?subrr ?normr0 // ?ltW.
by move=> /(lt_trans y_big); rewrite ltr_pmulr // invf_gt1 // le_gtF.
Qed.

Lemma ler_hornerW a b p : (forall x, x \in `]a, b[ -> p^`().[x] >= 0) ->
  {in `[a, b] &, {homo horner p : x y / x <= y}}.
Proof.
move=> der_nneg x y axb ayb; rewrite le_eqVlt => /orP[/eqP->//|ltxy].
have [c xcy /(canRL (@subrK _ _))->]:= poly_mvt p ltxy.
rewrite ler_addr mulr_ge0 ?subr_ge0 ?(ltW ltxy) ?der_nneg //.
by apply: subitvP xcy; rewrite /= (itvP axb) (itvP ayb).
Qed.

End Prelim.

Section MonotonictyAndRoots.

Section DerPos.

Variable (p : {poly R}).

Variables (a b : R).

Hypothesis der_gt0 : forall x, x \in `]a, b[ -> (p^`()).[x] > 0.

Lemma ltr_hornerW : {in `[a, b] &, {homo horner p : x y / x < y}}.
Proof.
move=> x y axb ayb ltxy; have [c xcy /(canRL (@subrK _ _))->]:= poly_mvt p ltxy.
rewrite ltr_addr mulr_gt0 ?subr_gt0 ?der_gt0 //.
by apply: subitvP xcy; rewrite /= (itvP axb) (itvP ayb).
Qed.

Lemma ler_horner : {in `[a, b] &, {mono horner p : x y / x <= y}}.
Proof. exact/le_mono_in/ltr_hornerW. Qed.

Lemma ltr_horner : {in `[a, b] &, {mono horner p : x y / x < y}}.
Proof. exact/leW_mono_in/ler_horner. Qed.

Lemma derp_inj : {in `[a, b] &, injective (horner p)}.
Proof. exact/inc_inj_in/ler_horner. Qed.

Lemma derpr x : x \in `]a, b] -> p.[x] > p.[a].
Proof.
by move=> axb; rewrite ltr_horner ?(itvP axb) //; apply: subitvPl axb => /=.
Qed.

Lemma derpl x : x \in `[a, b[ -> p.[x] < p.[b].
Proof.
by move=> axb; rewrite ltr_horner ?(itvP axb) //; apply: subitvPr axb => /=.
Qed.

Lemma derprW x : x \in `[a, b] -> p.[x] >= p.[a].
Proof. by move=> axb; rewrite ler_horner ?(itvP axb). Qed.

Lemma derplW x : x \in `[a, b] -> p.[x] <= p.[b].
Proof. by move=> axb; rewrite ler_horner ?(itvP axb). Qed.

End DerPos.

Section DerNeg.

Variable (p : {poly R}).

Variables (a b : R).

Hypothesis der_neg : forall x, x \in `]a, b[ -> (p^`()).[x] < 0.
Let dern_gt0 x : x \in `]a, b[ -> ((- p)^`()).[x] > 0.
Proof. by move=> axb; rewrite derivN hornerN oppr_gt0 der_neg. Qed.

Lemma gtr_hornerW : {in `[a, b] &, {homo horner p : x y /~ x < y}}.
Proof.
by move=> x y axb ayb yx; rewrite -ltr_opp2 -!hornerN (ltr_hornerW dern_gt0).
Qed.

Lemma ger_horner : {in `[a, b] &, {mono horner p : x y /~ x <= y}}.
Proof. exact/le_nmono_in/gtr_hornerW. Qed.

Lemma gtr_horner : {in `[a, b] &, {mono horner p : x y /~ x < y}}.
Proof. exact/leW_nmono_in/ger_horner. Qed.

Lemma dern_inj : {in `[a, b] &, injective (horner p)}.
Proof. exact/dec_inj_in/ger_horner. Qed.

Lemma dernr x : x \in `]a, b] -> p.[x] < p.[a].
Proof.
by move=> axb; rewrite gtr_horner ?(itvP axb) //; apply: subitvPl axb => /=.
Qed.

Lemma dernl x : x \in `[a, b[ -> p.[x] > p.[b].
Proof.
by move=> axb; rewrite gtr_horner ?(itvP axb) //; apply: subitvPr axb => /=.
Qed.

Lemma dernrW x : x \in `[a, b] -> p.[x] <= p.[a].
Proof. by move=> axb; rewrite ger_horner ?(itvP axb). Qed.

Lemma dernlW x : x \in `[a, b] -> p.[x] >= p.[b].
Proof. by move=> axb; rewrite ger_horner ?(itvP axb). Qed.

End DerNeg.

Section NoRoot_sg.

Variable (p : {poly R}).

Variables (a b c : R).

Hypothesis lt_ab : a < b.
Hypothesis derp_neq0 : {in `]a, b[, noroot p^`()}.
Let mid_in : mid a b \in `]a, b[. Proof. exact: mid_in_itv. Qed.
Hint Resolve mid_in.

Local Notation s := (p^`().[mid a b] < 0).
Local Notation sp' := ((- 1) ^+ s).
Let q := (sp' *: p).

Lemma sgr_sign : sgr ((-1) ^+ s) = (-1) ^+ s :> R.
Proof. by case: s; rewrite ?(sgr1, sgrN1). Qed.

Fact signpE : p = (sp' *: q).
Proof. by rewrite scalerA [_ ^+ _ * _]sqrr_sign scale1r. Qed.

Fact sgp x : sgr p.[x] = sp' * sgr q.[x].
Proof. by rewrite {1}signpE hornerZ sgrM sgr_sign. Qed.

Fact derq_gt0 x : x \in `]a, b[ -> (q^`()).[x] > 0.
Proof.
move=> hx; rewrite derivZ hornerZ -sgr_cp0 neqr0_sign ?(derp_neq0 _) //.
rewrite sgrM sgr_id mulr_sg_eq1 ?derp_neq0 //=.
by apply/eqP; apply: (@polyrN0_itv `]a, b[).
Qed.
Hint Resolve derq_gt0.

Lemma lgtr_horner : {in `[a, b] &, forall x y,
  p.[x] < p.[y] = (sp' * x < sp' * y)}.
Proof.
move=> x y axb ayb; rewrite /= [in LHS]signpE ![(_ *: q).[_]]hornerZ.
by case: s; rewrite ?mul1r ?mulN1r ?ltr_opp2 (ltr_horner derq_gt0).
Qed.

Lemma lger_horner : {in `[a, b] &, forall x y,
  p.[x] <= p.[y] = (sp' * x <= sp' * y)}.
Proof.
move=> x y axb ayb; rewrite /= [in LHS]signpE ![(_ *: q).[_]]hornerZ.
by case: s; rewrite ?mul1r ?mulN1r ?ler_opp2 (ler_horner derq_gt0).
Qed.

Lemma horner_inj : {in `[a, b] &, injective (horner p)}.
Proof.
move=> x y xab yab; rewrite signpE ![(_ *: q).[_]]hornerE.
by move=> /mulfI /(derp_inj derq_gt0)-> //; rewrite signr_eq0.
Qed.

Lemma uniq_root : {in `[a, b] &, forall x y, root p x -> root p y -> x = y}.
Proof. by move=> x y ?? /eqP? /eqP rpy; apply: horner_inj; rewrite //rpy. Qed.

Lemma sgrB (x y : R) : sgr (x - y) = (- 1) ^+ (x < y)%R *+ (x != y).
Proof.
have [xy|xy|->] := ltrgtP y x; last by rewrite subrr sgr0.
  by rewrite gtr0_sg ?subr_gt0.
by rewrite ltr0_sg ?subr_lt0.
Qed.

Lemma root_sgp : {in `[a, b] &, forall x y, root p x ->
  sgr p.[y] = (- 1) ^+ s * sgr (y - x)}.
Proof.
move=> x y xab yab rpx; rewrite {1}signpE hornerZ sgrM sgr_sign; congr (_ * _).
have rqx : root q x by rewrite /root hornerZ mulf_eq0 [p.[_] == _]rpx orbT.
rewrite sgrB; have [xy|xy|<-]/= := ltrgtP x y; last first.
- by rewrite hornerZ sgrM (eqP rpx) sgr0 mulr0.
- by apply/eqP; rewrite sgr_cp0 -(eqP rqx) (ltr_horner derq_gt0).
- by apply/eqP; rewrite sgr_cp0 -(eqP rqx) (ltr_horner derq_gt0).
Qed.

Lemma root_has_ivt r : r \in `[a, b] -> root p r ->
  {in `[a, r] & `[r, b], forall x y, p.[x] * p.[y] <= 0}.
Proof.
move=> rab rpr x y xar yrb; rewrite -sgr_le0 sgrM.
have xab : x \in `[a, b] by apply: subitvP xar; rewrite /= lexx ?(itvP rab).
have yab : y \in `[a, b] by apply: subitvP yrb; rewrite /= lexx ?(itvP rab).
rewrite ?(root_sgp _ _ rpr)// mulrACA [_ ^+ _ * _]sqrr_sign mul1r -sgrM sgr_le0.
by rewrite mulr_le0_ge0 ?subr_ge0 ?subr_le0 ?(itvP xar) ?(itvP yrb).
Qed.

Lemma noroot_noivt : {in `[a, b], forall r, ~~ root p r} ->
  {in `[a, b] &, forall x y, p.[x] * p.[y] > 0}.
Proof.
move=> rpr x y xar yrb; wlog xy : x y xar yrb / x <= y => [hw|].
  by have /orP[/hw->//|/hw] := le_total x y; rewrite mulrC; apply.
rewrite ltNge -irootK ?rpr//; apply: subitvP (iroot_in p xy).
by rewrite /= ?(itvP xar) ?(itvP yrb).
Qed.

Fact gtr0_sgp x : 0 < q.[x] -> sgr p.[x] = sp'.
Proof. by move=> qx_gt0; rewrite sgp gtr0_sg ?mulr1. Qed.

Fact ltr0_sgpN x : q.[x] < 0 -> sgr p.[x] = - sp'.
Proof. by move=> qx_gt0; rewrite sgp ltr0_sg ?mulrN1. Qed.

Lemma root_dersr : p.[a] = 0 -> {in `]a, b], forall x, sgr p.[x] = sp'}.
Proof.
move=> pa0 x xab; have qa0 : q.[a] = 0 by rewrite hornerE pa0 mulr0.
by rewrite gtr0_sgp// -qa0 (derpr derq_gt0).
Qed.

Lemma derspr : sgr p.[a] = sp' -> {in `[a, b], forall x, sgr p.[x] = sp'}.
Proof.
move=> pa_sp' x xab; rewrite gtr0_sgp// (lt_le_trans _ (derprW derq_gt0 _))//.
by rewrite hornerE -sgr_cp0 sgrM sgr_sign pa_sp' [_ * _]sqrr_sign.
Qed.

Lemma root_dersl : p.[b] = 0 -> {in `[a, b[, forall x, sgr p.[x] = - sp'}.
Proof.
move=> pb0 x xab; have qb0 : q.[b] = 0 by rewrite hornerE pb0 mulr0.
by rewrite ltr0_sgpN// -qb0 (derpl derq_gt0).
Qed.

Lemma derspl : sgr p.[b] = - sp' -> forall x, x \in `[a, b] -> sgr p.[x] = - sp'.
Proof.
move=> pbNsp' x xab; rewrite ltr0_sgpN// (le_lt_trans (derplW derq_gt0 _))//.
by rewrite hornerE -sgr_cp0 sgrM sgr_sign pbNsp' mulrN [_ * _]sqrr_sign.
Qed.

Lemma eq_iroot : {in `[a, b], {in root p, all_equal_to (iroot a b p)}}.
Proof.
move=> x xab rpx; apply: uniq_root; rewrite ?iroot_in 1?ltW //.
by rewrite irootK ?(ltW lt_ab)// (root_has_ivt _ rpx) ?inE/= ?(itvP xab, lexx).
Qed.

End NoRoot_sg.

Notation edfltN c := (edflt (- c)%R c%R).

Lemma roots_subproof (p : {poly R}) : p != 0 -> {rs : seq R | mem rs =1 root p}.
Proof.
elim: (size p) {-2}p (eqxx (size p)) => [|[|sp] ihsp] {p}p.
- by rewrite size_poly_eq0 => ->.
- by move=> /size_poly1P/sig2_eqW[c /negPf?->]; exists [::] => x; rewrite rootC.
move=> /eqP eq_sp p_neq0; have [||rs' rs'P {ihsp}] := ihsp p^`();
  do ?by rewrite -?size_poly_eq0 ?size_deriv ?eq_sp ?eqxx.
wlog /andP [rs'uniq rs'sorted] : rs' rs'P / uniq rs' && sorted <=%R rs' => [hw|].
  apply: (hw (sort <=%R (undup rs'))) => [x /=|].
    by rewrite mem_sort mem_undup -rs'P.
 by rewrite sort_sorted ?sort_uniq ?undup_uniq //; apply: le_total.
have p'neq0 : p^`() != 0 by rewrite -size_poly_eq0 size_deriv eq_sp.
pose cp  := maxr (cauchy_bound p) (cauchy_bound p^`()).
pose cpi := `](- cp), cp[.
have cp0 : 0 \in cpi by rewrite itvE oppr_lt0 lt_maxr ?cauchy_bound_gt0.
have rscpi  : {subset rs' <= cpi}.
  move=> x; rewrite [_ \in _]rs'P => /(root_in_cauchy_bound p'neq0) /=.
  by apply: subitvP; rewrite /= ler_opp2 andbb le_maxr lexx orbT.
pose rs'_ i := edfltN cp rs'`[i].
exists (pmap (fun i => some_iroot (rs'_ i) (rs'_ i.+1) p)
   (iota 0 (locked succn (size rs')))) => x /=.
rewrite mem_pmap; apply/mapP/idP => [[i i_in /some_eq_iroot[]//]|rpx].
have xcpoo : x \in cpi.
  apply: subitvP (root_in_cauchy_bound p_neq0 _) => //=.
  by rewrite ler_opp2 andbb le_maxr lexx.
exists (rindex rs' x); first by rewrite mem_iota add0n -lock/= ltnS.
have rprev_cp : edflt1 0 (rprev rs' x) \in cpi.
  have := map_f (edflt1 0) (in_rprev rs' x).
  by rewrite /= inE => /predU1P[->//|]; rewrite -map_comp /= map_id => /rscpi.
have rnext_cp : edflt1 0 (rnext rs' x) \in cpi.
  have := map_f (edflt1 0) (in_rnext rs' x); rewrite /= inE => /predU1P[->//|].
  by rewrite -map_comp /= map_id => /rscpi.
apply/some_eq_iroot; split => //; apply: eq_iroot => //; last 1 first.
- by rewrite !inE/= /rs'_ !(ge_edflt, le_edflt, itvP xcpoo)// ge_rprev le_rnext.
- by rewrite /rs'_ (@lt_edflt2 _ _ 0) ?(itvP cp0).
move=> y y_rs; have y_cp : y \in cpi.
  apply: subitvP y_rs; rewrite //= /rs'_.
  by rewrite !(@edflt_ge_inf _ _ 0, @edflt_le_sup _ _ 0);
     rewrite ?(itvP cp0, itvP rprev_cp, itvP rnext_cp).
rewrite -rs'P /= (@rindex_notin _ _ _ _ (rindex rs' x))// !inE/=.
by rewrite -!(@lt_edflt2 _ _ 0 (- cp) cp) ?(itvP cp0).
Qed.

Definition roots p := if (p != 0) =P true isn't ReflectT p_gt0 then [::]
                      else sort <=%R (undup (projT1 (roots_subproof p_gt0))).

Lemma roots0 : roots 0 = [::].
Proof. by rewrite /roots; case: eqP => // p; move: {-1}p; rewrite eqxx. Qed.

Lemma rootsE p : p != 0 -> forall x, x \in roots p = root p x.
Proof.
rewrite /roots; case: eqP => //= p0 _ x.
by case: roots_subproof => //= s /(_ x) /= <-; rewrite mem_sort mem_undup.
Qed.

Lemma horner_roots p x : x \in roots p -> p.[x] = 0.
Proof. by have [->|/rootsE->] := eqVneq p 0; rewrite ?horner0// => /eqP. Qed.

Lemma roots_le_sorted p : sorted <=%R (roots p).
Proof.
by rewrite /roots; case: eqP => // ?; rewrite sort_sorted //; apply: le_total.
Qed.
Hint Resolve roots_le_sorted.

Lemma roots_uniq p : uniq (roots p).
Proof. by rewrite /roots; case: eqP => // ?; rewrite sort_uniq undup_uniq. Qed.
Hint Resolve roots_uniq.

Lemma roots_lt_sorted p : sorted <%R (roots p).
Proof. by rewrite lt_sorted_uniq_le roots_le_sorted roots_uniq. Qed.
Hint Resolve roots_lt_sorted.

Lemma eq_roots p q : p != 0 -> q != 0 -> root p =1 root q <-> roots p = roots q.
Proof.
move=> pN0 qN0; split => [rpq|rpq x]; last by rewrite -!rootsE // rpq.
apply: (eq_sorted (@le_trans _ _) (@le_anti _ _)) => //.
by apply: uniq_perm_eq => // x; rewrite !rootsE ?rpq.
Qed.

Lemma rootsC x : roots x%:P = [::].
Proof.
have [->|x_neq0] := eqVneq x 0; first by rewrite roots0.
apply: (eq_sorted (@le_trans _ _) (@le_anti _ _)) => //.
apply: uniq_perm_eq => // y; rewrite rootsE ?polyC_eq0//.
by rewrite /root  hornerE (negPf x_neq0).
Qed.

Lemma rootsN p : roots (- p) = roots p.
Proof.
have [->|pN0] := eqVneq p 0; first by rewrite oppr0.
by apply/eq_roots; rewrite ?oppr_eq0 // => x; rewrite rootN.
Qed.

Lemma rootsXsubC a : roots ('X - a%:P) = [:: a].
Proof.
apply: (eq_sorted (@le_trans _ _) (@le_anti _ _)) => //.
apply: uniq_perm_eq => // y; rewrite rootsE ?polyXsubC_eq0//=.
by rewrite /root !hornerE subr_eq0 inE.
Qed.

Lemma rootsXaddC a : roots ('X + a%:P) = [:: - a].
Proof. by rewrite -rootsXsubC rmorphN opprK. Qed.

Lemma comp_poly2_eq0 (R' : idomainType) (p q : {poly R'}) :
  (size q > 1)%N -> (p \Po q == 0) = (p == 0).
Proof.
move=> q_big; apply: negb_inj; rewrite -!size_poly_gt0.
have [|sp_gt0] := leqP (size p) 1.
  by move=> /size1_polyC->; rewrite comp_polyC.
rewrite (leq_trans _ sp_gt0)// (@leq_trans 2)// -subn_gt0 subn1.
by rewrite size_comp_poly muln_gt0 -!subn1 !subn_gt0 q_big sp_gt0.
Qed.

Lemma comp_poly_eq0 (R' : idomainType) (p q : {poly R'}) :
  (p \Po q == 0) = (p == 0) || ((size q <= 1)%N && root p q`_0).
Proof.
have [] := leqP; last by move=> /comp_poly2_eq0->; rewrite orbF.
have [->|p_neq0] := altP (p =P 0); first by rewrite comp_polyC eqxx.
by move=> /size1_polyC{1}->; rewrite comp_polyCr polyC_eq0.
Qed.

Lemma roots_comp p q : roots (p \Po q) =
  sort <=%R (undup (flatten [seq roots (q - x%:P) | x <- roots p])).
Proof.
apply: (eq_sorted (@le_trans _ _) (@le_anti _ _)) => //.
  by rewrite sort_sorted //; apply: le_total.
apply: uniq_perm_eq; rewrite ?roots_uniq ?sort_uniq ?undup_uniq //.
move=> x; rewrite ?mem_sort ?mem_undup.
have [pq_eq0|pq_neq0] := eqVneq (p \Po q) 0.
  rewrite pq_eq0 roots0 in_nil.
  have /eqP := pq_eq0; rewrite comp_poly_eq0.
  move=> /orP[/eqP->|/andP[/size1_polyC-> /eqP]]; first by rewrite roots0.
  rewrite coefC eqxx => pq0_eq0.
  by apply/idP/flatten_mapP=> // - [y yp]; rewrite -rmorphB rootsC.
have := pq_neq0; rewrite comp_poly_eq0 => /norP[p_neq0 size_q].
rewrite rootsE// /root horner_comp -/(root p _) -rootsE //.
apply/idP/flatten_mapP => [qx_p|[y py]].
  exists q.[x] => //; rewrite rootsE /root ?hornerE ?subrr//.
  rewrite subr_eq0; apply: contra_neq pq_neq0 => ->.
  by rewrite comp_polyCr horner_roots.
rewrite !rootsE// /root ?hornerE.
  by rewrite subr_eq0 => /eqP->; rewrite horner_roots.
rewrite subr_eq0; apply: contraNneq pq_neq0 => ->.
by rewrite comp_polyCr horner_roots.
Qed.

Lemma roots_sym p : roots (p \Po (-'X)) = sort <=%R [seq - x | x <- roots p].
Proof.
have oppR_inj := @oppr_inj R; have leR_total := @le_total _ R.
(* transitivity (sort <=%R [seq - x | x <- roots p]); last first. *)
(*   apply: (eq_sorted (@le_trans _ _) (@le_anti _ _)); last 1 first. *)
(*   - rewrite uniq_perm_eq// ?sort_uniq ?rev_uniq ?map_inj_uniq ?roots_uniq// => i. *)
(*     by rewrite mem_sort mem_rev. *)
(*   - by rewrite sort_sorted. *)
(*   - rewrite rev_sorted. *)
rewrite roots_comp; apply: (eq_sorted (@le_trans _ _) (@le_anti _ _)) => //;
  do ?by rewrite sort_sorted.
apply: uniq_perm_eq; rewrite ?roots_uniq ?sort_uniq ?undup_uniq ?map_inj_uniq//.
move=> x; rewrite ?mem_sort mem_undup (@eq_map _ _ _ (fun x => [:: - x])).
  by rewrite (map_comp (fun x => [::x])) flatten_seq1.
by move=> {x}x; rewrite -opprD rootsN rootsXaddC.
Qed.

End MonotonictyAndRoots.

Lemma roots_def p s : p != 0 -> (forall x, root p x = (x \in s)) ->
  sorted <%R s -> s = roots p.
Proof.
move=> p_neq0 s_roots; rewrite lt_sorted_uniq_le => /andP[s_uniq s_sorted].
apply: (eq_sorted (@le_trans _ _) (@le_anti _ _)); rewrite ?roots_le_sorted //.
by apply: uniq_perm_eq; rewrite ?roots_uniq // => x; rewrite rootsE.
Qed.

Section NeighborHood.

Implicit Types a b : R.

Implicit Types p : {poly R}.

Definition prev_root p x := rprev (roots p) x.
Definition next_root p x := rnext (roots p) x.

Implicit Types a b : R.

Implicit Types p : {poly R}.

Definition next_root (p : {poly R}) x b :=
  if p == 0 then x else head (maxr b x) (roots p x b).

Lemma next_root0 a b : next_root 0 a b = a.
Proof. by rewrite /next_root eqxx. Qed.

Variant next_root_spec (p : {poly R}) x b : bool -> R -> Type :=
| NextRootSpec0 of p = 0 : next_root_spec p x b true x
| NextRootSpecRoot y of p != 0 & p.[y] = 0 & y \in `]x, b[
  & {in `]x, y[, forall z, ~~(root p z)} : next_root_spec p x b true y
| NextRootSpecNoRoot c of p != 0 & c = maxr b x
  & {in `]x, b[, forall z, ~~(root p z)} : next_root_spec p x b (p.[c] == 0) c.

Lemma next_rootP (p : {poly R}) a b :
  next_root_spec p a b (p.[next_root p a b] == 0) (next_root p a b).
Proof.
rewrite /next_root /=; case hs: roots => [|x s] /=.
  case: (altP (p =P 0))=> p0.
    by rewrite {2}p0 hornerC eqxx; constructor; rewrite p0.
  by constructor=> // y hy; apply: (roots_nil p0 hs).
move/eqP: hs; rewrite roots_cons; case/and5P=> p0 hx; move/eqP=> rap rpx rx.
rewrite (negPf p0) (rootPt rpx); constructor=> //; first by move/eqP: rpx.
by move=> y hy /=; move/(roots_nil p0): (rap); apply.
Qed.

Lemma next_root_in p a b : next_root p a b \in `[a, maxr b a].
Proof.
case: next_rootP => [p0|y np0 py0 hy _|c np0 hc _].
* by rewrite bound_in_itv /= le_maxr lexx orbT.
* by apply: subitvP hy=> /=; rewrite le_maxr !lexx.
* by rewrite hc bound_in_itv /= le_maxr lexx orbT.
Qed.

Lemma next_root_gt p a b : a < b -> p != 0 -> next_root p a b > a.
Proof.
move=> ab np0; case: next_rootP=> [p0|y _ py0 hy _|c _ -> _].
* by rewrite p0 eqxx in np0.
* by rewrite (itvP hy).
* by rewrite lt_maxr ab.
Qed.

Lemma next_noroot p a b : {in `]a, (next_root p a b)[, noroot p}.
Proof.
move=> z; case: next_rootP; first by rewrite itv_xx.
  by move=> y np0 py0 hy hp hz; rewrite (negPf (hp _ _)).
move=> c p0 -> hp hz; rewrite (negPf (hp _ _)) //.
by case: leP hz; first rewrite itv_xx.
Qed.

Lemma is_next_root p a b x :
  next_root_spec p a b (root p x) x -> x = next_root p a b.
Proof.
case; first by move->; rewrite /next_root eqxx.
  move=> y; case: next_rootP; first by move->; rewrite eqxx.
  move=> y' np0 py'0 hy' hp' _ py0 hy hp.
    wlog: y y' hy' hy hp' hp py0 py'0 / y <= y'.
      by case/orP: (le_total y y')=> lyy' hw; [|symmetry]; apply: hw.
    case: ltrgtP=> // hyy' _; move: (hp' y).
    by rewrite rootE py0 eqxx inE /= (itvP hy) hyy'; move/(_ isT).
  move=> c p0 ->; case: leP => hba; first by rewrite itv_gte.
  by move=> hpz _ py0 hy; move/hpz:hy; rewrite rootE py0 eqxx.
case: next_rootP => //; first by move->; rewrite eqxx.
  by move=> y np0 py0 hy _ c _ _; move/(_ _ hy); rewrite rootE py0 eqxx.
by move=> c _ -> _ c' _ ->.
Qed.

Definition prev_root (p : {poly R}) a x :=
  if p == 0 then x else last (minr a x) (roots p a x).

Lemma prev_root0 a b : prev_root 0 a b = b.
Proof. by rewrite /prev_root eqxx. Qed.

Variant prev_root_spec (p : {poly R}) a x : bool -> R -> Type :=
| PrevRootSpec0 of p = 0 : prev_root_spec p a x true x
| PrevRootSpecRoot y of p != 0 & p.[y] = 0 & y \in`]a, x[
  & {in `]y, x[, forall z, ~~(root p z)} : prev_root_spec p a x true y
| PrevRootSpecNoRoot c of p != 0 & c = minr a x
 & {in `]a, x[, forall z, ~~(root p z)} : prev_root_spec p a x (p.[c] == 0) c.

Lemma prev_rootP (p : {poly R}) a b :
  prev_root_spec p a b (p.[prev_root p a b] == 0) (prev_root p a b).
Proof.
rewrite /prev_root /=; move hs: (roots _ _ _)=> s.
case: (lastP s) hs=> {s} [|s x] hs /=.
  case: (altP (p =P 0))=> p0.
    by rewrite {2}p0 hornerC eqxx; constructor; rewrite p0.
  by constructor=> // y hy; apply: (roots_nil p0 hs).
rewrite last_rcons; move/eqP: hs.
rewrite roots_rcons; case/and5P=> p0 hx; move/eqP=> rap rpx rx.
rewrite (negPf p0) (rootPt rpx); constructor=> //; first by move/eqP: rpx.
by move=> y hy /=; move/(roots_nil p0): (rap); apply.
Qed.

Lemma prev_root_in p a b : prev_root p a b \in `[minr a b, b].
Proof.
case: prev_rootP => [p0|y np0 py0 hy _|c np0 hc _].
* by rewrite bound_in_itv /= le_minl lexx orbT.
* by apply: subitvP hy=> /=; rewrite le_minl !lexx.
* by rewrite hc bound_in_itv /= le_minl lexx orbT.
Qed.

Lemma prev_noroot p a b : {in `](prev_root p a b), b[, noroot p}.
Proof.
move=> z; case: prev_rootP; first by rewrite itv_xx.
  by move=> y np0 py0 hy hp hz; rewrite (negPf (hp _ _)).
move=> c np0 ->; case: leP=> hab; last by rewrite itv_xx.
by move=> hp hz; rewrite (negPf (hp _ _)).
Qed.

Lemma prev_root_lt p a b : a < b -> p != 0 -> prev_root p a b < b.
Proof.
move=> ab np0; case: prev_rootP=> [p0|y _ py0 hy _|c _ -> _].
* by rewrite p0 eqxx in np0.
* by rewrite (itvP hy).
* by rewrite lt_minl ab.
Qed.

Lemma is_prev_root p a b x :
  prev_root_spec p a b (root p x) x -> x = prev_root p a b.
Proof.
case; first by move->; rewrite /prev_root eqxx.
  move=> y; case: prev_rootP; first by move->; rewrite eqxx.
  move=> y' np0 py'0 hy' hp' _ py0 hy hp.
    wlog: y y' hy' hy hp' hp py0 py'0 / y <= y'.
      by case/orP: (le_total y y')=> lyy' hw; [|symmetry]; apply: hw.
    case: ltrgtP=> // hyy' _; move/implyP: (hp y').
    by rewrite rootE py'0 eqxx inE /= (itvP hy') hyy'.
  by move=> c _ _ hpz _ py0 hy; move/hpz:hy; rewrite rootE py0 eqxx.
case: prev_rootP=> //; first by move->; rewrite eqxx.
  move=> y ? py0 hy _ c _ ->.
  case: ltP hy=> hab; last by rewrite itv_gte.
  by move=> hy; move/(_ _ hy); rewrite rootE py0 eqxx.
by move=> c  _ -> _ c' _ ->.
Qed.

Definition neighpr p a b := `]a, (next_root p a b)[.

Definition neighpl p a b := `](prev_root p a b), b[.

Lemma neighpl_root p a x : {in neighpl p a x, noroot p}.
Proof. exact: prev_noroot. Qed.

Lemma sgr_neighplN p a x :
  ~~ root p x -> {in neighpl p a x, forall y, (sgr p.[y] = sgr p.[x])}.
Proof.
rewrite /neighpl=> nrpx /= y hy.
apply: (@polyrN0_itv `[y, x]); do ?by rewrite bound_in_itv /= (itvP hy).
move=> z; rewrite (@itv_splitU _ x false) ?itv_xx /=; last first.
(* Todo : Lemma itv_splitP *)
  by rewrite bound_in_itv /= (itvP hy).
rewrite orbC => /predU1P[-> // | hz].
rewrite (@prev_noroot _ a x) //.
by apply: subitvPl hz; rewrite /= (itvP hy).
Qed.

Lemma sgr_neighpl_same p a x :
  {in neighpl p a x &, forall y z, (sgr p.[y] = sgr p.[z])}.
Proof.
by rewrite /neighpl=> y z *; apply: (polyrN0_itv (@prev_noroot p a x)).
Qed.

Lemma neighpr_root p x b : {in neighpr p x b, noroot p}.
Proof. exact: next_noroot. Qed.

Lemma sgr_neighprN p x b :
  p.[x] != 0 -> {in neighpr p x b, forall y, (sgr p.[y] = sgr p.[x])}.
Proof.
rewrite /neighpr=> nrpx /= y hy; symmetry.
apply: (@polyrN0_itv `[x, y]); do ?by rewrite bound_in_itv /= (itvP hy).
move=> z; rewrite (@itv_splitU _ x true) ?itv_xx /=; last first.
(* Todo : Lemma itv_splitP *)
  by rewrite bound_in_itv /= (itvP hy).
case/orP=> [|hz]; first by rewrite inE /=; move/eqP->.
rewrite (@next_noroot _ x b) //.
by apply: subitvPr hz; rewrite /= (itvP hy).
Qed.

Lemma sgr_neighpr_same p x b :
  {in neighpr p x b &, forall y z, (sgr p.[y] = sgr p.[z])}.
Proof.
by rewrite /neighpl=> y z *; apply: (polyrN0_itv (@next_noroot p x b)).
Qed.

Lemma uniq_roots a b p : uniq (roots p a b).
Proof.
case p0: (p == 0); first by rewrite (eqP p0) roots0.
by apply: (@sorted_uniq _ <%R); [apply: lt_trans | apply: ltxx|].
Qed.

Hint Resolve uniq_roots.

Lemma in_roots p (a b x : R) :
  (x \in roots p a b) = [&& root p x, x \in `]a, b[ & p != 0].
Proof.
case: rootsP=> //=; first by rewrite in_nil !andbF.
by move=> p0 hr sr; rewrite andbT -hr andbC.
Qed.

(* Todo : move to polyorder => need char 0 *)
Lemma gdcop_eq0 p q : (gdcop p q == 0) = (q == 0) && (p != 0).
Proof.
case: (eqVneq q 0) => [-> | q0].
  by rewrite gdcop0 /=; case: (eqVneq p 0) => _; rewrite ?eqxx ?oner_eq0.
rewrite /gdcop; move: {-1}(size q) (leqnn (size q))=> k hk.
case: (eqVneq p 0) => [-> | p0] /=; apply: negPf.
  elim: k q q0 {hk} => [|k ihk] q q0 /=; first by rewrite eqxx oner_eq0.
  case: ifP => _ //.
  by apply: ihk; rewrite gcdp0 divpp ?q0 // polyC_eq0; apply/lc_expn_scalp_neq0.
elim: k q q0 hk => [|k ihk] /= q q0 hk.
  by move: hk q0; rewrite leqn0 size_poly_eq0; move->.
case: ifP=> cpq; first by rewrite (negPf q0).
apply: ihk.
  rewrite divpN0; last by rewrite gcdp_eq0 negb_and q0.
  by rewrite dvdp_leq // dvdp_gcdl.
rewrite -ltnS; apply: leq_trans hk; move: (dvdp_gcdl q p); rewrite dvdp_eq.
move/eqP=> eqq; move/(f_equal (fun x : {poly R} => size x)): (eqq).
rewrite size_scale; last exact: lc_expn_scalp_neq0.
have gcdn0 : gcdp q p != 0 by rewrite gcdp_eq0 negb_and q0.
have qqn0 : q %/ gcdp q p != 0.
   apply: contraTneq q0; rewrite negbK => e.
   move: (scaler_eq0 (lead_coef (gcdp q p) ^+ scalp q (gcdp q p)) q).
   by rewrite (negPf (lc_expn_scalp_neq0 _ _)) /=; move<-; rewrite eqq e mul0r.
move->; rewrite size_mul //; case sgcd: (size (gcdp q p)) => [|n].
  by move/eqP: sgcd gcdn0; rewrite size_poly_eq0; move->.
case: n sgcd => [|n]; first by move/eqP; rewrite size_poly_eq1 gcdp_eqp1 cpq.
by rewrite addnS /= -{1}[size (_ %/ _)]addn0 ltn_add2l.
Qed.

Lemma roots_mul a b : a < b -> forall p q,
  p != 0 -> q != 0 -> perm_eq (roots (p*q) a b)
  (roots p a b ++ roots ((gdcop p q)) a b).
Proof.
move=> hab p q np0 nq0.
apply: uniq_perm; first exact: uniq_roots.
  rewrite cat_uniq ?uniq_roots andbT /=; apply/hasPn=> x /=.
  move/root_roots; rewrite root_gdco //; case/andP=> _.
  by rewrite in_roots !negb_and=> ->.
move=> x; rewrite mem_cat !in_roots root_gdco //.
rewrite rootM mulf_eq0 gdcop_eq0 negb_and.
case: (x \in `]_, _[); last by rewrite !andbF.
by rewrite negb_or !np0 !nq0 !andbT /=; do 2?case: root=> //=.
Qed.

Lemma roots_mul_coprime a b :
  a < b ->
  forall p q, p != 0 -> q != 0 -> coprimep p q ->
  perm_eq (roots (p * q) a b)
  (roots p a b ++ roots q a b).
Proof.
move=> hab p q np0 nq0 cpq.
rewrite (perm_trans (roots_mul hab np0 nq0)) //.
suff ->: roots (gdcop p q) a b = roots q a b by apply: perm_refl.
case: gdcopP=> r rq hrp; move/(_ q (dvdpp _)).
rewrite coprimep_sym; move/(_ cpq)=> qr.
have erq : r %= q by rewrite /eqp rq qr.
(* Todo : relate eqp with roots *)
apply/roots_eq=> // [|x hx]; last exact: eqp_root.
by rewrite -size_poly_eq0 (eqp_size erq) size_poly_eq0.
Qed.


Lemma next_rootM a b (p q : {poly R}) :
  next_root (p * q) a b = minr (next_root p a b) (next_root q a b).
Proof.
symmetry; apply: is_next_root.
wlog: p q / next_root p a b <= next_root q a b.
  case: leP=> hpq; first by move/(_ _ _ hpq); case: leP hpq.
  by move/(_ _ _ (ltW hpq)); rewrite mulrC; case: ltP hpq.
case: leP => //; case: next_rootP=> [|y np0 py0 hy|c np0 ->] hp hpq _.
* by rewrite hp mul0r root0; constructor.
* rewrite rootM; move/rootP:(py0)->; constructor=> //.
  - by rewrite mulf_neq0 //; case: next_rootP hpq; rewrite // (itvP hy).
  - by rewrite hornerM py0 mul0r.
  - move=> z hz /=; rewrite rootM negb_or ?hp //.
    by rewrite (@next_noroot _ a b) //; apply: subitvPr hz.
* case: (altP (q =P 0)) => q0.
    move: hpq; rewrite q0 mulr0 root0 next_root0 le_maxl lexx andbT.
    by move/max_r->; constructor.
  constructor=> //; first by rewrite mulf_neq0.
  move=> z hz /=; rewrite rootM negb_or ?hp //.
  rewrite (@next_noroot _ a b) //; apply: subitvPr hz=> /=.
  by move: hpq; rewrite le_maxl; case/andP.
Qed.

Lemma neighpr_mul a b p q :
  (neighpr (p * q) a b) =i [predI (neighpr p a b) & (neighpr q a b)].
Proof.
move=> x; rewrite inE /= !inE /= next_rootM.
by case: (a < x); rewrite // lt_minr.
Qed.

Lemma prev_rootM a b (p q : {poly R}) :
  prev_root (p * q) a b = maxr (prev_root p a b) (prev_root q a b).
Proof.
symmetry; apply: is_prev_root.
wlog: p q / prev_root p a b >= prev_root q a b.
  case: leP=> hpq; last by move/(_ _ _ (ltW hpq)); case: leP hpq.
  by move/(_ _ _ hpq); case: ltP hpq; rewrite mulrC.
case: ltP => //; case: (@prev_rootP p)=> [|y np0 py0 hy|c np0 ->] hp hpq _.
* by rewrite hp mul0r root0; constructor.
* rewrite rootM; move/rootP:(py0)->; constructor=> //.
  - by rewrite mulf_neq0 //; case: prev_rootP hpq; rewrite // (itvP hy).
  - by rewrite hornerM py0 mul0r.
  - move=> z hz /=; rewrite rootM negb_or ?hp //.
    by rewrite (@prev_noroot _ a b) //; apply: subitvPl hz.
* case: (altP (q =P 0))=> q0.
    move: hpq; rewrite q0 mulr0 root0 prev_root0 le_minr lexx andbT.
    by move/min_r->; constructor.
  constructor=> //; first by rewrite mulf_neq0.
  move=> z hz /=; rewrite rootM negb_or ?hp //.
  rewrite (@prev_noroot _ a b) //; apply: subitvPl hz=> /=.
  by move: hpq; rewrite le_minr; case/andP.
Qed.

Lemma neighpl_mul a b p q :
  (neighpl (p * q) a b) =i [predI (neighpl p a b) & (neighpl q a b)].
Proof.
move=> x; rewrite !inE /= prev_rootM.
by case: (x < b); rewrite // lt_maxl !(andbT, andbF).
Qed.

Lemma neighpr_wit p x b : x < b -> p != 0 -> {y | y \in neighpr p x b}.
Proof.
move=> xb; exists (mid x (next_root p x b)).
by rewrite mid_in_itv //= next_root_gt.
Qed.

Lemma neighpl_wit p a x : a < x -> p != 0 -> {y | y \in neighpl p a x}.
Proof.
move=> xb; exists (mid (prev_root p a x) x).
by rewrite mid_in_itv //= prev_root_lt.
Qed.

End NeighborHood.

Section SignRight.

Definition sgp_right (p : {poly R}) x :=
  let fix aux (p : {poly R}) n :=
  if n is n'.+1
    then if ~~ root p x
      then sgr p.[x]
      else aux p^`() n'
    else 0
      in aux p (size p).

Lemma sgp_right0 x : sgp_right 0 x = 0.
Proof. by rewrite /sgp_right size_poly0. Qed.

Lemma sgr_neighpr b p x :
  {in neighpr p x b, forall y, (sgr p.[y] = sgp_right p x)}.
Proof.
elim: (size p) {-2}p (leqnn (size p))=> [|n ihn] {p} p.
  rewrite leqn0 size_poly_eq0 /neighpr; move/eqP=> -> /=.
  by move=> y; rewrite next_root0 itv_xx.
rewrite leq_eqVlt ltnS; case/orP; last exact: ihn.
move/eqP=> sp; rewrite /sgp_right sp /=.
case px0: root=> /=; last first.
  move=> y; rewrite /neighpr => hy /=; symmetry.
  apply: (@polyrN0_itv `[x, y]); do ?by rewrite bound_in_itv /= (itvP hy).
  move=> z; rewrite (@itv_splitU _ x true) ?bound_in_itv /= ?(itvP hy) //.
  rewrite itv_xx /=; case/predU1P=> hz; first by rewrite hz px0.
  rewrite (@next_noroot p x b) //.
  by apply: subitvPr hz=> /=; rewrite (itvP hy).
have <-: size p^`() = n by rewrite size_deriv sp.
rewrite -/(sgp_right p^`() x).
move=> y; rewrite /neighpr=> hy /=.
case: (@neighpr_wit (p * p^`()) x b)=> [||m hm].
* case: next_rootP hy; first by rewrite itv_xx.
    by move=> ? ? ?; move/itvP->.
  move=> c p0 -> _; first by case: leP; rewrite ?itv_xx.
* rewrite mulf_neq0 //.
    by move/eqP:sp; apply: contraTneq=> ->; rewrite size_poly0.
  (* Todo : a lemma for this *)
  move: (size_deriv p); rewrite sp /=; move/eqP; apply: contraTneq=> ->.
  rewrite size_poly0; apply: contraTneq px0=> hn; rewrite -hn in sp.
  by move/eqP: sp; case/size_poly1P=> c nc0 ->; rewrite rootC.
* move: hm; rewrite neighpr_mul /neighpr inE /=; case/andP=> hmp hmp'.
  rewrite (polyrN0_itv _ hmp) //; last exact: next_noroot.
  rewrite (@ders0r p x m (mid x m)) ?(eqP px0) ?mid_in_itv ?bound_in_itv //;
    rewrite /= ?(itvP hmp) //; last first.
    move=> u hu /=; rewrite (@next_noroot _ x b) //.
    by apply: subitvPr hu; rewrite /= (itvP hmp').
  rewrite ihn ?size_deriv ?sp /neighpr //.
  by rewrite (subitvP _ (@mid_in_itv _ true true _ _ _)) //= ?lexx (itvP hmp').
Qed.

Lemma sgr_neighpl a p x :
  {in neighpl p a x, forall y,
    (sgr p.[y] = (-1) ^+ (odd (\mu_x p)) * sgp_right p x)
  }.
Proof.
elim: (size p) {-2}p (leqnn (size p))=> [|n ihn] {p} p.
  rewrite leqn0 size_poly_eq0 /neighpl; move/eqP=> -> /=.
  by move=> y; rewrite prev_root0 itv_xx.
rewrite leq_eqVlt ltnS; case/orP; last exact: ihn.
move/eqP=> sp; rewrite /sgp_right sp /=.
case px0: root=> /=; last first.
  move=> y; rewrite /neighpl => hy /=; symmetry.
  move: (negbT px0); rewrite -mu_gt0; last first.
    by apply: contraFN px0; move/eqP->; rewrite rootC.
  rewrite -leqNgt leqn0; move/eqP=> -> /=; rewrite expr0 mul1r.
  symmetry; apply: (@polyrN0_itv `[y, x]);
    do ?by rewrite bound_in_itv /= (itvP hy).
  move=> z; rewrite (@itv_splitU _ x false) ?bound_in_itv /= ?(itvP hy) //.
  rewrite itv_xx /= orbC; case/predU1P=> hz; first by rewrite hz px0.
  rewrite (@prev_noroot p a x) //.
  by apply: subitvPl hz=> /=; rewrite (itvP hy).
have <-: size p^`() = n by rewrite size_deriv sp.
rewrite -/(sgp_right p^`() x).
move=> y; rewrite /neighpl=> hy /=.
case: (@neighpl_wit (p * p^`()) a x)=> [||m hm].
* case: prev_rootP hy; first by rewrite itv_xx.
    by move=> ? ? ?; move/itvP->.
  move=> c p0 -> _; first by case: ltP; rewrite ?itv_xx.
* rewrite mulf_neq0 //.
    by move/eqP:sp; apply: contraTneq=> ->; rewrite size_poly0.
  (* Todo : a lemma for this *)
  move: (size_deriv p); rewrite sp /=; move/eqP; apply: contraTneq=> ->.
  rewrite size_poly0; apply: contraTneq px0=> hn; rewrite -hn in sp.
  by move/eqP: sp; case/size_poly1P=> c nc0 ->; rewrite rootC.
* move: hm; rewrite neighpl_mul /neighpl inE /=; case/andP=> hmp hmp'.
  rewrite (polyrN0_itv _ hmp) //; last exact: prev_noroot.
  rewrite (@ders0l p m x (mid m x)) ?(eqP px0) ?mid_in_itv ?bound_in_itv //;
    rewrite /= ?(itvP hmp) //; last first.
    move=> u hu /=; rewrite (@prev_noroot _ a x) //.
    by apply: subitvPl hu; rewrite /= (itvP hmp').
  rewrite ihn ?size_deriv ?sp /neighpl //; last first.
    by rewrite (subitvP _ (@mid_in_itv _ true true _ _ _)) //=
       ?lexx (itvP hmp').
  rewrite mu_deriv // odd_sub ?mu_gt0 //=; last by rewrite -size_poly_eq0 sp.
  by rewrite signr_addb /= mulrN1 mulNr opprK.
Qed.

Lemma sgp_right_deriv (p : {poly R}) x :
  root p x -> sgp_right p x = sgp_right (p^`()) x.
Proof.
elim: (size p) {-2}p (erefl (size p)) x => {p} [p|sp hp p hsp x].
  by move/eqP; rewrite size_poly_eq0; move/eqP=> -> x _; rewrite derivC.
by rewrite /sgp_right size_deriv hsp /= => ->.
Qed.

Lemma sgp_rightNroot (p : {poly R}) x :
  ~~ root p x -> sgp_right p x = sgr p.[x].
Proof.
move=> nrpx; rewrite /sgp_right; case hsp: (size _)=> [|sp].
  by move/eqP:hsp; rewrite size_poly_eq0; move/eqP->; rewrite hornerC sgr0.
by rewrite nrpx.
Qed.

Lemma sgp_right_mul p q x : sgp_right (p * q) x = sgp_right p x * sgp_right q x.
Proof.
case: (altP (q =P 0))=> q0; first by rewrite q0 /sgp_right !(size_poly0,mulr0).
case: (altP (p =P 0))=> p0; first by rewrite p0 /sgp_right !(size_poly0,mul0r).
case: (@neighpr_wit (p * q) x (1 + x))=> [||m hpq]; do ?by rewrite mulf_neq0.
  by rewrite ltr_spaddl ?ltr01.
rewrite -(@sgr_neighpr (1 + x) _ _ m) //.
move: hpq; rewrite neighpr_mul inE /=; case/andP=> hp hq.
by rewrite hornerM sgrM !(@sgr_neighpr (1 + x) _ x) /neighpr.
Qed.

Lemma sgp_right_scale c p x : sgp_right (c *: p) x = sgr c * sgp_right p x.
Proof.
case c0: (c == 0); first by rewrite (eqP c0) scale0r sgr0 mul0r sgp_right0.
by rewrite -mul_polyC sgp_right_mul sgp_rightNroot ?hornerC ?rootC ?c0.
Qed.

Lemma sgp_right_square p x : p != 0 -> sgp_right p x * sgp_right p x = 1.
Proof.
move=> np0; case: (@neighpr_wit p x (1 + x))=> [||m hpq] //.
  by rewrite ltr_spaddl ?ltr01.
rewrite -(@sgr_neighpr (1 + x) _ _ m) //.
by rewrite -expr2 sqr_sg (@next_noroot _ x (1 + x)).
Qed.

Lemma sgp_right_rec p x :
  sgp_right p x =
   (if p == 0 then 0 else if ~~ root p x then sgr p.[x] else sgp_right p^`() x).
Proof.
rewrite /sgp_right; case hs: size => [|s]; rewrite -size_poly_eq0 hs //=.
by rewrite size_deriv hs.
Qed.

Lemma sgp_right_addp0 (p q : {poly R}) x :
  q != 0 -> (\mu_x p > \mu_x q)%N -> sgp_right (p + q) x = sgp_right q x.
Proof.
move=> nq0; move hm: (\mu_x q)=> m.
elim: m p q nq0 hm => [|mq ihmq] p q nq0 hmq; case hmp: (\mu_x p)=> // [mp];
  do[
    rewrite ltnS=> hm;
      rewrite sgp_right_rec {1}addrC;
        rewrite GRing.Theory.addr_eq0]. (* Todo : fix this ! *)
  case: (altP (_ =P _))=> hqp.
    move: (nq0); rewrite {1}hqp oppr_eq0=> np0.
    rewrite sgp_right_rec (negPf nq0) -mu_gt0 // hmq /=.
    apply/eqP; rewrite eq_sym hqp hornerN sgrN.
    by rewrite oppr_eq0 sgr_eq0 -[_ == _]mu_gt0 ?hmp.
  rewrite rootE hornerD.
  have ->: p.[x] = 0.
    apply/eqP; rewrite -[_ == _]mu_gt0 ?hmp //.
    by move/eqP: hmp; apply: contraTneq=> ->; rewrite mu0.
  symmetry; rewrite sgp_right_rec (negPf nq0) add0r.
  by rewrite -/(root _ _) -mu_gt0 // hmq.
case: (altP (_ =P _))=> hqp.
  by move: hm; rewrite -ltnS -hmq -hmp hqp mu_opp ltnn.
have px0: p.[x] = 0.
  apply/rootP; rewrite -mu_gt0 ?hmp //.
  by move/eqP: hmp; apply: contraTneq=> ->; rewrite mu0.
have qx0: q.[x] = 0 by apply/rootP; rewrite -mu_gt0 ?hmq //.
rewrite rootE hornerD px0 qx0 add0r eqxx /=; symmetry.
rewrite sgp_right_rec rootE (negPf nq0) qx0 eqxx /=.
rewrite derivD ihmq // ?mu_deriv ?rootE ?px0 ?qx0 ?hmp ?hmq ?subn1 //.
apply: contra nq0; rewrite -size_poly_eq0 size_deriv.
case hsq: size=> [|sq] /=.
  by move/eqP: hsq; rewrite size_poly_eq0.
move/eqP=> sq0; move/eqP: hsq qx0; rewrite sq0; case/size_poly1P=> c c0 ->.
by rewrite hornerC; move/eqP; rewrite (negPf c0).
Qed.

End SignRight.

(* redistribute some of what follows with in the file *)
Section PolyRCFPdiv.
Import Pdiv.Ring Pdiv.ComRing.

Lemma sgp_rightc (x c : R) : sgp_right c%:P x = sgr c.
Proof.
rewrite /sgp_right size_polyC.
case cn0: (_ == 0)=> /=; first by rewrite (eqP cn0) sgr0.
by rewrite rootC hornerC cn0.
Qed.

Lemma sgp_right_eq0 (x : R) p : (sgp_right p x == 0) = (p == 0).
Proof.
case: (altP (p =P 0))=> p0; first by rewrite p0 sgp_rightc sgr0 eqxx.
rewrite /sgp_right.
elim: (size p) {-2}p (erefl (size p)) p0=> {p} [|sp ihsp] p esp p0.
  by move/eqP:esp; rewrite size_poly_eq0 (negPf p0).
rewrite esp /=; case px0: root=> //=; rewrite ?sgr_cp0 ?px0//.
have hsp: sp = size p^`() by rewrite size_deriv esp.
rewrite hsp ihsp // -size_poly_eq0 -hsp; apply/negP; move/eqP=> sp0.
move: px0; rewrite root_factor_theorem.
by move=> /rdvdp_leq // /(_ p0); rewrite size_XsubC esp sp0.
Qed.

(* :TODO: backport to polydiv *)
Lemma lc_expn_rscalp_neq0 (p q : {poly R}): lead_coef q ^+ rscalp p q != 0.
Proof.
case: (eqVneq q 0) => [->|nzq]; last by rewrite expf_neq0 ?lead_coef_eq0.
by rewrite /rscalp unlock /= eqxx /= expr0 oner_neq0.
Qed.
Notation lcn_neq0 := lc_expn_rscalp_neq0.

Lemma sgp_right_mod p q x : (\mu_x p < \mu_x q)%N ->
  sgp_right (rmodp p q) x = (sgr (lead_coef q)) ^+ (rscalp p q) * sgp_right p x.
Proof.
move=> mupq; case p0: (p == 0).
  by rewrite (eqP p0) rmod0p !sgp_right0 mulr0.
have qn0 : q != 0.
  by apply/negP; move/eqP=> q0; rewrite q0  mu0 ltn0 in mupq.
move/eqP: (rdivp_eq q p).
rewrite eq_sym (can2_eq (addKr _ ) (addNKr _)); move/eqP->.
case qpq0: ((rdivp p q) == 0).
  by rewrite (eqP qpq0) mul0r oppr0 add0r sgp_right_scale // sgrX.
rewrite sgp_right_addp0 ?sgp_right_scale ?sgrX //.
  by rewrite scaler_eq0 negb_or p0 lcn_neq0.
rewrite mu_mulC ?lcn_neq0 // mu_opp mu_mul ?mulf_neq0 ?qpq0 //.
by rewrite ltn_addl.
Qed.

Lemma rootsC (a b c : R) : roots c%:P a b = [::].
Proof.
case: (altP (c =P 0))=> hc; first by rewrite hc roots0.
by apply: no_root_roots=> x hx; rewrite rootC.
Qed.

Lemma rootsZ a b c p : c != 0 -> roots (c *: p) a b = roots p a b.
Proof.
have [->|p_neq0 c_neq0] := eqVneq p 0; first by rewrite scaler0.
by apply/roots_eq => [||x axb]; rewrite ?scaler_eq0 ?(negPf c_neq0) ?rootZ.
Qed.

Lemma root_bigrgcd (x : R) (ps : seq {poly R}) :
  root (\big[(@rgcdp _)/0]_(p <- ps) p) x = all (root^~ x) ps.
Proof.
elim: ps; first by rewrite big_nil root0.
move=> p ps ihp; rewrite big_cons /=.
by rewrite (eqp_root (eqp_rgcd_gcd _ _)) root_gcd ihp.
Qed.

Definition rootsR p := roots p (- cauchy_bound p) (cauchy_bound p).

Lemma roots_on_rootsR p : p != 0 -> roots_on p `]-oo, +oo[ (rootsR p).
Proof.
rewrite /rootsR => p_neq0 x /=; rewrite -roots_on_roots // andbC.
by have [/(cauchy_boundP p_neq0) /=|//] := altP rootP; rewrite ltr_norml.
Qed.

Lemma rootsR0 : rootsR 0 = [::]. Proof. exact: roots0. Qed.

Lemma rootsRC c : rootsR c%:P = [::]. Proof. exact: rootsC. Qed.

Lemma rootsRP p a b :
    {in `]-oo, a], noroot p} -> {in `[b , +oo[, noroot p} ->
  roots p a b = rootsR p.
Proof.
move=> rpa rpb.
have [->|p_neq0] := eqVneq p 0; first by rewrite rootsR0 roots0.
apply: (eq_sorted_irr lt_trans); rewrite ?sorted_roots // => x.
rewrite -roots_on_rootsR -?roots_on_roots //=.
have [rpx|] := boolP (root _ _); rewrite ?(andbT, andbF) //.
apply: contraLR rpx; rewrite inE negb_and -!leNgt.
by move=> /orP[/rpa //|xb]; rewrite rpb // inE andbT.
Qed.

Lemma sgp_pinftyP x (p : {poly R}) :
    {in `[x , +oo[, noroot p} ->
  {in `[x, +oo[, forall y, sgr p.[y] = sgp_pinfty p}.
Proof.
rewrite /sgp_pinfty; wlog lp_gt0 : x p / lead_coef p > 0 => [hwlog|rpx y Hy].
  have [|/(hwlog x p) //|/eqP] := ltrgtP (lead_coef p) 0; last first.
    by rewrite lead_coef_eq0 => /eqP -> ? ? ?; rewrite lead_coef0 horner0.
  rewrite -[p]opprK lead_coef_opp oppr_cp0 => /(hwlog x _) Hp HNp y Hy.
  by rewrite hornerN !sgrN Hp => // z /HNp; rewrite rootN.
have [z Hz] := poly_pinfty_gt_lc lp_gt0.
have {Hz} Hz u : u \in `[z, +oo[ -> Num.sg p.[u] = 1.
  by rewrite inE andbT => /Hz pu_ge1; rewrite gtr0_sg // (lt_le_trans lp_gt0).
rewrite (@polyrN0_itv _ _ rpx (maxr y z)) ?inE /= ?le_maxr ?(itvP Hy) //.
by rewrite Hz ?gtr0_sg // inE /= le_maxr lexx orbT.
Qed.

Lemma sgp_minftyP x (p : {poly R}) :
    {in `]-oo, x], noroot p} ->
  {in `]-oo, x], forall y, sgr p.[y] = sgp_minfty p}.
Proof.
move=> rpx y Hy; rewrite -sgp_pinfty_sym.
have -> : p.[y] = (p \Po -'X).[-y] by rewrite horner_comp !hornerE opprK.
apply: (@sgp_pinftyP (- x)); last by rewrite inE /= ler_opp2 (itvP Hy).
by move=> z Hz /=; rewrite root_comp !hornerE rpx // inE /= ler_oppl (itvP Hz).
Qed.

Lemma odd_poly_root (p : {poly R}) : ~~ odd (size p) -> {x | root p x}.
Proof.
move=> size_p_even.
have [->|p_neq0] := altP (p =P 0); first by exists 0; rewrite root0.
pose b := cauchy_bound p.
have [] := @ivt_sign p (-b) b; last by move=> x _; exists x.
  by rewrite ge0_cp // ?cauchy_bound_ge0.
rewrite (sgp_minftyP (le_cauchy_bound p_neq0)) ?bound_in_itv //.
rewrite (sgp_pinftyP (ge_cauchy_bound p_neq0)) ?bound_in_itv //.
move: size_p_even; rewrite polySpred //= negbK /sgp_minfty -signr_odd => ->.
by rewrite expr1 mulN1r sgrN mulNr -expr2 sqr_sg lead_coef_eq0 p_neq0.
Qed.
End PolyRCFPdiv.

End PolyRCF.
