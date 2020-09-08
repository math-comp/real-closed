Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect order.
Set Warnings "+notation-overridden".

(******************************************************************************)
(* This files provides support for tabulating ordered numbers, such as in sign*)
(* tables of functions.                                                       *)
(*    ext T == the type of ordered types extended with two formal infinities, *)
(*             such that -oo <= x    <= +oo for all x of type ext T,          *)
(*                   and -oo <  t%:x  < +oo for all t of type T.              *)
(*     t%:x == the injection of t of type T in ext T, through the constructor *)
(*             Fin of ext T                                                   *)
(*          := @Fin T t                                                       *)
(*      -oo == the formal minimum element of ext T                            *)
(*          := Infty false                                                    *)
(*      +oo == the formal maximu element of ext T                             *)
(*          := Infty true                                                     *)
(*                                                                            *)
(* Given a sequence s, which is sometimes supposed totally ordered using, and *)
(* sometimes also such that uniq s.                                           *)
(*         s`[i] == | -oo                       if i = 0,                     *)
(*                  | +oo                       if i > size s,                *)
(*                  | the i.-1th element of s   otherwise                     *)
(*               := nth +oo (-oo :: s) i                                      *)
(*    rindex s t == the unique natural number such that                       *)
(*                  s`[rindex s t] < t%:x <= s`[(rindex s t).+1]              *)
(*                  (under total and uniq ordering of rindex)                 *)
(*               := find (>= t) s                                             *)
(*     rprev s t == the last element u of s s.t. u < t, otherwise -oo         *)
(*               := s`[index s t]                                             *)
(*     rnext s t == the first element u of s s.t. t <= u, otherwise +oo       *)
(*               := s`[(index s t).+1]                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma subseq_cons2 (T : eqType) (x : T) (s s' : seq T) :
  subseq (x :: s) (x :: s') = subseq s s'.
Proof. by rewrite /= eqxx. Qed.

Import Order.TTheory.

Delimit Scope ext_scope with x.
Local Open Scope ext_scope.

Reserved Notation "s `[ i ]" (at level 3, i at level 2, left associativity,
  format "s `[ i ]").
Reserved Notation "x %:x" (format "x %:x", left associativity, at level 2).
Reserved Notation "+oo" (at level 0).
Reserved Notation "-oo" (at level 0).

Local Open Scope order_scope.

Hint Resolve le_trans.

Section ext.
Variable (T : Type).

Inductive ext := Infty of bool | Fin of T.

Lemma Fin_inj : injective Fin. Proof. by move=> ? ? []. Qed.
Lemma Infty_inj : injective Infty. Proof. by move=> ? ? []. Qed.

Definition ext_encode x := match x with Infty b => inl b | Fin t => inr t end.
Definition ext_decode a := match a with inl b => Infty b | inr t => Fin t end.
Lemma ext_encodeK : cancel ext_encode ext_decode. Proof. by case. Qed.

Definition finite := [qualify x : ext | if x is Fin _ then true else false].
Coercion is_finite x := x \is finite.

End ext.

Arguments Infty {T}.
Arguments Fin {T}.
Arguments ext_encodeK {T}.
Arguments finite {T}.
Arguments is_finite T /.

Notation "x %:x" := (Fin x).
Notation "+oo" := (Infty false).
Notation "-oo" := (Infty true).
Hint Resolve Fin_inj Infty_inj.

Canonical ext_eqType (T : eqType) := EqType (ext T) (CanEqMixin ext_encodeK).
Canonical ext_choiceType (T : choiceType) :=
  ChoiceType (ext T) (CanChoiceMixin ext_encodeK).
Canonical ext_countType (T : countType) :=
  CountType (ext T) (CanCountMixin ext_encodeK).
Canonical ext_finType (T : finType) :=
  FinType (ext T) (CanFinMixin ext_encodeK).

Section rindex.

Variables (d : unit) (T : orderType d).

Notation ext := (ext T).
Implicit Types (m t u v : T) (x y z : ext).

Let FinT_inj := @Fin_inj T.

Definition ext_le x y := match x, y with
  | Infty bl, Infty br => br ==> bl | Fin t, Fin u => t <= u
  | Infty bl, _ => bl               | _, Infty br => ~~ br
end.

Definition ext_lt x y := match x, y with
  | Infty bl, Infty br => bl && ~~ br  | Fin t, Fin u => t < u
  | Infty bl, _ => bl                  | _ , Infty br => ~~ br
end.

Lemma ext_lt_def : forall x y, ext_lt x y = (y != x) && ext_le x y.
Proof. by move=> [[]|t] [[]|u]//=; rewrite inj_eq ?lt_def => // ? ? []. Qed.

Lemma ext_le_anti : antisymmetric ext_le.
Proof. by move=> [[]|t] [[]|u]//= /le_anti->. Qed.

Lemma ext_le_trans : transitive ext_le.
Proof. by move=> [[]|t] [[]|u] [[]|v]//=; apply: le_trans. Qed.

Lemma ext_le_total : total ext_le.
Proof. by move=> [[]|t] [[]|u]//=; apply: le_total. Qed.

Definition ext_orderMixin :=
  LeOrderMixin ext_lt_def (fun _ _ => erefl) (fun _ _ =>  erefl)
    ext_le_anti ext_le_trans ext_le_total.

Canonical ext_porderType := POrderType d ext ext_orderMixin.
Canonical ext_latticeType := LatticeType ext ext_orderMixin.
Canonical ext_dlatticeType := DistrLatticeType ext ext_orderMixin.
Canonical ext_orderType := OrderType ext ext_orderMixin.

Lemma leEext x y : (x <= y) = (ext_le x y). Proof. by []. Qed.
Lemma ltEext x y : (x < y) = (ext_lt x y).  Proof. by []. Qed.

Lemma le_ext t t' : (t%:x <= t'%:x) = (t <= t'). Proof. by []. Qed.
Lemma lt_ext t t' : (t%:x < t'%:x)  = (t < t').  Proof. by []. Qed.

Lemma ge_xmin x : -oo <= x.     Proof. by case: x => [[]|]. Qed.
Lemma le_xmax x : x <= +oo.     Proof. by case: x => [[]|]. Qed.
Lemma gt_xmin x : x -> -oo < x. Proof. by case: x. Qed.
Lemma lt_xmax x : x -> x < +oo. Proof. by case: x. Qed.

Lemma minxmax x : Order.min x +oo = x.   Proof. by case: x => [[]|]. Qed.
Lemma minmaxx x : Order.min +oo x = x.   Proof. by case: x => [[]|]. Qed.
Lemma minxmin x : Order.min x -oo = -oo. Proof. by case: x => [[]|]. Qed.
Lemma minminx x : Order.min -oo x = -oo. Proof. by case: x => [[]|]. Qed.

Lemma maxxmax x : Order.max x +oo = +oo. Proof. by case: x => [[]|]. Qed.
Lemma maxmaxx x : Order.max +oo x = +oo. Proof. by case: x => [[]|]. Qed.
Lemma maxxmin x : Order.max x -oo = x.   Proof. by case: x => [[]|]. Qed.
Lemma maxminx x : Order.max -oo x = x.   Proof. by case: x => [[]|]. Qed.

Definition edflt t t' x :=
  match x with Fin t'' => t'' | Infty s => if s then t else t' end.
Notation edflt1 t := (edflt t t).

Lemma le_edflt2  m t t' x x' : t <= m <= t' ->
  t < edflt1 m x <= t' -> t <= edflt1 m x' < t' ->
  (edflt t t' x <= edflt t t' x') = (x <= x').
Proof.
case: x x' => [[]|u] [[]|v]//= /andP[tm mt] /andP[tu ut] /andP[tv vt];
do ?by [rewrite ?lexx ?tv ?vt// (le_trans tm)|rewrite ?lt_geF ?(lt_le_trans tu)].
Qed.

Lemma lt_edflt2  m t t' x x' : t <= m <= t' ->
  t < edflt1 m x < t' -> t < edflt1 m x' < t' ->
  (edflt t t' x < edflt t t' x') = (x < x').
Proof.
case: x x' => [[]|u] [[]|v]//= /andP[tm mt] /andP[tu ut] /andP[tv vt];
do ?by [rewrite ?tv ?vt// (lt_trans tu)|rewrite lt_gtF// ?(lt_trans tu)].
Qed.

Lemma edflt_le_sup m t t' x : t <= m < t' ->
  edflt1 m x <= t' -> edflt t t' x <= t'.
Proof. by case: x => [[]|u]//= /andP[tm mt]; apply: le_trans. Qed.

Lemma edflt_ge_inf m t t' x : t < m <= t' ->
  t <= edflt1 m x -> t <= edflt t t' x.
Proof. by case: x => [[]|u]//= /andP[tm mt] /le_trans->. Qed.

Lemma ge_edflt t t' t'' x :
  t <= t'' < t' -> (edflt t t' x <= t'') = (x <= t''%:x).
Proof. by case: x => [[]|u]//= /andP[tu ut]; rewrite ?tu// lt_geF. Qed.

Lemma le_edflt t t' t'' x :
  t < t'' <= t' -> (t'' <= edflt t t' x) = (t''%:x <= x).
Proof. by case: x => [[]|u]//= /andP[tu ut]; rewrite ?ut// lt_geF. Qed.

Lemma gt_edflt t t' t'' x :
  t < t'' < t' -> (edflt t t' x < t'') = (x < t''%:x).
Proof. by case: x => [[]|u]//= /andP[tu ut]; rewrite ?tu// lt_gtF//=. Qed.

Lemma lt_edflt t t' t'' x :
  t < t'' < t' -> (t'' < edflt t t' x) = (t''%:x < x).
Proof. by case: x => [[]|u]//= /andP[tu ut]; rewrite ?ut// lt_gtF. Qed.

Lemma undup_subseq (s : seq T) : subseq (undup s) s.
Proof.
elim: s => //= x s ihs; case: ifP => _; rewrite ?eqxx//.
case: (undup s) ihs => //= y u yus; case: ifP => // _.
by rewrite -(subseq_cons2 y) (@subseq_trans _ s)// subseq_cons.
Qed.

Lemma undup_sorted (s : seq T) : sorted <=%O s -> sorted <=%O (undup s).
Proof. exact: (subseq_sorted le_trans (undup_subseq s)). Qed.

Lemma all_find (s : seq T) : find predT s = 0. Proof. by elim: s. Qed.

Section lrindex_def.
Variable (x0 : T) (s : seq T).
Hypothesis s_sorted : sorted <=%O s.
(* Let leT_trans := @le_trans _ T. *)

Notation lindex t := (find (>= t) s).
Notation rindex t := (find (> t) s).

Print HintDb core.

Lemma eq_count_undup : s = flatten [seq nseq (count_mem x s) x | x <- undup s].
Proof.
rewrite (eq_sorted _ le_anti _ _ ((@perm_count_undup _ _)))//.
have := subseq_sorted le_trans (undup_subseq s) s_sorted.
elim: (undup) => //= x l ihl; rewrite path_sortedE// => /andP[/allP le_xl l_s].
elim: (count_mem _ _)=> [|/= k ihk]; rewrite ?path_min_sorted ?ihl//.
apply/allP => y; rewrite mem_cat mem_nseq.
case: eqP => [->//|_]; rewrite andbF/=.
move=> /flattenP[z /mapP[w wl ->]]; rewrite mem_nseq => /andP[_ /eqP ->].
by apply: le_xl.
Qed.

Lemma lindex_size t : (lindex t <= size s)%N. Proof. exact: find_size. Qed.
Lemma rindex_size t : (rindex t <= size s)%N. Proof. exact: find_size. Qed.

Lemma le_lrindex t : (lindex t <= rindex t)%N.
Proof. by rewrite sub_find => // u /ltW. Qed.

Lemma eq_lrindex t : t \notin s -> lindex t = rindex t.
Proof.
move=> tNs; apply: eq_in_find.
by move=> t' t's; rewrite lt_neqAle; case: eqP t's tNs => //-> ->.
Qed.

(* ---- t -- i ----- j ---- *)
Lemma lindex_le t j : (j < size s)%N -> (lindex t <= j)%N = (t <= nth x0 s j)%O.
Proof.
move=> j_lt; set i := find _ _.
case: (leqP i) => [ij|/(before_find x0)//]; have i_lt := leq_ltn_trans ij j_lt.
by rewrite (@le_trans _ _ (nth x0 s i)) ?sorted_le_nth ?nth_find ?has_find.
Qed.

Lemma lindex_gt t j : (j < size s)%N -> (j < lindex t)%N = (nth x0 s j < t)%O.
Proof. by move=> j_lt; rewrite ltnNge lindex_le// ltNge. Qed.

Lemma lindex_ge t j : (0 < j <= size s)%N ->
  (j <= lindex t)%N = (nth x0 s j.-1 < t)%O.
Proof. by case: j => //= j; apply: lindex_gt. Qed.

Lemma lindex_lt t j : (0 < j <= size s)%N ->
  (lindex t < j)%N = (t <= nth x0 s j.-1)%O.
Proof. by move=> jP; rewrite ltnNge lindex_ge// leNgt. Qed.

Lemma rindex_le t j : (j < size s)%N -> (rindex t <= j)%N = (t < nth x0 s j)%O.
Proof.
move=> j_lt; set i := find _ _.
case: (leqP i) => [ij|/(before_find x0)//]; have i_lt := leq_ltn_trans ij j_lt.
by rewrite (@lt_le_trans _ _ (nth x0 s i)) ?sorted_le_nth ?nth_find ?has_find.
Qed.

Lemma rindex_gt t j : (j < size s)%N -> (j < rindex t)%N = (nth x0 s j <= t)%O.
Proof. by move=> j_lt; rewrite ltnNge rindex_le// leNgt. Qed.

Lemma rindex_ge t j : (0 < j <= size s)%N ->
  (j <= rindex t)%N = (nth x0 s j.-1 <= t)%O.
Proof. by case: j => //= j; apply: rindex_gt. Qed.

Lemma rindex_lt t j : (0 < j <= size s)%N ->
  (rindex t < j)%N = (t < nth x0 s j.-1)%O.
Proof. by move=> jP; rewrite ltnNge rindex_ge// ltNge. Qed.

Lemma lindex_lt_size t : t \in s -> (lindex t < size s)%N.
Proof. by move=> t_in; rewrite -has_find; apply/hasP; exists t. Qed.

Lemma rindex_gt0 t : t \in s -> (rindex t > 0)%N.
Proof.
move=> /(nthP x0)[i i_lt <- {t}]; have s_gt0 := leq_trans (ltn0Sn i) i_lt.
by rewrite rindex_gt// sorted_le_nth.
Qed.

Lemma lindex_in t : t \in s -> lindex t = index t s.
Proof.
move=> ts; elim: s ts s_sorted => //= x l ihl; rewrite inE => /predU1P[<-|tl].
  by rewrite lexx eqxx.
rewrite path_sortedE // => /andP[/allP le_xl l_sorted].
by rewrite le_eqVlt eq_sym le_gtF ?le_xl// orbF ihl.
Qed.

End lrindex_def.
Hint Resolve lindex_size rindex_size le_lrindex.
Notation lindex s t := (find (>= t) s).
Notation rindex s t := (find (> t) s).

Section lrindex_theory.
Variable (s : seq T).
Hypothesis s_sorted : sorted <=%O s.

Lemma le_lindex t : all (>= t)%O s -> lindex s t = 0.
Proof. by case: s => //= y s'; case: ltgtP. Qed.

Lemma gt_lindex t : all (< t)%O s -> lindex s t = size s.
Proof. by move=> /allP/= lt_st; apply/hasNfind/hasPn=> y /lt_st; case: ltP. Qed.

Lemma lindex_rcons t u : all (<= t)%O s ->
  lindex (rcons s t) u = if (u <= t)%O then lindex s u else (size s).+1.
Proof.
move=> /allP/= le_st; rewrite -cats1 find_cat/=.
case: ifPn => [|/hasNfind->]; last by case: ifP; rewrite ?(addn0, addn1).
by move=> /hasP[z zs /le_trans->]//; apply: le_st.
Qed.

Lemma lt_rindex t : all (> t)%O s -> rindex s t = 0.
Proof. by case: s => //= y s'; case: ltgtP. Qed.

Lemma ge_rindex t : all (<= t)%O s -> rindex s t = size s.
Proof. by move=> /allP/= lt_st; apply/hasNfind/hasPn=> y /lt_st; case: ltP. Qed.

Lemma rindex_rcons t u : all (<= t)%O s ->
  rindex (rcons s t) u = if (u < t)%O then rindex s u else (size s).+1.
Proof.
move=> /allP/= le_st; rewrite -cats1 find_cat/=.
case: ifPn => [|/hasNfind->]; last by case: ifP; rewrite ?(addn0, addn1).
by move=> /hasP[z zs /lt_le_trans->]//; apply: le_st.
Qed.

End lrindex_theory.

Section lrindex_take_drop.

Lemma take_lindex s t : sorted <=%O%O s ->
  take (lindex s t) s = [seq y <- s | (y < t)%O].
Proof.
elim: s => //= a s IHs pas; rewrite -IHs ?(path_sorted pas)//.
case: leP => //= le_ta; rewrite le_lindex ?take0//.
by have /(order_path_min le_trans) := pas; apply/sub_all => y; apply: le_trans.
Qed.

Lemma drop_lindex s t : sorted <=%O%O s ->
  drop (lindex s t) s = [seq y <- s | (y >= t)%O].
Proof.
elim: s => //= a s IHs pas; rewrite -IHs ?(path_sorted pas)//.
case: leP => //= le_ta; rewrite le_lindex ?drop0//.
by have /(order_path_min le_trans) := pas; apply/sub_all => y; apply: le_trans.
Qed.

Lemma take_rindex s t : sorted <=%O%O s ->
  take (rindex s t) s = [seq y <- s | (y <= t)%O].
Proof.
elim: s => //= a s IHs pas; rewrite -IHs ?(path_sorted pas)//.
case: leP => //= le_ta; rewrite lt_rindex ?take0//.
have /(order_path_min le_trans) := pas; apply/sub_all => y.
exact: lt_le_trans.
Qed.

Lemma drop_rindex s t : sorted <=%O%O s ->
  drop (rindex s t) s = [seq y <- s | (y > t)%O].
Proof.
elim: s => //= a s IHs pas; rewrite -IHs ?(path_sorted pas)//.
case: leP => //= le_ta; rewrite lt_rindex ?drop0//.
have /(order_path_min le_trans) := pas; apply/sub_all => y.
exact: lt_le_trans.
Qed.

Variable (s : seq T).
Hypothesis s_sorted : sorted <=%O s.

Lemma lindex_count t : lindex s t = count (< t) s.
Proof.
by rewrite -size_filter -take_lindex ?size_take; case: ltngtP (lindex_size s t).
Qed.

Lemma rindex_count t : rindex s t = count (<= t) s.
Proof.
by rewrite -size_filter -take_rindex ?size_take; case: ltngtP (rindex_size s t).
Qed.

Lemma rindexEl t : rindex s t = count_mem t s + lindex s t.
Proof.
rewrite rindex_count// lindex_count// -count_predUI.
rewrite (@eq_count _ (predU _ _) (<= t)); last by move=> y /=; case: ltgtP.
rewrite (@eq_count _ (predI _ _) pred0); last by move=> y /=; case: ltgtP.
by rewrite count_pred0 addn0.
Qed.

Lemma leqif_lrindex t : lindex s t <= rindex s t ?= iff (t \notin s).
Proof.
rewrite rindexEl; apply/leqifP; case: ifPn => /count_memPn; first by move->.
by move=> /eqP cnt_neq0; rewrite addnC -ltn_psubLR ?subnn lt0n.
Qed.

Hypothesis s_uniq : uniq s.

Lemma rindex_uniq t : rindex s t = (t \in s) + lindex s t.
Proof. by rewrite rindexEl count_uniq_mem. Qed.

Lemma rindex_in t : t \in s -> rindex s t = (index t s).+1.
Proof. by move=> ts; rewrite rindex_uniq ts lindex_in. Qed.

End lrindex_take_drop.

Section ext_seq.

Variable (s : seq T).
Hypothesis s_sorted : sorted <=%O s.
Let leT_trans := @le_trans _ T.
Let le_extT_trans := @le_trans _ [porderType of ext].

Definition ext_seq := -oo :: map Fin s.
Definition ext_seqrl := -oo :: rcons (map Fin s) +oo.
Local Notation "[ i ]" := (nth +oo ext_seq i).
Local Notation "[ i ]'" := (nth +oo ext_seqrl i).
Definition sprev t := [lindex s t].
Definition snext t := [(rindex s t).+1].
Definition aprev t := [rindex s t].
Definition anext t := [(lindex s t).+1].

Lemma nth_extrl i : [i] = [i]'.
Proof.
case: i => [|i]//=; rewrite nth_rcons size_map.
by case: ltngtP => [|i_gt|->]//=; rewrite nth_default// ?size_map// ltnW.
Qed.

Lemma size_ext_seq : size ext_seqrl = (size s).+2.
Proof. by rewrite /ext_seq/= size_rcons size_map. Qed.

Lemma subseq_extrl : subseq ext_seq ext_seqrl.
Proof. by rewrite subseq_cons2 -cats1 prefix_subseq. Qed.

Lemma ext_seqrl_sorted : sorted <=%O ext_seqrl.
Proof.
rewrite /= path_min_sorted ?sorted_map//; last first.
  by apply/allP => x; rewrite ge_xmin.
rewrite -(rev_sorted >=%O) rev_rcons/= path_min_sorted; last first.
  by apply/allP => x /=; rewrite le_xmax.
by rewrite rev_sorted ?sorted_map.
Qed.
Hint Resolve ext_seqrl_sorted.

Definition ext_seq_sorted :=
  subseq_sorted le_trans subseq_extrl ext_seqrl_sorted.
Hint Resolve ext_seq_sorted.

Lemma eq_from_lindex i j x : [i] < x <= [i.+1] -> [j] < x <= [j.+1] -> i = j.
Proof.
wlog lt_ij : i j / (i < j)%N => [hw ti tj|/andP[it ti] /andP[jt tj]].
  by have [/hw->//|/hw->//|//] := ltngtP i j.
have [i_le|i_ge] := leqP j (size s); last first.
  by have := lt_le_trans jt tj; rewrite nth_default/= ?size_map// ltNge le_xmax.
suff /(le_trans ti) /le_lt_trans /(_ jt) : [i.+1] <= [j] by rewrite ltxx.
by rewrite sorted_le_nth -?topredE//= ?size_map// ?ltnS (leq_trans lt_ij).
Qed.

Lemma eq_from_rindex i j x : [i] <= x < [i.+1] -> [j] <= x < [j.+1] -> i = j.
Proof.
wlog lt_ij : i j / (i < j)%N => [hw ti tj|/andP[it ti] /andP[jt tj]].
  by have [/hw->//|/hw->//|//] := ltngtP i j.
have [i_le|i_ge] := leqP j (size s); last first.
  by have := le_lt_trans jt tj; rewrite nth_default/= ?size_map// ltNge le_xmax.
suff /(lt_le_trans ti) /lt_le_trans/(_ jt) : [i.+1] <= [j] by rewrite ltxx.
by rewrite sorted_le_nth -?topredE//= ?size_map// ?ltnS (leq_trans lt_ij).
Qed.

Hypothesis s_uniq : uniq s.

Let s_lt_sorted : sorted <%O s.
Proof. by rewrite lt_sorted_uniq_le s_uniq. Qed.
Hint Resolve le_trans lt_trans.

Lemma ext_seqrl_uniq : uniq ext_seqrl.
Proof.
rewrite /= ?rcons_uniq ?mem_rcons map_inj_uniq ?s_uniq ?andbT//=.
by apply/andP; split; apply/negP=> /mapP[].
Qed.
Hint Resolve ext_seqrl_uniq.

Definition ext_seq_uniq := subseq_uniq subseq_extrl ext_seqrl_uniq.
Hint Resolve ext_seq_uniq.

Lemma ext_seqrl_lt_sorted : sorted <%O ext_seqrl.
Proof. by rewrite lt_sorted_uniq_le ext_seqrl_uniq. Qed.
Hint Resolve ext_seqrl_lt_sorted.

Definition ext_seq_lt_sorted :=
  subseq_sorted lt_trans subseq_extrl ext_seqrl_lt_sorted.
Hint Resolve ext_seq_lt_sorted.

Lemma le_nth_ext : {in [pred i | (i <= (size s).+1)%N] &,
  {mono nth +oo ext_seq : i j / (i <= j)%N >-> i <= j}}.
Proof.
apply: le_mono_in => i j i_s j_s; rewrite !nth_extrl.
by apply: (sorted_lt_nth lt_trans _ _); rewrite // inE/= size_rcons size_map.
Qed.

Lemma lt_nth_ext : {in [pred i | (i <= (size s).+1)%N] &,
  {mono nth +oo ext_seq : i j / (i < j)%N >-> i < j}}.
Proof. exact/leW_mono_in/le_nth_ext. Qed.

Lemma anextE t : anext t = if t \in s then t%:x else snext t.
Proof.
rewrite /anext /snext; case: ifPn => [ts|tNs]; last by rewrite eq_lrindex.
by rewrite lindex_in/= ?(nth_map t) ?index_mem ?nth_index.
Qed.

Lemma aprevE t : aprev t = if t \in s then t%:x else sprev t.
Proof.
rewrite /aprev /sprev; case: ifPn => [ts|tNs]; last by rewrite eq_lrindex.
by rewrite ?rindex_uniq/= ?ts// [[_]]anextE ?ts.
Qed.

Lemma eq_in_anext t : t \in s -> t%:x = anext t.
Proof. by rewrite anextE; case: ifP. Qed.

Lemma eq_in_aprev t : t \in s -> t%:x = aprev t.
Proof. by rewrite aprevE; case: ifP. Qed.

Lemma in_sprev t : sprev t \in -oo :: map Fin s.
Proof.
rewrite /sprev /= in_cons; case: (lindex _ _) (lindex_size s t) => //= n n_lt.
by rewrite (nth_map t)// mem_map// mem_nth.
Qed.

Lemma in_aprev t : aprev t \in -oo :: map Fin s.
Proof.
by rewrite aprevE; case: ifPn => [ts|_]; rewrite ?in_sprev// in_cons mem_map.
Qed.

Lemma in_snext t : snext t \in +oo :: map Fin s.
Proof.
rewrite /snext /= in_cons; case: (ltnP (rindex s t) (size (map Fin s))).
  by move=> /mem_nth->; rewrite orbT.
by move=> /(nth_default _)->.
Qed.

Lemma in_anext t : anext t \in +oo :: map Fin s.
Proof.
by rewrite anextE; case: ifPn => [ts|_]; rewrite ?in_snext// in_cons mem_map.
Qed.

Lemma sprev_snextP t : sprev t < t%:x < snext t.
Proof.
rewrite /sprev /snext; have [ts|tNs] := boolP (t \in s).
  rewrite [X in _ < X]eq_in_anext// [_%:x as X in X < _]eq_in_aprev//.
  by rewrite !lt_nth_ext ?leqnn ?inE ?ltnS ?leqW.
rewrite /snext /sprev/=; apply/andP; split; last first.
  case: (ltngtP (size _)) (rindex_size s t) => [//|i_lt|<-] _; last first.
    by rewrite nth_default//= ?size_map.
  by rewrite /= (nth_map t)// ltEext/= nth_find// has_find.
have /= := @before_find _ t (>= t) s (lindex s t).-1; rewrite -/(lindex s t).
case: (lindex _ _) (lindex_size s t) => //= i i_lt  /(_ (ltnSn _))/negbT.
by rewrite (nth_map t)// ltEext/= -ltNge.
Qed.
Hint Resolve sprev_snextP.

Lemma gt_sprev t : sprev t < t%:x. Proof. by case/andP: (sprev_snextP t). Qed.
Hint Resolve gt_sprev.

Lemma ge_sprev t : sprev t <= t%:x. Proof. by rewrite ltW. Qed.
Hint Resolve ge_sprev.

Lemma geif_aprev t : aprev t <= t%:x ?= iff (t \in s).
Proof.
by apply/leifP; rewrite aprevE ?(fun_if, if_arg) eqxx gt_sprev; case: ifP => ->.
Qed.
Hint Resolve geif_aprev.

Lemma ge_aprev t : aprev t <= t%:x. Proof. by rewrite geif_aprev. Qed.
Hint Resolve ge_aprev.

Lemma lt_snext t : t%:x < snext t. Proof. by case/andP: (sprev_snextP t). Qed.
Hint Resolve lt_snext.

Lemma le_snext t : t%:x <= snext t. Proof. by rewrite ltW. Qed.
Hint Resolve le_snext.

Lemma leif_anext t : t%:x <= anext t ?= iff (t \in s).
Proof.
by apply/leifP; rewrite anextE ?(fun_if, if_arg) eqxx lt_snext; case: ifP => ->.
Qed.
Hint Resolve leif_anext.

Lemma le_anext t : t%:x <= anext t. Proof. by rewrite leif_anext. Qed.
Hint Resolve le_anext.

Lemma eq_lindex t u : sprev t < u%:x <= anext t -> lindex s t = lindex s u.
Proof. by move=> /eq_from_lindex; apply; rewrite ?gt_sprev ?le_anext. Qed.

Lemma eq_rindex t u : aprev t <= u%:x < snext t -> rindex s t = rindex s u.
Proof. by move=> /eq_from_rindex; apply; rewrite ?ge_aprev ?lt_snext. Qed.

Lemma lt_sprev_anext t : sprev t < anext t.
Proof. by have := lt_le_trans (gt_sprev t) (le_anext t). Qed.
Hint Resolve lt_sprev_anext.

Lemma lt_aprev_snext t : aprev t < snext t.
Proof. by have := le_lt_trans (ge_aprev t) (lt_snext t). Qed.
Hint Resolve lt_aprev_snext.

Lemma lt_sprev_snext t : sprev t < snext t.
Proof. by have := lt_trans (gt_sprev t) (lt_snext t). Qed.
Hint Resolve lt_sprev_snext.

Section sorted_mono.
Variables (d' : unit) (T' : orderType d) (t0 : T')
  (s' : seq T') (ss : sorted <%O s') (ssle : sorted <=%O s').
Definition total_sorted_le_nthW := sorted_le_nth (@le_trans _ _) (@lexx _ _) t0 ssle.
Let sorted_lt_nthW := sorted_lt_nth (@lt_trans _ _) t0 ss.
Definition total_sorted_le_nth := le_mono_in sorted_lt_nthW.
Definition total_sorted_lt_nth := leW_mono_in total_sorted_le_nth.
End sorted_mono.

Lemma lindex_eq i : {in [pred t | [i] < t%:x <= [i.+1]], forall t, lindex s t = i}.
Proof. by move=> t; apply: eq_from_lindex; rewrite gt_sprev le_anext. Qed.
Print HintDb core.
Lemma lindex_eq' u : {in [pred t | sprev u < t%:x <= u%:x],
  forall t, lindex s t = lindex s u}.
Proof.
move=> t; rewrite inE => /andP[ut tu]; apply: eq_lindex.
by rewrite  le_anext.
Qed.

Lemma rindex_eq i : {in [pred t | [i] <= t%:x < [i.+1]], forall t, rindex s t = i}.
Proof. by move=> t; apply: eq_from_rindex; rewrite ge_aprev lt_snext. Qed.

Lemma ext_inF i : {in [pred t | [i] < t%:x < [i.+1]], forall t, t \in s = false}.
Proof.
move=> t; rewrite inE => /andP[t_gt t_lt]; have := t_lt.

rewrite -(@lindexE i t); last by rewrite inE t_gt ltW.
by apply: contraTF => /mem_rnext->; rewrite ltxx.
Qed.

Lemma lrindex_notin i :
  {in [pred t | [i] < t%:x < [i.+1]], forall t, t \notin s}.
Proof. by move=> x /lindex_inF->. Qed.

Lemma lindex_next t tnext : rnext t = tnext%:x -> lindex s tnext = lindex s t.
Proof. by move=> sneq; apply: lindexE; rewrite inE -sneq lexx andbT. Qed.

End ext_seq.
End lindex.

Bind Scope ext_scope with ext.
Notation edflt1 t := (edflt t t).
Notation "s `[ i ]" := (nth +oo%x (ext_seq s) i) : ext_scope.
Notation rprev s t := s`[lindex s t].
Notation rnext s t := s`[(lindex s t).+1].
Hint Resolve lrindex_size lrindexP gt_rprev ge_rprev le_rnext lt_rprev_rnext.
