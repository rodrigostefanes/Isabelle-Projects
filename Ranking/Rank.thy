theory Rank

imports Main "HOL-Library.FuncSet" HOL.List

begin


(************************ Rank ************************)

fun rank :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
"rank  d [] = 0"
|
"rank  d (x#xs) = x+ d*(rank d xs)"

definition cond_rank :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "cond_rank d xs \<equiv> (\<forall> i. ( i< length xs \<longrightarrow> (xs! i \<le>d-1)) )\<and> d>1"

value "rank 5 [1,3,4,2,2,2,1]"

(************************ Unrank ************************)

fun unrank :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where 
  "unrank 0 d k = Nil"
|
"unrank (Suc n) d k = (k mod d) # (unrank n d (k div d))"


definition cond_unrank :: " nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "cond_unrank n d k \<equiv> (k< (d^n))\<and> d> 1"

value "unrank 7 5 23491"

(************************ Lemmas ************************)


(*lemma rank_image : "(cond_rank d xs) \<Longrightarrow> (cond_unrank (length xs) d (rank d xs))"
proof (induction xs arbitrary: d)
  case Nil
  then show ?case
    by (simp add: cond_rank_def cond_unrank_def)
next
  case (Cons a xs)
  then show ?case
  proof - 
    assume 1: "cond_rank d (a#xs)"
    have 2: "cond_rank d xs" using 1 and cond_rank_def by auto
    have 3: "rank d (a#xs) = a+ d*(rank d xs)" by simp
    have 4: "cond_unrank (length xs) d (rank d xs)" using 2 and Cons.IH and cond_unrank_def by simp
    have 5: "rank d xs \<le> (d^(length xs)-1)" using 3 by (metis "4" add_le_imp_le_diff cond_unrank_def less_iff_succ_less_eq)
    have 6: "rank d (a#xs) \<le> a + d*(d^(length xs)-1)" using 4 and 5 by simp
    have 7: "a \<le> d-1" using 1 and cond_rank_def by auto
    have 8: "rank d (a#xs) \<le> (d-1)+ d*(d^(length xs)-1)" using 6 and 7 by (simp add: add_le_mono)
    have 9: "(d-1)+d*(d^(length xs)-1) = d^((length xs)+1)-1" by (smt (verit) Nat.add_diff_assoc2 add_cancel_right_left diff_is_0_eq diff_mult_distrib2 le_add2 le_add_diff_inverse less_add_same_cancel2 mult.right_neutral
        order.order_iff_strict power_add power_commutes power_less_one_iff power_one_right self_le_power zero_less_diff) (*Really?*)
    have 10: "rank d (a#xs)\<le> d^((length xs)+1) -1" using 8 and 9 by simp
    have 11: "cond_unrank (length (a#xs)) d (rank d (a#xs))" using 10 by (metis "2" Nat.le_diff_conv2 Suc_eq_plus1_left add.commute cond_rank_def cond_unrank_def length_Cons less_iff_succ_less_eq one_le_power
        order_less_imp_le)
    show ?thesis using 11 by simp
  qed
qed*)


(*These two lemmas guarantees that it is allowed to compose unrank with rank and rank with unrank
provided that the conditions holds*)
lemma rank_image : "(cond_rank d xs) \<Longrightarrow> ((rank d xs) \<le> (d^(length xs))-1)"
proof (induction xs arbitrary: d)
  case Nil
  then show ?case
    by (simp add: cond_rank_def)
next
  case (Cons a xs)
  then show ?case
  proof - 
    assume 1: "cond_rank d (a#xs)"
    have 2: "cond_rank d xs" using 1 and cond_rank_def by auto
    have 3: "rank d (a#xs) = a+ d*(rank d xs)" by simp
    have 4: "rank d xs \<le> (d^(length xs)-1)" using 2 and Cons.IH by simp
    have 5: "rank d (a#xs) \<le> a + d*(d^(length xs)-1)" using 3 and 4 by simp
    have 6: "a \<le> d-1" using 1 and cond_rank_def by auto
    have 7: "rank d (a#xs) \<le> (d-1)+ d*(d^(length xs)-1)" using 5 and 6 by (simp add: add_le_mono)
    have 8: "(d-1)+d*(d^(length xs)-1) = d^((length xs)+1)-1" by (smt (verit) Nat.add_diff_assoc2 add_cancel_right_left diff_is_0_eq diff_mult_distrib2 le_add2 le_add_diff_inverse less_add_same_cancel2 mult.right_neutral
        order.order_iff_strict power_add power_commutes power_less_one_iff power_one_right self_le_power zero_less_diff) (*Really?*)
    have 9: "rank d (a#xs)\<le> d^((length xs)+1) -1" using 7 and 8 by simp
    show ?thesis using 9 by simp
  qed
qed


lemma unrank_image : "cond_unrank n d k \<Longrightarrow> cond_rank d (unrank n d k)"
proof (induction n arbitrary: d k)
  case 0
  then show ?case
    by (simp add: cond_rank_def cond_unrank_def)
next
  case (Suc n)
  then show ?case
  proof -
    assume 1: "cond_unrank (Suc n) d k"
    have 2: "unrank (Suc n) d k = (k mod d)# (unrank n d (k div d))" by simp
    have 3: "k mod d \<le> d-1" by (metis "1" One_nat_def Suc_pred bot_nat_0.not_eq_extremum cond_unrank_def less_Suc_eq_le mod_less_divisor not_one_less_zero)
    have 4: "cond_unrank n d (k div d)" using 1 by (simp add: cond_unrank_def less_mult_imp_div_less mult.commute)
    have 5: "cond_rank d (unrank n d (k div d))" using 4 and Suc.IH by simp
    have 6: "(\<forall> i. ( i< length (unrank n d (k div d)) \<longrightarrow> ((unrank n d (k div d))! i \<le>d-1)))" using 5 and cond_rank_def by blast
    have 7: "(\<forall> i. ( i< length (unrank (Suc n) d k) \<longrightarrow> ((unrank (Suc n) d k)! i \<le>d-1)))" using 2 and 3 and 6 by (simp add: nth_Cons')
    have 8: "cond_rank d (unrank (Suc n) d k)" using 1 and 7 and cond_rank_def cond_unrank_def by blast
    show ?thesis using 8 by simp
  qed
qed






(*These two lemmas are necessary for proving the main theorems*)

lemma unrank_rank_inverse_aux1: "cond_rank d (a#xs) \<Longrightarrow> ((rank d (a#xs)) mod d = a)"
proof (induction xs arbitrary: a d)
  case Nil
  then show ?case
  proof - 
    assume 1: "cond_rank d (a#[])"
    have 2: "rank d (a#[]) = a" by simp
    have 3: "a\<le> d-1" using 1 by (simp add: cond_rank_def)
    have 4: "a mod d = a" using 3 and mod_if by fastforce
    show ?thesis using 4 by simp
  qed
next
  case (Cons b ys)
  then show ?case
  proof -
    assume 1: "cond_rank d (a#(b#ys))"
    have 2: "rank d (a#(b#ys)) = a + d*(rank d (b#ys))" by simp
    have 3: "a\<le> d-1" using 1 unfolding cond_rank_def by auto
    have 4: "(a + d*(rank d (b#ys))) mod d = a" by (metis "3" Suc_eq_plus1 Suc_eq_plus1_left add_cancel_right_right gr0_conv_Suc leD le_add2 less_imp_diff_less linorder_less_linear
        linordered_semidom_class.add_diff_inverse mod_div_decomp mod_less mod_mult_self2)
    have 5: "(rank d (a#(b#ys))) mod d = a" using 2 and 4 by simp
    show ?thesis using 5 by simp
  qed
qed

lemma unrank_rank_inverse_aux2: "cond_rank d (a#xs) \<Longrightarrow> ((rank d (a#xs)) div d = rank d xs)"
proof (induction xs arbitrary: a d)
  case Nil
  then show ?case by (metis add.comm_neutral mod_eq_self_iff_div_eq_0 mult_0_right rank.simps(1,2) unrank_rank_inverse_aux1)
next
  case (Cons b ys)
  then show ?case
  proof -
    assume 1: "cond_rank d (a#(b#ys))"
    have 2: "rank d (a#(b#ys)) = a + d*(rank d (b#ys))" by simp
    have 3: "a\<le> d-1" using 1 unfolding cond_rank_def by auto
    have 4: "(d*(rank d (b#ys))) div d = rank d (b#ys)" using 1 by (simp add: cond_rank_def)
    have 5: "(rank d (a#(b#ys))) div d = (rank d (b#ys))" using 2 and 3 and 4 by (metis Suc_eq_plus1_left add.right_neutral add_diff_cancel_left' div_greater_zero_iff div_mult_self2 gr0_conv_Suc not_less_eq_eq) 
    show ?thesis using 5 by simp
  qed
qed



(************************ Theorems ************************)


theorem unrank_rank_inverse : "(cond_rank d xs) \<Longrightarrow>  (cond_unrank (length xs) d (rank d xs))\<and>(unrank (length xs) d (rank d xs) = xs)"
proof (induction xs arbitrary: d)
  case Nil
  then show ?case by (simp add: cond_rank_def cond_unrank_def)
next
  case (Cons a xs)
  then show ?case
  proof - 
    assume 1 : "cond_rank d (a#xs)"
    have 2: "cond_unrank (length (a#xs)) d (rank d (a#xs))" using 1 and rank_image by (meson Nat.le_diff_conv2 cond_rank_def cond_unrank_def less_iff_succ_less_eq less_imp_le_nat one_le_power)
    have 3: "unrank(length (a#xs)) d (rank d (a#xs)) = ((rank d (a#xs)) mod d) # (unrank (length xs) d ((rank d (a#xs))div d))" by simp
    have 4: "(rank d (a#xs)) mod d = a" using 1 and unrank_rank_inverse_aux1 by simp
    have 5: "((rank d (a#xs))div d) = rank d xs" using 1 and unrank_rank_inverse_aux2 by simp
    have 6: " (unrank (length xs) d ((rank d (a#xs))div d)) = (unrank (length xs) d ( rank d xs))" using 5 by simp
    have 7: "cond_rank d xs" using 1 and cond_rank_def by auto
    have 8: "(unrank (length xs) d ( rank d xs)) = xs" using 7 and Cons.IH by simp
    have 9: "unrank(length (a#xs)) d (rank d (a#xs)) = (a # xs)" using  4 and 6 and 8 by simp
    show ?thesis using 2 and 9 by simp
  qed
qed




end