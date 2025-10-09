theory Rank2

imports Main "HOL-Library.FuncSet" HOL.List

begin


fun rank :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
"rank  d [] = 0"
|
"rank  d (x#xs) = x*d^(length xs)+rank d xs"

definition cond_rank :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "cond_rank d xs \<equiv> (\<forall> i. ( i< length xs \<longrightarrow> (xs! i <d)) )\<and> d>1"

value "rank 5 [1,3,4,2,2,2,1]"

lemma rank_image [simp]: "(cond_rank d xs) \<Longrightarrow> ((rank d xs) < d^(length xs))"
proof (induction xs arbitrary: d)
  case Nil
  then show ?case
    by (simp add: cond_rank_def)
next
  case (Cons a xs)
  then show ?case
  proof - 
    assume 1: "cond_rank d (a#xs)"
    have 2:  "rank d (a#xs) = a* d^(length xs) + rank d xs" by simp
    have 3: "cond_rank d xs" using 1 and cond_rank_def by auto
    have 4: "rank d xs < d^(length xs)" using 3 and Cons.IH by simp
    have 5: "rank d (a#xs) < (a+1)* d^(length xs)" using 2 and 4 by simp
    have 6: "a+1\<le> d" using 1 and cond_rank_def by auto
    have 7: " (a+1)* d^(length xs) \<le> d*d^(length xs)" using 6 and mult_le_cancel2 by blast (*sledgehammer gave me the call to use mult_le_cancel2*)
    have 8: "rank d (a#xs) < d^(length xs +1)" using 5 and 7 by simp
    have 9: "rank d (a#xs) < d^(length (a#xs))" using 8 by simp
    show ?thesis using 9.
  qed
qed


(*Unrank*)

fun unrank :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where 
  "unrank 0 d k = Nil"
|
"unrank (Suc n) d k =  (unrank n d (k div d)) @ [k mod d]"


definition cond_unrank :: " nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "cond_unrank n d k \<equiv> (k< (d^n))\<and> d> 1"

value "unrank 7 5 23491"

(*Now let us prove that the rank and unrank are inverse of each other*)


 
theorem unrank_rank_inverse : "(cond_rank d xs) \<Longrightarrow>  (unrank (length xs) d (rank d xs) = xs)"
proof (induction xs arbitrary: d)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
  proof - 


end