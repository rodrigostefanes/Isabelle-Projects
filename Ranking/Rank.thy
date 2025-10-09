theory Rank

imports Main "HOL-Library.FuncSet" HOL.List

begin

(************************ Rank ************************)

fun rank :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
"rank  d [] = 0"
|
"rank  d (x#xs) = x*d^(length xs)+rank d xs"



(*The following condition, when true, assure us that a list of size n is a member of F^n_q*)
definition cond_rank :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "cond_rank d xs \<equiv> (\<forall> i. ( i< length xs \<longrightarrow> (xs! i <d)) )\<and> d>1"



(*The following lemma assure us that the rank always give us a number between 0 and d^(length xs)-1*)
lemma rank_image : "(cond_rank d xs) \<Longrightarrow> ((rank d xs) < d^(length xs))"
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




(************************ Unrank ************************)


(*Function*) 

fun unrank :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where 
  "unrank 0 d k = Nil"
|
"unrank (Suc n) d k = (unrank n d (k div d)) @ [k mod d]"

(*Condition*)

definition cond_unrank :: " nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "cond_unrank n d k \<equiv> (k< (d^n))\<and> d> 1"

(*As an example, let us calculate the element 45684 of the set F^7_5*)

value "unrank 7 5 45684"


(************************ Rank and Unrank ************************)

(*Let us now prove that Rank and Unrank are inverse of each other*)

(*Before that, we will prove that the rank n d xs always give a number less then d^n and 
that unrank n d k always give a list of length n with entries less then d so that it is allowed
to compose the rank with unrank and unrank with rank*)


(*Inudction on xs*)

lemma rank_image2 : "(cond_rank n d xs) \<Longrightarrow> (rank n d xs < d^n)"
proof (induction xs)
  case Nil
  then show ?case
    by (simp add: cond_rank_def)
next
  case (Cons a xs)
  then show ?case
    by (simp add: cond_rank_def)


(*Induction on n)*)

lemma rank_image : "(cond_rank n d xs) \<Longrightarrow> (rank n d xs < d^n)"
proof (induction n)
  case 0
  then show "(cond_rank 0 d xs) \<Longrightarrow> (rank 0 d xs < d^0)" 
    by (simp add: cond_rank_def)
next
  case (Suc n)
  then show "(cond_rank (Suc n) d xs) \<Longrightarrow> (rank (Suc n) d xs < d^(Suc n))" 
  proof - 
    assume 1 : "cond_rank (Suc n) d xs"
    have 2 : "length xs = Suc n"
      using 1 by (simp add: cond_rank_def)
    obtain x ys where 3 : "xs = x # ys"
      using 2 by (induction xs) auto
    have 4 : "rank (Suc n) d xs = x*d^(length ys) + rank (Suc n) d ys"
      using 3 by simp



    have "rank n d xs < d ^ n" by 






(*length xs = Suc n \<and> (\<forall>i<length xs. xs ! i < d) \<and> Suc 0 < d \<Longrightarrow> rank (Suc n) d xs < d * d ^ n*)
(*theorem unrank_rank_inverse : "(cond_rank n d xs) \<Longrightarrow>  (unrank n d (rank n d xs) = xs)"*)


  
 



end