theory GLn_roundtrip_general
imports
  Main
  "HOL-Library.List_Lexorder"
  "HOL-Library.Multiset"
  HOL.Power
begin


type_synonym vec = "nat list"
type_synonym mat = "vec list"

(* ------------------------------------------------------------------ *)
(* Utils executáveis *)
(* ------------------------------------------------------------------ *)

fun pow :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "pow _ 0 = 1"
| "pow x (Suc n) = x * pow x n"

fun prod_list :: "nat list \<Rightarrow> nat" where
  "prod_list [] = 1"
| "prod_list (x#xs) = x * prod_list xs"

fun all_vecs_of_len :: "nat \<Rightarrow> nat \<Rightarrow> vec list" where
  "all_vecs_of_len _ 0 = [[]]"
| "all_vecs_of_len q (Suc n) =
      concat (map (\<lambda>x. map (\<lambda>v. x#v) (all_vecs_of_len q n)) [0..<q])"

(* ------------------------------------------------------------------ *)
(* Aritmética vetorial modular e eliminação de Gauss (executável)      *)
(* ------------------------------------------------------------------ *)

fun vec_map2 :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> vec \<Rightarrow> vec \<Rightarrow> vec" where
  "vec_map2 f [] [] = []"
| "vec_map2 f (x#xs) (y#ys) = f x y # vec_map2 f xs ys"

fun vec_add :: "nat \<Rightarrow> vec \<Rightarrow> vec \<Rightarrow> vec" where
  "vec_add p v1 v2 = vec_map2 (\<lambda>a b. (a + b) mod p) v1 v2"

fun vec_scal_mul :: "nat \<Rightarrow> nat \<Rightarrow> vec \<Rightarrow> vec" where
  "vec_scal_mul p a [] = []"
| "vec_scal_mul p a (x#xs) = ((a * x) mod p) # vec_scal_mul p a xs"

fun is_zero_row :: "vec \<Rightarrow> bool" where
  "is_zero_row r = (\<forall>x\<in>set r. x = 0)"

fun transpose_cols :: "vec list \<Rightarrow> vec list" where
  "transpose_cols [] = []"
| "transpose_cols ([] # _) = []"
| "transpose_cols cs = map (\<lambda>i. map (\<lambda>c. c ! i) cs) [0..<length (hd cs)]"

fun map_index :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_index f [] = []"
| "map_index f (x#xs) = f 0 x # map_index (\<lambda>i y. f (Suc i) y) xs"

(* ------------------------------------------------------------------ *)
(* Encontrar inverso multiplicativo modular (brute force) *)
(* ------------------------------------------------------------------ *)

fun find_inv_exec :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "find_inv_exec p 0 = 0"
| "find_inv_exec p a =
     (if a = 0 then 0
      else (case filter (\<lambda>x. (a * x) mod p = 1) [1..<p] of
              [] \<Rightarrow> 0
            | x#_ \<Rightarrow> x))"

(* ------------------------------------------------------------------ *)
(* Operações sobre matrizes para eliminação de Gauss *)
(* ------------------------------------------------------------------ *)
fun swap_list :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "swap_list xs i j =
     list_update (list_update xs i (xs ! j)) j (xs ! i)"



fun normalize_row :: "nat \<Rightarrow> vec \<Rightarrow> nat \<Rightarrow> vec" where
  "normalize_row p row col =
     (let a = row ! col;
          inv = find_inv_exec p a
      in vec_scal_mul p inv row)"

fun find_pivot_from :: "nat \<Rightarrow> vec list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "find_pivot_from p rows col start =
     (let idxs = [start..<length rows] in
      (case filter (\<lambda>i. i < length rows \<and> (rows ! i) ! col \<noteq> 0) idxs of
         [] \<Rightarrow> None | j#_ \<Rightarrow> Some j))"

fun eliminate_step :: "nat \<Rightarrow> vec list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> vec list" where
  "eliminate_step p rows col pivot_idx =
     (let pivot = normalize_row p (rows ! pivot_idx) col in
      map_index (\<lambda>i r. if i = pivot_idx then pivot
                       else let factor = r ! col in
                            vec_add p r (vec_scal_mul p (p - factor) pivot)) rows)"

function gauss_rows_rec :: 
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list list \<Rightarrow> nat list list" 
where
  "gauss_rows_rec p m n col rows =
     (if col \<ge> n \<or> col \<ge> m then rows
      else (case find_pivot_from p rows col col of
              None \<Rightarrow> gauss_rows_rec p m n (col + 1) rows
            | Some pr \<Rightarrow>
                gauss_rows_rec p m n (col + 1)
                  (eliminate_step p (if pr \<noteq> col then swap_list rows pr col else rows) col col)))"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(p, m, n, col, rows). n - col)") auto



fun gauss_rows :: "nat \<Rightarrow> vec list \<Rightarrow> vec list" where
  "gauss_rows p rows =
     (let m = length rows;
          n = if rows = [] then 0 else length (hd rows)
      in gauss_rows_rec p m n 0 rows)"

fun rank_cols :: "nat \<Rightarrow> mat \<Rightarrow> nat" where
  "rank_cols p cols =
     (let rows = transpose_cols cols;
          eche = gauss_rows p rows
      in length (filter (\<lambda>r. \<not> is_zero_row r) eche))"
definition independent_cols :: "nat \<Rightarrow> mat \<Rightarrow> bool" where
  "independent_cols p cols = (rank_cols p cols = length cols)"


(* ------------------------------------------------------------------ *)
(* Funções concretas UL_local / RL_local *)
(* ------------------------------------------------------------------ *)

fun vectors_outside_span_concrete :: "nat \<Rightarrow> mat \<Rightarrow> vec list" where
  "vectors_outside_span_concrete p U =
     (let n = if U = [] then 0 else length (hd U) in
      filter (\<lambda>v. independent_cols p (U @ [v])) (all_vecs_of_len p n))"

fun UL_local_concrete :: "nat \<Rightarrow> mat \<Rightarrow> nat \<Rightarrow> vec" where
  "UL_local_concrete p U k =
     (let vs = vectors_outside_span_concrete p U in
      if k < length vs then vs ! k else [])"

fun find_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "find_index x [] = None"
| "find_index x (y#ys) = (if x = y then Some 0 else (case find_index x ys of None \<Rightarrow> None | Some n \<Rightarrow> Some (n+1)))"

fun RL_local_concrete :: "nat \<Rightarrow> mat \<Rightarrow> vec \<Rightarrow> nat option" where
  "RL_local_concrete p U v =
     find_index v (vectors_outside_span_concrete p U)"


(* ------------------------------------------------------------------ *)
(* Concrete test for UL_local_concrete / RL_local_concrete *)
(* ------------------------------------------------------------------ *)

definition p_test :: nat where "p_test = 2"

(* Example vectors *)
definition v1 :: vec where "v1 = [1,0]"
definition v2 :: vec where "v2 = [0,1]"

(* Matrix U *)
definition U_test :: mat where "U_test = [v1]"

(* Compute vectors outside span of U_test *)
value "vectors_outside_span_concrete p_test U_test"
(* Expected: [[0,1],[1,1]] 
   - [0,1] is linearly independent from [1,0]
   - [1,1] is also independent *)

(* UL_local_concrete examples *)
value "UL_local_concrete p_test U_test 0"  (* Expected: [0,1] *)
value "UL_local_concrete p_test U_test 1"  (* Expected: [1,1] *)

(* RL_local_concrete examples *)
definition v_test1 :: vec where "v_test1 = [0,1]"
definition v_test2 :: vec where "v_test2 = [1,1]"

value "RL_local_concrete p_test U_test v_test1"  (* Expected: 0 *)
value "RL_local_concrete p_test U_test v_test2"  (* Expected: 1 *)

definition p2 :: nat where "p2 = 7"
definition U_test2 :: "vec list" where
  "U_test2 = [[1,0,0,0], [0,1,0,0]]"

value "UL_local_concrete p2 U_test2 0"
value "UL_local_concrete p2 U_test2 5"
value "RL_local_concrete p2 U_test2 [2,3,1,0]"
value "UL_local_concrete p2 U_test2 822"

end
