theory Task imports Main begin


subsection \<open>Part I\<close>

\<comment> \<open>If @{term foldr} over conjuctions evaluates to @{term True}, the initial value is @{term True}.\<close>
lemma foldr_conj_init: \<open>foldr (\<lambda> x b. P x \<and> b) xs y \<Longrightarrow> y\<close>
proof (induction xs arbitrary: y)
  case Nil
  assume \<open>foldr (\<lambda> x b. P x \<and> b) [] y\<close>
  then show \<open>y\<close> by simp
next
  case (Cons x xs)
  assume IH: \<open>\<And>y. foldr (\<lambda> x b. P x \<and> b) xs y \<Longrightarrow> y\<close>
  assume \<open>foldr (\<lambda> x b. P x \<and> b) (x # xs) y\<close>
  then have \<open>P x \<and> (foldr (\<lambda> x b. P x \<and> b) xs y)\<close> by simp
  then have \<open>foldr (\<lambda> x b. P x \<and> b) xs y\<close> by blast
  moreover with IH have \<open>foldr (\<lambda> x b. P x \<and> b) xs y \<Longrightarrow> y\<close> by blast
  ultimately show \<open>y\<close> by blast
qed
  
\<comment> \<open>@{term foldr} over conjuctions with initial value @{term True} evaluates to @{term True} if an only if all conjuncts are @{term True}.\<close>
lemma foldr_conj_prop:
	\<open>foldr (\<lambda> x b. P x \<and> b) xs True \<longleftrightarrow> (\<forall> x \<in> set xs. P x)\<close>
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons y ys)
  assume IH: \<open>foldr (\<lambda> x b. P x \<and> b) ys True \<longleftrightarrow> (\<forall> x \<in> set ys. P x)\<close>
  have \<open>foldr (\<lambda> x b. P x \<and> b) (y # ys) True \<longleftrightarrow> (P y) \<and> (foldr (\<lambda> x b. P x \<and> b) ys True)\<close> by simp
  moreover have \<open>(\<forall> x \<in> set (y # ys). P x) \<longleftrightarrow> (P y) \<and> (\<forall> x \<in> set ys. P x)\<close> by simp
  moreover have \<open>((P y) \<and> (foldr (\<lambda> x b. P x \<and> b) ys True)) \<longleftrightarrow> ((P y) \<and> (\<forall> x \<in> set ys. P x))\<close> using IH by blast
  then show ?case by simp
qed


subsection \<open>Part II\<close>

\<comment> \<open>Pick the given number of first elements of the given list.
The function uses recursion on the number of elements to pick.\<close>
primrec pick :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
	\<open>pick 0 xs = []\<close> |
	\<open>pick (Suc n) xs = (case xs of [] \<Rightarrow> [] | y # ys \<Rightarrow> y # (pick n ys))\<close>

\<comment> \<open>The length of the prefix is the minimum between the specified prefix length and the original list length.\<close>
lemma pick_length: \<open>length (pick n xs) = min n (length xs)\<close>
proof (induction n arbitrary: xs)
  case 0
  show ?case by simp
next
  case (Suc k)
  then show ?case
  proof (induction xs)
    case Nil
    show ?case by simp
  next
    case (Cons y ys)
    have \<open>length (pick (Suc k) (y # ys)) = Suc (length (pick k ys))\<close> by simp
    assume IH1: \<open>\<And>ws :: 'a list. length (pick k ws) = min k (length ws)\<close>
    then have \<open>length (pick (Suc k) (y # ys)) = Suc (min k (length ys))\<close> by simp
    then have \<open>length (pick (Suc k) (y # ys)) = min (Suc k) (Suc (length ys))\<close> by simp
    then show \<open>length (pick (Suc k) (y # ys)) = min (Suc k) (length (y # ys))\<close> by simp
  qed
qed

\<comment> \<open>The elements of the prefix obtained with @{term pick} are the first elements of the original list.\<close>
lemma pick_items: \<open>\<forall> i < length (pick n xs). (pick n xs) ! i = xs ! i\<close>
  sorry

\<comment> \<open>Function @{term pick} is equivalent to function @{term take}.\<close>
lemma pick_take_eq: \<open>pick n xs = take n xs\<close>
	by (simp add: list_eq_iff_nth_eq pick_items pick_length)


subsection \<open>Part III\<close>

\<comment> \<open>The function precedes every list in the second argument (which is a list of lists) with the corresponding item from the first argument. The lists that have no corresponding pair are replaced with an empty list.\<close>
primrec conss :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
	conss_Nil:	"conss xs [] = []" |
	conss_Cons:	"conss xs (y # ys) =
			(case xs of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z # y) # conss zs ys)"

\<comment> \<open>The following tests demonstrate how the function @{term conss} is expected to work.\<close>
lemma conss_test_1: \<open>conss [1] [] = []\<close> by simp
lemma conss_test_2: \<open>conss [1, 2] [] = []\<close> by simp
lemma conss_test_3: \<open>conss [] [[1]] = []\<close> by simp
lemma conss_test_4: \<open>conss [] [[1, 2]] = []\<close> by simp
lemma conss_test_5: \<open>conss [1] [[2]] = [[1, 2]]\<close> by simp
lemma conss_test_6: \<open>conss [1, 2] [[3], [4]] = [[1, 3], [2, 4]]\<close> by simp
lemma conss_test_7: \<open>conss [1, 2] [[3]] = [[1, 3]]\<close> by simp
lemma conss_test_8: \<open>conss [1] [[2], [3]] = [[1, 2]]\<close> by simp

\<comment> \<open>The length of @{term \<open>conss xs ys\<close>} is the minimum length of @{term xs} and @{term ys}.\<close>
lemma conss_length: \<open>length (conss xs ys) = min (length xs) (length ys)\<close>
proof (induction ys arbitrary: xs)
  case Nil
  show ?case by simp
next
  case (Cons z zs)
  assume IH0: \<open>\<And>xs :: 'a list. length (conss xs zs) = min (length xs) (length zs)\<close>
  then show ?case
  proof (induction xs)
    case Nil
    show ?case by simp
  next
    case (Cons w ws)
    have IH: \<open>length (conss ws zs) = min (length ws) (length zs)\<close> using IH0 by simp
    have \<open>min (length (w # ws)) (length (z # zs)) = min (Suc (length ws)) (Suc (length zs))\<close> by simp
    moreover have \<open>min (length (w # ws)) (length (z # zs)) = Suc (min (length ws) (length zs))\<close> by simp
    moreover have \<open>length (conss (w # ws) (z # zs)) = length ((w # z) # conss ws zs)\<close> by simp
    moreover then have \<open>length (conss (w # ws) (z # zs)) = Suc (length (conss ws zs))\<close> by simp
    moreover then have \<open>length (conss (w # ws) (z # zs)) = Suc (min (length ws) (length zs))\<close> using IH by simp
    moreover then show \<open>length (conss (w # ws) (z # zs)) = min (length (w # ws)) (length (z # zs))\<close> by simp
  qed
qed

\<comment> \<open>The result of @{term conss}, applied to non-empty lists, is a @{term Cons} of the lists heads with a @{term conss}, applied to the lists tails.\<close>
lemma conss_Cons_Cons: \<open>conss (x # xs) (y # ys) = (x # y) # conss xs ys\<close>
  using conss_Cons by simp

\<comment> \<open>If all lists in the list of lists are non-empty, it can be obtained by applying @{term conss} to the maps of heads and tails.\<close>
lemma hd_conss_tl:
	\<open>\<forall> x \<in> set xs. x \<noteq> [] \<Longrightarrow> conss (map hd xs) (map tl xs) = xs\<close>
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons y ys)
  assume IH: \<open>\<forall> x \<in> set ys. x \<noteq> [] \<Longrightarrow> conss (map hd ys) (map tl ys) = ys\<close>
  assume \<open>\<forall> x \<in> set (y # ys). x \<noteq> []\<close>
  then have P: \<open>y \<noteq> [] \<and> (\<forall> x \<in> set ys. x \<noteq> [])\<close> by simp
  then have Q: \<open>conss (map hd ys) (map tl ys) = ys\<close> using IH by simp
  have \<open>map hd (y # ys) = hd y # map hd ys\<close> by simp
  moreover have \<open>map tl (y # ys) = tl y # map tl ys\<close> by simp
  then have \<open>conss (map hd (y # ys)) (map tl (y # ys)) = conss (hd y # map hd ys) (tl y # map tl ys)\<close> by simp
  then have \<open>conss (map hd (y # ys)) (map tl (y # ys)) = (hd y # tl y) # conss (map hd ys) (map tl ys)\<close> by simp
  then show \<open>conss (map hd (y # ys)) (map tl (y # ys)) = y # ys\<close> using P Q by simp
qed

\<comment> \<open>If a list is obtained from a list of lists @{term s} by filtering all non-empty nested lists with a given property @{term P}, then applying @{term conss} to the heads and tails of the list, gives this list.\<close>
lemma hd_conss_tl_filter:
	\<open>conss
		(map hd (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))
		(map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))
	= filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s\<close>
proof (induction s)
  case Nil
  show ?case by simp
next
  case (Cons y ys)
  have \<open>\<forall>x \<in> set (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) (y # ys)). x \<noteq> []\<close> by simp
  then show ?case using hd_conss_tl by blast
qed

lemma filter_in: \<open>P x \<Longrightarrow>  x \<in> set s \<Longrightarrow> x \<in> set (filter P s)\<close>
proof (induction s)
  case Nil
  assume H: \<open>x \<in> set Nil\<close>
  have \<open>set Nil = set (filter P Nil)\<close> by simp
  then show \<open>x \<in> set (filter P Nil)\<close> using H by simp
next
  case (Cons y ys)
  assume IH: \<open>P x \<Longrightarrow>  x \<in> set ys \<Longrightarrow> x \<in> set (filter P ys)\<close>
  assume H: \<open>P x\<close>
  assume \<open>x \<in> set (y # ys)\<close>
  then have C: \<open>x = y \<or> x \<in> set ys\<close> by simp
  then show ?case
  proof (cases \<open>x = y\<close>)
    case True
    assume x_is_y: \<open>x = y\<close>
    then have \<open>P y\<close> using H by simp
    then have \<open>y \<in> set (filter P (y # ys))\<close> by simp
    then show ?thesis using x_is_y by simp
  next
    case False
    assume \<open>x \<noteq> y\<close>
    then have \<open>x \<in> set ys\<close> using C by simp
    then have \<open>x \<in> set (filter P ys)\<close> using IH H by blast
    then show ?thesis by simp
  qed
qed

lemma tl_in: \<open>xs \<noteq> [] \<Longrightarrow> xs \<in> set s \<Longrightarrow> tl xs \<in> set (map tl s)\<close>
proof (induction s)
  case Nil
  assume \<open>xs \<in> set Nil\<close>
  then have False by simp
  then show ?case by simp
next
  case (Cons y ys)
  assume IH: \<open>xs \<noteq> [] \<Longrightarrow> xs \<in> set ys \<Longrightarrow> tl xs \<in> set (map tl ys)\<close>
  assume \<open>xs \<noteq> []\<close>
  assume \<open>xs \<in> set (y # ys)\<close>
  then have D: \<open>xs = y \<or> xs \<in> set ys\<close> by simp
  then show ?case
  proof (cases \<open>xs = y\<close>)
    case True
    assume \<open>xs = y\<close>
    then show \<open>tl xs \<in> set (map tl (y # ys))\<close> by simp
  next
    case False
    assume \<open>xs \<noteq> y\<close>
    then have \<open>xs \<in> set ys\<close> using D by simp
    then have \<open>tl xs \<in> set (map tl ys)\<close> using IH by simp
    then show \<open>tl xs \<in> set (map tl (y # ys))\<close> by simp
  qed
qed

lemma all_tl: \<open>\<forall>x \<in> set s. tl x \<noteq> ys \<Longrightarrow> ys \<notin> set (map tl s)\<close>
proof (induction s)
  case Nil
  show \<open>ys \<notin> set (map tl Nil)\<close> by simp
next
  case (Cons w ws)
  assume IH: \<open>\<forall>x \<in> set ws. tl x \<noteq> ys \<Longrightarrow> ys \<notin> set (map tl ws)\<close>
  assume H: \<open>\<forall>x \<in> set (w # ws). tl x \<noteq> ys\<close>
  then have tl_w: \<open>tl w \<noteq> ys\<close> by simp
  with H have \<open>\<forall>x \<in> set ws. tl x \<noteq> ys\<close> by simp
  then have \<open>ys \<notin> set (map tl ws)\<close> using IH by simp
  then show \<open>ys \<notin> set (map tl (w # ws))\<close> using tl_w by simp
qed

lemma tl_ne: \<open>xs \<noteq> [] \<Longrightarrow> hd xs # ys \<noteq> xs \<Longrightarrow> tl xs \<noteq> ys\<close>
proof (induction xs)
  case Nil
  assume \<open>Nil \<noteq> []\<close>
  then have False by simp
  then show ?case by blast
next
  case (Cons w ws)
  assume H1: \<open>(w # ws) \<noteq> []\<close>
  assume H2: \<open>hd (w # ws) # ys \<noteq> w # ws\<close>
  then have \<open>w # ys \<noteq> w # ws\<close> by simp
  then show \<open>tl (w # ws) \<noteq> ys\<close> by simp
qed

lemma not_tl: \<open>x # xs \<notin> set (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s) \<Longrightarrow> \<forall>y \<in> set (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s). tl y \<noteq> xs\<close>
proof (induction s)
  case Nil
  assume \<open>x # xs \<notin> set (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) Nil)\<close>
  have \<open>set (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) Nil) = {}\<close> by simp
  then show \<open>\<forall>y \<in> set (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) Nil).  tl y \<noteq> xs\<close> by simp
next
  case (Cons w ws)
  assume IH: \<open>x # xs \<notin> set (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) ws) \<Longrightarrow> \<forall>y \<in> set (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) ws). tl y \<noteq> xs\<close>
  assume H: \<open>x # xs \<notin> set (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) (w # ws))\<close>
  then show ?case
  proof (cases \<open>w \<noteq> [] \<and> hd w = x\<close>)
    case False
    assume \<open>\<not>(w \<noteq> [] \<and> hd w = x)\<close>
    then have FE: \<open>filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) (w # ws) = filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) ws\<close> by simp
    then have \<open>x # xs \<notin> set (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) ws)\<close> using H by simp
    then have \<open>\<forall>y \<in> set (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) ws). tl y \<noteq> xs\<close> using IH by simp
    then show ?thesis using FE by simp
  next
    case True
    assume H1: \<open>w \<noteq> [] \<and> hd w = x\<close>
    then have \<open>(filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) (w # ws)) = w # (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) ws)\<close> by simp
    then have C: \<open>x # xs \<noteq> w \<and> x # xs \<notin> set (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) ws)\<close> using H by simp
    then have \<open>hd w # xs \<noteq> w\<close> using C H1 by simp
    then have tl_w: \<open>tl w \<noteq> xs\<close> using tl_ne H1 by blast
    then have \<open>\<forall>y \<in> set (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) ws). tl y \<noteq> xs\<close> using C IH by simp
    then show ?thesis using tl_w by simp
  qed
qed  

\<comment> \<open>A non-empty list with head @{term x} and tail @{term xs} is in the list of lists @{term s} if and only if @{term xs} is in the tails of the lists from @{term s} that have @{term x} as their head.\<close>
lemma tl_filter_hd: \<open>x # xs \<in> set s \<longleftrightarrow>
			xs \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s))\<close>
proof (cases \<open>x # xs \<in> set s\<close>)
  case True
  assume H: \<open>x # xs \<in> set s\<close>
  then have RL: \<open>xs \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s)) \<Longrightarrow> x # xs \<in> set s\<close> by simp
  then have list_fits: \<open>x # xs \<noteq> [] \<and> hd (x # xs) = x\<close> by simp
  then have \<open>x # xs \<in> set (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s)\<close> using H filter_in by simp
  then have \<open>tl (x # xs) \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s))\<close> using list_fits tl_in by blast
  then have \<open>xs \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s))\<close> by simp
  then have LR: \<open>x # xs \<in> set s \<Longrightarrow> xs \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s))\<close> by simp
  show ?thesis using LR RL by blast
next
  case False
  assume H: \<open>x # xs \<notin> set s\<close>
  then have LR: \<open>x # xs \<in> set s \<Longrightarrow> xs \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s))\<close> by simp
  with H have \<open>x # xs \<notin> set (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s)\<close> by simp
  then have \<open>\<forall>y \<in> set (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s). tl y \<noteq> xs\<close> using not_tl by simp
  then have \<open>xs \<notin> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s))\<close> using all_tl by blast
  then have RL: \<open>xs \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s)) \<Longrightarrow> x # xs \<in> set s\<close> by simp
  show ?thesis using LR RL by blast
qed

end