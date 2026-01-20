theory Task imports Main begin


subsection \<open>Part I\<close>

\<comment> \<open>If @{term foldr} over conjuctions evaluates to @{term True}, the initial value is @{term True}.\<close>
lemma foldr_conj_init: \<open>foldr (\<lambda> x b. P x \<and> b) xs y \<Longrightarrow> y\<close>
proof(induction xs)
  case Nil
  then  show ?case by simp
next
  case IH: (Cons x xs)
  then have "foldr (\<lambda>x. (\<and>) (P x)) xs y" by simp
  with IH show ?case by simp
qed

\<comment> \<open>@{term foldr} over conjuctions with initial value @{term True} evaluates to @{term True} if an only if all conjuncts are @{term True}.\<close>
lemma foldr_conj_prop:
	\<open>foldr (\<lambda> x b. P x \<and> b) xs True \<longleftrightarrow> (\<forall> x \<in> set xs. P x)\<close>
proof(induction xs)
  case Nil
  then  show ?case by simp
next
  case IH: (Cons x xs)
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
proof(induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case IHn: (Suc n)
  show ?case
  proof(cases xs)
    case Nil
    then show ?thesis by simp
  next
    case xs: (Cons y ys)
    from IHn have "length (pick n ys) = min n (length ys)" by simp
    with xs show ?thesis by simp
  qed
qed

\<comment> \<open>The elements of the prefix obtained with @{term pick} are the first elements of the original list.\<close>
lemma pick_items: \<open>\<forall> i < length (pick n xs). (pick n xs) ! i = xs ! i\<close>
proof(induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case IHn: (Suc n)
  show ?case
  proof(cases xs)
    case Nil
    then show ?thesis by simp
  next
    case xs: (Cons y ys)
    show ?thesis
    proof
      fix i
      show "i < length (pick (Suc n) xs) \<longrightarrow> pick (Suc n) xs ! i = xs ! i"
      proof(cases i)
        case 0
        then show ?thesis using xs by simp
      next
        case i: (Suc j)
        show ?thesis
        proof
          assume i_less_length: "i < length (pick (Suc n) xs)"
          with xs i have "pick (Suc n) xs ! i = pick n ys ! j" by simp
          moreover from IHn i_less_length i xs have "pick n ys ! j = ys ! j" by simp
          moreover from i_less_length xs i have "ys ! j = xs ! i" by simp
          ultimately show "pick (Suc n) xs ! i = xs ! i" by simp
        qed
      qed
    qed
  qed
qed      

\<comment> \<open>Function @{term pick} is equivalent to function @{term take}.\<close>
lemma pick_take_eq: \<open>pick n xs = take n xs\<close>
	by (simp add: list_eq_iff_nth_eq pick_items pick_length)

subsection \<open>Part III\<close>

\<comment> \<open>The function precedes every list in the second argument (which is a list of lists) with the corresponding item from the first argument. The lists that have no corresponding pair are replaced with an empty list.\<close>
primrec conss :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
	conss_Nil:	"conss [] ys = []" |
	conss_Cons:	"conss (x # xs) ys =
			(case ys of [] \<Rightarrow> [] | z # zs \<Rightarrow> (x # z) # conss xs zs)"

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
proof(induction xs arbitrary: ys)
  case Nil
  show ?case by simp
next
  case IHys: (Cons z zs)
  show ?case
  proof(cases ys)
    case Nil
    then  show ?thesis by simp
  next
    case (Cons l ls)
    with IHys show ?thesis by simp
  qed
qed

\<comment> \<open>The result of @{term conss}, applied to non-empty lists, is a @{term Cons} of the lists heads with a @{term conss}, applied to the lists tails.\<close>
lemma conss_Cons_Cons: \<open>conss (x # xs) (y # ys) = (x # y) # conss xs ys\<close>
	by simp

\<comment> \<open>If all lists in the list of lists are non-empty, it can be obtained by applying @{term conss} to the maps of heads and tails.\<close>
lemma hd_conss_tl:
	\<open>\<forall> x \<in> set xs. x \<noteq> [] \<Longrightarrow> conss (map hd xs) (map tl xs) = xs\<close>
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then show ?case by simp
qed

\<comment> \<open>If a list is obtained from a list of lists @{term s} by filtering all non-empty nested lists with a given property @{term P}, then applying @{term conss} to the heads and tails of the list, gives this list.\<close>
lemma hd_conss_tl_filter:
	\<open>conss
		(map hd (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))
		(map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))
	= filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s\<close>
proof(induction s)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by simp
qed

lemma tl_ne: \<open>xs \<noteq> [] \<Longrightarrow> hd xs # ys \<noteq> xs \<Longrightarrow> tl xs \<noteq> ys\<close>
proof -
  assume 1: "xs \<noteq> []" and 2: "hd xs # ys \<noteq> xs"
  show ?thesis
  proof(cases xs)
    case Nil
    with 1 show ?thesis by simp
  next
    case (Cons y ys)
    with 2 show ?thesis by simp
  qed
qed

\<comment> \<open>A non-empty list with head @{term x} and tail @{term xs} is in the list of lists @{term s} if and only if @{term xs} is in the tails of the lists from @{term s} that have @{term x} as their head.\<close>
lemma tl_filter_hd_aux: "y \<noteq> x # xs \<Longrightarrow>
   (xs \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) (y # ys)))) \<longleftrightarrow> (xs \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) ys)))"
proof -
  assume y: "y \<noteq> x # xs"
  show ?thesis
  proof(cases "y")
    case Nil
    then show ?thesis by simp
  next
    case yCons: (Cons z zs)
    show ?thesis
    proof(cases "z = x")
      case z: True
      with y yCons have "xs \<noteq> zs" by simp
      with yCons z show ?thesis by simp
    next
      case False
      with yCons show ?thesis by simp
    qed
  qed
qed

lemma tl_filter_hd: \<open>x # xs \<in> set s \<longleftrightarrow>
			xs \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s))\<close>
proof(induction s)
  case Nil
  then show ?case by simp
next
  case IH: (Cons y ys)
  then show ?case
  proof(cases "y = x # xs")
    case True
    then show ?thesis by simp
  next
    case y: False
    then have "(x # xs \<in> set (y # ys)) = (x # xs \<in> set ys)" by simp
    with IH have "(x # xs \<in> set (y # ys)) = (xs \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) ys)))" by simp
    with tl_filter_hd_aux[OF y] show ?thesis by simp
  qed
qed    

end