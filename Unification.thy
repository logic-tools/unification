theory Unification imports Main begin

type_synonym vname = "string \<times> int"

datatype "term" = V vname | T "string \<times> term list"

type_synonym subst = "(vname \<times> term) list"

definition indom :: "vname \<Rightarrow> subst \<Rightarrow> bool" where
  "indom x s = list_ex (\<lambda>(y, _). x = y) s"

fun app :: "subst \<Rightarrow> vname \<Rightarrow> term" where
  "app ((y,t)#s) x = (if x = y then t else app s x)"
| "app [] _ = undefined"

fun lift :: "subst \<Rightarrow> term \<Rightarrow> term" where
  "lift s (V x) = (if indom x s then app s x else V x)"
| "lift s (T(f,ts)) = T(f, map (lift s) ts)"

fun occurs :: "vname \<Rightarrow> term \<Rightarrow> bool" where
  "occurs x (V y) = (x = y)"
| "occurs x (T(_,ts)) = list_ex (occurs x) ts"

definition vars :: "term list \<Rightarrow> vname set" where
  "vars S = {x. \<exists>t \<in> set S. occurs x t}"

lemma vars_nest_eq:
  fixes ts :: "term list"
    and S :: "term list"
    and vn :: "string"
  shows "vars (ts @ S) = vars (T(vn, ts) # S)"
  unfolding vars_def
  by (induction ts, auto)

lemma vars_concat:
  fixes ts:: "term list"
    and S:: "term list"
  shows "vars (ts @ S) = vars ts \<union> vars S"
  unfolding vars_def
  by (induction ts, auto)

definition vars_eqs :: "(term \<times> term) list \<Rightarrow> vname set" where
  "vars_eqs l = vars (map fst l) \<union> vars (map snd l)"

lemma vars_eqs_zip:
  fixes ts:: "term list"
    and us:: "term list"
    and S:: "term list"
  shows "vars_eqs (zip ts us) \<subseteq> vars ts \<union> vars us"
proof -
  have
    "map fst (zip xs ys) = take (min (length xs) (length ys)) xs"
    "map snd (zip xs ys) = take (min (length xs) (length ys)) ys"
    for xs ys :: "'a list"
    by (induct xs ys rule: list_induct2') simp_all
  then show ?thesis
    unfolding vars_eqs_def
    using vars_concat append_take_drop_id sup_ge1 Un_mono
    by metis
qed

lemma vars_eqs_concat:
  fixes ts:: "(term \<times> term) list"
    and S:: "(term \<times> term) list"
  shows "vars_eqs (ts @ S) = vars_eqs ts \<union> vars_eqs S"
  using vars_concat vars_eqs_def by auto

lemma vars_eqs_nest_subset:
  fixes ts :: "term list"
    and us :: "term list"
    and S :: "(term \<times> term) list"
    and vn :: "string"
    and wn :: "string"
  shows "vars_eqs (zip ts us @ S) \<subseteq> vars_eqs ((T(vn, ts), T(wn, us)) # S)"
proof -
  have "vars_eqs ((T(vn, ts), T(wn, us)) # S) = vars ts \<union> vars us \<union> vars_eqs S"
    using vars_concat vars_eqs_def vars_nest_eq by auto
  then show ?thesis
    using vars_eqs_concat vars_eqs_zip by fastforce
qed

definition n_var :: "(term \<times> term) list \<Rightarrow> nat" where
  "n_var l = card (vars_eqs l)"

lemma var_eqs_finite:
  fixes ts
  shows "finite (vars_eqs ts)"
proof -
  {
    fix t
    have "finite ({x. occurs x t})"
    proof (induction t rule: occurs.induct)
      case (1 x y)
      then show ?case by simp
    next
      case (2 x fn ts)
      have "{x. occurs x (T (fn, ts))} = vars ts"
        using vars_def Bex_set_list_ex
        by fastforce
      then show ?case using vars_def "2.IH" by simp
    qed
  }
  then show ?thesis
    using vars_def vars_eqs_def by simp
qed

lemma vars_eqs_subset_n_var_le:
  fixes S1:: "(term \<times> term) list"
    and S2:: "(term \<times> term) list"
  assumes "vars_eqs S1 \<subseteq> vars_eqs S2"
  shows "n_var S1 \<le> n_var S2"
  using assms var_eqs_finite n_var_def
  by (simp add: card_mono)

lemma vars_eqs_psubset_n_var_lt:
  fixes S1:: "(term \<times> term) list"
    and S2:: "(term \<times> term) list"
  assumes "vars_eqs S1 \<subset> vars_eqs S2"
  shows "n_var S1 < n_var S2"
  using assms var_eqs_finite n_var_def
  by (simp add: psubset_card_mono)

fun fun_count :: "term list \<Rightarrow> nat" where
  "fun_count [] = 0"
| "fun_count ((V _)#S) = fun_count S"
| "fun_count (T(_,ts)#S) = 1 + fun_count ts + fun_count S"

lemma fun_count_concat:
  fixes ts:: "term list"
    and us:: "term list"
  shows "fun_count (ts @ us) = fun_count ts + fun_count us"
proof (induction ts)
  case Nil
  then show ?case
    by force
next
  case (Cons a ts)
  show ?case
  proof (cases a)
    case (V _)
    then have "fun_count ((a # ts) @ us) = fun_count (ts @ us)"
      by simp
    then show ?thesis
      by (simp add: Cons.IH V)
  next
    case (T x)
    then obtain fn ts' where ts'_def: "x=(fn, ts')"
      by fastforce
    then have "fun_count ((a # ts) @ us) = 1 + fun_count (ts @ us) + fun_count ts'"
      by (simp add: T)
    then show ?thesis
      by (simp add: Cons.IH T ts'_def)
  qed
qed

definition n_fun :: "(term \<times> term) list \<Rightarrow> nat" where
  "n_fun l = fun_count (map fst l) + fun_count (map snd l)"

lemma n_fun_concat:
  fixes ts us
  shows "n_fun (ts @ us) = n_fun ts + n_fun us"
  unfolding n_fun_def using fun_count_concat
  by simp

lemma n_fun_nest_head:
  fixes ts g us S
  shows "n_fun (zip ts us @ S) + 2 \<le> n_fun ((T (g, ts), T (g, us)) # S)"
proof -
  let "?trunc_ts" = "map fst (zip ts us)"
  let "?trunc_us" = "map snd (zip ts us)"
  have trunc_sum: "n_fun ((T (g, ?trunc_ts), T (g, ?trunc_us)) # S) = 2 + n_fun (zip ts us @ S)"
    using n_fun_concat n_fun_def by auto

  obtain tsp where ts_rest: "map fst (zip ts us) @ tsp = ts"
    by (induct ts us rule:list_induct2') simp_all
  obtain usp where us_rest: "map snd (zip ts us) @ usp = us"
    by (induct ts us rule:list_induct2') simp_all
  have "fun_count [T(g, ?trunc_ts)] + fun_count tsp = fun_count [T(g, ts)]"
    using ts_rest fun_count_concat
    by (metis add.assoc add.right_neutral fun_count.simps(1) fun_count.simps(3))
  moreover have "fun_count [T(g, ?trunc_us)] + fun_count usp = fun_count [T(g, us)]"
    using us_rest fun_count_concat
    by (metis add.assoc add.right_neutral fun_count.simps(1) fun_count.simps(3))
  ultimately have "n_fun [(T (g, ?trunc_ts), T (g, ?trunc_us))] + fun_count tsp + fun_count usp =
      fun_count [T(g, ts)] + fun_count [T(g, us)]"
    by (simp add: n_fun_def)
  then have "n_fun ((T (g, ?trunc_ts), T (g, ?trunc_us)) # S) + fun_count tsp + fun_count usp =
      n_fun ((T (g, ts), T (g, us)) # S)"
    using n_fun_def n_fun_concat by simp
  from this and trunc_sum show ?thesis by simp
qed

abbreviation (noprint) "liftmap v t S' \<equiv>
  map (\<lambda>(t1, t2). (lift [(v, t)] t1, lift [(v, t)] t2)) S'"

lemma lift_elims:
  fixes x :: "vname"
    and t :: "term"
    and t0 :: "term"
  assumes "\<not> occurs x t"
  shows "\<not> occurs x (lift [(x, t)] t0)"
proof (induction "[(x, t)]" t0 rule: lift.induct)
  case (1 x)
  then show ?case
    by (simp add: assms indom_def vars_def)
next
  case (2 f ts)
  {
    fix v
    assume "occurs v (lift [(x, t)] (T (f, ts)))"
    then have "list_ex (occurs v) (map (lift [(x,t)]) ts)"
      by simp
    then obtain t1 where t1_def: "t1 \<in> set (map (lift [(x,t)]) ts) \<and> occurs v t1"
      by (meson Bex_set_list_ex)
    then obtain t1' where "t1 = lift [(x,t)] t1' \<and> t1' \<in> set ts" by auto

    then have "\<exists>t1 \<in> set ts. occurs v (lift [(x,t)] t1)"
      using t1_def by blast
  }
  then show ?case
    using "2.hyps" by blast
qed

lemma lift_inv_occurs:
  fixes x :: "vname"
    and v :: "vname"
    and st :: "term"
    and t :: "term"
  assumes "occurs v (lift [(x, st)] t)"
    and "\<not> occurs v st"
    and "v \<noteq> x"
  shows "occurs v t"
  using assms proof (induction t rule: occurs.induct)
  case (1 v y)
  have "lift [(x, st)] (V y) = V y"
    using "1.prems" indom_def by auto
  then show ?case
    using "1.prems"(1) by auto
next
  case (2 x f ts)
  then show ?case
    by (metis (mono_tags, lifting) Bex_set_list_ex imageE lift.simps(2) occurs.simps(2) set_map)
qed

lemma vars_elim:
  fixes x st S
  assumes "\<not> occurs x st"
  shows "vars (map (lift [(x,st)]) S) \<subseteq> vars [st] \<union> vars S \<and>
         x \<notin> vars (map (lift [(x,st)]) S)"
proof (induction S)
  case Nil
  then show ?case
    by (simp add: vars_def)
next
  case (Cons tx S)
  moreover have "vars (map (lift [(x, st)]) (tx # S)) =
    vars [lift [(x,st)] tx] \<union> vars (map (lift [(x, st)]) S)"
    using vars_concat
    by (metis append.left_neutral append_Cons list.simps(9))
  moreover have "vars [st] \<union> vars (tx # S) = vars [st] \<union> vars S \<union> vars [tx]"
    using vars_concat
    by (metis append.left_neutral append_Cons sup_commute)
  moreover {
    fix v
    assume v_mem_vars_lift: "v \<in> vars [lift [(x,st)] tx]"
    have v_neq_x: "v \<noteq> x" using lift_elims assms v_mem_vars_lift vars_def
      by fastforce
    moreover have "v \<in> vars [st] \<union> vars [tx]"
    proof (cases)
      assume "occurs v st"
      then show ?thesis unfolding vars_def by simp
    next
      assume not_occurs_v_st: "\<not>occurs v st"
      have "occurs v (lift [(x, st)] tx)"
        using v_mem_vars_lift vars_def by force
      then have "occurs v tx" using lift_inv_occurs
        using v_neq_x not_occurs_v_st by blast
      then show ?thesis
        by (simp add: vars_def)
    qed
    ultimately have "v \<in> vars [st] \<union> vars [tx] \<and> v \<noteq> x" by simp
  }
  ultimately show ?case by blast
qed

lemma n_var_elim:
  fixes x st S
  assumes "\<not> occurs x st"
  shows "n_var (liftmap x st S) < n_var ((V x, st) # S)"
proof -
  have "\<And>l f. map fst (map (\<lambda>(t1, t2). (f t1, f t2)) l) = map f (map fst l)"
    by (simp add: case_prod_unfold)
  moreover have "\<And>l f. map snd (map (\<lambda>(t1, t2). (f t1, f t2)) l) = map f (map snd l)"
    by (simp add: case_prod_unfold)
  ultimately have lhs_split: "vars_eqs (liftmap x st S) =
    vars (map (lift [(x,st)]) (map fst S)) \<union> vars (map (lift [(x,st)]) (map snd S))"
    unfolding vars_eqs_def by metis

  have "vars_eqs ((V x, st) # S) = vars_eqs [(V x, st)] \<union> vars_eqs S"
    using vars_eqs_concat
    by (metis append_Cons self_append_conv2)
  moreover have "vars_eqs [(V x, st)] = {x} \<union> vars [st]"
    unfolding vars_eqs_def using vars_def occurs.simps(1) by force
  ultimately have rhs_eq1: "vars_eqs ((V x, st) # S) = {x} \<union> vars [st] \<union> vars_eqs S"
    by presburger
  then have rhs_eq2:
    "vars_eqs ((V x, st) # S) = {x} \<union> vars [st] \<union> vars (map fst S) \<union> vars (map snd S)"
    unfolding vars_eqs_def
    by (simp add: sup.assoc)

  from this lhs_split vars_elim assms
  have "vars_eqs (liftmap x st S) \<subseteq> vars [st] \<union> vars_eqs S \<and>
        x \<notin> vars_eqs (liftmap x st S)"
    using vars_concat vars_eqs_def by (metis map_append)
  moreover have "x \<in> vars_eqs ((V x, st) # S)"
    by (simp add: rhs_eq2)
  ultimately have "vars_eqs (liftmap x st S) \<subset> vars_eqs ((V x, st) # S)"
    using rhs_eq1 by blast
  then show ?thesis using vars_eqs_psubset_n_var_lt by blast
qed

function (sequential) solve :: "(term \<times> term) list \<times> subst \<Rightarrow> subst option"
  and elim :: "vname \<times> term \<times> (term \<times> term) list \<times> subst \<Rightarrow> subst option" where
  "solve([], s) = Some s"
| "solve((V x, t) # S, s) = (
    if V x = t then solve(S,s) else elim(x,t,S,s))"
| "solve((t, V x) # S, s) = elim(x,t,S,s)"
| "solve((T(f,ts),T(g,us)) # S, s) = (
    if f = g then solve((zip ts us) @ S, s) else None)"

| "elim(x,t,S,s) = (
    if occurs x t then None
    else let xt = lift [(x,t)]
      in solve(map (\<lambda> (t1,t2). (xt t1, xt t2)) S,
        (x,t) # (map (\<lambda> (y,u). (y, xt u)) s)))"
  by pat_completeness auto
termination proof (
    relation "
      (\<lambda>XX. case XX of Inl(l,_) \<Rightarrow> n_var l | Inr(x,t,S,_) \<Rightarrow> n_var ((V x, t)#S)) <*mlex*>
      (\<lambda>XX. case XX of Inl(l,_) \<Rightarrow> n_fun l | Inr(x,t,S,_) \<Rightarrow> n_fun ((V x, t)#S)) <*mlex*>
      (\<lambda>XX. case XX of Inl(l,_) \<Rightarrow> size l | Inr(x,t,S,_) \<Rightarrow> size ((V x, t)#S)) <*mlex*>
      (\<lambda>XX. case XX of Inl(l,_) \<Rightarrow> 1 | Inr(x,t,S,_) \<Rightarrow> 0) <*mlex*>
      {}",
    auto simp add: wf_mlex mlex_less mlex_prod_def)
  have "\<And>v S. vars_eqs S \<subseteq> vars_eqs ((V v, V v)#S)"
    using vars_eqs_def vars_def by force
  then show "\<And>a b S. \<not> n_var S < n_var ((V (a, b), V (a, b)) # S) \<Longrightarrow>
      n_var S = n_var ((V (a, b), V (a, b)) # S)"
    using vars_eqs_subset_n_var_le by (simp add: nat_less_le)

  show "\<And>a b S. \<not> n_var S < n_var ((V (a, b), V (a, b)) # S) \<Longrightarrow>
             n_fun S \<noteq> n_fun ((V (a, b), V (a, b)) # S) \<Longrightarrow>
             n_fun S < n_fun ((V (a, b), V (a, b)) # S)"
    using n_fun_def by simp

  have "\<And>tx v. vars_eqs [(V v, T tx)] = vars_eqs [(T tx, V v)]"
    using vars_eqs_def
    by (simp add: sup_commute)
  then have "\<And>tx v S. vars_eqs ((V v, T tx) # S) = vars_eqs ((T tx, V v) # S)"
    using vars_eqs_concat
    by (metis append_Cons self_append_conv2)
  then have "\<And>a b v S. n_var ((V v, T (a, b)) # S) = n_var ((T (a, b), V v) # S)"
    unfolding n_var_def vars_eqs_def
    by presburger
  then show "\<And>a b aa ba S.
       \<not> n_var ((V (aa, ba), T (a, b)) # S) < n_var ((T (a, b), V (aa, ba)) # S) \<Longrightarrow>
       n_var ((V (aa, ba), T (a, b)) # S) = n_var ((T (a, b), V (aa, ba)) # S)"
    by simp

  show "\<And>a b aa ba S.
       \<not> n_var ((V (aa, ba), T (a, b)) # S) < n_var ((T (a, b), V (aa, ba)) # S) \<Longrightarrow>
       n_fun ((V (aa, ba), T (a, b)) # S) \<noteq> n_fun ((T (a, b), V (aa, ba)) # S) \<Longrightarrow>
       n_fun ((V (aa, ba), T (a, b)) # S) < n_fun ((T (a, b), V (aa, ba)) # S)"
    by (simp add: n_fun_def)

  show "\<And>ts g us S. \<not> n_var (zip ts us @ S) < n_var ((T (g, ts), T (g, us)) # S) \<Longrightarrow>
          n_var (zip ts us @ S) = n_var ((T (g, ts), T (g, us)) # S)"
    using vars_eqs_nest_subset vars_eqs_subset_n_var_le le_neq_implies_less by meson

  have n_fun_nested_gt: "\<And>ts g us S. n_fun (zip ts us @ S) < n_fun ((T (g, ts), T (g, us)) # S)"
    using n_fun_nest_head
    by (metis add_leD1 le_neq_implies_less add_2_eq_Suc' leD less_Suc_eq)
  show "\<And>ts g us S.
       \<not> n_var (zip ts us @ S) < n_var ((T (g, ts), T (g, us)) # S) \<Longrightarrow>
       \<not> n_fun (zip ts us @ S) < n_fun ((T (g, ts), T (g, us)) # S) \<Longrightarrow>
        n_fun (zip ts us @ S) = n_fun ((T (g, ts), T (g, us)) # S)"
    using n_fun_nested_gt by meson

  show "\<And>ts g us S.
       \<not> n_var (zip ts us @ S) < n_var ((T (g, ts), T (g, us)) # S) \<Longrightarrow>
       \<not> n_fun (zip ts us @ S) < n_fun ((T (g, ts), T (g, us)) # S) \<Longrightarrow>
        min (length ts) (length us) = 0"
    using n_fun_nested_gt by blast

  show "\<And>x t S.
       \<not> occurs x t \<Longrightarrow>
       \<not> n_var (liftmap x t S) < n_var ((V x, t) # S) \<Longrightarrow>
       n_var (liftmap x t S) = n_var ((V x, t) # S)"
    using n_var_elim leD linorder_neqE_nat by blast

  show "\<And>x t S.
       \<not> occurs x t \<Longrightarrow>
       \<not> n_var (liftmap x t S) < n_var ((V x, t) # S) \<Longrightarrow>
       n_fun (liftmap x t S) \<noteq> n_fun ((V x, t) # S) \<Longrightarrow>
       n_fun (liftmap x t S) < n_fun ((V x, t) # S)"
    using n_var_elim by simp
qed

code_reflect Unification
  datatypes
    "term" = V | T
    and
    char = zero_char_inst.zero_char | Char
  functions
    solve

export_code solve in SML

ML \<open> open Unification \<close>

lemma "solve([(T([],[]),T([],[]))],[]) = Some []"
  by code_simp

ML_val \<open> solve([(T([],[]),T([],[]))],[]) \<close>

lemma "solve([(T([zero_char_inst.zero_char],[]),T([],[]))],[]) = None"
  by code_simp

ML_val \<open> solve([(T([Zero_char],[]),T([],[]))],[]) \<close>

end
