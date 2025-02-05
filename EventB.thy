(*<*)
theory
  EventB
imports
  Igloo.Event_Systems
  Igloo.Event_Systems_into_IO_Processes
  Igloo.Interleaving
  Optics.Dataspace
keywords
  "model" :: thy_goal_defn and
  "extends" "variables" "initialise" "invariants"
  "events" "when" "do"
  "refines" "via"
begin

lemma ES_make_init: "ES = ES.make i t \<Longrightarrow> init ES = i"
  by (simp add: ES.make_def)

lemma ES_make_trans: "ES = ES.make i t \<Longrightarrow> (ES: s\<midarrow>e\<rightarrow> s') = t s e s'"
  by (simp add: ES.make_def)

lemma vwb_weakI: "vwb_lens L \<Longrightarrow> weak_lens L" by simp

lemma ASM_RL: "A \<Longrightarrow> A" by (rule asm_rl)

lemma join_invariant: "\<lbrakk> R \<longrightarrow> P; R \<longrightarrow> Q \<rbrakk> \<Longrightarrow> R \<longrightarrow> P \<and> Q"
  by simp

lemma reachD: "reach ES s \<Longrightarrow> True" ..

lemma trivial: \<open>(\<forall>x. P x \<longrightarrow> P x) = True\<close>
  by simp

ML_file \<open>eventb.ML\<close>

hide_fact
 ES_make_init ES_make_trans
 vwb_weakI
 ASM_RL
 join_invariant
 reachD
 trivial
(*>*)

section \<open>Introduction\<close>
text \<open>This document describes the @{command model} command provided by this theory.
The command integrates a dataspace representation using lenses
\<^cite>\<open>"Optics-AFP"\<close> with standard Isabelle locales
\<^cite>\<open>Ballarin23\<close>. It supports refinement through additional proof
obligations.

The approach follows the standard Event-B modeling methodology \<^cite>\<open>Abrial_2010\<close>
and builds on top of the Igloo framework for event-based models of distributed systems
\<^cite>\<open>Sprenger_2020\<close>.\<close>

section \<open>The @{command model} Command\<close>

subsection \<open>Syntax\<close>

text \<open>
\label{sec:model}

The general syntax for an Event-B model definition looks like this:
\begin{quote}
\begin{tabular}{@ {}l}
\indexed{\isacom{model}}{model} \<open>('a\<^sub>1,\<dots>,'a\<^sub>n) model_name\<close> = \\
  \makebox[1em][r]{[\ }\isacom{extends} \<open>locale_expression\<close>\ ] \\
  \quad\isacom{variables}
    \(\mathit{var}_1\)\<open>" :: "\<close>\(\mathit{type}_1 \ \cdots
      \ \mathit{var}_j\)\<open>" :: "\<close>\(\mathit{type}_j\) \\
  \quad\isacom{initialise}
    \("\mathit{var}_1 = \mathit{v}_1" \cdots
      "\mathit{var}_j = \mathit{v}_j"\) \\
  \quad\isacom{invariants} \\
    \quad\quad \(\mathit{inv}_1:\ "\mathit{P}_1 \ \mathit{var}_1 \cdots \mathit{var}_j"\) \\
    \quad\quad \ \vdots \\
    \quad\quad \(\mathit{inv}_i:\ "\mathit{P}_i \ \mathit{var}_1 \cdots \mathit{var}_j"\)
      [ \isacom{uses} \<open>inv\<^sub>a \<dots>\<close> ] \\
  \quad\isacom{events} \\
    \quad\quad \(E_1 \ \alpha_{1,1} \dots \alpha_{1,l_1}\)
      \isacom{when} \(G_{1,1} \cdots G_{1,m_1} \)
      \isacom{do} \(A_{1,1} \cdots A_{1,n_1} \) \\
    \quad\quad \ \vdots \\
    \makebox[2em][r]{|\ } \(E_k \ \alpha_{k,1} \dots \alpha_{k,l_k}\)
      \isacom{when} \(G_{k,1} \cdots G_{k,m_k} \)
      \isacom{do} \(A_{k,1} \cdots A_{k,n_k} \) \\
  \makebox[1em][r]{[\ }\isacom{refines} \<open>model_name\<^sub>0\<close>
      \isacom{via} \<open>mediator_eq\<close>\(^+\)
      \isacom{where} \<open>\<pi>\<close>\ ] \\
\end{tabular}
\end{quote}\<close>
text \<open>The syntax for \<open>locale_expression\<close> is described in \<^cite>\<open>Ballarin23\<close>. In the guard and after
expressions (\(G\) and \(A\) respectively) each variable \<open>var\<close> is bound. In after expressions \(A\)
a primed version \<open>var'\<close> (the variable after an event \(E\) occurred) is bound too.

When declaring a refinement, each variable from \<open>model_name\<^sub>0\<close> must have a corresponding mediator
equality \<open>mediator_eq\<close> of the form "\<open>var\<^sub>0 = \<dots>\<close>". This function \<open>\<pi>\<close> is specified infix:

\hspace*{1em}\(
  E_a\<open> \<Zsurj> model_name\<^sub>0.\<close>E_b
\)\<close>

subsection \<open>Semantics\<close>

text \<open>Each invocation defines a new datatype \<open>model_name.event\<close> with constructors
\(\<open>model_name.\<close>E_1, \dots, \<open>model_name.\<close>E_k\) and \<open>model_name.Skip\<close>.\<close>
(*<*)
lemma
  "var = v \<Longrightarrow> P var"
  "P var \<Longrightarrow> G var \<Longrightarrow> A var var' \<Longrightarrow> P var'"
(*>*)
text\<open>A simple invocation (no refinement) of the command will propose the following
proof obligations:
@{subgoals[display]}
\<close>
(*<*)
  oops
(*>*)
text \<open>The invocation defines a new locale extension with an associated lens for each variable
\<open>var\<close> in the sense of a dataspace \<^cite>\<open>"Optics-AFP"\<close>:

\begin{quote}
\begin{tabular}{@ {}rl}
\indexed{\isacom{locale}}{locale}&\<open>model_name\<close> = \\
  \isacom{fixes} & \(\mathit{var}_1\)\<open>\<^sub>L" :: "\<close>\(\mathit{type}_1 \)\<open> \<Longrightarrow> 'st\<close> \\
                 & \(\vdots\) \\
    \isacom{and} & \(\mathit{var}_j\)\<open>\<^sub>L" :: "\<close>\(\mathit{type}_j\)\<open> \<Longrightarrow> 'st\<close> \\
  \quad\isacom{assumes} & \<open>dataspace_assms\<close>
\end{tabular}
\end{quote}

The \<open>dataspace_assms\<close> state that all lenses \<open>var\<^sub>L\<close> satisfy \<open>vwb_lens\<close> and mutual exclusivity.\<close>

subsubsection \<open>Refinement\<close>

text \<open>Refinement introduces additional proof obligations. It relies on a function \<open>\<pi>\<close> mapping
the new model’s event type to the old model’s event type. This function is automatically defined.
By default all constructors are skipped during refinement (\<open>\<pi>\<close> maps events to \<open>old_model.Skip\<close>
unless another definition is provided).\<close>
(*<*)
lemma
  "\<lbrakk>\<And>s. reach ES s \<Longrightarrow> P (get\<^bsub>var\<^sub>v\<^esub> s);
    model_name\<^sub>0 var0\<^sub>v;
    P (get\<^bsub>var\<^sub>v\<^esub> s);
    G (get\<^bsub>var\<^sub>v\<^esub> s);
    A (get\<^bsub>var\<^sub>v\<^esub> s) (get\<^bsub>var\<^sub>v\<^esub> s');
    P\<^sub>0 (m (get\<^bsub>var\<^sub>0\<^sub>v\<^esub> s))
   \<rbrakk> \<Longrightarrow> G (m (get\<^bsub>var\<^sub>v\<^esub> s)) \<and> A (m (get\<^bsub>var\<^sub>v\<^esub> s)) (m (get\<^bsub>var\<^sub>v\<^esub> s'))"
  subgoal premises ps
    using ps
(*>*)
text\<open>The additional proof obligations are (assumptions omitted):
@{subgoals[display]}\<close>
(*<*)
  oops

(* register eventb attribute *)
setup \<open>Attrib.setup EventB.eventb_attrib
  (Scan.lift (Args.del >> K EventB.eventb_split_del || Scan.succeed EventB.eventb_split_add))
  "Event-B predicate-intro rules for event translation."\<close>

(* this method model_cases is re-defined each time the @{command model} is invoked *)
method model_cases = cases
(*>*)

subsubsection \<open>Generated Constants and Theorems\<close>

text \<open>By default for each \<open>inv\<close> a standard invariant theorem is proved of the form:

\hspace*{1em}\(
  \<open>inv: reach ES ?s \<Longrightarrow> P (get\<close>\)\isactrlbsub\(\mathit{var}_1\<open>\<^sub>v\<close>\)\isactrlesub\(\<open> ?s) \<close>\cdots
    \<open> (get\<close>\)\isactrlbsub\(\mathit{var}_j\<open>\<^sub>v\<close>\)\isactrlesub\(\<open> ?s)\<close>
\)

Whenever a refinement took place a refinement theorem is proved:

\hspace*{1em}\(
  \<open>refines_model_name\<^sub>0:\<close> \\
\)
\hspace*{2em}\(
  \<open>model_name\<^sub>0 ?var \<Longrightarrow> ES \<sqsubseteq>\<^sub>\<pi>_model_name\<^sub>0 model_name\<^sub>0.ES (m ?var)\<close>
\)\<close>

section \<open>The @{method model_cases} Method and @{attribute eventb} Theorems\<close>

text \<open>To keep proof obligations as simple as possible, the infrastructure needs to be able to split
facts about the before-and-after predicates.

To this end this theory introduces a new named attribute @{attribute eventb}. Core theorems for
splitting facts are:\<close>

lemma eventb_if[case_names if_True if_False, eventb]:
  assumes \<open>Q \<Longrightarrow> P x\<close> and \<open>\<not> Q \<Longrightarrow> P y\<close>
  shows \<open>P (if Q then x else y)\<close>
  using assms by simp

lemma eventb_case_sum[case_names Inl Inr, eventb]:
  assumes \<open>\<And>a. x = Inl a \<Longrightarrow> P (f a)\<close> and \<open>\<And>b. x = Inr b \<Longrightarrow> P (g b)\<close>
  shows \<open>P (case_sum f g x)\<close>
  using assms by (auto split: sum.split)

lemma eventb_case_option[case_names None Some, eventb]:
  assumes \<open>mx = None \<Longrightarrow> P y\<close> and \<open>\<And>x. mx = Some x \<Longrightarrow> P (f x)\<close>
  shows \<open>P (case_option y f mx)\<close>
  using assms by (auto split: option.split)

text \<open>These named theorems facilitate structured case analysis which can predictably be dealt with
using @{method model_cases}. For example a refinement proof might look like this
(only interesing cases need to be considered):\<close>

(*<*)
notepad
begin
  consider ("inv:E\<^sub>a") I | ("refine:E\<^sub>a") P | False
    \<proof>
  then have "I \<or> P"
  (*>*)
  proof model_cases
    case "inv:E\<^sub>a"
    then show ?thesis ..
  next
    case "refine:E\<^sub>a"
    then show ?thesis ..
  qed auto
(*<*)
end

(* define outer syntax for Isabelle and register command *)
ML \<open>
local
  val locale_context_elements =
    Scan.repeat1 Parse_Spec.context_element;

  val locale_ext =
    ((Parse_Spec.locale_expression -- Scan.optional Parse_Spec.opening [])) --
    Scan.optional (\<^keyword>\<open>+\<close> |-- Parse.!!! locale_context_elements) [];

  val parse_inv =
    Parse_Spec.simple_specs --
    Scan.optional  (\<^keyword>\<open>uses\<close> |-- Scan.repeat1 Parse.binding) [];

  val parse_evt_spec =
    (Scan.succeed Binding.empty -- Parse.binding) --
      Scan.repeat BNF_FP_Def_Sugar.parse_ctr_arg --
      Parse.opt_mixfix;

  val parse_evt = parse_evt_spec --
    Scan.optional (\<^keyword>\<open>when\<close> |-- Scan.repeat1 Parse.prop) [] --
    Scan.optional (\<^keyword>\<open>do\<close> |-- Scan.repeat1 Parse.prop) [];

  val parse_model =
    (BNF_Util.parse_type_args_named_constrained -- Parse.binding --| \<^keyword>\<open>=\<close>) --
       Scan.optional (\<^keyword>\<open>extends\<close> |-- locale_ext) ((([],[]), []), []) --
       Scan.optional (\<^keyword>\<open>variables\<close> |-- Parse_Spec.locale_fixes) [] --
       (\<^keyword>\<open>initialise\<close> |-- Scan.repeat1 Parse.prop) --
       Scan.optional (\<^keyword>\<open>invariants\<close> |-- Parse.enum1 "and" parse_inv) [] --
       (\<^keyword>\<open>events\<close> |-- Parse.enum1 "|" parse_evt) --
       Scan.option (\<^keyword>\<open>refines\<close>
          |-- Parse.name_position -- Scan.repeat Parse.term
          -- (\<^keyword>\<open>via\<close> |-- Scan.repeat Parse.term)
          -- Parse_Spec.where_multi_specs)
in
  val _ = Outer_Syntax.local_theory_to_proof @{command_keyword model} "Declare an Event-B model."
    (parse_model >> EventB.eventb_cmd)
end\<close>

end
(*>*)
