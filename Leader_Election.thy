(*<*)
theory
  Leader_Election
imports
  EventB
  Ring_network
begin
(*>*)

text \<open>\newpage\<close>

section \<open>Example: Leader Election\<close>

text \<open>This chapter compares the running example of the Leader Election using the newly
defined command. The goal is to highlight, how the command is able to automate model definitions
and goal construction. The user can focus on the interesting bits, no auxiliary constructions
and lemmas are necessary.\<close>

subsection \<open>Abstract System Model\<close>

model ('b::countable) election0 =
  variables leader :: "'b \<Rightarrow> bool"
  initialise "leader = (\<lambda>_. False)"
  invariants
    no_multiple_leaders: "\<forall>i j . leader i \<longrightarrow> leader j \<longrightarrow> i = j"
  events
    Elect (i:'b) when "\<forall>j. leader j \<longrightarrow> i = j" do "leader' = leader(i := True)"
  by auto

thm election0.ES_def
thm election0.no_multiple_leaders

subsubsection \<open>Satisfiability\<close>

text \<open>It easy to define non-sensical locales in Isabelle and the standard way to show that a locale
is not non-sensical is to show that there is at least one inhabitant.

Indeed, the locale has a trivial inhabitant:\<close>

interpretation ec0: election0 "1\<^sub>L"
  by (rule election0.intro, simp)

thm ec0.no_multiple_leaders[unfolded id_lens_def, simplified, folded id_lens_def]


subsection \<open>Protocol Model\<close>

record 'a local1 =
  elected1 :: bool
  chan1 :: "'a set"

abbreviation add_msg_to_chan1 where
  "add_msg_to_chan1 s x msg \<equiv> s(x := s x\<lparr>chan1 := insert msg (chan1 (s x))\<rparr>)"

lemma (in ringnetwork) topEqI: "\<lbrakk>\<And>z. z \<noteq> x \<Longrightarrow> z \<^bold>< x\<rbrakk> \<Longrightarrow> x = \<^bold>\<top>"
  by fastforce

model ('a::countable) election1 =
  extends ringnetwork less for less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix \<open>\<^bold><\<close> 50)
  variables local1 :: "'a \<Rightarrow> 'a local1"
  initialise "local1 = (\<lambda>a. \<lparr>elected1=False, chan1={}\<rparr>)"
  invariants
    \<comment> \<open>if msg is in buffer of x, then all z in the interval between (msg,x)
        are strictly smaller than msg\<close>
    valid_interval: "\<forall>x msg. msg \<in> chan1 (local1 x) \<longrightarrow> (\<forall>z \<in> collect msg x. z \<^bold>< msg)"
    and
    \<comment> \<open>only top can be elected leader\<close>
    leader_top: "\<forall>i. elected1 (local1 i) \<longrightarrow> i = \<^bold>\<top>" uses valid_interval
  events
    \<comment> \<open>add own ID to the next node's buffer\<close>
    Setup (x:'a) do "local1' = add_msg_to_chan1 local1 (nxt x) x"
  | Accept (x:'a) (msg:'a)
      \<comment> \<open>node x received a name msg higher than his own x.\<close>
      when "msg \<in> chan1 (local1 x)" "x \<^bold>< msg"
      \<comment> \<open>forward to next node in ring.\<close>
        do "local1' = add_msg_to_chan1 local1 (nxt x) msg"
  | Elect (z:'a)
      \<comment> \<open>node x received its own name.\<close>
      when "z \<in> chan1 (local1 z)"
        do "local1' = local1(z := (local1 z)\<lparr>elected1 := True\<rparr>)"
  refines election0
    via
      "leader = elected1 \<circ> local1"
    where
      "Elect y \<Zsurj> election0.Elect y"
proof model_cases
  case "leader_top:Elect"
  then show ?case
    using topEqI collect_self by simp
next
  case ("refine:Elect" s a s' y)
  then show ?case
    apply safe
     apply (metis collect_self comp_def extremum_strict)
    by (simp add: fun_upd_comp)
qed ((rule ext)?; clarsimp simp: fun_upd_comp; fastforce dest: collect_nxt_r)+


subsection \<open>Interface Model\<close>

text \<open>We add local input buffers and output buffers. Here, they are modelled as sets and messages
       are never removed from the buffers.\<close>

subsubsection \<open>Local Buffers Model tr2\<close>

record 'a local2 =
  leader2 :: bool      \<comment> \<open>has this node declared itself a leader?\<close>
  ibuf2   :: "'a set"  \<comment> \<open>incoming internal buffer of a node\<close> 
  obuf2   :: "'a set"  \<comment> \<open>outgoing internal buffer of a node\<close>

abbreviation (input) add_msg_to_ibuf2 where 
  "add_msg_to_ibuf2 s x msg \<equiv> s(x := s x \<lparr>ibuf2 := insert msg (ibuf2 (s x))\<rparr>)"

abbreviation (input) add_msg_to_obuf2 where 
  "add_msg_to_obuf2 s x msg \<equiv> s(x := s x \<lparr>obuf2 := insert msg (obuf2 (s x))\<rparr>)"

abbreviation (input) add_msg_to_chan2 where
  "add_msg_to_chan2 s x msg \<equiv> s(x := insert msg (s x))"

model ('a::countable, 'ADDR::countable) election2 =
  extends addressedRingnetwork less top _ _ addr
  for top :: "'a"                   (\<open>\<^bold>\<top>\<close>)
    and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix \<open>\<^bold><\<close> 50)
    and addr :: "'a \<Rightarrow> 'ADDR"
  variables local2 :: "'a \<Rightarrow> 'a local2" and chan :: "'ADDR \<Rightarrow> 'a set"
  initialise
    "local2 = (\<lambda>_. \<lparr>leader2=False,ibuf2={},obuf2={}\<rparr>)" "chan = (\<lambda>_. {})"
  invariants
    inv_buffers:
      "\<forall>x msg. (msg \<in> obuf2 (local2 x) \<longrightarrow> msg \<in> chan (addr x) \<and> x \<^bold>< msg \<or> msg = x) \<and>
               (msg \<in> ibuf2 (local2 x) \<longrightarrow> msg \<in> chan (addr x))"
  events
    Setup (x:'a) do "local2' = add_msg_to_obuf2 local2 x x"
  | Receive (x:'a) (msg:'a)
      when "msg \<in> chan (addr x)"  
        do "local2' = add_msg_to_ibuf2 local2 x msg"
  | Accept (x:'a) (msg:'a)
      \<comment> \<open>node x received a name msg higher than his own x\<close>
      when "msg \<in> ibuf2 (local2 x)" "x \<^bold>< msg"
        do "local2' = add_msg_to_obuf2 local2 x msg"
  | Elect (x:'a)
      when "x \<in> ibuf2 (local2 x)"
        do "local2' = local2(x := local2 x \<lparr>leader2 := True\<rparr>)"
  | Send (x:'a) (msg:'a) (a:'ADDR)
      when "msg \<in> obuf2 (local2 x)" "a = addr (nxt x)"
        do "chan' = add_msg_to_chan2 chan a msg"
  refines election1 "\<^bold>\<top>" ordr nxt less
    via
      "local1 = (\<lambda>x. \<lparr>elected1 = leader2 (local2 x), chan1 = chan (addr x)\<rparr>)"
    where
      "election2.Send x y _ \<Zsurj>
        (if x = y then election1.Setup x
                  else election1.Accept x y)"
    | "election2.Elect x \<Zsurj> election1.Elect x"
proof model_cases
  case ("refine:Send:if_False" s a s' x y msg)
  moreover hence "y \<in> get\<^bsub>chan\<^sub>v\<^esub> s (addr x) \<and> x \<^bold>< y \<or> y = x" by blast
  ultimately show ?case by force
qed (force intro!: ext)+

thm election2.refines_election1

(*<*)
end
(*>*)