structure EventB = struct
  (* raw model specification *)
  type model =
      (((((((binding option * (string * string option)) list * binding) * ((Expression.expression * (xstring * Position.T) list) * Element.context list)) * (binding * string option * mixfix) list) * string list) *
           ((Attrib.binding * string list) * binding list) list)
          *
          (((((binding * binding) * (binding * string) list) * mixfix) * string list) * string list) list)
         *
         ((((string * Position.T) * string list) * string list) * Specification.multi_specs_cmd) option

  type definition = {tm: term, def: thm};
  type function   = {tm: term, simps: thm list, induct: thm};

  (* before-and-after predicates specification *)
  type bap_spec =
    {args: (binding * typ * mixfix) list,
     guards: term list,
     actions: term list,
     accessed: (string * typ) list,
     unmodified: (string * typ) list} Symtab.table;

  (* EventB model information which is stored internally *)
  type model_info =
    {name: string,
     Tnss: (string * sort) list,
     modelp: term,
     lenses: term list,
     vars: (binding * typ * mixfix) list,
     bap: function,
     bap_spec: bap_spec,
     ES: definition,
     init: term list,
     invs: (string * thm) list};
end;

signature EVENTB = sig

  val eventb_cmd: EventB.model -> Proof.context -> Proof.state;
  val eventb_lookup_model: string -> Proof.context -> EventB.model_info option;

  (* intro rules for predicates over events *)
  val eventb_attrib: binding;

  (* event splitting *)
  val eventb_split_add: Context.generic * thm -> Context.generic option * thm option;
  val eventb_split_del: Context.generic * thm -> Context.generic option * thm option;
  val eventb_split_get: Symtab.key -> Proof.context -> thm option;

  (*val eventb: (term * thm) * EventB.model * Proof.context -> thm option list -> thm list list -> Proof.context -> Proof.context;*)
end;

local
  (* complete equations for an event transformation *)
  fun eqs_pi ctxt pi =
    let
      val (num_eqs, all_eqs) = #eqs pi |> `(fn x => length x - 1)
      val eq_from_simp =
        Thm.cprop_of #> Thm.term_of
        #> HOLogic.dest_Trueprop #> HOLogic.dest_eq
        #> pair Binding.empty;
      val rest = Function.get_info ctxt (#tm pi)
        |> #simps |> the
        |> drop num_eqs
        |> map (Variable.import_vars ctxt #> eq_from_simp)
    in
      take num_eqs all_eqs @ rest
    end;

  val eqs_to_spec =
    map (fn eq => (((Binding.empty, []), HOLogic.mk_Trueprop (HOLogic.mk_eq eq)), [], []));

  (* FIXME: primrec does not generate an induction theorem *)
  fun primrec (N, T) specs lthy =
    let
      val lthy' =
        Function_Fun.add_fun [(Binding.name N, SOME T, NoSyn)] (eqs_to_spec specs)
          Function_Fun.fun_config lthy;
      val tm = Free (N, T);
    in
      (case Function.get_info lthy' tm |> ` #inducts ||> #simps of
        (SOME inducts, SOME simps) =>
          {tm=tm, simps=simps, induct=hd inducts}
        | _ => error "fun",
       lthy')
    end;

  (* some sugar for simple definitions from a name and term *)
  fun define N tm =
    Local_Theory.define_internal ((Binding.name N, NoSyn), (Binding.empty_atts, tm))
    #> (fn ((tm, (_, def)), lthy) => ({tm=tm,def=def}, lthy));

  (* fmap type morphisms on models: *)

  fun map_evt_spec_types f {args,actions,guards,accessed,unmodified} =
    {args=map (fn (b,T,m) => (b,f T,m)) args,
     actions=map (map_types f) actions,
     guards=map (map_types f) guards,
     accessed=accessed,
     unmodified=unmodified};

  fun map_model_info_types f {name,Tnss,modelp,init,lenses,vars,bap={tm=bap_tm,simps=bap_simps,induct=bap_induct},bap_spec,ES={tm=ES_tm,def=ES_def},invs} =
    {name=name,
     Tnss=Tnss,
     modelp=map_types f modelp,
     init=map (map_types f) init,
     lenses=map (map_types f) lenses,
     vars=map (fn (b,T,x) => (b,f T,x)) vars,
     bap={tm=map_types f bap_tm,simps=bap_simps,induct=bap_induct},
     bap_spec=Symtab.map (K (map_evt_spec_types f)) bap_spec,
     ES={tm=map_types f ES_tm,def=ES_def},
     invs=invs}

  (* generic helpers *)
  fun on f g (x, y) = f (g x, g y);

  fun fst3 (a, _, _) = a;

  fun all_duplicates eq lst =
    let
      fun dups (rev_dups, []) = rev rev_dups
        | dups (rev_dups, x :: xs) =
            if not (member eq xs x orelse member eq rev_dups x) then
              dups (rev_dups, xs)
            else dups (x :: rev_dups, xs);
    in dups ([], lst) end;

  val list_find =
    let
      fun go k [] _ = k
        | go k (x :: xs) el = (if x = el then k else go (k+1) xs el);
    in go 0 end;

  (* Names & Bindings *)
  fun bstr b = quote (Binding.name_of b) ^ Position.here (Binding.pos_of b);

  fun add_fixes' fixes = Proof_Context.add_fixes fixes #> snd;
  val add_fixes = map (fn (b,T,m) => (b,SOME T,m)) #> add_fixes';

  fun bind_Free (b,T,_) = Free (Binding.name_of b, T);
  val bind_Frees = map bind_Free;

  fun bind_Free' (b,T,_) = Free (Binding.name_of b ^ "'", T);
  val bind_Frees' = map bind_Free';

  (* Types & Terms *)
  val stateT  = TFree ("'st", [@{class type}]);
  val state0T = TFree ("'st0", [@{class type}]);
  val strip_lens = dest_Type #> snd #> hd;

  fun lensT (stT, T) = Lens_Lib.lensT T stT;
  fun mk_lens stT (n, T) = Free (n, lensT (stT, T));

  fun mk_lens_get stT (n, T) =
    let val lT = lensT (stT, T) in
      Const ("Lens_Laws.lens.lens_get", lT --> stT --> T) $
        Free (n, lT)
    end;

  fun lens_getters Ls tm = Ls |>
    map (fn (b,T,_) => mk_lens_get stateT (Binding.name_of b ^ Lens_Lib.lens_suffix, T) $ tm);

  fun mk_lens_put stT (n, T) =
    let val lT = lensT (stT, T) in
      Const ("Lens_Laws.lens.lens_put", lT --> stT --> T --> stT) $
        Free (n, lT)
    end;

  val mk_indeps = Lens_Lib.pairings
    #> map (fn (x, y) => (Lens_Lib.mk_indep (Syntax.free x) (Syntax.free y), []));

  fun mk_ES init trans = Const ("Event_Systems.ES.make", dummyT) $ init $ trans;

  fun mk_eq1 t = HOLogic.eq_const (fastype_of t) $ t;

  val mk_imp = on Logic.mk_implies HOLogic.mk_Trueprop;
  fun mk_imps (hyps, concl) = Logic.list_implies (map HOLogic.mk_Trueprop hyps, HOLogic.mk_Trueprop concl);

  (* un-atomize equality: \<open>?A = ?B\<close> to \<open>?A \<equiv> ?B\<close> *)
  fun eq_reflect thm = thm RS @{thm eq_reflection};

  fun beta_reduce lthy =
       Thm.cterm_of lthy
    #> Thm.beta_conversion true
    #> Thm.rhs_of
    #> Thm.term_of;

  fun unify_match lthy (a, b) =
    Unify.matcher (Context.Proof lthy) [a] [b]
    |> (fn mx => case mx of SOME x => x |> `Envir.type_env ||> Envir.term_env
        | _ => Pretty.str "oops" :: Pretty.fbrk ::
               map (Syntax.pretty_term lthy #> single #> Pretty.item) [a,b]
            |> Pretty.paragraph |> Pretty.string_of |> error);

  (* Proofs & Theorems *)
  fun FOCUS1' f ctxt = (Subgoal.FOCUS (HEADGOAL o f) ctxt);
  val FOCUS1 = HEADGOAL oo FOCUS1';

  fun induct_tac insts rule ctxt = Induct.induct_tac ctxt false
    (map (fn t => [SOME (NONE, (t, false))]) insts) [] [] (SOME [rule]) [];

  fun unfold_tac ctxt =
    map (fn t => eq_reflect t handle THM _ => t)
    #> rewrite_goal_tac ctxt;

  (*fun print_tac' ctxt m = (fn i => print_tac ctxt ("goal #" ^ string_of_int i ^ ": " ^ m));*)
  
  (* join a list of invariants into one (trivial) *)
  local
    fun join_alg lthy x y =
      ((Local_Defs.unfold lthy @{thms atomize_imp} y)
          RS ((Local_Defs.unfold lthy @{thms atomize_imp} x)
          RS @{thm join_invariant}))
      |> Local_Defs.fold lthy @{thms atomize_imp};
  in
    fun join_invs lthy Is = fold_rev (join_alg lthy) Is @{thm ASM_RL}
      |> Local_Defs.unfold lthy @{thms atomize_imp conj_assoc[symmetric]};
  end;

  (* store notes and pretty-print what has just been noted *)
  fun notes what notes lthy =
    Local_Theory.notes notes lthy
    |> tap (fn (notes, ctxt) =>
          if null notes then {} else
            (Pretty.str ("Proved " ^ what ^": ") ::
             map (fn n => Pretty.item [Proof_Context.pretty_fact ctxt n]) notes |> Pretty.fbreaks)
            |> Pretty.block |> Pretty.writeln);

  (* use this to prove theorems (respects quick_and_dirty, just in case there are broken tacs) *)
  fun prove lthy fvars tm tac =
    Goal.prove_sorry lthy fvars [] tm (fn {context, ...} => tac context);

  (* Pretty Printing *)  
  fun add_pos pos =
      Pretty.mark (Markup.properties (Position.properties_of pos) Markup.position);

  fun binding_pretty b = Pretty.str (Binding.name_of b) |> add_pos (Binding.pos_of b);
  val cat = Pretty.block o Pretty.breaks;

in

structure EventB : EVENTB =
struct
  open EventB;

  (* Theorem store for intro rules of predicates over events, used for resolving
     event translation to obtain goals free from generated constants: *)

  val eventb_attrib = @{binding eventb};

  (* store by F where rules are of the form: \<lbrakk>...\<rbrakk> \<Longrightarrow> ?P (F ... :: .event) *)
  val head_name_of =
    head_of #> (fn x => case x of Free (n, _) => n | Const (n, _) => n);

  local
    structure EventbSplits = Generic_Data
    (
      type T = thm Symtab.table;
      val empty = Symtab.empty;
      fun merge data: T = Symtab.merge (K true) data;
    )

    fun head_name_of_thm thm =
         Thm.cconcl_of thm
      |> Thm.term_of
      |> HOLogic.dest_Trueprop
      |> dest_comb |> snd |> head_name_of
      handle _ => error "wrong format for predicate intro";
  in
  fun eventb_split_get k lthy =
    Symtab.lookup (EventbSplits.get (Context.Proof lthy)) k;

  fun eventb_split_add (lthy, thm: thm) =
    let
      val head_name  = head_name_of_thm thm;
      val _ = case Symtab.lookup (EventbSplits.get lthy) head_name of
        NONE => {}
        | _ => warning ("overriding predicate intro for " ^ quote head_name)
    in
      EventbSplits.map (Symtab.update (head_name, thm)) lthy |> SOME |> rpair NONE
    end;

  fun eventb_split_del (lthy, thm) =
    EventbSplits.map (Symtab.delete (head_name_of_thm thm)) lthy |> SOME |> rpair (NONE);
  end;

  (* Model store: store information about Event-B models *)
  local
  structure Model_Data = Generic_Data
  (
    type T = model_info Symtab.table;
    val empty = Symtab.empty;
    fun merge data: T = Symtab.merge (K true) data;
  )
  in
    fun register_model model =
      Local_Theory.declaration {syntax = false, pervasive = true, pos = \<^here>}
        (fn _ => Model_Data.map (Symtab.update (#name model, model)));

    fun eventb_lookup_model name lthy =
      Symtab.lookup (Model_Data.get (Context.Proof lthy)) name
  end;

  (* Model Preparation ****************************************************************************)

  (* prepare context extension *)
  local
  fun map_term _ g (Expression.Positional xtms) = map (Option.map g) xtms |> Expression.Positional
    | map_term f g (Expression.Named nts) = map (fn (n,tm) => (f n, g tm)) nts |> Expression.Named;
  in
  fun prepare_ext ssubst
        lthy ((raw_import, raw_includes), raw_elems) =
    let
      val includes = map (Bundle.check lthy) raw_includes;
      val lthy' = Bundle.includes includes lthy;
      val lthy' = fold (Variable.declare_typ o snd) ssubst lthy';

      val prep_typ  = typ_subst_atomic ssubst o Syntax.read_typ lthy';

      val body_elems = map (fn _ => error "raw elements") raw_elems;

      val fixes = snd raw_import |> map (fn (b,raw_xT,m) => (b, Option.map prep_typ raw_xT,m));

      val prep_term = add_fixes' fixes lthy'
          |> Syntax.read_term #> subst_atomic_types ssubst;

      val imports = fst raw_import |> map (fn (x,(y,(m,rs))) =>
        (Locale.check (Proof_Context.theory_of lthy) x,
         (y, (map_term I prep_term m,
              map (I ##> prep_term) rs))))
    in
      (((imports, fixes), includes), body_elems)
    end
  end;

  (* prepare raw event specification (event datatype and bap predicate) *)
  local
  (* fold whenever predicate holds for Free variable add, or remove when `kill` *)
  fun inspect_alg p kill t (ts: term list) = case t of
      Free nT =>
        (if p nT then (if kill then Ord_List.remove else Ord_List.insert) Term_Ord.term_ord t else I) ts
    | Abs (_, _, body) => inspect_alg p kill body ts
    | f $ t =>  inspect_alg p kill f (inspect_alg p kill t ts)
    | _ => ts;

  fun string_init n = Substring.string (Substring.trimr 1 (Substring.full n));
  fun get_unmodified vars' actions =
    let
      val unmodified_alg = inspect_alg (fn (n, _) => String.isSuffix "'" n) true
    in
      fold unmodified_alg actions (vars' |> Ord_List.make Term_Ord.term_ord)
      |> map (fn Free (n, T) => (string_init n, T) | _ => error "unreachable")
    end;

  fun get_unaccessed unmodified guarded_actions =
      unmodified
      |> Ord_List.make Term_Ord.term_ord
      |> fold (inspect_alg (K true) true) guarded_actions;

  (* find all type variables that are not bound *)
  fun find_extras Tnss (b,T,_) = fold_atyps
        (fn TFree v => if member op= Tnss v then I else cons (b, v)| _ => I) T [];

  (* check whether there are extra type variables or duplicate selectors *)
  fun validate_args Tnss ctorb args lthy =
    (case all_duplicates (on op= (fst3 #> Binding.name_of)) args of
      [] => I
    | sels => cons
        (Pretty.item
         (Pretty.str "Duplicate selectors for" ::
          Pretty.brk 1 :: binding_pretty ctorb :: Pretty.str ":" :: Pretty.brk 1 ::
          Pretty.commas (map (fn (b,T,_) =>
              cat [binding_pretty b, Pretty.str "::", Syntax.pretty_typ lthy T]) sels)))
    ) #>
    (case maps (find_extras Tnss) args of
      [] => I
    | extra_Ts => cons
          (Pretty.item
            (Pretty.str "Extra type variables on right-hand side:" ::
            Pretty.brk 1 ::
            Pretty.commas (map (fn (b, v) =>
               (add_pos (Binding.pos_of b) o Syntax.pretty_typ lthy o TFree) v) extra_Ts)))
    );

  (* check whether there are extra variables not fixed *)
  fun validate_vars which ctorb eqs lthy errs' =
    let val fixes = Variable.dest_fixes lthy |> map fst
    in (case maps (fn tm => inspect_alg (fst #> member op= fixes #> not) false tm []) eqs of
      [] => errs'
    | extra_tms =>
        Pretty.item
          (Pretty.str "Extra variables in " :: Pretty.str which :: Pretty.str " for" ::
           Pretty.brk 1 :: binding_pretty ctorb :: Pretty.str ":" :: Pretty.brk 1 ::
           Pretty.commas (map (Syntax.pretty_term lthy) extra_tms)) ::
        errs'
    ) end

  fun prep_event_specs prep_term prep_typ' Tnss event_name fixes raw_evts lthy =
    let
      fun prepare_event_alg (((((constrb, ctorb), raw_args), mf), raw_guards), raw_actions) =
        let
          (* prepare constructor and args *)
          val args  = raw_args |> map (fn (b, raw_T) => (b, prep_typ' lthy raw_T, NoSyn));
          val args' = filter (fst3 #> Binding.is_empty #> not) args;

          (* prepare guard and action equations *)
          val guards_lthy = lthy |> add_fixes (#vars fixes @ args');
          val actions_lthy = guards_lthy |> add_fixes (#vars' fixes);

          val (guards, guards') = map (prep_term guards_lthy) raw_guards
            |> ` (map (fold_rev lambda (#vars fixes @ args |> bind_Frees)));

          val (actions, actions') = map (prep_term actions_lthy) raw_actions
            |> ` (map (fold_rev lambda (#vars fixes @ #vars' fixes @ args |> bind_Frees)));

          (* validate the specs *)
          val validate =
              validate_args Tnss ctorb args' lthy
              #> validate_vars "guards" ctorb guards guards_lthy
              #> validate_vars "actions" ctorb actions actions_lthy;

          val unmodified = get_unmodified (#vars' fixes |> bind_Frees) actions';
          val accessed = get_unaccessed (map Free unmodified) (guards' @ actions')
            |> Ord_List.make Term_Ord.term_ord
            |> (fn f => fn a => fn b => f b a) (Ord_List.subtract Term_Ord.term_ord)
              (#vars fixes |> bind_Frees |> Ord_List.make Term_Ord.term_ord)
            |> map dest_Free;

          (* add specs *)
          val add_evt_spec = {args=args, guards=guards, actions=actions, accessed=accessed, unmodified=unmodified}
            |> pair (event_name ^ "." ^ Binding.name_of ctorb)
            |> Symtab.insert (K true);

          (* ctor spec for defining the datatype: remove selectors *)
          val args' = map (fn (_,T,_) => (Binding.empty,T)) args;
          val add_ctor_spec = cons (((constrb, ctorb), args'), mf);
        in
          I #>> validate ##> (I #>> add_evt_spec ##> add_ctor_spec)
        end;

      val defaultab =
        Symtab.insert (K true)
          (event_name ^ ".Skip",
           {args=[], guards=[], actions=[],
            accessed=[],
            unmodified=map (fn (b,T,_) => (Binding.name_of b, T)) (#vars fixes)})
          Symtab.empty
    in
      (case fold prepare_event_alg raw_evts ([], (defaultab, [])) of
        ([], (evts_tab, evt_specs)) => (evts_tab, rev evt_specs)
      | (errs, _) => Pretty.fbreaks errs |> Pretty.paragraph |> Pretty.string_of |> error)
      handle Symtab.DUP ee => error ("duplicate constructor: " ^ ee)
    end
  in
    val prepare_event_specs = prep_event_specs Syntax.check_term;
    val prepare_event_specs_cmd = prep_event_specs Syntax.read_term;
  end;

  (* define the event datatype *)
  local
  fun add_datatype (Tnss, tname) ctors =
    let
      val opts = Ctr_Sugar.default_ctr_options;
      val tvs  = map (`TFree ##> snd #> pair NONE) Tnss
      val mapr = (Binding.empty, Binding.empty, Binding.empty);
      val sels = []
    in
      BNF_FP_Def_Sugar.co_datatypes BNF_Util.Least_FP BNF_LFP.construct_lfp
        (opts, [(((((tvs, Binding.name tname), NoSyn), ctors), mapr), sels)])
    end;
  in
  fun prepare_datatype_cmd Tnss (typn, typb) ctors lthy =
    let
      val skip = typn ^ ".Skip";
      val skip_ctor = (((Binding.empty, Binding.name "Skip"), []), NoSyn);

      (* define datatype *)
      val lthy' = add_datatype (Tnss, Binding.name_of typb) (skip_ctor :: ctors) lthy;

      val evtT = Syntax.read_term lthy' skip |> fastype_of |> body_type;
    in
      ((evtT, skip), lthy')
    end
  end;

  (* prepare refinement (infer type from state mediator and merge with event translation) *)
  local

  type pi = {name: binding, typ: typ, tm: term, eqs: (binding * (term * term)) list};
  fun map_types_pi f {name,typ,tm,eqs} =
    {name=name,typ=f typ,tm=map_types f tm,eqs=map (I ##> apply2 (map_types f)) eqs};

  fun dest_all_alg rev_vars tm =
    if Logic.is_all tm then
        let val (v, tm') = Logic.dest_all_global tm
         in dest_all_alg (v :: rev_vars) tm' end
      else (rev rev_vars, tm)

  fun unexpected lthy tm = [Pretty.str "Unexpected term: ", Syntax.pretty_term lthy tm]
    |> Pretty.paragraph |> Pretty.string_of |> error;

  (* internal mixfix syntax *)
  val mf =
    Infix (Input.source true "\127\<Zsurj>\127" Position.no_range, 25, Position.no_range);

  fun warn_attribs attribs =
    if null attribs then {} else
      Pretty.str ("Ignoring attribute(s): " ^
        commas (map (map (Token.print #> quote) #> commas) attribs))
      |> Pretty.string_of |> warning;

  fun prep_pi lthy (refines, raw_pi_specs) =
    let
      (* event transformation *)
      val pib = Binding.name ("\<pi>_" ^ Long_Name.base_name refines);
  
      val dest_all = dest_all_alg []
  
      fun split_spec lthy tm =
        let
          val (vars, body') = dest_all tm
            ||> HOLogic.dest_Trueprop;
        in
          (vars,
           case strip_comb body' of
              (Free (n, _), [lhs, rhs]) =>
                if n = Binding.name_of pib
                  then (lhs, rhs)
                  else unexpected lthy body'
            | _ => unexpected lthy body')
        end;
  
      val ((evtT', event0T), pi_specs') =
        lthy
        |> Specification.read_multi_specs
            [(pib, NONE, mf)]
            raw_pi_specs
        |>> (I ##> map (I ##> split_spec lthy))
        |> fst
        |>> (hd #> fst #> snd (* _ event \<Rightarrow> _ \<Rightarrow> bool *)
             #> strip_type #> fst #> (fn [T,U] => (T, U) | _ => error "ill formed"));
  
      val piT = evtT' --> event0T;
      val pi_tm = Free (Binding.name_of pib, piT);
  
      val eqs =
        pi_specs'
        |> map (fn ((n, attribs), (_, (e,e0))) =>
            let val _ = warn_attribs attribs
             in (n, (pi_tm $ e, e0)) end)
        |> (fn eqs => append eqs
             [(Binding.empty,
               (pi_tm $ Term.dummy_pattern evtT', Const (refines ^ ".event.Skip", event0T)))])
    in
      {name=pib, typ=piT, tm=pi_tm, eqs=eqs}
    end;

  fun assert_types lthy ((b0, T0, mf) :: (b, T, _) :: rest) =
        if T0 = T then (b0, T0, mf) :: assert_types lthy rest else
          [Pretty.str "variables with different types: ",
           binding_pretty b0, Pretty.keyword1 "::", Syntax.pretty_typ lthy T0,
           binding_pretty b, Pretty.keyword1 "::", Syntax.pretty_typ lthy T]
          |> Pretty.breaks |> Pretty.paragraph |> Pretty.string_of |> error
    | assert_types _ [] = []
    | assert_types _ _ = error "ill-formed variables"

  val schematize = map_type_tfree (I #>> rpair 0 #> TVar);
  in
  fun prepare_refinement_cmd Tnss fixes (((raw_model0, raw_model0_tms), raw_meqs), raw_pi_specs) lthy =
    let
      val thy = Proof_Context.theory_of lthy;
      val refines = Locale.check thy raw_model0;

      val model = eventb_lookup_model refines lthy |> the;
      val model_tms = map (Syntax.read_term lthy) raw_model0_tms;

      val abs_mediator = bind_Frees (#vars fixes) |> fold_rev lambda;
      val vars0 = #lenses model
        |> map_filter (dest_Free #> (fn (n,T) =>
            if String.isSuffix Lens_Lib.lens_suffix n
              then SOME (Lens_Lib.remove_lens_suffix n |> Binding.name,
                         schematize (strip_lens T), NoSyn)
              else NONE));

      val cmp = fst3 #> Binding.name_of;
      val del_dups =
        all_duplicates (on op= cmp) (vars0 @ #vars fixes)
        |> sort (on fast_string_ord cmp)
        |> assert_types lthy
        |> subtract (on op= cmp)

      val lthymeqs = add_fixes (#vars fixes) lthy;

      fun die xdetail tms =
        Pretty.str "Invalid mediator equation"
          :: (case xdetail of SOME detail => [Pretty.str " (", Pretty.str detail, Pretty.str ")"] | _ => [])
          @ Pretty.str ": " :: map (Syntax.pretty_term lthy) tms
          |> Pretty.paragraph |> Pretty.string_of |> error;

      (* stated equations *)
      val meqs = map (HOLogic.dest_eq o Syntax.read_term lthymeqs) raw_meqs
        handle TERM (_,tms) => die (SOME "not an equation") tms;
      val meqtab = map (fst #> dest_Free) meqs |> Symtab.make
        handle TERM (_,tms) => die (SOME "invalid lhs") tms;

      (* required/valid *)
      val reqs = del_dups vars0;
      val v0tab =
        reqs
        |> map (fn (b,T,_) => (Binding.name_of b, T))
        |> Symtab.make;

      (* validate *)
      val expected = reqs |> fold (fn (b,T',_) =>
        let val n = Binding.name_of b in
        case Symtab.lookup meqtab n of
          SOME _ => I
        | NONE => I #>> cons (Pretty.item
            [Pretty.str "Expected mediator equation for ",
             Syntax.pretty_term lthy (Free (Binding.name_of b, T'))])
        end);

      val given = meqs |> fold (fn (lhs, rhs) =>
        let val (n, T) = dest_Free lhs in
        case Symtab.lookup v0tab n of
            SOME T' => I ##>
              Symtab.insert (K true) (n, ((T, T'), abs_mediator rhs))
          | NONE => I #>> cons (Pretty.item
              (Pretty.str "Invalid head for mediator equation:" ::
               Pretty.brk 1 :: Syntax.pretty_term lthy lhs :: []))
        end);

      val specstab =
        (case ([], Symtab.empty) |> expected |> given of
          ([], x) => x
        | (errs,_) => Pretty.fbreaks errs |> Pretty.paragraph
                      |> Pretty.string_of |> error);

      fun infer_alg (n, (tc, tm)) tyenv = Type.raw_unify tc tyenv
        handle Type.TUNIFY => Pretty.item
            [Pretty.str "In equation for ", Pretty.str n,
             Pretty.str ", cannot match ", Syntax.pretty_typ lthy (fst tc),
             Pretty.str " with ", Syntax.pretty_typ lthy (snd tc),
             Pretty.str ": ", Syntax.pretty_term lthy tm |> Pretty.cartouche]
          |> Pretty.string_of |> error;

      (* type inference and instantiate types *)
      val tyenv = fold infer_alg (Symtab.dest specstab) Vartab.empty
        |> Type.raw_unify (stateT, TVar (("'st", 0), @{sort type}))
        |> Type.raw_unify (state0T, TVar (("'st0", 0), @{sort type}));

      fun type_lookup tyenv (v as (N,S)) =
        case Type.lookup tyenv v of
          NONE =>
            Pretty.str ("Extra type variable in event translation: ") ::
            [Syntax.pretty_typ lthy (TVar (N,S))]
              |> Pretty.paragraph |> Pretty.string_of |> error
        |  SOME T => T;

      val type_of = map_type_tvar (type_lookup tyenv)

      (* ordered specs with inferred types *)
      val specs = vars0 |>
        map (fn (b,T',_) =>
          let val n = Binding.name_of b in
          case Symtab.lookup specstab n of
              SOME ((T,_), tm) => (n, type_of T, tm)
            | NONE => (n, T', Free (n, T') |> abs_mediator)
          end);

      (* prepare event transformation *)
      val pi = prep_pi lthy (refines, raw_pi_specs);
                     
      val pi_Tvars = #typ pi |> binder_types |> hd |> dest_Type |> snd
        |> map (dest_TFree #>> rpair 0 #> TVar)

      (* merge tyenvs and propagate *)
      val type_of = tyenv
        |> fold2 (Type.raw_unify oo pair) (map TFree Tnss) pi_Tvars
        |> map_type_tvar o type_lookup;

      val st0 = typ_subst_atomic [(stateT, state0T)]
      val pi' = pi |> map_types_pi (schematize #> type_of)

      (* define event transformation *)
      val lthy' = lthy
        |> Function_Fun.add_fun [(#name pi', NONE, NoSyn)]
            (#eqs pi' |> map snd |> eqs_to_spec) Function_Fun.fun_config;
    in
      ({model=map_model_info_types (schematize #> type_of #> st0) model,
        model_name=refines,
        ext_tms=model_tms,
        mediator=specs,
        pi=pi'
       }, lthy')
    end
  end;

  (* prepare complete raw model *)
  local
  fun prep_model prep_sort prep_typ prep_term prep_att prep_event_specs prep_datatype prep_refinement lthy
    (((((((raw_tvs, raw_name), raw_ext), raw_vars), raw_init_eqs), raw_invs), raw_evts), raw_xrefines) =
    let
      (* prepare sorted tvs *)
      fun sort_of NONE = @{sort type}
        | sort_of (SOME s) = prep_sort lthy s;

      val Tnss = map (snd #> (fn (Tn, xs) => (Tn, sort_of xs))) raw_tvs;

      (* fix sorts *)
      val ssubst = map (TFree o rpair @{sort type} o fst) Tnss ~~ map TFree Tnss;
      val prep_typ' = typ_subst_atomic ssubst oo prep_typ;

      (* validate binding *)
      val _ =
        let
          val name = Local_Theory.full_name lthy raw_name
        in
          if Locale.defined (Proof_Context.theory_of lthy) name then
            error ("Duplicate definition of state/locale " ^ quote name) else name
        end;

      (* prepare model variables *)
      val vars = (case map_filter (fn (b,NONE,_) => SOME b | _ => NONE) raw_vars of
        vs as (_ :: _) => error ("variables without type annotations:" ^ commas (map bstr vs))
      | _ => map (fn (b,xT,m) => (b, prep_typ' lthy (the xT), m)) raw_vars
      );

      val _ = (case all_duplicates (on op= (fst3 #> Binding.name_of)) vars of [] => {}
        | dups => error ("Duplicate state variables: " ^ commas (map (fst3 #> bstr) dups)));

      val fixes = {vars=vars, vars'=map (fn (b,T,m) => (Binding.suffix_name "'" b, T, m)) vars};

      (* prepare imports *)
      val ((import, includes), ext_elems) = prepare_ext ssubst lthy raw_ext;

      (* define lenses and add locale *)
      val lenses = map (fn (b,T,m) => (Binding.suffix_name Lens_Lib.lens_suffix b, SOME (lensT (stateT, T)), m)) vars;
      val lens_assms =
        let
          val lens_names = map (Binding.name_of o fst3) lenses;

          val lens = @{attributes [simp]};
          val mk_vwb_lens = Lens_Lib.mk_vwb_lens o Syntax.free
        in
          ((Binding.name "lens", lens), map (fn n => (mk_vwb_lens n, [])) lens_names) ::
          (if length lens_names > 1 then
            [((Binding.name "indeps", lens), mk_indeps lens_names)]
          else [])
        end;

      val elems = [Element.Fixes lenses, Element.Assumes lens_assms] @ ext_elems;

      val (name, lthy') = Local_Theory.exit_global lthy
        |> Expression.add_locale raw_name Binding.empty includes import elems;

      val fvars = #vars fixes |> bind_Frees;

      (* prepare initialisation and invariants *)
      val (init_eqs, invs) =
        let
          val lthy'' = lthy' |> add_fixes (#vars fixes);

          val (rev_invns, invtab) = fold (fn (((b, raw_attrs), raw_tms), raw_deps) => fn (accb, accs) =>
            let
              val n = Binding.name_of b;

              val _ = Symtab.defined accs n andalso
                Pretty.str "duplicate invariant: " :: [binding_pretty b]
                  |> Pretty.paragraph |> Pretty.string_of |> error;

              val _ = (case filter (not o Symtab.defined accs o Binding.name_of) raw_deps of
                  [] => {}
                | undeps => Pretty.str "undefined invariants: " :: map binding_pretty undeps
                    |> Pretty.paragraph |> Pretty.string_of |> error
                );

              val tm = map (prep_term lthy'') raw_tms
                |> BNF_GFP_Rec_Sugar.mk_conjs
                |> fold_rev lambda fvars;

              (*val deps = map Binding.name_of raw_deps;*)

              val attrs = map (prep_att lthy) raw_attrs
            in
              (b :: accb, Symtab.insert (K true) (n, {tm=tm,deps=raw_deps,attrs=attrs}) accs)
            end) raw_invs ([], Symtab.empty);

          val init_eqs = map (prep_term lthy'' #> fold_rev lambda fvars) raw_init_eqs;
        in
          (init_eqs, (rev rev_invns, invtab))
        end;
      (* prepare data type (instantiate with fresh type variables) *)
      val (fresh_Tnss, _) = Variable.invent_types (map snd Tnss) lthy';
      val fsubst = map TFree Tnss ~~ map TFree fresh_Tnss;
      val fsubst' = map swap fsubst;

      (* prepare events specification *)
      val event_name = Binding.name "event" |> `(Local_Theory.full_name lthy');

      val (evt_specs, ctors) =
        prep_event_specs prep_typ' Tnss (fst event_name) fixes raw_evts lthy'
        ||> map (I #>> (I##> map (I ##> typ_subst_atomic fsubst)));

      val ((fresh_evtT, skipn), lthy'') = prep_datatype fresh_Tnss event_name ctors lthy';
      val evtT = fresh_evtT |> typ_subst_atomic fsubst';

      (* prepare refinement *)
      val (xrefines, lthy'') = (case raw_xrefines of
        NONE => (NONE, lthy'')
        | SOME refines => prep_refinement Tnss fixes refines lthy'' |>> SOME);
    in
      ({Tnss=Tnss,name=name,vars=vars,init=init_eqs,invs=invs,
        evts=evt_specs,evtT=evtT,skip=skipn,xrefines=xrefines},
       lthy'')
    end
  in
    (*val prepare_model = prep_model (K I) (K I) (K I) (K I) prepare_event_specs;*)
    val prepare_model_cmd = prep_model Syntax.read_sort Syntax.read_typ Syntax.read_term 
      Attrib.check_src prepare_event_specs_cmd prepare_datatype_cmd prepare_refinement_cmd
  end;

  fun init_eq fvars =
    #init
    #> map (list_comb o rpair fvars)
    #> BNF_GFP_Rec_Sugar.mk_conjs
    #> fold_rev lambda fvars

  (* Model Definition *****************************************************************************)
  local
  fun define_refinement model refines lthy =
    let
      val [s, s'] =
        Variable.variant_frees lthy [] [("s", stateT), ("s'", stateT)]
        |> map Free

      (* construct mediator definition *)
      val mediator =
        #mediator refines
        |> map (fn (n, T, tm) => (n ^ Lens_Lib.lens_suffix, (T, tm)))
        |> Variable.variant_frees lthy [];
      val lenses0 = map (fn (n, (T, _)) => mk_lens state0T (n,T)) mediator;

      val med_tm' =
        fold (fn (n, (T, tm)) => fn acc =>
                mk_lens_put state0T (n, T) $ acc $ list_comb (tm, lens_getters (#vars model) s))
             mediator (BNF_GFP_Util.mk_undefined state0T)
        |> lambda s
        |> fold_rev lambda lenses0;

      val (med, lthy) = define "med" med_tm' lthy

     in (SOME {lenses0=lenses0,med=med,pi= #pi refines}, lthy) end;

  fun mk_bap_lhs evtT (s, s', arg_tms) (n, T) =
    let
      val ev = list_comb (Const (n,T), arg_tms)
    in
      Free ("\<delta>", stateT --> evtT --> stateT --> HOLogic.boolT) $ s $ ev $ s'
    end

  fun mk_bap_rhs vars (svars, svars', arg_tms) (Gs': term list) (As': term list) Us' =
    let
      val unmodified_eqs =
        Us'
        |> map (fn (n,T) => HOLogic.mk_eq (Free (n ^ "'", T), Free (n,T))
            |> fold_rev lambda
                (bind_Frees vars @
                 map (fn (b,T,_) => Free (Binding.name_of b ^ "'",T)) vars @
                 arg_tms));

      (* instantiate with lenses *)
      val Gs = map (list_comb o rpair (svars @ arg_tms)) Gs';
      val As = map (list_comb o rpair (svars @ svars' @ arg_tms)) (As' @ unmodified_eqs)
    in
      on HOLogic.mk_conj BNF_GFP_Rec_Sugar.mk_conjs (Gs, As)
    end;
  in
  fun define_model model lthy =
    let
      val (lthy_names, [s, s']) =
        Variable.variant_frees lthy [] [("s", stateT), ("s'", stateT)]
        |> map Free
        |> `(fn tms => fold Variable.declare_term tms lthy)

      val (svars, svars') = apply2 (lens_getters (#vars model)) (s, s');

      (* construct bap equations *)
      val bap_eqs = Function_Lib.inst_constrs_of lthy (#evtT model) |> map
        (fn Const (n, T) =>
           let
              val {args,actions,guards,unmodified,...} = Symtab.lookup (#evts model) n |> the;

              (* create new terms for arguments and states *)
              val arg_tms = map (fn (b,T,_) => (Binding.name_of b, T)) args
                |> Variable.variant_frees lthy_names [] |> map Free
            in
              (mk_bap_lhs (#evtT model) (s, s', arg_tms) (n,T),
               mk_bap_rhs (#vars model) (svars, svars', arg_tms) guards actions unmodified)
            end
         (* should not get here *)
         | c => Pretty.block [Pretty.str "illegal ctor: ", Syntax.pretty_term lthy c]
                |> Pretty.string_of |> error);

      (* define bap *)
      val bapT = stateT --> #evtT model --> stateT --> HOLogic.boolT;
      val (bap, lthy') = primrec ("\<delta>", bapT) bap_eqs lthy

      (* construct ES definition *)
      val fvars = #vars model |> bind_Frees
      val init_tm = list_comb (init_eq fvars model, svars) |> lambda s;
      val ES_tm = Free ("ES", Type ("Event_Systems.ES", bapT |> binder_types |> drop 1));
      val ES_def = mk_eq1 ES_tm $ mk_ES init_tm (#tm bap);

      val ((ES_tm, (_, ES_def)), lthy') = lthy' |>
        Specification.definition
          (SOME (Binding.name "ES", NONE, NoSyn)) [] []
          ((Binding.empty, []), HOLogic.mk_Trueprop ES_def)

      (* define refinement *)
      val (xrefine, lthy') =
        (case #xrefines model of
            SOME refines => define_refinement model refines lthy'
         | _ => (NONE, lthy'))

    in ({bap=bap, ES={tm=ES_tm, def=ES_def}, xrefine=xrefine}, lthy') end
  end;

  (**)

  fun bind_model_cases names =
    Method.local_setup @{binding model_cases}
      (CONTEXT_METHOD (Method.goal_cases_tac names |> K) |> K |> Scan.succeed)
      "model_cases - to insert case names";

  local
  fun model_invs model =
    let val (invns, invtab) = #invs model
     in map (fn b =>
          let val n = Binding.name_of b
           in n |> Symtab.lookup invtab |> the |> pair n end) invns
    end;

  fun mk_inv_goal model lthy (invn:bstring,inv: {attrs: Token.T list list, tm: term, deps: binding list}) =
    let
      val fvars  = #vars model |> bind_Frees;
      val fvars' = #vars model |> bind_Frees';

      val deps = #deps inv |> map
        (Binding.name_of
          #> Symtab.lookup (#invs model |> snd) #> the
          #> #tm #> (list_comb o rpair fvars));

      val ctorns = Function_Lib.inst_constrs_of lthy (#evtT model) |> map (dest_Const #> fst);
      val rev_nevt_hypss =
        fold
          (fn ctorn =>
            let
              val spec  = the (Symtab.lookup (#evts model) ctorn);
              val fargs = #args spec |> bind_Frees
            in
              ((invn ^ ":" ^ Long_Name.base_name ctorn),
               deps @ list_comb (#tm inv, fvars) ::
               map (list_comb o rpair (fvars @ fargs)) (#guards spec) @
               map (list_comb o rpair (fvars @ fvars' @ fargs)) (#actions spec) @
               map (fn (n,T) => HOLogic.mk_eq (Free (n ^ "'",T), Free (n,T))) (#unmodified spec))
              |> cons end)
          (tl ctorns) [];

      val evt_concl = list_comb (#tm inv, fvars')
    in
      ((invn ^ ":initialise", mk_imp (list_comb (init_eq fvars model, fvars), list_comb (#tm inv, fvars))) ::
      map (I ##> mk_imps o rpair evt_concl) (rev rev_nevt_hypss))
    end
  in

  fun prove_invs inp thmss lthy =
    let
      val (invns, invtab) = #invs inp;
      val s = Variable.variant_frees lthy [] [("s", stateT)] |> map Free |> the_single;

      fun alg (invb, init_intro :: inv_intros) (rev_notes, thmtab: thm Symtab.table) =
        let
          val invn = Binding.name_of invb;
          val inv  = Symtab.lookup invtab invn |> the;

          (* get the theorem dependencies *)
          val deps = map (Binding.name_of #> Symtab.lookup thmtab #> the) (#deps inv);

          (* construct invariant theorem *)
          val ES_tm = #tm (#ES inp);
          val EST = fastype_of ES_tm;
          val reach_tm = Const ("Event_Systems.reach", EST --> stateT --> HOLogic.boolT);

          val vars = lens_getters (#vars inp) s;
          val tm = (reach_tm $ ES_tm $ s, list_comb (#tm inv, vars))
                |> on Logic.mk_implies HOLogic.mk_Trueprop;

          val ES_init = (#def (#ES inp) RS @{thm ES_make_init});
          val ES_trans = (#def (#ES inp) RS @{thm ES_make_trans});

          (** construct tactic for proofs **)
          fun inv_tac ctxt inv_intro = HEADGOAL
            (FOCUS1' (fn {context,prems,...} =>
              Method.insert_tac context (map (fn dep => hd prems RS dep) deps)
            ) ctxt THEN'
            resolve_tac ctxt [inv_intro] THEN_ALL_NEW
            Clasimp.fast_force_tac ctxt);

          fun tac ctxt = EVERY
             ([HEADGOAL (induct_tac [s] @{thm reach.induct} ctxt),
               Local_Defs.unfold0_tac ctxt [ES_init, ES_trans],
               (* 1: init ES s \<Longrightarrow> inv s *)
               HEADGOAL (resolve_tac ctxt [init_intro] THEN_ALL_NEW assume_tac ctxt),
               (* 2: trans ES s e s' \<Longrightarrow> inv s \<Longrightarrow> inv s' *)
               Local_Defs.unfold0_tac ctxt @{thms atomize_imp},
               FOCUS1 (fn {context,params,...} =>
                 let
                  val induct_thm =
                    #induct (#bap inp)
                    |> infer_instantiate' context (NONE :: map (SOME o snd) params)
                 in resolve_tac context [induct_thm] end) ctxt,
               Local_Defs.unfold0_tac ctxt (@{thms atomize_imp[symmetric]} @ #simps (#bap inp)),
               (* 2.1: Skip *)
               HEADGOAL (Clasimp.fast_force_tac ctxt)] @
               ALLGOALS (eresolve_tac ctxt @{thms conjE}) ::
               (* 2.2-: remaining events *)
               map (inv_tac ctxt) inv_intros);

          val thm = prove lthy ["s"] tm tac
        in
          (((invb, #attrs inv), [([thm], [])]) :: rev_notes,
           Symtab.insert (K true) (invn, thm) thmtab)
        end
        | alg _ _ = error "ill-formed theorems"

      val (rev_notes, _) = fold alg (ListPair.zip (invns, thmss)) ([], Symtab.empty)
    in
      notes "invariants" (rev rev_notes) lthy
    end;

  fun after_qed_refinement N0 invs thms lthy =
    let
      val invs_thm = Object_Logic.rulify lthy (join_invs lthy invs) RSN (1, @{thm conjunct1});
      val refinement_thm =
        @{thm TrueI} RS
          ((invs_thm RS the_single thms)
           |> Local_Defs.unfold lthy @{thms atomize_imp atomize_all trivial}
           |> Object_Logic.rulify lthy)
      val note = ((Binding.name ("refines_" ^ N0), []), [([refinement_thm], [])])
      val (_, lthy') = notes "refinement" [note] lthy
    in
      (SOME refinement_thm, lthy')
    end;

  fun after_qed aux thmss lthy =
    let
      val (modelp, loctms) =
        #name aux
        |> Locale.specification_of (Proof_Context.theory_of lthy)
        |>> (the #> HOLogic.dest_Trueprop #> strip_comb)
        ||> (fn defs => if null defs then {} else
              Pretty.str "dropping defines: " ::
              Pretty.breaks (map (Syntax.pretty_term lthy #> Pretty.cartouche) defs)
              |> Pretty.item |> Pretty.string_of |> warning)
        |> fst;

      (** invariant proofs **)
      val (nthms, lthy') = prove_invs aux thmss lthy;

      (* refinement proofs *)
      val (_, lthy') = lthy' |>
        (case #refinement aux of
            SOME r =>
            let
              val N0 = #name (#model r) |> Long_Name.base_name
              val (num_invs, all_invs) = maps snd nthms |> `length
            in
              after_qed_refinement N0 (take num_invs all_invs) (drop num_invs thmss |> the_single)
            end
          | _ => pair NONE)

      (* store model info *)
      val phi = Proof_Context.export_morphism lthy' (#original_lthy aux)

      val model_info: model_info =
        {name = #name aux,
         Tnss = #Tnss aux,
         modelp = modelp,
         init = #init aux,
         lenses= drop (length loctms - length (#vars aux)) loctms,
         vars = #vars aux,
         bap = {tm = #tm (#bap aux), simps = #simps (#bap aux) |> map (Morphism.thm phi), induct = #induct (#bap aux) |> Morphism.thm phi},
         bap_spec = #bap_spec aux,
         ES={tm = #tm (#ES aux),def = #def (#ES aux) |> Morphism.thm phi},
         invs=map (I ##> the_single ##> Morphism.thm phi) nthms}

    in register_model model_info lthy' end;

  (* transform goal "ES0 \<Longrightarrow> ES \<sqsubseteq>\<^sub>\<pi> ES0" into theorems(s) [init, trans, I, J] *)
  local
(**)
local
fun bap_intro_alg (evt_specs0, lthy) acc tm =
  let
    val (k, tm') = strip_comb tm |> fst |> `head_name_of;
  in
    case Symtab.lookup evt_specs0 k of
      SOME spec => (@{thm asm_rl}, acc)
    | NONE =>
      let
        val thm = case eventb_split_get k lthy of
          NONE =>
            [Pretty.str "No ",
             binding_pretty eventb_attrib,
             Pretty.str " theorem for term: ",
             Syntax.pretty_term lthy tm']
            |> Pretty.paragraph |> Pretty.string_of |> error
          | SOME thm => thm;

        val case_names = Rule_Cases.get thm |> fst |> map (fst #> fst)

        val (hyps', concl') = thm
          |> `(Thm.cprems_of #> map Thm.term_of)
          ||> (Thm.cconcl_of #> Thm.term_of #> HOLogic.dest_Trueprop);

        val (matched, tenv) =
          unify_match lthy (concl', tm)
          |> `(fn env as (tyenv,_) =>
              Envir.subst_term_types tyenv #> Envir.subst_term env)
          ||> (snd #> Vartab.dest #> map (I ##> snd ##> Thm.cterm_of lthy))
      in
        infer_instantiate lthy (tenv |> tl) thm
        |> (fn x => (x, []))
        |> fold
            (fn (hyp', case_name) => fn (b, acc') =>
                let
                  val hyp = Logic.dest_all_global hyp' |> snd handle TERM _ => hyp';
                  val (a, acc'') = Logic.strip_imp_concl hyp
                    |> HOLogic.dest_Trueprop
                    |> beta_reduce lthy
                    |> bap_intro_alg (evt_specs0, lthy) (map (cons case_name) acc)
                 in
                   (a RS  b, acc'' @ acc')
                 end)
            (map2 (pair o matched) hyps' case_names)
      end
  end;

  in
    fun refine_bap_intro (evt_specs0, lthy) tm0 =
      bap_intro_alg (evt_specs0, lthy) [[]] tm0 ||> rev ||> map rev
  end
(**)

  fun delta_intro_tac bap_spec0 (tm, tm0) {params,context,...} =
    let
      val argsubst =
        (dest_comb tm |> snd |> strip_comb |> snd) ~~ (drop 3 params |> map (snd #> Thm.term_of));
      val (intro, _) = refine_bap_intro (bap_spec0, context) (subst_atomic argsubst tm0)
    in
      resolve_tac context [intro]
    end

  fun refinement_tac
        {vars,bap,ES,mediator,refine={pi,med,lenses0,...},
         name0,bap0,ES0,invs0,bap_spec0,
         ...}
        {prems,context=ctxt,...} =
    let
      val [I_thm, loc_assm0] = prems;
      fun inst thm = loc_assm0 RS thm;

      (* prove "getters" *)
      fun find_theorems x = Find_Theorems.find_theorems ctxt NONE NONE true
            [(true, Find_Theorems.Name (name0 ^ "." ^ x))]
        |> snd |> map snd;

      val lens_thms0 = find_theorems "indeps" |> map inst;
      val lens_thms = find_theorems "lens"
        |> map (fn thm => inst thm RS @{thm vwb_weakI[THEN weak_lens.put_get]});

      fun lens_get_pi_tac ctxt =
        Local_Defs.unfold0_tac ctxt [#def med] THEN
        (REPEAT1 o HEADGOAL o FIRST' o map EVERY')
         [[EqSubst.eqsubst_tac ctxt [1] @{thms lens_indep.lens_put_irr2},
           eresolve_tac ctxt lens_thms0],
          [EqSubst.eqsubst_tac ctxt [1] @{thms lens_indep.lens_put_irr1},
           Clasimp.fast_force_tac ctxt],
          [EqSubst.eqsubst_tac ctxt [1] lens_thms]]
        THEN HEADGOAL (resolve_tac ctxt @{thms refl});

      val s = Variable.variant_frees ctxt [] [("s", stateT)] |> hd |> Free;

      val lens_get_thms = map (fn (N, T, tm) =>
        (mk_lens_get state0T (N ^ Lens_Lib.lens_suffix,T) $ (list_comb (#tm med, lenses0) $ s),
         list_comb (tm, lens_getters vars s))
        |> HOLogic.mk_eq |> HOLogic.mk_Trueprop) mediator
        |> map (fn tm => prove ctxt (map fst3 mediator @ ["s"]) tm lens_get_pi_tac);

      val simulation_thm =
        infer_instantiate ctxt [(("h", 0), Thm.cterm_of ctxt (list_comb (#tm med, lenses0)))]
        @{thm simulate_ES_fun_with_invariants};

      val J_thm = invs0 |> map (snd #> inst) |> join_invs ctxt;

      (* event transformation *)
      val (pi_induct, pi_simps) = 
        (case Function.get_info ctxt (#tm pi) |> ` #inducts ||> #simps of
           (SOME inducts, SOME simps) => (hd inducts, simps)
         | _ => error "invalid pi"
        );

    in EVERY [
      HEADGOAL (resolve_tac ctxt [simulation_thm]),
      (* 4: reach (ES0 ...) t \<longrightarrow> J t *)
      resolve_tac ctxt [J_thm] 4,
      (* 3: reach ES s \<longrightarrow> I s *)
      (resolve_tac ctxt [@{thm impI}] THEN' eresolve_tac ctxt [I_thm]) 3,
      (**)
      HEADGOAL (unfold_tac ctxt
        ([#def ES RS @{thm ES_make_init},
          loc_assm0 RS #def ES0 RS @{thm ES_make_init}] @
          lens_get_thms)),
      (**)
      EVERY'
        [unfold_tac ctxt @{thms atomize_imp},
         resolve_tac ctxt [pi_induct] THEN_ALL_NEW
           unfold_tac ctxt
             (pi_simps @ [#def ES RS @{thm ES_make_trans}] @
              #simps bap @ @{thms atomize_imp[symmetric]}),
         RANGE (eqs_pi ctxt pi |> map (fn (_, eq) =>
           Subgoal.FOCUS (HEADGOAL o delta_intro_tac bap_spec0 eq) ctxt THEN_ALL_NEW
           (unfold_tac ctxt
             ([inst (#def ES0) RS @{thm ES_make_trans}] @
              map inst (#simps bap0) @ lens_get_thms) THEN'
            (resolve_tac ctxt @{thms conjI[OF TrueI]} ORELSE' K all_tac))))] 2,
      (**)
      REPEAT_SOME (eresolve_tac ctxt @{thms conjE}),
      REPEAT_SOME (dresolve_tac ctxt @{thms reachD}),
      REPEAT_SOME (Rule_Insts.thin_tac ctxt "True" [])]
    end
  in
  fun refinement_method aux' =
    SIMPLE_METHOD o (fn ctxt => Subgoal.FOCUS (refinement_tac aux') ctxt (#offset aux'))
    |> Method.Basic
  end;


  local

(**)
local
fun bap_intro_alg (evt_specs0, lthy) acc tm =
  let
    val (k, tm') = strip_comb tm |> fst |> `head_name_of;
  in
    case Symtab.lookup evt_specs0 k of
      SOME _ => acc
    | NONE =>
      let
        val thm = case eventb_split_get k lthy of
          NONE =>
            [Pretty.str "No ",
             binding_pretty eventb_attrib,
             Pretty.str " theorem for term: ",
             Syntax.pretty_term lthy tm']
            |> Pretty.paragraph |> Pretty.string_of |> error
          | SOME thm => thm;

        val case_names = Rule_Cases.get thm |> fst |> map (fst #> fst)

        val (hyps', concl') = thm
          |> `(Thm.cprems_of #> map Thm.term_of)
          ||> (Thm.cconcl_of #> Thm.term_of #> HOLogic.dest_Trueprop);

        val matched =
          unify_match lthy (concl', tm)
          |> (fn env as (tyenv,_) =>
              Envir.subst_term_types tyenv #> Envir.subst_term env)
      in
        fold
            (fn (hyp', case_name) => fn acc' =>
                let
                  val hyp = Logic.dest_all_global hyp' |> snd handle TERM _ => hyp';
                  val acc'' = Logic.strip_imp_concl hyp
                    |> HOLogic.dest_Trueprop
                    |> beta_reduce lthy
                    |> bap_intro_alg (evt_specs0, lthy) (map (cons case_name) acc)
                 in
                   (acc'' @ acc')
                 end)
            (map2 (pair o matched) hyps' case_names) []
      end
  end;

  in
    fun refine_bap_intro (evt_specs0, lthy) (name,tm0) =
      let
      in
        bap_intro_alg (evt_specs0, lthy) [[name]] tm0 |> rev |> map rev
      end
  end
(**)


  in
  fun eventb_cmd raw_model lthy =
    let
      val (model, lthy') = prepare_model_cmd lthy raw_model;

      val ({bap, ES, xrefine}, lthy') = define_model model lthy';

      (* construct refinement theorem *)
      val (refine_names, refine_goals) = (case #xrefines model of
        SOME refines =>
          let
            val lenses0 = #lenses0 (the xrefine);

            val loc_assm = list_comb (#model refines |> #modelp, #ext_tms refines @ lenses0)
              |> subst_atomic_types [(stateT, state0T)];

            val s = Variable.variant_frees lthy' [] [("s", stateT)] |> hd |> Free;
            val EST = fastype_of (#tm ES);
            val reach_tm = Const ("Event_Systems.reach", EST --> stateT --> HOLogic.boolT);

            val inv_assm = model_invs model
              |> map (snd #> #tm #> rpair (lens_getters (#vars model) s) #> list_comb)
              |> BNF_GFP_Rec_Sugar.mk_conjs
              |> pair (reach_tm $ #tm ES $ s) |> mk_imp
              |> Logic.all s;

            val sim_ES_const = Const ("Event_Systems.sim_ES", dummyT);

            val thy = Proof_Context.theory_of lthy;
            val locale_args = Locale.params_of thy (#model_name refines)
              |> map (fst #> fst);

            val ES0_args = Locale.locale_notes thy (#model_name refines)
              |> List.mapPartial
                  (fn (_, facts) => case facts of
                    [((n, _), [thm])] => if Binding.name_of n = "ES_def" then SOME thm else NONE
                   | _ => NONE)
              |> the_single |> fst |> the_single
              |> Thm.full_prop_of |> HOLogic.dest_Trueprop
              |> HOLogic.dest_eq |> fst
              |> strip_comb |> snd
              |> map (dest_Free #> fst #> list_find locale_args #>
                      nth (#ext_tms refines @ lenses0));

            val ES0_tm = list_comb (Const (#name (#model refines) ^ ".ES", dummyT), ES0_args);

            val sim_concl = sim_ES_const $ #tm ES $ #tm (#pi refines) $ ES0_tm;

            val names = "refine:initialise" :: maps (fn (b,(tm,tm0)) =>
                refine_bap_intro (#bap_spec (#model refines), lthy')
                  (if Binding.is_empty b
                    then dest_comb tm |> snd
                          |> strip_comb |> fst
                          |> dest_Const |> fst
                          |> Long_Name.base_name
                    else Binding.name_of b,
                    tm0) |> map (fn xs => String.concatWith ":" ("refine" :: xs))
              ) (eqs_pi lthy' (#pi refines));

          in (names, [mk_imp (loc_assm, sim_concl) |> pair inv_assm |> Logic.mk_implies
              |> Syntax.check_term lthy']) end
        | _ => ([], []));

      val aux = {
        name = #name model,
        Tnss = #Tnss model,
        invs = #invs model,
        vars = #vars model,
        init = #init model,
        bap  = bap,
        bap_spec = #evts model,
        ES   = ES,
        refinement = #xrefines model,
        original_lthy = lthy
      };

      val ngoals = map (mk_inv_goal model lthy') (model_invs model);
      val names  = maps (map fst) ngoals;

      val inv_goals = map (map (snd)) ngoals;
      val all_goals = inv_goals @ [refine_goals] |> map (map (rpair []));

      fun aux' _ = {
        offset   = 1 + length (flat inv_goals),
        ES       = ES,
        vars     = #vars model,
        bap      = bap,
        refine   = the xrefine,
        name0    = #xrefines model |> the |> #model |> #name,
        invs0    = #xrefines model |> the |> #model |> #invs,
        ES0      = #xrefines model |> the |> #model |> #ES,
        bap0     = #xrefines model |> the |> #model |> #bap,
        bap_spec0 = #xrefines model |> the |> #model |> #bap_spec,
        mediator  = #xrefines model |> the |> #mediator
      }
    in
      lthy'
      |> bind_model_cases (names @ refine_names)
      |> Proof.theorem NONE (after_qed aux) all_goals
      |> (case #xrefines model of
            SOME _ => Proof.apply (refinement_method (aux' ()), Position.no_range)
                   #> Seq.the_result "this won't happen"
          | _ => I)
    end
  end
  end
end
end;


