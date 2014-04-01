(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Elimination of useless Llet(Alias) bindings.
   Also transform let-bound references into variables. *)

ouvre Asttypes
ouvre Lambda

(* To transform let-bound references into variables *)

exception Real_reference

soit rec eliminate_ref id = fonction
    Lvar v tel lam ->
      si Ident.same v id alors raise Real_reference sinon lam
  | Lconst cst tel lam -> lam
  | Lapply(e1, el, loc) ->
      Lapply(eliminate_ref id e1, List.map (eliminate_ref id) el, loc)
  | Lfunction(kind, params, body) tel lam ->
      si IdentSet.mem id (free_variables lam)
      alors raise Real_reference
      sinon lam
  | Llet(str, v, e1, e2) ->
      Llet(str, v, eliminate_ref id e1, eliminate_ref id e2)
  | Lletrec(idel, e2) ->
      Lletrec(List.map (fonc (v, e) -> (v, eliminate_ref id e)) idel,
              eliminate_ref id e2)
  | Lprim(Pfield 0, [Lvar v]) quand Ident.same v id ->
      Lvar id
  | Lprim(Psetfield(0, _), [Lvar v; e]) quand Ident.same v id ->
      Lassign(id, eliminate_ref id e)
  | Lprim(Poffsetref delta, [Lvar v]) quand Ident.same v id ->
      Lassign(id, Lprim(Poffsetint delta, [Lvar id]))
  | Lprim(p, el) ->
      Lprim(p, List.map (eliminate_ref id) el)
  | Lswitch(e, sw) ->
      Lswitch(eliminate_ref id e,
        {sw_numconsts = sw.sw_numconsts;
         sw_consts =
            List.map (fonc (n, e) -> (n, eliminate_ref id e)) sw.sw_consts;
         sw_numblocks = sw.sw_numblocks;
         sw_blocks =
            List.map (fonc (n, e) -> (n, eliminate_ref id e)) sw.sw_blocks;
         sw_failaction = filtre sw.sw_failaction avec
         | None -> None
         | Some l -> Some (eliminate_ref id l)})
  | Lstringswitch(e, sw, default) ->
      Lstringswitch
        (eliminate_ref id e,
         List.map (fonc (s, e) -> (s, eliminate_ref id e)) sw,
         eliminate_ref id default)
  | Lstaticraise (i,args) ->
      Lstaticraise (i,List.map (eliminate_ref id) args)
  | Lstaticcatch(e1, i, e2) ->
      Lstaticcatch(eliminate_ref id e1, i, eliminate_ref id e2)
  | Ltrywith(e1, v, e2) ->
      Ltrywith(eliminate_ref id e1, v, eliminate_ref id e2)
  | Lifthenelse(e1, e2, e3) ->
      Lifthenelse(eliminate_ref id e1,
                  eliminate_ref id e2,
                  eliminate_ref id e3)
  | Lsequence(e1, e2) ->
      Lsequence(eliminate_ref id e1, eliminate_ref id e2)
  | Lwhile(e1, e2) ->
      Lwhile(eliminate_ref id e1, eliminate_ref id e2)
  | Lfor(v, e1, e2, dir, e3) ->
      Lfor(v, eliminate_ref id e1, eliminate_ref id e2,
           dir, eliminate_ref id e3)
  | Lassign(v, e) ->
      Lassign(v, eliminate_ref id e)
  | Lsend(k, m, o, el, loc) ->
      Lsend(k, eliminate_ref id m, eliminate_ref id o,
            List.map (eliminate_ref id) el, loc)
  | Levent(l, ev) ->
      Levent(eliminate_ref id l, ev)
  | Lifused(v, e) ->
      Lifused(v, eliminate_ref id e)

(* Simplification of exits *)

soit simplify_exits lam =

  (* Count occurrences of (exit n ...) statements *)
  soit exits = Hashtbl.create 17 dans

  soit count_exit i =
    essaie
      !(Hashtbl.find exits i)
    avec
    | Not_found -> 0

  et incr_exit i =
    essaie
      incr (Hashtbl.find exits i)
    avec
    | Not_found -> Hashtbl.add exits i (ref 1) dans

  soit rec count = fonction
  | (Lvar _| Lconst _) -> ()
  | Lapply(l1, ll, _) -> count l1; List.iter count ll
  | Lfunction(kind, params, l) -> count l
  | Llet(str, v, l1, l2) ->
      count l2; count l1
  | Lletrec(bindings, body) ->
      List.iter (fonc (v, l) -> count l) bindings;
      count body
  | Lprim(p, ll) -> List.iter count ll
  | Lswitch(l, sw) ->
      count_default sw ;
      count l;
      List.iter (fonc (_, l) -> count l) sw.sw_consts;
      List.iter (fonc (_, l) -> count l) sw.sw_blocks
  | Lstringswitch(l, sw, d) ->
      count l;
      List.iter (fonc (_, l) -> count l) sw;
      count d
  | Lstaticraise (i,ls) -> incr_exit i ; List.iter count ls
  | Lstaticcatch (l1,(i,[]),Lstaticraise (j,[])) ->
      (* i will be replaced by j in l1, so each occurence of i in l1
         increases j's ref count *)
      count l1 ;
      soit ic = count_exit i dans
      début essaie
        soit r = Hashtbl.find exits j dans r := !r + ic
      avec
      | Not_found ->
          Hashtbl.add exits j (ref ic)
      fin
  | Lstaticcatch(l1, (i,_), l2) ->
      count l1;
      (* If l1 does not contain (exit i),
         l2 will be removed, so don't count its exits *)
      si count_exit i > 0 alors
        count l2
  | Ltrywith(l1, v, l2) -> count l1; count l2
  | Lifthenelse(l1, l2, l3) -> count l1; count l2; count l3
  | Lsequence(l1, l2) -> count l1; count l2
  | Lwhile(l1, l2) -> count l1; count l2
  | Lfor(_, l1, l2, dir, l3) -> count l1; count l2; count l3
  | Lassign(v, l) ->
      (* Lalias-bound variables are never assigned, so don't increase
         v's refcount *)
      count l
  | Lsend(k, m, o, ll, _) -> List.iter count (m::o::ll)
  | Levent(l, _) -> count l
  | Lifused(v, l) -> count l

  et count_default sw = filtre sw.sw_failaction avec
  | None -> ()
  | Some al ->
      soit nconsts = List.length sw.sw_consts
      et nblocks = List.length sw.sw_blocks dans
      si
        nconsts < sw.sw_numconsts && nblocks < sw.sw_numblocks
      alors début (* default action will occur twice in native code *)
        count al ; count al
      fin sinon début (* default action will occur once *)
        affirme (nconsts < sw.sw_numconsts || nblocks < sw.sw_numblocks) ;
        count al
      fin
  dans
  count lam;

  (*
     Second pass simplify  ``catch body with (i ...) handler''
      - if (exit i ...) does not occur in body, suppress catch
      - if (exit i ...) occurs exactly once in body,
        substitute it with handler
      - If handler is a single variable, replace (exit i ..) with it
   Note:
    In ``catch body with (i x1 .. xn) handler''
     Substituted expression is
      let y1 = x1 and ... yn = xn in
      handler[x1 <- y1 ; ... ; xn <- yn]
     For the sake of preserving the uniqueness  of bound variables.
     (No alpha conversion of ``handler'' is presently needed, since
     substitution of several ``(exit i ...)''
     occurs only when ``handler'' is a variable.)
  *)

  soit subst = Hashtbl.create 17 dans

  soit rec simplif = fonction
  | (Lvar _|Lconst _) tel l -> l
  | Lapply(l1, ll, loc) -> Lapply(simplif l1, List.map simplif ll, loc)
  | Lfunction(kind, params, l) -> Lfunction(kind, params, simplif l)
  | Llet(kind, v, l1, l2) -> Llet(kind, v, simplif l1, simplif l2)
  | Lletrec(bindings, body) ->
      Lletrec(List.map (fonc (v, l) -> (v, simplif l)) bindings, simplif body)
  | Lprim(p, ll) -> début
    soit ll = List.map simplif ll dans
    filtre p, ll avec
        (* Simplify %revapply, for n-ary functions with n > 1 *)
      | Prevapply loc, [x; Lapply(f, args, _)]
      | Prevapply loc, [x; Levent (Lapply(f, args, _),_)] ->
        Lapply(f, args@[x], loc)
      | Prevapply loc, [x; f] -> Lapply(f, [x], loc)

        (* Simplify %apply, for n-ary functions with n > 1 *)
      | Pdirapply loc, [Lapply(f, args, _); x]
      | Pdirapply loc, [Levent (Lapply(f, args, _),_); x] ->
        Lapply(f, args@[x], loc)
      | Pdirapply loc, [f; x] -> Lapply(f, [x], loc)

      | _ -> Lprim(p, ll)
     fin
  | Lswitch(l, sw) ->
      soit new_l = simplif l
      et new_consts =  List.map (fonc (n, e) -> (n, simplif e)) sw.sw_consts
      et new_blocks =  List.map (fonc (n, e) -> (n, simplif e)) sw.sw_blocks
      et new_fail = filtre sw.sw_failaction avec
      | None -> None
      | Some l -> Some (simplif l) dans
      Lswitch
        (new_l,
         {sw avec sw_consts = new_consts ; sw_blocks = new_blocks;
                  sw_failaction = new_fail})
  | Lstringswitch(l,sw,d) ->
      Lstringswitch
        (simplif l,List.map (fonc (s,l) -> s,simplif l) sw,simplif d)
  | Lstaticraise (i,[]) tel l ->
      début essaie
        soit _,handler =  Hashtbl.find subst i dans
        handler
      avec
      | Not_found -> l
      fin
  | Lstaticraise (i,ls) ->
      soit ls = List.map simplif ls dans
      début essaie
        soit xs,handler =  Hashtbl.find subst i dans
        soit ys = List.map Ident.rename xs dans
        soit env =
          List.fold_right2
            (fonc x y t -> Ident.add x (Lvar y) t)
            xs ys Ident.empty dans
        List.fold_right2
          (fonc y l r -> Llet (Alias, y, l, r))
          ys ls (Lambda.subst_lambda env handler)
      avec
      | Not_found -> Lstaticraise (i,ls)
      fin
  | Lstaticcatch (l1,(i,[]),(Lstaticraise (j,[]) tel l2)) ->
      Hashtbl.add subst i ([],simplif l2) ;
      simplif l1
  | Lstaticcatch (l1,(i,xs), (Lvar _ tel l2)) ->
      début filtre count_exit i avec
      | 0 -> simplif l1
      | _ ->
          Hashtbl.add subst i (xs,l2) ;
          simplif l1
      fin
  | Lstaticcatch (l1,(i,xs),l2) ->
      début filtre count_exit i avec
      | 0 -> simplif l1
      | 1 ->
          Hashtbl.add subst i (xs,simplif l2) ;
          simplif l1
      | _ ->
          Lstaticcatch (simplif l1, (i,xs), simplif l2)
      fin
  | Ltrywith(l1, v, l2) -> Ltrywith(simplif l1, v, simplif l2)
  | Lifthenelse(l1, l2, l3) -> Lifthenelse(simplif l1, simplif l2, simplif l3)
  | Lsequence(l1, l2) -> Lsequence(simplif l1, simplif l2)
  | Lwhile(l1, l2) -> Lwhile(simplif l1, simplif l2)
  | Lfor(v, l1, l2, dir, l3) ->
      Lfor(v, simplif l1, simplif l2, dir, simplif l3)
  | Lassign(v, l) -> Lassign(v, simplif l)
  | Lsend(k, m, o, ll, loc) ->
      Lsend(k, simplif m, simplif o, List.map simplif ll, loc)
  | Levent(l, ev) -> Levent(simplif l, ev)
  | Lifused(v, l) -> Lifused (v,simplif l)
  dans
  simplif lam

(* Compile-time beta-reduction of functions immediately applied:
      Lapply(Lfunction(Curried, params, body), args, loc) ->
        let paramN = argN in ... let param1 = arg1 in body
      Lapply(Lfunction(Tupled, params, body), [Lprim(Pmakeblock(args))], loc) ->
        let paramN = argN in ... let param1 = arg1 in body
   Assumes |args| = |params|.
*)

soit beta_reduce params body args =
  List.fold_left2 (fonc l param arg -> Llet(Strict, param, arg, l))
                  body params args

(* Simplification of lets *)

soit simplify_lets lam =

  (* Disable optimisations for bytecode compilation with -g flag *)
  soit optimize = !Clflags.native_code || not !Clflags.debug dans

  (* First pass: count the occurrences of all let-bound identifiers *)

  soit occ = (Hashtbl.create 83: (Ident.t, int ref) Hashtbl.t) dans
  (* The global table [occ] associates to each let-bound identifier
     the number of its uses (as a reference):
     - 0 if never used
     - 1 if used exactly once in and not under a lambda or within a loop
     - > 1 if used several times or under a lambda or within a loop.
     The local table [bv] associates to each locally-let-bound variable
     its reference count, as above.  [bv] is enriched at let bindings
     but emptied when crossing lambdas and loops. *)

  (* Current use count of a variable. *)
  soit count_var v =
    essaie
      !(Hashtbl.find occ v)
    avec Not_found ->
      0

  (* Entering a [let].  Returns updated [bv]. *)
  et bind_var bv v =
    soit r = ref 0 dans
    Hashtbl.add occ v r;
    Tbl.add v r bv

  (* Record a use of a variable *)
  et use_var bv v n =
    essaie
      soit r = Tbl.find v bv dans r := !r + n
    avec Not_found ->
      (* v is not locally bound, therefore this is a use under a lambda
         or within a loop.  Increase use count by 2 -- enough so
         that single-use optimizations will not apply. *)
    essaie
      soit r = Hashtbl.find occ v dans r := !r + 2
    avec Not_found ->
      (* Not a let-bound variable, ignore *)
      () dans

  soit rec count bv = fonction
  | Lconst cst -> ()
  | Lvar v ->
      use_var bv v 1
  | Lapply(Lfunction(Curried, params, body), args, _)
    quand optimize && List.length params = List.length args ->
      count bv (beta_reduce params body args)
  | Lapply(Lfunction(Tupled, params, body), [Lprim(Pmakeblock _, args)], _)
    quand optimize && List.length params = List.length args ->
      count bv (beta_reduce params body args)
  | Lapply(l1, ll, _) ->
      count bv l1; List.iter (count bv) ll
  | Lfunction(kind, params, l) ->
      count Tbl.empty l
  | Llet(str, v, Lvar w, l2) quand optimize ->
      (* v will be replaced by w in l2, so each occurrence of v in l2
         increases w's refcount *)
      count (bind_var bv v) l2;
      use_var bv w (count_var v)
  | Llet(str, v, l1, l2) ->
      count (bind_var bv v) l2;
      (* If v is unused, l1 will be removed, so don't count its variables *)
      si str = Strict || count_var v > 0 alors count bv l1
  | Lletrec(bindings, body) ->
      List.iter (fonc (v, l) -> count bv l) bindings;
      count bv body
  | Lprim(p, ll) -> List.iter (count bv) ll
  | Lswitch(l, sw) ->
      count_default bv sw ;
      count bv l;
      List.iter (fonc (_, l) -> count bv l) sw.sw_consts;
      List.iter (fonc (_, l) -> count bv l) sw.sw_blocks
  | Lstringswitch(l, sw, d) ->
      count bv l ;
      List.iter (fonc (_, l) -> count bv l) sw ;
      count bv d
  | Lstaticraise (i,ls) -> List.iter (count bv) ls
  | Lstaticcatch(l1, (i,_), l2) -> count bv l1; count bv l2
  | Ltrywith(l1, v, l2) -> count bv l1; count bv l2
  | Lifthenelse(l1, l2, l3) -> count bv l1; count bv l2; count bv l3
  | Lsequence(l1, l2) -> count bv l1; count bv l2
  | Lwhile(l1, l2) -> count Tbl.empty l1; count Tbl.empty l2
  | Lfor(_, l1, l2, dir, l3) -> count bv l1; count bv l2; count Tbl.empty l3
  | Lassign(v, l) ->
      (* Lalias-bound variables are never assigned, so don't increase
         v's refcount *)
      count bv l
  | Lsend(_, m, o, ll, _) -> List.iter (count bv) (m::o::ll)
  | Levent(l, _) -> count bv l
  | Lifused(v, l) ->
      si count_var v > 0 alors count bv l

  et count_default bv sw = filtre sw.sw_failaction avec
  | None -> ()
  | Some al ->
      soit nconsts = List.length sw.sw_consts
      et nblocks = List.length sw.sw_blocks dans
      si
        nconsts < sw.sw_numconsts && nblocks < sw.sw_numblocks
      alors début (* default action will occur twice in native code *)
        count bv al ; count bv al
      fin sinon début (* default action will occur once *)
        affirme (nconsts < sw.sw_numconsts || nblocks < sw.sw_numblocks) ;
        count bv al
      fin
  dans
  count Tbl.empty lam;

  (* Second pass: remove Lalias bindings of unused variables,
     and substitute the bindings of variables used exactly once. *)

  soit subst = Hashtbl.create 83 dans

(* This (small)  optimisation is always legal, it may uncover some
   tail call later on. *)

  soit mklet (kind,v,e1,e2) = filtre e2 avec
  | Lvar w quand optimize && Ident.same v w -> e1
  | _ -> Llet (kind,v,e1,e2) dans


  soit rec simplif = fonction
    Lvar v tel l ->
      début essaie
        Hashtbl.find subst v
      avec Not_found ->
        l
      fin
  | Lconst cst tel l -> l
  | Lapply(Lfunction(Curried, params, body), args, _)
    quand optimize && List.length params = List.length args ->
      simplif (beta_reduce params body args)
  | Lapply(Lfunction(Tupled, params, body), [Lprim(Pmakeblock _, args)], _)
    quand optimize && List.length params = List.length args ->
      simplif (beta_reduce params body args)
  | Lapply(l1, ll, loc) -> Lapply(simplif l1, List.map simplif ll, loc)
  | Lfunction(kind, params, l) -> Lfunction(kind, params, simplif l)
  | Llet(str, v, Lvar w, l2) quand optimize ->
      Hashtbl.add subst v (simplif (Lvar w));
      simplif l2
  | Llet(Strict, v, Lprim(Pmakeblock(0, Mutable), [linit]), lbody)
    quand optimize ->
      soit slinit = simplif linit dans
      soit slbody = simplif lbody dans
      début essaie
       mklet (Variable, v, slinit, eliminate_ref v slbody)
      avec Real_reference ->
        mklet(Strict, v, Lprim(Pmakeblock(0, Mutable), [slinit]), slbody)
      fin
  | Llet(Alias, v, l1, l2) ->
      début filtre count_var v avec
        0 -> simplif l2
      | 1 quand optimize -> Hashtbl.add subst v (simplif l1); simplif l2
      | n -> Llet(Alias, v, simplif l1, simplif l2)
      fin
  | Llet(StrictOpt, v, l1, l2) ->
      début filtre count_var v avec
        0 -> simplif l2
      | n -> mklet(Alias, v, simplif l1, simplif l2)
      fin
  | Llet(kind, v, l1, l2) -> mklet(kind, v, simplif l1, simplif l2)
  | Lletrec(bindings, body) ->
      Lletrec(List.map (fonc (v, l) -> (v, simplif l)) bindings, simplif body)
  | Lprim(p, ll) -> Lprim(p, List.map simplif ll)
  | Lswitch(l, sw) ->
      soit new_l = simplif l
      et new_consts =  List.map (fonc (n, e) -> (n, simplif e)) sw.sw_consts
      et new_blocks =  List.map (fonc (n, e) -> (n, simplif e)) sw.sw_blocks
      et new_fail = filtre sw.sw_failaction avec
      | None -> None
      | Some l -> Some (simplif l) dans
      Lswitch
        (new_l,
         {sw avec sw_consts = new_consts ; sw_blocks = new_blocks;
                  sw_failaction = new_fail})
  | Lstringswitch (l,sw,d) ->
      Lstringswitch
        (simplif l,List.map (fonc (s,l) -> s,simplif l) sw,simplif d)
  | Lstaticraise (i,ls) ->
      Lstaticraise (i, List.map simplif ls)
  | Lstaticcatch(l1, (i,args), l2) ->
      Lstaticcatch (simplif l1, (i,args), simplif l2)
  | Ltrywith(l1, v, l2) -> Ltrywith(simplif l1, v, simplif l2)
  | Lifthenelse(l1, l2, l3) -> Lifthenelse(simplif l1, simplif l2, simplif l3)
  | Lsequence(Lifused(v, l1), l2) ->
      si count_var v > 0
      alors Lsequence(simplif l1, simplif l2)
      sinon simplif l2
  | Lsequence(l1, l2) -> Lsequence(simplif l1, simplif l2)
  | Lwhile(l1, l2) -> Lwhile(simplif l1, simplif l2)
  | Lfor(v, l1, l2, dir, l3) ->
      Lfor(v, simplif l1, simplif l2, dir, simplif l3)
  | Lassign(v, l) -> Lassign(v, simplif l)
  | Lsend(k, m, o, ll, loc) ->
      Lsend(k, simplif m, simplif o, List.map simplif ll, loc)
  | Levent(l, ev) -> Levent(simplif l, ev)
  | Lifused(v, l) ->
      si count_var v > 0 alors simplif l sinon lambda_unit
  dans
  simplif lam

(* Tail call info in annotation files *)

soit is_tail_native_heuristic : (int -> bool) ref =
  ref (fonc n -> vrai)

soit rec emit_tail_infos is_tail lambda =
  soit call_kind args =
    si is_tail
    && ((not !Clflags.native_code)
        || (!is_tail_native_heuristic (List.length args)))
   alors Annot.Tail
   sinon Annot.Stack dans
  filtre lambda avec
  | Lvar _ -> ()
  | Lconst _ -> ()
  | Lapply (func, l, loc) ->
      list_emit_tail_infos faux l;
      Stypes.record (Stypes.An_call (loc, call_kind l))
  | Lfunction (_, _, lam) ->
      emit_tail_infos vrai lam
  | Llet (_, _, lam, body) ->
      emit_tail_infos faux lam;
      emit_tail_infos is_tail body
  | Lletrec (bindings, body) ->
      List.iter (fonc (_, lam) -> emit_tail_infos faux lam) bindings;
      emit_tail_infos is_tail body
  | Lprim (Pidentity, [arg]) ->
      emit_tail_infos is_tail arg
  | Lprim (Psequand, [arg1; arg2])
  | Lprim (Psequor, [arg1; arg2]) ->
      emit_tail_infos faux arg1;
      emit_tail_infos is_tail arg2
  | Lprim (_, l) ->
      list_emit_tail_infos faux l
  | Lswitch (lam, sw) ->
      emit_tail_infos faux lam;
      list_emit_tail_infos_fun snd is_tail sw.sw_consts;
      list_emit_tail_infos_fun snd is_tail sw.sw_blocks
  | Lstringswitch (lam, sw, d) ->
      emit_tail_infos faux lam;
      List.iter
        (fonc (_,lam) ->  emit_tail_infos is_tail lam)
        sw ;
      emit_tail_infos is_tail d
  | Lstaticraise (_, l) ->
      list_emit_tail_infos faux l
  | Lstaticcatch (body, _, handler) ->
      emit_tail_infos is_tail body;
      emit_tail_infos is_tail handler
  | Ltrywith (body, _, handler) ->
      emit_tail_infos faux body;
      emit_tail_infos is_tail handler
  | Lifthenelse (cond, ifso, ifno) ->
      emit_tail_infos faux cond;
      emit_tail_infos is_tail ifso;
      emit_tail_infos is_tail ifno
  | Lsequence (lam1, lam2) ->
      emit_tail_infos faux lam1;
      emit_tail_infos is_tail lam2
  | Lwhile (cond, body) ->
      emit_tail_infos faux cond;
      emit_tail_infos faux body
  | Lfor (_, low, high, _, body) ->
      emit_tail_infos faux low;
      emit_tail_infos faux high;
      emit_tail_infos faux body
  | Lassign (_, lam) ->
      emit_tail_infos faux lam
  | Lsend (_, meth, obj, args, loc) ->
      emit_tail_infos faux meth;
      emit_tail_infos faux obj;
      list_emit_tail_infos faux args;
      Stypes.record (Stypes.An_call (loc, call_kind (obj :: args)))
  | Levent (lam, _) ->
      emit_tail_infos is_tail lam
  | Lifused (_, lam) ->
      emit_tail_infos is_tail lam
et list_emit_tail_infos_fun f is_tail =
  List.iter (fonc x -> emit_tail_infos is_tail (f x))
et list_emit_tail_infos is_tail =
  List.iter (emit_tail_infos is_tail)

(* The entry point:
   simplification + emission of tailcall annotations, if needed. *)

soit simplify_lambda lam =
  soit res = simplify_lets (simplify_exits lam) dans
  si !Clflags.annotations alors emit_tail_infos vrai res;
  res
