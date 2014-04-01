(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Luc Maranget, projet Moscova, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2000 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Store for actions in object style *)
exception Found de int

type 'a t_store =
    {act_get : unit -> 'a array ; act_store : 'a -> int}

soit mk_store same =
  soit r_acts = ref [] dans
  soit store act =
    soit rec store_rec i = fonction
      | [] -> i,[act]
      | act0::rem ->
          si same act0 act alors raise (Found i)
          sinon
            soit i,rem = store_rec (i+1) rem dans
            i,act0::rem dans
    essaie
      soit i,acts = store_rec 0 !r_acts dans
      r_acts := acts ;
      i
    avec
    | Found i -> i

  et get () = Array.of_list !r_acts dans
  {act_store=store ; act_get=get}



module type S =
 sig
   type primitive
   val eqint : primitive
   val neint : primitive
   val leint : primitive
   val ltint : primitive
   val geint : primitive
   val gtint : primitive
   type act

   val bind : act -> (act -> act) -> act
   val make_offset : act -> int -> act
   val make_prim : primitive -> act list -> act
   val make_isout : act -> act -> act
   val make_isin : act -> act -> act
   val make_if : act -> act -> act -> act
   val make_switch :
      act -> int array -> act array -> act
 fin

(* The module will ``produce good code for the case statement'' *)
(*
  Adaptation of
   R.L. Berstein
   ``Producing good code for the case statement''
   Sofware Practice and Experience, 15(10) (1985)
 and
   D.L. Spuler
    ``Two-Way Comparison Search Trees, a Generalisation of Binary Search Trees
      and Split Trees''
    ``Compiler Code Generation for Multiway Branch Statement as
      a Static Search Problem''
   Technical Reports, James Cook University
*)
(*
  Main adaptation is considering interval tests
 (implemented as one addition + one unsigned test and branch)
  which leads to exhaustive search for finding the optimal
  test sequence in small cases and heuristics otherwise.
*)
module Make (Arg : S) =
  struct

    type 'a inter =
        {cases : (int * int * int) array ;
          actions : 'a array}

type 'a t_ctx =  {off : int ; arg : 'a}

soit cut = ref 8
et more_cut = ref 16

soit pint chan i =
  si i = min_int alors Printf.fprintf chan "-oo"
  sinon si i=max_int alors Printf.fprintf chan "oo"
  sinon Printf.fprintf chan "%d" i

soit pcases chan cases =
  pour i =0 à Array.length cases-1 faire
    soit l,h,act = cases.(i) dans
    si l=h alors
      Printf.fprintf chan "%d:%d " l act
    sinon
      Printf.fprintf chan "%a..%a:%d " pint l pint h act
  fait

    soit prerr_inter i = Printf.fprintf stderr
        "cases=%a" pcases i.cases

soit get_act cases i =
  soit _,_,r = cases.(i) dans
  r
et get_low cases i =
  soit r,_,_ = cases.(i) dans
  r

type ctests = {
    modifiable n : int ;
    modifiable ni : int ;
  }

soit too_much = {n=max_int ; ni=max_int}

soit ptests chan {n=n ; ni=ni} =
  Printf.fprintf chan "{n=%d ; ni=%d}" n ni

soit pta chan t =
  pour i =0 à Array.length t-1 faire
    Printf.fprintf chan "%d: %a\n" i ptests t.(i)
  fait

soit count_tests s =
  soit r =
    Array.init
      (Array.length s.actions)
      (fonc _ -> {n=0 ; ni=0 }) dans
  soit c = s.cases dans
  soit imax = Array.length c-1 dans
  pour i=0 à imax faire
    soit l,h,act = c.(i) dans
    soit x = r.(act) dans
    x.n <- x.n+1 ;
    si l < h && i<> 0 && i<>imax alors
      x.ni <- x.ni+1 ;
  fait ;
  r


soit less_tests c1 c2 =
  si c1.n < c2.n alors
    vrai
  sinon si c1.n = c2.n alors début
    si c1.ni < c2.ni alors
      vrai
    sinon
      faux
  fin sinon
    faux

et eq_tests c1 c2 = c1.n = c2.n && c1.ni=c2.ni

soit min_tests c1 c2 = si less_tests c1 c2 alors c1 sinon c2

soit less2tests (c1,d1) (c2,d2) =
  si eq_tests c1 c2 alors
    less_tests d1 d2
  sinon
    less_tests c1 c2

soit add_test t1 t2 =
  t1.n <- t1.n + t2.n ;
  t1.ni <- t1.ni + t2.ni ;

type t_ret = Inter de int * int  | Sep de int | No

soit pret chan = fonction
  | Inter (i,j)-> Printf.fprintf chan "Inter %d %d" i j
  | Sep i -> Printf.fprintf chan "Sep %d" i
  | No -> Printf.fprintf chan "No"

soit coupe cases i =
  soit l,_,_ = cases.(i) dans
  l,
  Array.sub cases 0 i,
  Array.sub cases i (Array.length cases-i)


soit case_append c1 c2 =
  soit len1 = Array.length c1
  et len2 = Array.length c2 dans
  filtre len1,len2 avec
  | 0,_ -> c2
  | _,0 -> c1
  | _,_ ->
      soit l1,h1,act1 = c1.(Array.length c1-1)
      et l2,h2,act2 = c2.(0) dans
      si act1 = act2 alors
        soit r = Array.create (len1+len2-1) c1.(0) dans
        pour i = 0 à len1-2 faire
          r.(i) <- c1.(i)
        fait ;

        soit l =
          si len1-2 >= 0 alors début
            soit _,h,_ = r.(len1-2) dans
            si h+1 < l1 alors
              h+1
            sinon
              l1
          fin sinon
            l1
        et h =
          si 1 < len2-1 alors début
            soit l,_,_ = c2.(1) dans
            si h2+1 < l alors
              l-1
            sinon
              h2
          fin sinon
            h2 dans
        r.(len1-1) <- (l,h,act1) ;
        pour i=1 à len2-1  faire
          r.(len1-1+i) <- c2.(i)
        fait ;
        r
      sinon si h1 > l1 alors
        soit r = Array.create (len1+len2) c1.(0) dans
        pour i = 0 à len1-2 faire
          r.(i) <- c1.(i)
        fait ;
        r.(len1-1) <- (l1,l2-1,act1) ;
        pour i=0 à len2-1  faire
          r.(len1+i) <- c2.(i)
        fait ;
        r
      sinon si h2 > l2 alors
        soit r = Array.create (len1+len2) c1.(0) dans
        pour i = 0 à len1-1 faire
          r.(i) <- c1.(i)
        fait ;
        r.(len1) <- (h1+1,h2,act2) ;
        pour i=1 à len2-1  faire
          r.(len1+i) <- c2.(i)
        fait ;
        r
      sinon
        Array.append c1 c2


soit coupe_inter i j cases =
  soit lcases = Array.length cases dans
  soit low,_,_ = cases.(i)
  et _,high,_ = cases.(j) dans
  low,high,
  Array.sub cases i (j-i+1),
  case_append (Array.sub cases 0 i) (Array.sub cases (j+1) (lcases-(j+1)))

type kind = Kvalue de int | Kinter de int | Kempty

soit pkind chan = fonction
  | Kvalue i ->Printf.fprintf chan "V%d" i
  | Kinter i -> Printf.fprintf chan "I%d" i
  | Kempty -> Printf.fprintf chan "E"

soit rec pkey chan  = fonction
  | [] -> ()
  | [k] -> pkind chan k
  | k::rem ->
      Printf.fprintf chan "%a %a" pkey rem pkind k

soit t = Hashtbl.create 17

soit make_key  cases =
  soit seen = ref []
  et count = ref 0 dans
  soit rec got_it act = fonction
    | [] ->
        seen := (act,!count):: !seen ;
        soit r = !count dans
        incr count ;
        r
    | (act0,index) :: rem ->
        si act0 = act alors
          index
        sinon
          got_it act rem dans

  soit make_one l h act =
    si l=h alors
      Kvalue (got_it act !seen)
    sinon
      Kinter (got_it act !seen) dans

  soit rec make_rec i pl =
    si i < 0 alors
      []
    sinon
      soit l,h,act = cases.(i) dans
      si pl = h+1 alors
        make_one l h act::make_rec (i-1) l
      sinon
        Kempty::make_one l h act::make_rec (i-1) l dans

  soit l,h,act = cases.(Array.length cases-1) dans
  make_one l h act::make_rec (Array.length cases-2) l


    soit same_act t =
      soit len = Array.length t dans
      soit a = get_act t (len-1) dans
      soit rec do_rec i =
        si i < 0 alors vrai
        sinon
          soit b = get_act t i dans
          b=a && do_rec (i-1) dans
      do_rec (len-2)


(*
  Intervall test x in [l,h] works by checking x-l in [0,h-l]
   * This may be false for arithmetic modulo 2^31
   * Subtracting l may change the relative ordering of values
     and invalid the invariant that matched values are given in
     increasing order

   To avoid this, interval check is allowed only when the
   integers indeed present in the whole case interval are
   in [-2^16 ; 2^16]

   This condition is checked by zyva
*)

soit inter_limit = 1 dgl 16

soit ok_inter = ref faux

soit rec opt_count top cases =
  soit key = make_key cases dans
  essaie
    soit r = Hashtbl.find t key dans
    r
  avec
  | Not_found ->
      soit r =
        soit lcases = Array.length cases dans
        filtre lcases avec
        | 0 -> affirme faux
        | _ quand same_act cases -> No, ({n=0; ni=0},{n=0; ni=0})
        | _ ->
            si lcases < !cut alors
              enum top cases
            sinon si lcases < !more_cut alors
              heuristic top cases
            sinon
              divide top cases dans
      Hashtbl.add t key r ;
      r

et divide top cases =
  soit lcases = Array.length cases dans
  soit m = lcases/2 dans
  soit _,left,right = coupe cases m dans
  soit ci = {n=1 ; ni=0}
  et cm = {n=1 ; ni=0}
  et _,(cml,cleft) = opt_count faux left
  et _,(cmr,cright) = opt_count faux right dans
  add_test ci cleft ;
  add_test ci cright ;
  si less_tests cml cmr alors
    add_test cm cmr
  sinon
    add_test cm cml ;
  Sep m,(cm, ci)

et heuristic top cases =
  soit lcases = Array.length cases dans

  soit sep,csep = divide faux cases

  et inter,cinter =
    si !ok_inter alors début
      soit _,_,act0 = cases.(0)
      et _,_,act1 = cases.(lcases-1) dans
      si act0 = act1 alors début
        soit low, high, inside, outside = coupe_inter 1 (lcases-2) cases dans
        soit _,(cmi,cinside) = opt_count faux inside
        et _,(cmo,coutside) = opt_count faux outside
        et cmij = {n=1 ; ni=(si low=high alors 0 sinon 1)}
        et cij = {n=1 ; ni=(si low=high alors 0 sinon 1)} dans
        add_test cij cinside ;
        add_test cij coutside ;
        si less_tests cmi cmo alors
          add_test cmij cmo
        sinon
          add_test cmij cmi ;
        Inter (1,lcases-2),(cmij,cij)
      fin sinon
        Inter (-1,-1),(too_much, too_much)
    fin sinon
      Inter (-1,-1),(too_much, too_much) dans
  si less2tests csep cinter alors
    sep,csep
  sinon
    inter,cinter


et enum top cases =
  soit lcases = Array.length cases dans
  soit lim, with_sep =
    soit best = ref (-1) et best_cost = ref (too_much,too_much) dans

    pour i = 1 à lcases-(1) faire
      soit _,left,right = coupe cases i dans
      soit ci = {n=1 ; ni=0}
      et cm = {n=1 ; ni=0}
      et _,(cml,cleft) = opt_count faux left
      et _,(cmr,cright) = opt_count faux right dans
      add_test ci cleft ;
      add_test ci cright ;
      si less_tests cml cmr alors
        add_test cm cmr
      sinon
        add_test cm cml ;

      si
        less2tests (cm,ci) !best_cost
      alors début
        si top alors
          Printf.fprintf stderr "Get it: %d\n" i ;
        best := i ;
        best_cost := (cm,ci)
      fin
    fait ;
    !best, !best_cost dans

  soit ilow, ihigh, with_inter =
    si not !ok_inter alors
      soit rlow = ref (-1) et rhigh = ref (-1)
      et best_cost= ref (too_much,too_much) dans
      pour i=1 à lcases-2 faire
        soit low, high, inside, outside = coupe_inter i i cases dans
         si low=high alors début
           soit _,(cmi,cinside) = opt_count faux inside
           et _,(cmo,coutside) = opt_count faux outside
           et cmij = {n=1 ; ni=0}
           et cij = {n=1 ; ni=0} dans
           add_test cij cinside ;
           add_test cij coutside ;
           si less_tests cmi cmo alors
             add_test cmij cmo
           sinon
             add_test cmij cmi ;
           si less2tests (cmij,cij) !best_cost alors début
             rlow := i ;
             rhigh := i ;
             best_cost := (cmij,cij)
           fin
         fin
      fait ;
      !rlow, !rhigh, !best_cost
    sinon
      soit rlow = ref (-1) et rhigh = ref (-1)
      et best_cost= ref (too_much,too_much) dans
      pour i=1 à lcases-2 faire
        pour j=i à lcases-2 faire
          soit low, high, inside, outside = coupe_inter i j cases dans
          soit _,(cmi,cinside) = opt_count faux inside
          et _,(cmo,coutside) = opt_count faux outside
          et cmij = {n=1 ; ni=(si low=high alors 0 sinon 1)}
          et cij = {n=1 ; ni=(si low=high alors 0 sinon 1)} dans
          add_test cij cinside ;
          add_test cij coutside ;
          si less_tests cmi cmo alors
            add_test cmij cmo
          sinon
            add_test cmij cmi ;
          si less2tests (cmij,cij) !best_cost alors début
            rlow := i ;
            rhigh := j ;
            best_cost := (cmij,cij)
          fin
        fait
      fait ;
      !rlow, !rhigh, !best_cost dans
  soit r = ref (Inter (ilow,ihigh)) et rc = ref with_inter dans
  si less2tests with_sep !rc alors début
    r := Sep lim ; rc := with_sep
  fin ;
  !r, !rc

    soit make_if_test konst test arg i ifso ifnot =
      Arg.make_if
        (Arg.make_prim test [arg ; konst i])
        ifso ifnot

    soit make_if_lt konst arg i  ifso ifnot = filtre i avec
    | 1 ->
        make_if_test konst Arg.leint arg 0 ifso ifnot
    | _ ->
        make_if_test konst Arg.ltint arg i ifso ifnot

    et make_if_le konst arg i ifso ifnot = filtre i avec
    | -1 ->
        make_if_test konst Arg.ltint arg 0 ifso ifnot
    | _ ->
        make_if_test konst Arg.leint arg i ifso ifnot

    et make_if_gt konst arg i  ifso ifnot = filtre i avec
    | -1 ->
        make_if_test konst Arg.geint arg 0 ifso ifnot
    | _ ->
        make_if_test konst Arg.gtint arg i ifso ifnot

    et make_if_ge konst arg i  ifso ifnot = filtre i avec
    | 1 ->
        make_if_test konst Arg.gtint arg 0 ifso ifnot
    | _ ->
        make_if_test konst Arg.geint arg i ifso ifnot

    et make_if_eq  konst arg i ifso ifnot =
      make_if_test konst Arg.eqint arg i ifso ifnot

    et make_if_ne  konst arg i ifso ifnot =
      make_if_test konst Arg.neint arg i ifso ifnot

    soit do_make_if_out h arg ifso ifno =
      Arg.make_if (Arg.make_isout h arg) ifso ifno

    soit make_if_out konst ctx l d mk_ifso mk_ifno = filtre l avec
    | 0 ->
        do_make_if_out
          (konst d) ctx.arg (mk_ifso ctx) (mk_ifno ctx)
    | _ ->
        Arg.bind
          (Arg.make_offset ctx.arg (-l))
          (fonc arg ->
            soit ctx = {off= (-l+ctx.off) ; arg=arg} dans
            do_make_if_out
              (konst d) arg (mk_ifso ctx) (mk_ifno ctx))

    soit do_make_if_in h arg ifso ifno =
      Arg.make_if (Arg.make_isin h arg) ifso ifno

    soit make_if_in konst ctx l d mk_ifso mk_ifno = filtre l avec
    | 0 ->
        do_make_if_in
          (konst d) ctx.arg (mk_ifso ctx) (mk_ifno ctx)
    | _ ->
        Arg.bind
          (Arg.make_offset ctx.arg (-l))
          (fonc arg ->
            soit ctx = {off= (-l+ctx.off) ; arg=arg} dans
            do_make_if_in
              (konst d) arg (mk_ifso ctx) (mk_ifno ctx))


    soit rec c_test konst ctx ({cases=cases ; actions=actions} tel s) =
      soit lcases = Array.length cases dans
      affirme(lcases > 0) ;
      si lcases = 1 alors
        actions.(get_act cases 0) ctx
      sinon début

        soit w,c = opt_count faux cases dans
(*
  Printf.fprintf stderr
  "off=%d tactic=%a for %a\n"
  ctx.off pret w pcases cases ;
  *)
    filtre w avec
    | No -> actions.(get_act cases 0) ctx
    | Inter (i,j) ->
        soit low,high,inside, outside = coupe_inter i j cases dans
        soit _,(cinside,_) = opt_count faux inside
        et _,(coutside,_) = opt_count faux outside dans
(* Costs are retrieved to put the code with more remaining tests
   in the privileged (positive) branch of ``if'' *)
        si low=high alors début
          si less_tests coutside cinside alors
            make_if_eq
              konst ctx.arg
              (low+ctx.off)
              (c_test konst ctx {s avec cases=inside})
              (c_test konst ctx {s avec cases=outside})
          sinon
            make_if_ne
              konst ctx.arg
              (low+ctx.off)
              (c_test konst ctx {s avec cases=outside})
              (c_test konst ctx {s avec cases=inside})
        fin sinon début
          si less_tests coutside cinside alors
            make_if_in
              konst ctx
              (low+ctx.off)
              (high-low)
              (fonc ctx -> c_test konst ctx {s avec cases=inside})
              (fonc ctx -> c_test konst ctx {s avec cases=outside})
          sinon
            make_if_out
              konst ctx
              (low+ctx.off)
              (high-low)
              (fonc ctx -> c_test konst ctx {s avec cases=outside})
              (fonc ctx -> c_test konst ctx {s avec cases=inside})
        fin
    | Sep i ->
        soit lim,left,right = coupe cases i dans
        soit _,(cleft,_) = opt_count faux left
        et _,(cright,_) = opt_count faux right dans
        soit left = {s avec cases=left}
        et right = {s avec cases=right} dans

        si i=1 && (lim+ctx.off)=1 && get_low cases 0+ctx.off=0 alors
          make_if_ne konst
            ctx.arg 0
            (c_test konst ctx right) (c_test konst ctx left)
        sinon si less_tests cright cleft alors
          make_if_lt konst
            ctx.arg (lim+ctx.off)
            (c_test konst ctx left) (c_test konst ctx right)
        sinon
          make_if_ge konst
             ctx.arg (lim+ctx.off)
            (c_test konst ctx right) (c_test konst ctx left)

  fin


(* Minimal density of switches *)
soit theta = ref 0.33333

(* Minmal number of tests to make a switch *)
soit switch_min = ref 3

(* Particular case 0, 1, 2 *)
soit particular_case cases i j =
  j-i = 2 &&
  (soit l1,h1,act1 = cases.(i)
  et  l2,h2,act2 = cases.(i+1)
  et  l3,h3,act3 = cases.(i+2) dans
  l1+1=l2 && l2+1=l3 && l3=h3 &&
  act1 <> act3)

soit approx_count cases i j n_actions =
  soit l = j-i+1 dans
  si l < !cut alors
     soit _,(_,{n=ntests}) = opt_count faux (Array.sub cases i l) dans
     ntests
  sinon
    l-1

(* Sends back a boolean that says whether is switch is worth or not *)

soit dense {cases=cases ; actions=actions} i j =
  si i=j alors vrai
  sinon
    soit l,_,_ = cases.(i)
    et _,h,_ = cases.(j) dans
    soit ntests =  approx_count cases i j (Array.length actions) dans
(*
  (ntests+1) >= theta * (h-l+1)
*)
    particular_case cases i j ||
    (ntests >= !switch_min &&
    float_of_int ntests +. 1.0 >=
    !theta *. (float_of_int h -. float_of_int l +. 1.0))

(* Compute clusters by dynamic programming
   Adaptation of the correction to Bernstein
   ``Correction to `Producing Good Code for the Case Statement' ''
   S.K. Kannan and T.A. Proebsting
   Software Practice and Exprience Vol. 24(2) 233 (Feb 1994)
*)

soit comp_clusters ({cases=cases ; actions=actions} tel s) =
  soit len = Array.length cases dans
  soit min_clusters = Array.create len max_int
  et k = Array.create len 0 dans
  soit get_min i = si i < 0 alors 0 sinon min_clusters.(i) dans

  pour i = 0 à len-1 faire
    pour j = 0 à i faire
      si
        dense s j i &&
        get_min (j-1) + 1 < min_clusters.(i)
      alors début
        k.(i) <- j ;
        min_clusters.(i) <- get_min (j-1) + 1
      fin
    fait ;
  fait ;
  min_clusters.(len-1),k

(* Assume j > i *)
soit make_switch  {cases=cases ; actions=actions} i j =
  soit ll,_,_ = cases.(i)
  et _,hh,_ = cases.(j) dans
  soit tbl = Array.create (hh-ll+1) 0
  et t = Hashtbl.create 17
  et index = ref 0 dans
  soit get_index act =
    essaie
      Hashtbl.find t act
    avec
    | Not_found ->
        soit i = !index dans
        incr index ;
        Hashtbl.add t act i ;
        i dans

  pour k=i à j faire
    soit l,h,act = cases.(k) dans
    soit index = get_index act dans
    pour kk=l-ll à h-ll faire
      tbl.(kk) <- index
    fait
  fait ;
  soit acts = Array.create !index actions.(0) dans
  Hashtbl.iter
    (fonc act i -> acts.(i) <- actions.(act))
    t ;
  (fonc ctx ->
    filtre -ll-ctx.off avec
    | 0 -> Arg.make_switch ctx.arg tbl acts
    | _ ->
        Arg.bind
          (Arg.make_offset ctx.arg (-ll-ctx.off))
          (fonc arg -> Arg.make_switch arg tbl acts))


soit make_clusters ({cases=cases ; actions=actions} tel s) n_clusters k =
  soit len = Array.length cases dans
  soit r = Array.create n_clusters (0,0,0)
  et t = Hashtbl.create 17
  et index = ref 0
  et bidon = ref (Array.length actions) dans
  soit get_index act =
    essaie
      soit i,_ = Hashtbl.find t act dans
      i
    avec
    | Not_found ->
        soit i = !index dans
        incr index ;
        Hashtbl.add
          t act
          (i,(fonc _ -> actions.(act))) ;
        i
  et add_index act =
    soit i = !index dans
    incr index ;
    incr bidon ;
    Hashtbl.add t !bidon (i,act) ;
    i dans

  soit rec zyva j ir =
    soit i = k.(j) dans
    début si i=j alors
      soit l,h,act = cases.(i) dans
      r.(ir) <- (l,h,get_index act)
    sinon (* assert i < j *)
      soit l,_,_ = cases.(i)
      et _,h,_ = cases.(j) dans
      r.(ir) <- (l,h,add_index (make_switch s i j))
    fin ;
    si i > 0 alors zyva (i-1) (ir-1) dans

  zyva (len-1) (n_clusters-1) ;
  soit acts = Array.create !index (fonc _ -> affirme faux) dans
  Hashtbl.iter (fonc _ (i,act) -> acts.(i) <- act) t ;
  {cases = r ; actions = acts}
;;


soit zyva (low,high) konst arg cases actions =
  soit old_ok = !ok_inter dans
  ok_inter := (abs low <= inter_limit && abs high <= inter_limit) ;
  si !ok_inter <> old_ok alors Hashtbl.clear t ;

  soit s = {cases=cases ; actions=actions} dans
(*
  Printf.eprintf "ZYVA: %b\n" !ok_inter ;
  pcases stderr cases ;
  prerr_endline "" ;
*)
  soit n_clusters,k = comp_clusters s dans
  soit clusters = make_clusters s n_clusters k dans
  soit r = c_test konst {arg=arg ; off=0} clusters dans
  r



et test_sequence konst arg cases actions =
  soit old_ok = !ok_inter dans
  ok_inter := faux ;
  si !ok_inter <> old_ok alors Hashtbl.clear t ;
  soit s =
    {cases=cases ;
    actions=Array.map (fonc act -> (fonc _ -> act)) actions} dans
(*
  Printf.eprintf "SEQUENCE: %b\n" !ok_inter ;
  pcases stderr cases ;
  prerr_endline "" ;
*)
  soit r = c_test konst {arg=arg ; off=0} s dans
  r
;;

fin
