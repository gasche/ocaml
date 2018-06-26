(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Transformation of Mach code into a list of pseudo-instructions. *)

open Reg
open Mach

type label = Cmm.label

type instruction =
  { mutable desc: instruction_desc;
    mutable next: instruction;
    arg: Reg.t array;
    res: Reg.t array;
    dbg: Debuginfo.t;
    live: Reg.Set.t;
    mutable temperature : Lambda.temperature_attribute; }

and instruction_desc =
    Lend
  | Lop of operation
  | Lreloadretaddr
  | Lreturn
  | Llabel of label
  | Lbranch of label
  | Lcondbranch of test * label
  | Lcondbranch3 of label option * label option * label option
  | Lswitch of label array
  | Lsetuptrap of label
  | Lpushtrap
  | Lpoptrap
  | Lraise of Cmm.raise_kind

let has_fallthrough = function
  | Lreturn | Lbranch _ | Lswitch _ | Lraise _
  | Lop Itailcall_ind _ | Lop (Itailcall_imm _) -> false
  (* XXX | Lsetuptrap _ -> Config.trywith_optim*)
  | _ -> true

type fundecl =
  { fun_name: string;
    fun_body: instruction;
    fun_fast: bool;
    fun_dbg : Debuginfo.t;
    fun_spacetime_shape : Mach.spacetime_shape option;
    fun_temperature : Lambda.temperature_attribute;
  }

(* Invert a test *)

let invert_integer_test = function
    Isigned cmp -> Isigned(Cmm.negate_comparison cmp)
  | Iunsigned cmp -> Iunsigned(Cmm.negate_comparison cmp)

let invert_test = function
    Itruetest -> Ifalsetest
  | Ifalsetest -> Itruetest
  | Iinttest(cmp) -> Iinttest(invert_integer_test cmp)
  | Iinttest_imm(cmp, n) -> Iinttest_imm(invert_integer_test cmp, n)
  | Ifloattest(cmp, neg) -> Ifloattest(cmp, not neg)
  | Ieventest -> Ioddtest
  | Ioddtest -> Ieventest

(* The "end" instruction *)

let rec end_instr =
  { desc = Lend;
    next = end_instr;
    arg = [||];
    res = [||];
    dbg = Debuginfo.none;
    live = Reg.Set.empty;
    temperature = Lambda.Tepid; }

(* Cons an instruction (live, debug empty) *)

let instr_cons d a r n t =
  { desc = d; next = n; arg = a; res = r;
    dbg = Debuginfo.none; live = Reg.Set.empty;
    temperature = t; }

(* Cons a simple instruction (arg, res, live empty) *)

let cons_instr d n t =
  { desc = d; next = n; arg = [||]; res = [||];
    dbg = Debuginfo.none; live = Reg.Set.empty;
    temperature = t; }

(* Build an instruction with arg, res, dbg, live taken from
   the given Mach.instruction *)

let copy_instr d i n t =
  { desc = d; next = n;
    arg = i.Mach.arg; res = i.Mach.res;
    dbg = i.Mach.dbg; live = i.Mach.live;
    temperature = t; }


(*
   Label the beginning of the given instruction sequence.
   - If the sequence starts with a branch, jump over it.
   - If the sequence is the end, (tail call position), just do nothing
*)

let get_label n = match n.desc with
    Lbranch lbl -> (lbl, n)
  | Llabel lbl -> (lbl, n)
  | Lend -> (-1, n)
  | _ -> let lbl = Cmm.new_label() in (lbl, cons_instr (Llabel lbl) n n.temperature)

(* Check the fallthrough label *)
let check_label n = match n.desc with
  | Lbranch lbl -> lbl
  | Llabel lbl -> lbl
  | _ -> -1

(* Discard all instructions up to the next label.
   This function is to be called before adding a non-terminating
   instruction. *)

let rec discard_dead_code n =
  match n.desc with
    Lend -> n
  | Llabel _ -> n
(* Do not discard Lpoptrap/Lpushtrap or Istackoffset instructions,
   as this may cause a stack imbalance later during assembler generation. *)
  | Lpoptrap | Lpushtrap -> n
  | Lop(Istackoffset _) -> n
  | _ -> discard_dead_code n.next

(*
   Add a branch in front of a continuation.
   Discard dead code in the continuation.
   Does not insert anything if we're just falling through
   or if we jump to dead code after the end of function (lbl=-1)
*)

let add_branch lbl n t =
  if lbl >= 0 then
    let n1 = discard_dead_code n in
    match n1.desc with
    | Llabel lbl1 when lbl1 = lbl -> n1
    | _ -> cons_instr (Lbranch lbl) n1 t
  else
    discard_dead_code n

let try_depth = ref 0

(* Association list: exit handler -> (handler label, try-nesting factor) *)

let exit_label = ref []

let find_exit_label_try_depth k =
  try
    List.assoc k !exit_label
  with
  | Not_found -> Misc.fatal_error "Linearize.find_exit_label"

let find_exit_label k =
  let (label, t) = find_exit_label_try_depth k in
  assert(t = !try_depth);
  label

let is_next_catch n = match !exit_label with
| (n0,(_,t))::_  when n0=n && t = !try_depth -> true
| _ -> false

let local_exit k =
  snd (find_exit_label_try_depth k) = !try_depth

(* Linearize an instruction [i]: add it in front of the continuation [n] *)

let combine_temperature_for_ifthenelse ~attribute ~current =
  let open Lambda in
  match attribute, current with
  (* [@likely] *)
  | Hot _, Cold _ -> current, current
  | Hot { explicit; }, (Tepid | Hot _) -> current, Cold { explicit; }
  (* [@unlikely] *)
  | Cold _, Cold _ -> current, current
  | Cold { explicit; }, (Tepid | Hot _) -> Cold { explicit; }, current
  (* no attribute *)
  | Tepid, _ -> current, current

let combine_temperature_for_trywith ~attribute ~current =
  let open Lambda in
  match attribute, current with
  (* [@likely] *)
  | Hot _, Cold _ -> current, current
  | Hot { explicit; }, (Tepid | Hot _) -> current, Cold { explicit; }
  (* [@unlikely] *)
  | Cold _, _ -> current, current
  (* no attribute *)
  | Tepid, _ -> current, current

let rec linear curr_temp i n =
  match i.Mach.desc with
    Iend -> n
  | Iop(Itailcall_ind _ | Itailcall_imm _ as op) ->
      if not Config.spacetime then
        copy_instr (Lop op) i (discard_dead_code n) curr_temp
      else
        copy_instr (Lop op) i (linear curr_temp i.Mach.next n) curr_temp
  | Iop(Imove | Ireload | Ispill)
    when i.Mach.arg.(0).loc = i.Mach.res.(0).loc ->
      linear curr_temp i.Mach.next n
  | Iop op ->
      copy_instr (Lop op) i (linear curr_temp i.Mach.next n) curr_temp
  | Ireturn ->
      let n1 = copy_instr Lreturn i (discard_dead_code n) curr_temp in
      if !Proc.contains_calls
      then cons_instr Lreloadretaddr n1 curr_temp
      else n1
  | Iifthenelse(test, temp, ifso, ifnot) ->
      let n1 = linear curr_temp i.Mach.next n in
      let temp_ifso, temp_ifnot =
        combine_temperature_for_ifthenelse
          ~attribute:temp
          ~current:curr_temp
      in
      begin match (ifso.Mach.desc, ifnot.Mach.desc, n1.desc) with
        Iend, _, Lbranch lbl ->
          copy_instr (Lcondbranch(test, lbl)) i (linear temp_ifnot ifnot n1) curr_temp
      | _, Iend, Lbranch lbl ->
          copy_instr (Lcondbranch(invert_test test, lbl)) i (linear temp_ifso ifso n1) curr_temp
      | Iexit nfail1, Iexit nfail2, _
            when is_next_catch nfail1 && local_exit nfail2 ->
          let lbl2 = find_exit_label nfail2 in
          copy_instr
            (Lcondbranch (invert_test test, lbl2)) i (linear temp_ifso ifso n1) curr_temp
      | Iexit nfail, _, _ when local_exit nfail ->
          let n2 = linear temp_ifnot ifnot n1
          and lbl = find_exit_label nfail in
          copy_instr (Lcondbranch(test, lbl)) i n2 curr_temp
      | _,  Iexit nfail, _ when local_exit nfail ->
          let n2 = linear temp_ifso ifso n1 in
          let lbl = find_exit_label nfail in
          copy_instr (Lcondbranch(invert_test test, lbl)) i n2 curr_temp
      | Iend, _, _ ->
          let (lbl_end, n2) = get_label n1 in
          copy_instr (Lcondbranch(test, lbl_end)) i (linear temp_ifnot ifnot n2) curr_temp
      | _,  Iend, _ ->
          let (lbl_end, n2) = get_label n1 in
          copy_instr (Lcondbranch(invert_test test, lbl_end)) i
                     (linear temp_ifso ifso n2) curr_temp
      | _, _, _ ->
        (* Should attempt branch prediction here *)
          begin match temp with
          | Lambda.Tepid | Lambda.Hot _ ->
            let (lbl_end, n2) = get_label n1 in
            let (lbl_else, nelse) = get_label (linear temp_ifnot ifnot n2) in
            copy_instr (Lcondbranch(invert_test test, lbl_else)) i
              (linear temp_ifso ifso (add_branch lbl_end nelse curr_temp)) curr_temp
          | Lambda.Cold _ ->
            let (lbl_end, n2) = get_label n1 in
            let (lbl_then, nthen) = get_label (linear temp_ifso ifso n2) in
            copy_instr (Lcondbranch(test, lbl_then)) i
              (linear temp_ifnot ifnot (add_branch lbl_end nthen curr_temp)) curr_temp
        end
      end
  | Iswitch(index, cases) ->
      let lbl_cases = Array.make (Array.length cases) 0 in
      let (lbl_end, n1) = get_label(linear curr_temp i.Mach.next n) in
      let n2 = ref (discard_dead_code n1) in
      for i = Array.length cases - 1 downto 0 do
        let (lbl_case, ncase) =
                get_label(linear curr_temp cases.(i) (add_branch lbl_end !n2 curr_temp)) in
        lbl_cases.(i) <- lbl_case;
        n2 := discard_dead_code ncase
      done;
      (* Switches with 1 and 2 branches have been eliminated earlier.
         Here, we do something for switches with 3 branches. *)
      if Array.length index = 3 then begin
        let fallthrough_lbl = check_label !n2 in
        let find_label n =
          let lbl = lbl_cases.(index.(n)) in
          if lbl = fallthrough_lbl then None else Some lbl in
        copy_instr (Lcondbranch3(find_label 0, find_label 1, find_label 2))
                   i !n2 curr_temp
      end else
        copy_instr (Lswitch(Array.map (fun n -> lbl_cases.(n)) index)) i !n2 curr_temp
  | Iloop body ->
      let lbl_head = Cmm.new_label() in
      let n1 = linear curr_temp i.Mach.next n in
      let n2 = linear curr_temp body (cons_instr (Lbranch lbl_head) n1 curr_temp) in
      cons_instr (Llabel lbl_head) n2 curr_temp
  | Icatch(_rec_flag, handlers, body) ->
      let (lbl_end, n1) = get_label(linear curr_temp i.Mach.next n) in
      (* CR mshinwell for pchambart:
         1. rename "io"
         2. Make sure the test cases cover the "Iend" cases too *)
      let labels_at_entry_to_handlers = List.map (fun (_nfail, handler) ->
          match handler.Mach.desc with
          | Iend -> lbl_end
          | _ -> Cmm.new_label ())
          handlers in
      let exit_label_add = List.map2
          (fun (nfail, _) lbl -> (nfail, (lbl, !try_depth)))
          handlers labels_at_entry_to_handlers in
      let previous_exit_label = !exit_label in
      exit_label := exit_label_add @ !exit_label;
      let n2 = List.fold_left2 (fun n (_nfail, handler) lbl_handler ->
          match handler.Mach.desc with
          | Iend -> n
          | _ -> cons_instr (Llabel lbl_handler) (linear curr_temp handler n) curr_temp)
          n1 handlers labels_at_entry_to_handlers
      in
      let n3 = linear curr_temp body (add_branch lbl_end n2 curr_temp) in
      exit_label := previous_exit_label;
      n3
  | Iexit nfail ->
      let lbl, t = find_exit_label_try_depth nfail in
      (* We need to re-insert dummy pushtrap (which won't be executed),
         so as to preserve stack offset during assembler generation.
         It would make sense to have a special pseudo-instruction
         only to inform the later pass about this stack offset
         (corresponding to N traps).
       *)
      let rec loop i tt =
        if t = tt then i
        else loop (cons_instr Lpushtrap i curr_temp) (tt - 1)
      in
      let n1 = loop (linear curr_temp i.Mach.next n) !try_depth in
      let rec loop i tt =
        if t = tt then i
        else loop (cons_instr Lpoptrap i curr_temp) (tt - 1)
      in
      loop (add_branch lbl n1 curr_temp) !try_depth
  | Itrywith(body, temp, handler) ->
    let temp_body, temp_handler =
      combine_temperature_for_trywith
        ~attribute:temp
        ~current:curr_temp
    in
    if Config.trywith_optim then begin
      let (lbl_join, n1) = get_label (linear curr_temp i.Mach.next n) in
      let (lbl_handler, n2) = get_label (linear temp_handler handler n1) in
      incr try_depth;
      assert (i.Mach.arg = [| |] || Config.spacetime);
      let jump_join = add_branch lbl_join n2 temp_body in
      let n3 =
        instr_cons Lpushtrap i.Mach.arg [| |]
          (linear temp_body body (cons_instr Lpoptrap jump_join temp_body))
          temp_body
      in
      decr try_depth;
      instr_cons (Lsetuptrap lbl_handler) i.Mach.arg [||] n3 temp_body
    end else begin
      let (lbl_join, n1) = get_label (linear curr_temp i.Mach.next n) in
      incr try_depth;
      assert (i.Mach.arg = [| |] || Config.spacetime);
      let (lbl_body, n2) =
        get_label (instr_cons Lpushtrap i.Mach.arg [| |]
                    (linear temp_body body (cons_instr Lpoptrap n1 temp_body)) temp_body) in
      decr try_depth;
      instr_cons (Lsetuptrap lbl_body) i.Mach.arg [| |]
        (linear temp_handler handler (add_branch lbl_join n2 curr_temp))
        curr_temp
    end
  | Iraise k ->
    copy_instr (Lraise k) i (discard_dead_code n) curr_temp

(* Ensures that a label always has the same temperature as the following
   instructions *)
let rec fix_label_temperatures i =
  let rec get_temperature j =
    match j.desc with
    | Llabel _ -> get_temperature j.next
    | _ -> j.temperature
  in
  if i.desc <> Lend then begin
    begin match i.desc with
    | Llabel _ when i.next.desc <> Lend ->
      i.temperature <- get_temperature i.next
    | _ ->
      ()
    end;
    fix_label_temperatures i.next
  end

let rec add_jump_for_temperature_changes (i : instruction) =
  let copy_instr' d i n t =
    { desc = d; next = n;
      arg = i.arg; res = i.res;
      dbg = i.dbg; live = i.live;
      temperature = t; }
  in
  if (i.desc <> Lend)
  && (i.next.desc <> Lend)
  && not (Lambda.same_temperature i.temperature i.next.temperature)
  && (has_fallthrough i.desc) then begin
    match i.next.desc with
    | Lreloadretaddr ->
      i.next.temperature <- i.temperature
    | Llabel lbl ->
      let jump = copy_instr' (Lbranch lbl) i i.next i.temperature in
      i.next <- jump;
    | _ ->
      let new_label = Cmm.new_label () in
      let label =
        copy_instr' (Llabel  new_label) i.next i.next i.next.temperature
      in
      let jump =
        copy_instr' (Lbranch new_label) i label i.temperature in
      i.next <- jump;
  end;
  if i.desc <> Lend then
    add_jump_for_temperature_changes i.next

let fundecl f =
  let fun_body = linear f.Mach.fun_temperature f.Mach.fun_body end_instr in
  fix_label_temperatures fun_body;
  add_jump_for_temperature_changes fun_body;
  { fun_name = f.Mach.fun_name;
    fun_body;
    fun_fast = f.Mach.fun_fast;
    fun_dbg  = f.Mach.fun_dbg;
    fun_spacetime_shape = f.Mach.fun_spacetime_shape;
    fun_temperature = f.Mach.fun_temperature;
  }
