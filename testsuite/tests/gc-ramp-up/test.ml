(* TEST
   ocamlrunparam += ",v=0x0040";
*)


let log str =
  print_string "LOG: ";
  print_endline str

let allocate_on_major () =
  ignore (Sys.opaque_identity (Array.init 10_000 Fun.id))

let () =
  log "Phase 1: perform allocations as usual.";
  allocate_on_major ();
  log "End the current GC slice.";
  log "In the GC logging below we expect:";
  log "- allocated_words_suspended at 0";
  log "- work-to-do at some non-zero value";
  Gc.major ()

let deferred_work =
  log "";
  log "Phase 2: perform allocations during ramp-up";
  let (), deferred_work =
    Gc.ramp_up (fun () ->
      allocate_on_major ();
    )
  in
  log "End the current GC slice (after ramp-up).";
  log "In the GC logging below we expect:";
  log "- allocated_words_suspended at almost allocated_words";
  log "- work-to-do at an almost-zero value";
  Gc.major ();
  deferred_work

let () =
  log "";
  log "Phase 3: resume the suspended deallocation work";
  Gc.ramp_down deferred_work;
  log "End the current GC slice (after ramp-down).";
  log "In the GC logging below we expect:";
  log "- allocated_words at an almost-zero value";
  log "- allocated_words_resumed equal to \
       the allocated_words_suspended of Phase 2";
  log "- work-to-do close at some non-zero value";
  Gc.major ()

