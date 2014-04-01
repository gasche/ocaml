(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../../LICENSE.  *)
(*                                                                     *)
(***********************************************************************)

type error =
    E2BIG
  | EACCES
  | EAGAIN
  | EBADF
  | EBUSY
  | ECHILD
  | EDEADLK
  | EDOM
  | EEXIST
  | EFAULT
  | EFBIG
  | EINTR
  | EINVAL
  | EIO
  | EISDIR
  | EMFILE
  | EMLINK
  | ENAMETOOLONG
  | ENFILE
  | ENODEV
  | ENOENT
  | ENOEXEC
  | ENOLCK
  | ENOMEM
  | ENOSPC
  | ENOSYS
  | ENOTDIR
  | ENOTEMPTY
  | ENOTTY
  | ENXIO
  | EPERM
  | EPIPE
  | ERANGE
  | EROFS
  | ESPIPE
  | ESRCH
  | EXDEV
  | EWOULDBLOCK
  | EINPROGRESS
  | EALREADY
  | ENOTSOCK
  | EDESTADDRREQ
  | EMSGSIZE
  | EPROTOTYPE
  | ENOPROTOOPT
  | EPROTONOSUPPORT
  | ESOCKTNOSUPPORT
  | EOPNOTSUPP
  | EPFNOSUPPORT
  | EAFNOSUPPORT
  | EADDRINUSE
  | EADDRNOTAVAIL
  | ENETDOWN
  | ENETUNREACH
  | ENETRESET
  | ECONNABORTED
  | ECONNRESET
  | ENOBUFS
  | EISCONN
  | ENOTCONN
  | ESHUTDOWN
  | ETOOMANYREFS
  | ETIMEDOUT
  | ECONNREFUSED
  | EHOSTDOWN
  | EHOSTUNREACH
  | ELOOP
  | EOVERFLOW
  | EUNKNOWNERR de int

exception Unix_error de error * string * string

soit _ = Callback.register_exception "Unix.Unix_error"
                                    (Unix_error(E2BIG, "", ""))

dehors error_message : error -> string = "unix_error_message"

soit () =
  Printexc.register_printer
    (fonction
      | Unix_error (e, s, s') ->
          soit msg = filtre e avec
          | E2BIG -> "E2BIG"
          | EACCES -> "EACCES"
          | EAGAIN -> "EAGAIN"
          | EBADF -> "EBADF"
          | EBUSY -> "EBUSY"
          | ECHILD -> "ECHILD"
          | EDEADLK -> "EDEADLK"
          | EDOM -> "EDOM"
          | EEXIST -> "EEXIST"
          | EFAULT -> "EFAULT"
          | EFBIG -> "EFBIG"
          | EINTR -> "EINTR"
          | EINVAL -> "EINVAL"
          | EIO -> "EIO"
          | EISDIR -> "EISDIR"
          | EMFILE -> "EMFILE"
          | EMLINK -> "EMLINK"
          | ENAMETOOLONG -> "ENAMETOOLONG"
          | ENFILE -> "ENFILE"
          | ENODEV -> "ENODEV"
          | ENOENT -> "ENOENT"
          | ENOEXEC -> "ENOEXEC"
          | ENOLCK -> "ENOLCK"
          | ENOMEM -> "ENOMEM"
          | ENOSPC -> "ENOSPC"
          | ENOSYS -> "ENOSYS"
          | ENOTDIR -> "ENOTDIR"
          | ENOTEMPTY -> "ENOTEMPTY"
          | ENOTTY -> "ENOTTY"
          | ENXIO -> "ENXIO"
          | EPERM -> "EPERM"
          | EPIPE -> "EPIPE"
          | ERANGE -> "ERANGE"
          | EROFS -> "EROFS"
          | ESPIPE -> "ESPIPE"
          | ESRCH -> "ESRCH"
          | EXDEV -> "EXDEV"
          | EWOULDBLOCK -> "EWOULDBLOCK"
          | EINPROGRESS -> "EINPROGRESS"
          | EALREADY -> "EALREADY"
          | ENOTSOCK -> "ENOTSOCK"
          | EDESTADDRREQ -> "EDESTADDRREQ"
          | EMSGSIZE -> "EMSGSIZE"
          | EPROTOTYPE -> "EPROTOTYPE"
          | ENOPROTOOPT -> "ENOPROTOOPT"
          | EPROTONOSUPPORT -> "EPROTONOSUPPORT"
          | ESOCKTNOSUPPORT -> "ESOCKTNOSUPPORT"
          | EOPNOTSUPP -> "EOPNOTSUPP"
          | EPFNOSUPPORT -> "EPFNOSUPPORT"
          | EAFNOSUPPORT -> "EAFNOSUPPORT"
          | EADDRINUSE -> "EADDRINUSE"
          | EADDRNOTAVAIL -> "EADDRNOTAVAIL"
          | ENETDOWN -> "ENETDOWN"
          | ENETUNREACH -> "ENETUNREACH"
          | ENETRESET -> "ENETRESET"
          | ECONNABORTED -> "ECONNABORTED"
          | ECONNRESET -> "ECONNRESET"
          | ENOBUFS -> "ENOBUFS"
          | EISCONN -> "EISCONN"
          | ENOTCONN -> "ENOTCONN"
          | ESHUTDOWN -> "ESHUTDOWN"
          | ETOOMANYREFS -> "ETOOMANYREFS"
          | ETIMEDOUT -> "ETIMEDOUT"
          | ECONNREFUSED -> "ECONNREFUSED"
          | EHOSTDOWN -> "EHOSTDOWN"
          | EHOSTUNREACH -> "EHOSTUNREACH"
          | ELOOP -> "ELOOP"
          | EOVERFLOW -> "EOVERFLOW"
          | EUNKNOWNERR x -> Printf.sprintf "EUNKNOWNERR %d" x dans
          Some (Printf.sprintf "Unix.Unix_error(Unix.%s, %S, %S)" msg s s')
      | _ -> None)

soit handle_unix_error f arg =
  essaie
    f arg
  avec Unix_error(err, fun_name, arg) ->
    prerr_string Sys.argv.(0);
    prerr_string ": \"";
    prerr_string fun_name;
    prerr_string "\" failed";
    si String.length arg > 0 alors début
      prerr_string " on \"";
      prerr_string arg;
      prerr_string "\""
    fin;
    prerr_string ": ";
    prerr_endline (error_message err);
    exit 2

dehors environment : unit -> string array = "unix_environment"
dehors getenv: string -> string = "caml_sys_getenv"
dehors putenv: string -> string -> unit = "unix_putenv"

type process_status =
    WEXITED de int
  | WSIGNALED de int
  | WSTOPPED de int

type wait_flag =
    WNOHANG
  | WUNTRACED

dehors execv : string -> string array -> 'a = "unix_execv"
dehors execve : string -> string array -> string array -> 'a = "unix_execve"
dehors execvp : string -> string array -> 'a = "unix_execvp"
dehors execvpe : string -> string array -> string array -> 'a = "unix_execvpe"
dehors fork : unit -> int = "unix_fork"
dehors wait : unit -> int * process_status = "unix_wait"
dehors waitpid : wait_flag list -> int -> int * process_status
   = "unix_waitpid"
dehors getpid : unit -> int = "unix_getpid"
dehors getppid : unit -> int = "unix_getppid"
dehors nice : int -> int = "unix_nice"

type file_descr = int

soit stdin = 0
soit stdout = 1
soit stderr = 2

type open_flag =
    O_RDONLY
  | O_WRONLY
  | O_RDWR
  | O_NONBLOCK
  | O_APPEND
  | O_CREAT
  | O_TRUNC
  | O_EXCL
  | O_NOCTTY
  | O_DSYNC
  | O_SYNC
  | O_RSYNC
  | O_SHARE_DELETE
  | O_CLOEXEC

type file_perm = int


dehors openfile : string -> open_flag list -> file_perm -> file_descr
           = "unix_open"

dehors close : file_descr -> unit = "unix_close"
dehors unsafe_read : file_descr -> string -> int -> int -> int = "unix_read"
dehors unsafe_write : file_descr -> string -> int -> int -> int = "unix_write"
dehors unsafe_single_write : file_descr -> string -> int -> int -> int
   = "unix_single_write"

soit read fd buf ofs len =
  si ofs < 0 || len < 0 || ofs > String.length buf - len
  alors invalid_arg "Unix.read"
  sinon unsafe_read fd buf ofs len
soit write fd buf ofs len =
  si ofs < 0 || len < 0 || ofs > String.length buf - len
  alors invalid_arg "Unix.write"
  sinon unsafe_write fd buf ofs len
(* write misbehaves because it attempts to write all data by making repeated
   calls to the Unix write function (see comment in write.c and unix.mli).
   partial_write fixes this by never calling write twice. *)
soit single_write fd buf ofs len =
  si ofs < 0 || len < 0 || ofs > String.length buf - len
  alors invalid_arg "Unix.single_write"
  sinon unsafe_single_write fd buf ofs len

dehors in_channel_of_descr : file_descr -> in_channel
                             = "caml_ml_open_descriptor_in"
dehors out_channel_of_descr : file_descr -> out_channel
                              = "caml_ml_open_descriptor_out"
dehors descr_of_in_channel : in_channel -> file_descr
                             = "caml_channel_descriptor"
dehors descr_of_out_channel : out_channel -> file_descr
                              = "caml_channel_descriptor"

type seek_command =
    SEEK_SET
  | SEEK_CUR
  | SEEK_END

dehors lseek : file_descr -> int -> seek_command -> int = "unix_lseek"
dehors truncate : string -> int -> unit = "unix_truncate"
dehors ftruncate : file_descr -> int -> unit = "unix_ftruncate"

type file_kind =
    S_REG
  | S_DIR
  | S_CHR
  | S_BLK
  | S_LNK
  | S_FIFO
  | S_SOCK

type stats =
  { st_dev : int;
    st_ino : int;
    st_kind : file_kind;
    st_perm : file_perm;
    st_nlink : int;
    st_uid : int;
    st_gid : int;
    st_rdev : int;
    st_size : int;
    st_atime : float;
    st_mtime : float;
    st_ctime : float }

dehors stat : string -> stats = "unix_stat"
dehors lstat : string -> stats = "unix_lstat"
dehors fstat : file_descr -> stats = "unix_fstat"
dehors isatty : file_descr -> bool = "unix_isatty"
dehors unlink : string -> unit = "unix_unlink"
dehors rename : string -> string -> unit = "unix_rename"
dehors link : string -> string -> unit = "unix_link"

module LargeFile =
  struct
    dehors lseek : file_descr -> int64 -> seek_command -> int64
       = "unix_lseek_64"
    dehors truncate : string -> int64 -> unit = "unix_truncate_64"
    dehors ftruncate : file_descr -> int64 -> unit = "unix_ftruncate_64"
    type stats =
      { st_dev : int;
        st_ino : int;
        st_kind : file_kind;
        st_perm : file_perm;
        st_nlink : int;
        st_uid : int;
        st_gid : int;
        st_rdev : int;
        st_size : int64;
        st_atime : float;
        st_mtime : float;
        st_ctime : float;
      }
    dehors stat : string -> stats = "unix_stat_64"
    dehors lstat : string -> stats = "unix_lstat_64"
    dehors fstat : file_descr -> stats = "unix_fstat_64"
  fin

type access_permission =
    R_OK
  | W_OK
  | X_OK
  | F_OK

dehors chmod : string -> file_perm -> unit = "unix_chmod"
dehors fchmod : file_descr -> file_perm -> unit = "unix_fchmod"
dehors chown : string -> int -> int -> unit = "unix_chown"
dehors fchown : file_descr -> int -> int -> unit = "unix_fchown"
dehors umask : int -> int = "unix_umask"
dehors access : string -> access_permission list -> unit = "unix_access"

dehors dup : file_descr -> file_descr = "unix_dup"
dehors dup2 : file_descr -> file_descr -> unit = "unix_dup2"
dehors set_nonblock : file_descr -> unit = "unix_set_nonblock"
dehors clear_nonblock : file_descr -> unit = "unix_clear_nonblock"
dehors set_close_on_exec : file_descr -> unit = "unix_set_close_on_exec"
dehors clear_close_on_exec : file_descr -> unit = "unix_clear_close_on_exec"

(* FD_CLOEXEC should be supported on all Unix systems these days,
   but just in case... *)
soit try_set_close_on_exec fd =
  essaie set_close_on_exec fd; vrai avec Invalid_argument _ -> faux

dehors mkdir : string -> file_perm -> unit = "unix_mkdir"
dehors rmdir : string -> unit = "unix_rmdir"
dehors chdir : string -> unit = "unix_chdir"
dehors getcwd : unit -> string = "unix_getcwd"
dehors chroot : string -> unit = "unix_chroot"

type dir_handle

dehors opendir : string -> dir_handle = "unix_opendir"
dehors readdir : dir_handle -> string = "unix_readdir"
dehors rewinddir : dir_handle -> unit = "unix_rewinddir"
dehors closedir : dir_handle -> unit = "unix_closedir"

dehors pipe : unit -> file_descr * file_descr = "unix_pipe"
dehors symlink : string -> string -> unit = "unix_symlink"
dehors readlink : string -> string = "unix_readlink"
dehors mkfifo : string -> file_perm -> unit = "unix_mkfifo"
dehors select :
  file_descr list -> file_descr list -> file_descr list -> float ->
        file_descr list * file_descr list * file_descr list = "unix_select"

type lock_command =
    F_ULOCK
  | F_LOCK
  | F_TLOCK
  | F_TEST
  | F_RLOCK
  | F_TRLOCK

dehors lockf : file_descr -> lock_command -> int -> unit = "unix_lockf"
dehors kill : int -> int -> unit = "unix_kill"
type sigprocmask_command = SIG_SETMASK | SIG_BLOCK | SIG_UNBLOCK
dehors sigprocmask: sigprocmask_command -> int list -> int list
        = "unix_sigprocmask"
dehors sigpending: unit -> int list = "unix_sigpending"
dehors sigsuspend: int list -> unit = "unix_sigsuspend"

soit pause() =
  soit sigs = sigprocmask SIG_BLOCK [] dans sigsuspend sigs

type process_times =
  { tms_utime : float;
    tms_stime : float;
    tms_cutime : float;
    tms_cstime : float }

type tm =
  { tm_sec : int;
    tm_min : int;
    tm_hour : int;
    tm_mday : int;
    tm_mon : int;
    tm_year : int;
    tm_wday : int;
    tm_yday : int;
    tm_isdst : bool }

dehors time : unit -> float = "unix_time"
dehors gettimeofday : unit -> float = "unix_gettimeofday"
dehors gmtime : float -> tm = "unix_gmtime"
dehors localtime : float -> tm = "unix_localtime"
dehors mktime : tm -> float * tm = "unix_mktime"
dehors alarm : int -> int = "unix_alarm"
dehors sleep : int -> unit = "unix_sleep"
dehors times : unit -> process_times = "unix_times"
dehors utimes : string -> float -> float -> unit = "unix_utimes"

type interval_timer =
    ITIMER_REAL
  | ITIMER_VIRTUAL
  | ITIMER_PROF

type interval_timer_status =
  { it_interval: float;                 (* Period *)
    it_value: float }                   (* Current value of the timer *)

dehors getitimer: interval_timer -> interval_timer_status = "unix_getitimer"
dehors setitimer:
  interval_timer -> interval_timer_status -> interval_timer_status
  = "unix_setitimer"

dehors getuid : unit -> int = "unix_getuid"
dehors geteuid : unit -> int = "unix_geteuid"
dehors setuid : int -> unit = "unix_setuid"
dehors getgid : unit -> int = "unix_getgid"
dehors getegid : unit -> int = "unix_getegid"
dehors setgid : int -> unit = "unix_setgid"
dehors getgroups : unit -> int array = "unix_getgroups"
dehors setgroups : int array -> unit = "unix_setgroups"
dehors initgroups : string -> int -> unit = "unix_initgroups"

type passwd_entry =
  { pw_name : string;
    pw_passwd : string;
    pw_uid : int;
    pw_gid : int;
    pw_gecos : string;
    pw_dir : string;
    pw_shell : string }

type group_entry =
  { gr_name : string;
    gr_passwd : string;
    gr_gid : int;
    gr_mem : string array }


dehors getlogin : unit -> string = "unix_getlogin"
dehors getpwnam : string -> passwd_entry = "unix_getpwnam"
dehors getgrnam : string -> group_entry = "unix_getgrnam"
dehors getpwuid : int -> passwd_entry = "unix_getpwuid"
dehors getgrgid : int -> group_entry = "unix_getgrgid"

type inet_addr = string

soit is_inet6_addr s = String.length s = 16

dehors inet_addr_of_string : string -> inet_addr
                                    = "unix_inet_addr_of_string"
dehors string_of_inet_addr : inet_addr -> string
                                    = "unix_string_of_inet_addr"

soit inet_addr_any = inet_addr_of_string "0.0.0.0"
soit inet_addr_loopback = inet_addr_of_string "127.0.0.1"
soit inet6_addr_any =
  essaie inet_addr_of_string "::" avec Failure _ -> inet_addr_any
soit inet6_addr_loopback =
  essaie inet_addr_of_string "::1" avec Failure _ -> inet_addr_loopback

type socket_domain =
    PF_UNIX
  | PF_INET
  | PF_INET6

type socket_type =
    SOCK_STREAM
  | SOCK_DGRAM
  | SOCK_RAW
  | SOCK_SEQPACKET

type sockaddr =
    ADDR_UNIX de string
  | ADDR_INET de inet_addr * int

soit domain_of_sockaddr = fonction
    ADDR_UNIX _ -> PF_UNIX
  | ADDR_INET(a, _) -> si is_inet6_addr a alors PF_INET6 sinon PF_INET

type shutdown_command =
    SHUTDOWN_RECEIVE
  | SHUTDOWN_SEND
  | SHUTDOWN_ALL

type msg_flag =
    MSG_OOB
  | MSG_DONTROUTE
  | MSG_PEEK

dehors socket : socket_domain -> socket_type -> int -> file_descr
                                  = "unix_socket"
dehors socketpair :
        socket_domain -> socket_type -> int -> file_descr * file_descr
                                  = "unix_socketpair"
dehors accept : file_descr -> file_descr * sockaddr = "unix_accept"
dehors bind : file_descr -> sockaddr -> unit = "unix_bind"
dehors connect : file_descr -> sockaddr -> unit = "unix_connect"
dehors listen : file_descr -> int -> unit = "unix_listen"
dehors shutdown : file_descr -> shutdown_command -> unit = "unix_shutdown"
dehors getsockname : file_descr -> sockaddr = "unix_getsockname"
dehors getpeername : file_descr -> sockaddr = "unix_getpeername"

dehors unsafe_recv :
  file_descr -> string -> int -> int -> msg_flag list -> int
                                  = "unix_recv"
dehors unsafe_recvfrom :
  file_descr -> string -> int -> int -> msg_flag list -> int * sockaddr
                                  = "unix_recvfrom"
dehors unsafe_send :
  file_descr -> string -> int -> int -> msg_flag list -> int
                                  = "unix_send"
dehors unsafe_sendto :
  file_descr -> string -> int -> int -> msg_flag list -> sockaddr -> int
                                  = "unix_sendto" "unix_sendto_native"

soit recv fd buf ofs len flags =
  si ofs < 0 || len < 0 || ofs > String.length buf - len
  alors invalid_arg "Unix.recv"
  sinon unsafe_recv fd buf ofs len flags
soit recvfrom fd buf ofs len flags =
  si ofs < 0 || len < 0 || ofs > String.length buf - len
  alors invalid_arg "Unix.recvfrom"
  sinon unsafe_recvfrom fd buf ofs len flags
soit send fd buf ofs len flags =
  si ofs < 0 || len < 0 || ofs > String.length buf - len
  alors invalid_arg "Unix.send"
  sinon unsafe_send fd buf ofs len flags
soit sendto fd buf ofs len flags addr =
  si ofs < 0 || len < 0 || ofs > String.length buf - len
  alors invalid_arg "Unix.sendto"
  sinon unsafe_sendto fd buf ofs len flags addr

type socket_bool_option =
    SO_DEBUG
  | SO_BROADCAST
  | SO_REUSEADDR
  | SO_KEEPALIVE
  | SO_DONTROUTE
  | SO_OOBINLINE
  | SO_ACCEPTCONN
  | TCP_NODELAY
  | IPV6_ONLY

type socket_int_option =
    SO_SNDBUF
  | SO_RCVBUF
  | SO_ERROR
  | SO_TYPE
  | SO_RCVLOWAT
  | SO_SNDLOWAT

type socket_optint_option = SO_LINGER

type socket_float_option =
    SO_RCVTIMEO
  | SO_SNDTIMEO

type socket_error_option = SO_ERROR

module SO: sig
  type ('opt, 'v) t
  val bool: (socket_bool_option, bool) t
  val int: (socket_int_option, int) t
  val optint: (socket_optint_option, int option) t
  val float: (socket_float_option, float) t
  val error: (socket_error_option, error option) t
  val get: ('opt, 'v) t -> file_descr -> 'opt -> 'v
  val set: ('opt, 'v) t -> file_descr -> 'opt -> 'v -> unit
fin = struct
  type ('opt, 'v) t = int
  soit bool = 0
  soit int = 1
  soit optint = 2
  soit float = 3
  soit error = 4
  dehors get: ('opt, 'v) t -> file_descr -> 'opt -> 'v
              = "unix_getsockopt"
  dehors set: ('opt, 'v) t -> file_descr -> 'opt -> 'v -> unit
              = "unix_setsockopt"
fin

soit getsockopt fd opt = SO.get SO.bool fd opt
soit setsockopt fd opt v = SO.set SO.bool fd opt v

soit getsockopt_int fd opt = SO.get SO.int fd opt
soit setsockopt_int fd opt v = SO.set SO.int fd opt v

soit getsockopt_optint fd opt = SO.get SO.optint fd opt
soit setsockopt_optint fd opt v = SO.set SO.optint fd opt v

soit getsockopt_float fd opt = SO.get SO.float fd opt
soit setsockopt_float fd opt v = SO.set SO.float fd opt v

soit getsockopt_error fd = SO.get SO.error fd SO_ERROR

type host_entry =
  { h_name : string;
    h_aliases : string array;
    h_addrtype : socket_domain;
    h_addr_list : inet_addr array }

type protocol_entry =
  { p_name : string;
    p_aliases : string array;
    p_proto : int }

type service_entry =
  { s_name : string;
    s_aliases : string array;
    s_port : int;
    s_proto : string }

dehors gethostname : unit -> string = "unix_gethostname"
dehors gethostbyname : string -> host_entry = "unix_gethostbyname"
dehors gethostbyaddr : inet_addr -> host_entry = "unix_gethostbyaddr"
dehors getprotobyname : string -> protocol_entry
                                         = "unix_getprotobyname"
dehors getprotobynumber : int -> protocol_entry
                                         = "unix_getprotobynumber"
dehors getservbyname : string -> string -> service_entry
                                         = "unix_getservbyname"
dehors getservbyport : int -> string -> service_entry
                                         = "unix_getservbyport"

type addr_info =
  { ai_family : socket_domain;
    ai_socktype : socket_type;
    ai_protocol : int;
    ai_addr : sockaddr;
    ai_canonname : string }

type getaddrinfo_option =
    AI_FAMILY de socket_domain
  | AI_SOCKTYPE de socket_type
  | AI_PROTOCOL de int
  | AI_NUMERICHOST
  | AI_CANONNAME
  | AI_PASSIVE

dehors getaddrinfo_system
  : string -> string -> getaddrinfo_option list -> addr_info list
  = "unix_getaddrinfo"

soit getaddrinfo_emulation node service opts =
  (* Parse options *)
  soit opt_socktype = ref None
  et opt_protocol = ref 0
  et opt_passive = ref faux dans
  List.iter
    (fonction AI_SOCKTYPE s -> opt_socktype := Some s
            | AI_PROTOCOL p -> opt_protocol := p
            | AI_PASSIVE -> opt_passive := vrai
            | _ -> ())
    opts;
  (* Determine socket types and port numbers *)
  soit get_port ty kind =
    si service = "" alors [ty, 0] sinon
      essaie
        [ty, int_of_string service]
      avec Failure _ ->
      essaie
        [ty, (getservbyname service kind).s_port]
      avec Not_found -> []
  dans
  soit ports =
    filtre !opt_socktype avec
    | None ->
        get_port SOCK_STREAM "tcp" @ get_port SOCK_DGRAM "udp"
    | Some SOCK_STREAM ->
        get_port SOCK_STREAM "tcp"
    | Some SOCK_DGRAM ->
        get_port SOCK_DGRAM "udp"
    | Some ty ->
        si service = "" alors [ty, 0] sinon [] dans
  (* Determine IP addresses *)
  soit addresses =
    si node = "" alors
      si List.mem AI_PASSIVE opts
      alors [inet_addr_any, "0.0.0.0"]
      sinon [inet_addr_loopback, "127.0.0.1"]
    sinon
      essaie
        [inet_addr_of_string node, node]
      avec Failure _ ->
      essaie
        soit he = gethostbyname node dans
        List.map
          (fonc a -> (a, he.h_name))
          (Array.to_list he.h_addr_list)
      avec Not_found ->
        [] dans
  (* Cross-product of addresses and ports *)
  List.flatten
    (List.map
      (fonc (ty, port) ->
        List.map
          (fonc (addr, name) ->
            { ai_family = PF_INET;
              ai_socktype = ty;
              ai_protocol = !opt_protocol;
              ai_addr = ADDR_INET(addr, port);
              ai_canonname = name })
          addresses)
      ports)

soit getaddrinfo node service opts =
  essaie
    List.rev(getaddrinfo_system node service opts)
  avec Invalid_argument _ ->
    getaddrinfo_emulation node service opts

type name_info =
  { ni_hostname : string;
    ni_service : string }

type getnameinfo_option =
    NI_NOFQDN
  | NI_NUMERICHOST
  | NI_NAMEREQD
  | NI_NUMERICSERV
  | NI_DGRAM

dehors getnameinfo_system
  : sockaddr -> getnameinfo_option list -> name_info
  = "unix_getnameinfo"

soit getnameinfo_emulation addr opts =
  filtre addr avec
  | ADDR_UNIX f ->
      { ni_hostname = ""; ni_service = f } (* why not? *)
  | ADDR_INET(a, p) ->
      soit hostname =
        essaie
          si List.mem NI_NUMERICHOST opts alors raise Not_found;
          (gethostbyaddr a).h_name
        avec Not_found ->
          si List.mem NI_NAMEREQD opts alors raise Not_found;
          string_of_inet_addr a dans
      soit service =
        essaie
          si List.mem NI_NUMERICSERV opts alors raise Not_found;
          soit kind = si List.mem NI_DGRAM opts alors "udp" sinon "tcp" dans
          (getservbyport p kind).s_name
        avec Not_found ->
          string_of_int p dans
      { ni_hostname = hostname; ni_service = service }

soit getnameinfo addr opts =
  essaie
    getnameinfo_system addr opts
  avec Invalid_argument _ ->
    getnameinfo_emulation addr opts

type terminal_io = {
    modifiable c_ignbrk: bool;
    modifiable c_brkint: bool;
    modifiable c_ignpar: bool;
    modifiable c_parmrk: bool;
    modifiable c_inpck: bool;
    modifiable c_istrip: bool;
    modifiable c_inlcr: bool;
    modifiable c_igncr: bool;
    modifiable c_icrnl: bool;
    modifiable c_ixon: bool;
    modifiable c_ixoff: bool;
    modifiable c_opost: bool;
    modifiable c_obaud: int;
    modifiable c_ibaud: int;
    modifiable c_csize: int;
    modifiable c_cstopb: int;
    modifiable c_cread: bool;
    modifiable c_parenb: bool;
    modifiable c_parodd: bool;
    modifiable c_hupcl: bool;
    modifiable c_clocal: bool;
    modifiable c_isig: bool;
    modifiable c_icanon: bool;
    modifiable c_noflsh: bool;
    modifiable c_echo: bool;
    modifiable c_echoe: bool;
    modifiable c_echok: bool;
    modifiable c_echonl: bool;
    modifiable c_vintr: char;
    modifiable c_vquit: char;
    modifiable c_verase: char;
    modifiable c_vkill: char;
    modifiable c_veof: char;
    modifiable c_veol: char;
    modifiable c_vmin: int;
    modifiable c_vtime: int;
    modifiable c_vstart: char;
    modifiable c_vstop: char
  }

dehors tcgetattr: file_descr -> terminal_io = "unix_tcgetattr"

type setattr_when = TCSANOW | TCSADRAIN | TCSAFLUSH

dehors tcsetattr: file_descr -> setattr_when -> terminal_io -> unit
               = "unix_tcsetattr"
dehors tcsendbreak: file_descr -> int -> unit = "unix_tcsendbreak"
dehors tcdrain: file_descr -> unit = "unix_tcdrain"

type flush_queue = TCIFLUSH | TCOFLUSH | TCIOFLUSH

dehors tcflush: file_descr -> flush_queue -> unit = "unix_tcflush"

type flow_action = TCOOFF | TCOON | TCIOFF | TCION

dehors tcflow: file_descr -> flow_action -> unit = "unix_tcflow"

dehors setsid : unit -> int = "unix_setsid"

(* High-level process management (system, popen) *)

soit rec waitpid_non_intr pid =
  essaie waitpid [] pid
  avec Unix_error (EINTR, _, _) -> waitpid_non_intr pid

soit system cmd =
  filtre fork() avec
     0 -> début essaie
            execv "/bin/sh" [| "/bin/sh"; "-c"; cmd |]
          avec _ ->
            exit 127
          fin
  | id -> snd(waitpid_non_intr id)

soit rec safe_dup fd =
  soit new_fd = dup fd dans
  si new_fd >= 3 alors
    new_fd
  sinon début
    soit res = safe_dup fd dans
    close new_fd;
    res
  fin

soit safe_close fd =
  essaie close fd avec Unix_error(_,_,_) -> ()

soit perform_redirections new_stdin new_stdout new_stderr =
  soit newnewstdin = safe_dup new_stdin dans
  soit newnewstdout = safe_dup new_stdout dans
  soit newnewstderr = safe_dup new_stderr dans
  safe_close new_stdin;
  safe_close new_stdout;
  safe_close new_stderr;
  dup2 newnewstdin stdin; close newnewstdin;
  dup2 newnewstdout stdout; close newnewstdout;
  dup2 newnewstderr stderr; close newnewstderr

soit create_process cmd args new_stdin new_stdout new_stderr =
  filtre fork() avec
    0 ->
      début essaie
        perform_redirections new_stdin new_stdout new_stderr;
        execvp cmd args
      avec _ ->
        exit 127
      fin
  | id -> id

soit create_process_env cmd args env new_stdin new_stdout new_stderr =
  filtre fork() avec
    0 ->
      début essaie
        perform_redirections new_stdin new_stdout new_stderr;
        execvpe cmd args env
      avec _ ->
        exit 127
      fin
  | id -> id

type popen_process =
    Process de in_channel * out_channel
  | Process_in de in_channel
  | Process_out de out_channel
  | Process_full de in_channel * out_channel * in_channel

soit popen_processes = (Hashtbl.create 7 : (popen_process, int) Hashtbl.t)

soit open_proc cmd proc input output toclose =
  soit cloexec = List.for_all try_set_close_on_exec toclose dans
  filtre fork() avec
     0 -> si input <> stdin alors début dup2 input stdin; close input fin;
          si output <> stdout alors début dup2 output stdout; close output fin;
          si not cloexec alors List.iter close toclose;
          début essaie execv "/bin/sh" [| "/bin/sh"; "-c"; cmd |]
          avec _ -> exit 127
          fin
  | id -> Hashtbl.add popen_processes proc id

soit open_process_in cmd =
  soit (in_read, in_write) = pipe() dans
  soit inchan = in_channel_of_descr in_read dans
  début
    essaie
      open_proc cmd (Process_in inchan) stdin in_write [in_read];
    avec e ->
      close_in inchan;
      close in_write;
      raise e
  fin;
  close in_write;
  inchan

soit open_process_out cmd =
  soit (out_read, out_write) = pipe() dans
  soit outchan = out_channel_of_descr out_write dans
  début
    essaie
      open_proc cmd (Process_out outchan) out_read stdout [out_write];
    avec e ->
      close_out outchan;
      close out_read;
      raise e
  fin;
  close out_read;
  outchan

soit open_process cmd =
  soit (in_read, in_write) = pipe() dans
  soit fds_to_close = ref [in_read;in_write] dans
  essaie
    soit (out_read, out_write) = pipe() dans
    fds_to_close := [in_read;in_write;out_read;out_write];
    soit inchan = in_channel_of_descr in_read dans
    soit outchan = out_channel_of_descr out_write dans
    open_proc cmd (Process(inchan, outchan)) out_read in_write
                                           [in_read; out_write];
    close out_read;
    close in_write;
    (inchan, outchan)
  avec e ->
    List.iter close !fds_to_close;
    raise e

soit open_proc_full cmd env proc input output error toclose =
  soit cloexec = List.for_all try_set_close_on_exec toclose dans
  filtre fork() avec
     0 -> dup2 input stdin; close input;
          dup2 output stdout; close output;
          dup2 error stderr; close error;
          si not cloexec alors List.iter close toclose;
          début essaie execve "/bin/sh" [| "/bin/sh"; "-c"; cmd |] env
          avec _ -> exit 127
          fin
  | id -> Hashtbl.add popen_processes proc id

soit open_process_full cmd env =
  soit (in_read, in_write) = pipe() dans
  soit fds_to_close = ref [in_read;in_write] dans
  essaie
    soit (out_read, out_write) = pipe() dans
    fds_to_close := out_read::out_write:: !fds_to_close;
    soit (err_read, err_write) = pipe() dans
    fds_to_close := err_read::err_write:: !fds_to_close;
    soit inchan = in_channel_of_descr in_read dans
    soit outchan = out_channel_of_descr out_write dans
    soit errchan = in_channel_of_descr err_read dans
    open_proc_full cmd env (Process_full(inchan, outchan, errchan))
      out_read in_write err_write [in_read; out_write; err_read];
    close out_read;
    close in_write;
    close err_write;
    (inchan, outchan, errchan)
  avec e ->
    List.iter close !fds_to_close;
    raise e

soit find_proc_id fun_name proc =
  essaie
    soit pid = Hashtbl.find popen_processes proc dans
    Hashtbl.remove popen_processes proc;
    pid
  avec Not_found ->
    raise(Unix_error(EBADF, fun_name, ""))

soit close_process_in inchan =
  soit pid = find_proc_id "close_process_in" (Process_in inchan) dans
  close_in inchan;
  snd(waitpid_non_intr pid)

soit close_process_out outchan =
  soit pid = find_proc_id "close_process_out" (Process_out outchan) dans
  close_out outchan;
  snd(waitpid_non_intr pid)

soit close_process (inchan, outchan) =
  soit pid = find_proc_id "close_process" (Process(inchan, outchan)) dans
  close_in inchan;
  début essaie close_out outchan avec Sys_error _ -> () fin;
  snd(waitpid_non_intr pid)

soit close_process_full (inchan, outchan, errchan) =
  soit pid =
    find_proc_id "close_process_full"
                 (Process_full(inchan, outchan, errchan)) dans
  close_in inchan;
  début essaie close_out outchan avec Sys_error _ -> () fin;
  close_in errchan;
  snd(waitpid_non_intr pid)

(* High-level network functions *)

soit open_connection sockaddr =
  soit sock =
    socket (domain_of_sockaddr sockaddr) SOCK_STREAM 0 dans
  essaie
    connect sock sockaddr;
    ignore(try_set_close_on_exec sock);
    (in_channel_of_descr sock, out_channel_of_descr sock)
  avec exn ->
    close sock; raise exn

soit shutdown_connection inchan =
  shutdown (descr_of_in_channel inchan) SHUTDOWN_SEND

soit rec accept_non_intr s =
  essaie accept s
  avec Unix_error (EINTR, _, _) -> accept_non_intr s

soit establish_server server_fun sockaddr =
  soit sock =
    socket (domain_of_sockaddr sockaddr) SOCK_STREAM 0 dans
  setsockopt sock SO_REUSEADDR vrai;
  bind sock sockaddr;
  listen sock 5;
  pendant_que vrai faire
    soit (s, caller) = accept_non_intr sock dans
    (* The "double fork" trick, the process which calls server_fun will not
       leave a zombie process *)
    filtre fork() avec
       0 -> si fork() <> 0 alors exit 0; (* The son exits, the grandson works *)
            close sock;
            ignore(try_set_close_on_exec s);
            soit inchan = in_channel_of_descr s dans
            soit outchan = out_channel_of_descr s dans
            server_fun inchan outchan;
            (* Do not close inchan nor outchan, as the server_fun could
               have done it already, and we are about to exit anyway
               (PR#3794) *)
            exit 0
    | id -> close s; ignore(waitpid_non_intr id) (* Reclaim the son *)
  fait
