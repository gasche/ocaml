(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2002 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* Complex numbers *)

type t = { re: float; im: float }

soit zero = { re = 0.0; im = 0.0 }
soit one = { re = 1.0; im = 0.0 }
soit i = { re = 0.0; im = 1.0 }

soit add x y = { re = x.re +. y.re; im = x.im +. y.im }

soit sub x y = { re = x.re -. y.re; im = x.im -. y.im }

soit neg x = { re = -. x.re; im = -. x.im }

soit conj x = { re = x.re; im = -. x.im }

soit mul x y = { re = x.re *. y.re -. x.im *. y.im;
                im = x.re *. y.im +. x.im *. y.re }

soit div x y =
  si abs_float y.re >= abs_float y.im alors
    soit r = y.im /. y.re dans
    soit d = y.re +. r *. y.im dans
    { re = (x.re +. r *. x.im) /. d;
      im = (x.im -. r *. x.re) /. d }
  sinon
    soit r = y.re /. y.im dans
    soit d = y.im +. r *. y.re dans
    { re = (r *. x.re +. x.im) /. d;
      im = (r *. x.im -. x.re) /. d }

soit inv x = div one x

soit norm2 x = x.re *. x.re +. x.im *. x.im

soit norm x =
  (* Watch out for overflow in computing re^2 + im^2 *)
  soit r = abs_float x.re et i = abs_float x.im dans
  si r = 0.0 alors i
  sinon si i = 0.0 alors r
  sinon si r >= i alors
    soit q = i /. r dans r *. sqrt(1.0 +. q *. q)
  sinon
    soit q = r /. i dans i *. sqrt(1.0 +. q *. q)

soit arg x = atan2 x.im x.re

soit polar n a = { re = cos a *. n; im = sin a *. n }

soit sqrt x =
  si x.re = 0.0 && x.im = 0.0 alors { re = 0.0; im = 0.0 }
  sinon début
    soit r = abs_float x.re et i = abs_float x.im dans
    soit w =
      si r >= i alors début
        soit q = i /. r dans
        sqrt(r) *. sqrt(0.5 *. (1.0 +. sqrt(1.0 +. q *. q)))
      fin sinon début
        soit q = r /. i dans
        sqrt(i) *. sqrt(0.5 *. (q +. sqrt(1.0 +. q *. q)))
      fin dans
    si x.re >= 0.0
    alors { re = w;  im = 0.5 *. x.im /. w }
    sinon { re = 0.5 *. i /. w;  im = si x.im >= 0.0 alors w sinon -. w }
  fin

soit exp x =
  soit e = exp x.re dans { re = e *. cos x.im; im = e *. sin x.im }

soit log x = { re = log (norm x); im = atan2 x.im x.re }

soit pow x y = exp (mul y (log x))
