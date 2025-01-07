/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*          Xavier Leroy and Damien Doligez, INRIA Rocquencourt           */
/*                                                                        */
/*   Copyright 1996 Institut National de Recherche en Informatique et     */
/*     en Automatique.                                                    */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

/* Operations on mutexes from the OCaml stdlib */

#ifndef CAML_SYNC_H
#define CAML_SYNC_H

#ifdef CAML_INTERNALS

#include "mlvalues.h"
#include "platform.h"

/* The mutexes defined in this file are lower-ranked than the domain
   mutex: if the [_lock] functions need to block to take them,
   they will release the domain lock to do so (if it is held).

   Conversely, it is safe to release the domain lock and perform
   other runtime effects within their critical section. The
   functions will themselves raise on failure -- fatal errors for
   caml_mutex_* and proper exceptions for caml_ml_*.
 */

typedef caml_plat_mutex * sync_mutex;
typedef caml_plat_cond * sync_condvar;

#define Mutex_val(v) (* ((sync_mutex *) Data_custom_val(v)))
#define Condition_val(v) (* (sync_condvar *) Data_custom_val(v))

CAMLextern void caml_mutex_init(sync_mutex *mut);
CAMLextern void caml_mutex_free(sync_mutex *mut);

CAMLextern void caml_mutex_lock_non_blocking(sync_mutex mut);
CAMLextern void caml_mutex_unlock(sync_mutex mut);

value caml_ml_mutex_lock(value wrapper);
value caml_ml_mutex_unlock(value wrapper);
value caml_ml_condition_broadcast(value wrapper);

#endif /* CAML_INTERNALS */

#endif /* CAML_SYNC_H */
