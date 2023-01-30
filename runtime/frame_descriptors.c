/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*      KC Sivaramakrishnan, Indian Institute of Technology, Madras       */
/*                   Tom Kelly, OCaml Labs Consultancy                    */
/*                 Stephen Dolan, University of Cambridge                 */
/*                                                                        */
/*   Copyright 2019 Indian Institute of Technology, Madras                */
/*   Copyright 2021 OCaml Labs Consultancy Ltd                            */
/*   Copyright 2019 University of Cambridge                               */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

#define CAML_INTERNALS

#include "caml/platform.h"
#include "caml/frame_descriptors.h"
#include "caml/major_gc.h" /* for caml_major_cycles_completed */
#include "caml/memory.h"
#include "caml/fail.h"
#include "caml/shared_heap.h"
#include <stddef.h>

/* Defined in code generated by ocamlopt */
extern intnat * caml_frametable[];

/* Note: [cur] is bound by this macro */
#define iter_list(list,cur) \
  for (caml_frametable_list *cur = list; cur != NULL; cur = cur->next)

static frame_descr * next_frame_descr(frame_descr * d) {
  unsigned char num_allocs = 0, *p;
  CAMLassert(d->retaddr >= 4096);
  if (d->frame_size != 0xFFFF) {
    /* Skip to end of live_ofs */
    p = (unsigned char*)&d->live_ofs[d->num_live];
    /* Skip alloc_lengths if present */
    if (d->frame_size & 2) {
      num_allocs = *p;
      p += num_allocs + 1;
    }
    /* Skip debug info if present */
    if (d->frame_size & 1) {
      /* Align to 32 bits */
      p = Align_to(p, uint32_t);
      p += sizeof(uint32_t) * (d->frame_size & 2 ? num_allocs : 1);
    }
    /* Align to word size */
    p = Align_to(p, void*);
    return ((frame_descr*) p);
  } else {
    /* This marks the top of an ML stack chunk. Skip over empty
     * frame descriptor */
    /* Skip to address of zero-sized live_ofs */
    CAMLassert(d->num_live == 0);
    p = (unsigned char*)&d->live_ofs[0];
    /* Align to word size */
    p = Align_to(p, void*);
    return ((frame_descr*) p);
  }
}

static intnat count_descriptors(caml_frametable_list *list) {
  intnat num_descr = 0;
  iter_list(list,cur) {
    num_descr += *((intnat*) cur->frametable);
  }
  return num_descr;
}

static caml_frametable_list* frametables_list_tail(caml_frametable_list *list) {
  caml_frametable_list *tail = NULL;
  iter_list(list,cur) {
    tail = cur;
  }
  return tail;
}

static int capacity(caml_frame_descrs table) {
  int capacity = table.mask + 1;
  CAMLassert(capacity == 0 || Is_power_of_2(capacity));
  return capacity;
}

static void fill_hashtable(
  caml_frame_descrs *table, caml_frametable_list *new_frametables)
{
  iter_list(new_frametables,cur) {
    intnat * tbl = (intnat*) cur->frametable;
    intnat len = *tbl;
    frame_descr * d = (frame_descr *)(tbl + 1);
    for (intnat j = 0; j < len; j++) {
      uintnat h = Hash_retaddr(d->retaddr, table->mask);
      while (table->descriptors[h] != NULL) {
        h = (h+1) & table->mask;
      }
      table->descriptors[h] = d;
      d = next_frame_descr(d);
    }
  }
}

static void add_frame_descriptors(
  caml_frame_descrs *table,
  caml_frametable_list *new_frametables)
{
  CAMLassert(new_frametables != NULL);

  caml_frametable_list *tail = frametables_list_tail(new_frametables);
  intnat increase = count_descriptors(new_frametables);
  intnat tblsize = capacity(*table);

  /* The size of the hashtable is a power of 2 that must remain
     greater or equal to 2 times the number of descriptors. */

  /* Reallocate the caml_frame_descriptor table if it is too small */
  if(tblsize < (table->num_descr + increase) * 2) {

    /* Merge both lists */
    tail->next = table->frametables;
    table->frametables = NULL;

    /* [num_descr] can be less than [num_descr + increase] if frame
       tables were unregistered */
    intnat num_descr = count_descriptors(new_frametables);

    tblsize = 4;
    while (tblsize < 2 * num_descr) tblsize *= 2;

    table->num_descr = num_descr;
    table->mask = tblsize - 1;

    if (table->descriptors != NULL) caml_stat_free(table->descriptors);
    table->descriptors =
      (frame_descr **) caml_stat_calloc_noexc(tblsize, sizeof(frame_descr *));
    if (table->descriptors == NULL) caml_raise_out_of_memory();

    fill_hashtable(table, new_frametables);
  } else {
    table->num_descr += increase;
    fill_hashtable(table, new_frametables);
    tail->next = table->frametables;
  }

  table->frametables = new_frametables;
}

/* protected by STW sections */
static caml_frame_descrs current_frame_descrs = { 0, -1, NULL, NULL };

static caml_frametable_list *cons(
  intnat *frametable, caml_frametable_list *tl)
{
  caml_frametable_list *li = caml_stat_alloc(sizeof(caml_frametable_list));
  li->frametable = frametable;
  li->next = tl;
  return li;
}

void caml_init_frame_descriptors(void)
{
  caml_frametable_list *frametables = NULL;
  for (int i = 0; caml_frametable[i] != 0; i++)
    frametables = cons(caml_frametable[i], frametables);

  /* `init_frame_descriptors` is called from `init_gc`, before
     any mutator can run. We can mutate [current_frame_descrs]
     at will. */
  add_frame_descriptors(&current_frame_descrs, frametables);
}


typedef struct frametable_array {
  void **table;
  int ntables;
} frametable_array;

static void register_frametables(frametable_array *array)
{
  caml_frametable_list *new_frametables = NULL;
  for (int i = 0; i < array->ntables; i++)
    new_frametables = cons((intnat*)array->table[i], new_frametables);

  add_frame_descriptors(&current_frame_descrs, new_frametables);
}

static void stw_register_frametables(
    caml_domain_state* domain,
    void* frametables,
    int participating_count,
    caml_domain_state** participating)
{
  barrier_status b = caml_global_barrier_begin ();

  if (caml_global_barrier_is_final(b)) {
    register_frametables((frametable_array*) frametables);
  }

  caml_global_barrier_end(b);
}

void caml_register_frametables(void **table, int ntables) {
  struct frametable_array frametables = { table, ntables };
  do {} while (!caml_try_run_on_all_domains(
                 &stw_register_frametables, &frametables, 0));
}

caml_frame_descrs caml_get_frame_descrs(void)
{
  return current_frame_descrs;
}

frame_descr* caml_find_frame_descr(caml_frame_descrs fds, uintnat pc)
{
  frame_descr * d;
  uintnat h;

  h = Hash_retaddr(pc, fds.mask);
  while (1) {
    d = fds.descriptors[h];
    if (d == 0) return NULL; /* can happen if some code compiled without -g */
    if (d->retaddr == pc) break;
    h = (h+1) & fds.mask;
  }
  return d;
}
