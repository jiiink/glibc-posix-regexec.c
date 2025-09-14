/* Extended regular expression matching and search library.
   Copyright (C) 2002-2025 Free Software Foundation, Inc.
   This file is part of the GNU C Library.
   Contributed by Isamu Hasegawa <isamu@yamato.ibm.com>.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <https://www.gnu.org/licenses/>.  */

static reg_errcode_t match_ctx_init (re_match_context_t *cache, int eflags,
				     Idx n);
static void match_ctx_clean (re_match_context_t *mctx);
static void match_ctx_free (re_match_context_t *cache);
static reg_errcode_t match_ctx_add_entry (re_match_context_t *cache, Idx node,
					  Idx str_idx, Idx from, Idx to);
static Idx search_cur_bkref_entry (const re_match_context_t *mctx, Idx str_idx);
static reg_errcode_t match_ctx_add_subtop (re_match_context_t *mctx, Idx node,
					   Idx str_idx);
static re_sub_match_last_t * match_ctx_add_sublast (re_sub_match_top_t *subtop,
						    Idx node, Idx str_idx);
static void sift_ctx_init (re_sift_context_t *sctx, re_dfastate_t **sifted_sts,
			   re_dfastate_t **limited_sts, Idx last_node,
			   Idx last_str_idx);
static reg_errcode_t re_search_internal (const regex_t *preg,
					 const char *string, Idx length,
					 Idx start, Idx last_start, Idx stop,
					 size_t nmatch, regmatch_t pmatch[],
					 int eflags);
static regoff_t re_search_2_stub (struct re_pattern_buffer *bufp,
				  const char *string1, Idx length1,
				  const char *string2, Idx length2,
				  Idx start, regoff_t range,
				  struct re_registers *regs,
				  Idx stop, bool ret_len);
static regoff_t re_search_stub (struct re_pattern_buffer *bufp,
				const char *string, Idx length, Idx start,
				regoff_t range, Idx stop,
				struct re_registers *regs,
				bool ret_len);
static unsigned re_copy_regs (struct re_registers *regs, regmatch_t *pmatch,
                              Idx nregs, int regs_allocated);
static reg_errcode_t prune_impossible_nodes (re_match_context_t *mctx);
static Idx check_matching (re_match_context_t *mctx, bool fl_longest_match,
			   Idx *p_match_first);
static Idx check_halt_state_context (const re_match_context_t *mctx,
				     const re_dfastate_t *state, Idx idx);
static void update_regs (const re_dfa_t *dfa, regmatch_t *pmatch,
			 regmatch_t *prev_idx_match, Idx cur_node,
			 Idx cur_idx, Idx nmatch);
static reg_errcode_t push_fail_stack (struct re_fail_stack_t *fs,
				      Idx str_idx, Idx dest_node, Idx nregs,
				      regmatch_t *regs, regmatch_t *prevregs,
				      re_node_set *eps_via_nodes);
static reg_errcode_t set_regs (const regex_t *preg,
			       const re_match_context_t *mctx,
			       size_t nmatch, regmatch_t *pmatch,
			       bool fl_backtrack);
static reg_errcode_t free_fail_stack_return (struct re_fail_stack_t *fs);

#ifdef RE_ENABLE_I18N
static int sift_states_iter_mb (const re_match_context_t *mctx,
				re_sift_context_t *sctx,
				Idx node_idx, Idx str_idx, Idx max_str_idx);
#endif /* RE_ENABLE_I18N */
static reg_errcode_t sift_states_backward (const re_match_context_t *mctx,
					   re_sift_context_t *sctx);
static reg_errcode_t build_sifted_states (const re_match_context_t *mctx,
					  re_sift_context_t *sctx, Idx str_idx,
					  re_node_set *cur_dest);
static reg_errcode_t update_cur_sifted_state (const re_match_context_t *mctx,
					      re_sift_context_t *sctx,
					      Idx str_idx,
					      re_node_set *dest_nodes);
static reg_errcode_t add_epsilon_src_nodes (const re_dfa_t *dfa,
					    re_node_set *dest_nodes,
					    const re_node_set *candidates);
static bool check_dst_limits (const re_match_context_t *mctx,
			      const re_node_set *limits,
			      Idx dst_node, Idx dst_idx, Idx src_node,
			      Idx src_idx);
static int check_dst_limits_calc_pos_1 (const re_match_context_t *mctx,
					int boundaries, Idx subexp_idx,
					Idx from_node, Idx bkref_idx);
static int check_dst_limits_calc_pos (const re_match_context_t *mctx,
				      Idx limit, Idx subexp_idx,
				      Idx node, Idx str_idx,
				      Idx bkref_idx);
static reg_errcode_t check_subexp_limits (const re_dfa_t *dfa,
					  re_node_set *dest_nodes,
					  const re_node_set *candidates,
					  re_node_set *limits,
					  struct re_backref_cache_entry *bkref_ents,
					  Idx str_idx);
static reg_errcode_t sift_states_bkref (const re_match_context_t *mctx,
					re_sift_context_t *sctx,
					Idx str_idx, const re_node_set *candidates);
static reg_errcode_t merge_state_array (const re_dfa_t *dfa,
					re_dfastate_t **dst,
					re_dfastate_t **src, Idx num);
static re_dfastate_t *find_recover_state (reg_errcode_t *err,
					 re_match_context_t *mctx);
static re_dfastate_t *transit_state (reg_errcode_t *err,
				     re_match_context_t *mctx,
				     re_dfastate_t *state);
static re_dfastate_t *merge_state_with_log (reg_errcode_t *err,
					    re_match_context_t *mctx,
					    re_dfastate_t *next_state);
static reg_errcode_t check_subexp_matching_top (re_match_context_t *mctx,
						re_node_set *cur_nodes,
						Idx str_idx);
#if 0
static re_dfastate_t *transit_state_sb (reg_errcode_t *err,
					re_match_context_t *mctx,
					re_dfastate_t *pstate);
#endif
#ifdef RE_ENABLE_I18N
static reg_errcode_t transit_state_mb (re_match_context_t *mctx,
				       re_dfastate_t *pstate);
#endif /* RE_ENABLE_I18N */
static reg_errcode_t transit_state_bkref (re_match_context_t *mctx,
					  const re_node_set *nodes);
static reg_errcode_t get_subexp (re_match_context_t *mctx,
				 Idx bkref_node, Idx bkref_str_idx);
static reg_errcode_t get_subexp_sub (re_match_context_t *mctx,
				     const re_sub_match_top_t *sub_top,
				     re_sub_match_last_t *sub_last,
				     Idx bkref_node, Idx bkref_str);
static Idx find_subexp_node (const re_dfa_t *dfa, const re_node_set *nodes,
			     Idx subexp_idx, int type);
static reg_errcode_t check_arrival (re_match_context_t *mctx,
				    state_array_t *path, Idx top_node,
				    Idx top_str, Idx last_node, Idx last_str,
				    int type);
static reg_errcode_t check_arrival_add_next_nodes (re_match_context_t *mctx,
						   Idx str_idx,
						   re_node_set *cur_nodes,
						   re_node_set *next_nodes);
static reg_errcode_t check_arrival_expand_ecl (const re_dfa_t *dfa,
					       re_node_set *cur_nodes,
					       Idx ex_subexp, int type);
static reg_errcode_t check_arrival_expand_ecl_sub (const re_dfa_t *dfa,
						   re_node_set *dst_nodes,
						   Idx target, Idx ex_subexp,
						   int type);
static reg_errcode_t expand_bkref_cache (re_match_context_t *mctx,
					 re_node_set *cur_nodes, Idx cur_str,
					 Idx subexp_num, int type);
static bool build_trtable (const re_dfa_t *dfa, re_dfastate_t *state);
#ifdef RE_ENABLE_I18N
static int check_node_accept_bytes (const re_dfa_t *dfa, Idx node_idx,
				    const re_string_t *input, Idx idx);
# ifdef _LIBC
static unsigned int find_collation_sequence_value (const unsigned char *mbs,
						   size_t name_len);
# endif /* _LIBC */
#endif /* RE_ENABLE_I18N */
static Idx group_nodes_into_DFAstates (const re_dfa_t *dfa,
				       const re_dfastate_t *state,
				       re_node_set *states_node,
				       bitset_t *states_ch);
static bool check_node_accept (const re_match_context_t *mctx,
			       const re_token_t *node, Idx idx);
static reg_errcode_t extend_buffers (re_match_context_t *mctx, int min_len);

/* Entry point for POSIX code.  */

/* regexec searches for a given pattern, specified by PREG, in the
   string STRING.

   If NMATCH is zero or REG_NOSUB was set in the cflags argument to
   'regcomp', we ignore PMATCH.  Otherwise, we assume PMATCH has at
   least NMATCH elements, and we set them to the offsets of the
   corresponding matched substrings.

   EFLAGS specifies "execution flags" which affect matching: if
   REG_NOTBOL is set, then ^ does not match at the beginning of the
   string; if REG_NOTEOL is set, then $ does not match at the end.

   Return 0 if a match is found, REG_NOMATCH if not, REG_BADPAT if
   EFLAGS is invalid.  */

#include <string.h>

int
regexec (const regex_t *__restrict preg, const char *__restrict string,
	 size_t nmatch, regmatch_t pmatch[_REGEX_NELTS (nmatch)], int eflags)
{
  reg_errcode_t err;
  Idx search_start_offset;
  Idx effective_string_len_for_search;
  re_dfa_t *dfa = NULL;

  if (preg == NULL || string == NULL)
    return REG_BADPAT;

  if (preg->buffer == NULL)
    return REG_BADPAT;

  dfa = preg->buffer;

  if (eflags & ~(REG_NOTBOL | REG_NOTEOL | REG_STARTEND))
    return REG_BADPAT;

  if (eflags & REG_STARTEND)
    {
      if (pmatch == NULL)
        return REG_BADPAT;

      search_start_offset = pmatch[0].rm_so;
      effective_string_len_for_search = pmatch[0].rm_eo;

      if (search_start_offset < 0 || effective_string_len_for_search < 0 ||
          search_start_offset > effective_string_len_for_search)
        return REG_BADPAT;
    }
  else
    {
      search_start_offset = 0;
      effective_string_len_for_search = (Idx)strlen(string);
    }

  if (!preg->no_sub && nmatch > 0 && pmatch == NULL)
    return REG_BADPAT;

  lock_lock (dfa->lock);

  if (preg->no_sub)
    err = re_search_internal (preg, string, effective_string_len_for_search,
                              search_start_offset, effective_string_len_for_search,
                              effective_string_len_for_search, 0, NULL, eflags);
  else
    err = re_search_internal (preg, string, effective_string_len_for_search,
                              search_start_offset, effective_string_len_for_search,
                              effective_string_len_for_search, nmatch, pmatch, eflags);

  lock_unlock (dfa->lock);

  return err != REG_NOERROR;
}

#ifdef _LIBC
libc_hidden_def (__regexec)

# include <shlib-compat.h>
versioned_symbol (libc, __regexec, regexec, GLIBC_2_3_4);

# if SHLIB_COMPAT (libc, GLIBC_2_0, GLIBC_2_3_4)
__typeof__ (__regexec) __compat_regexec;

int
attribute_compat_text_section
__compat_regexec (const regex_t *__restrict preg,
		  const char *__restrict string, size_t nmatch,
		  regmatch_t pmatch[_REGEX_NELTS (nmatch)], int eflags)
{
  return regexec (preg, string, nmatch, pmatch,
		  eflags & (REG_NOTBOL | REG_NOTEOL));
}
compat_symbol (libc, __compat_regexec, regexec, GLIBC_2_0);
# endif
#endif

/* Entry points for GNU code.  */

/* re_match, re_search, re_match_2, re_search_2

   The former two functions operate on STRING with length LENGTH,
   while the later two operate on concatenation of STRING1 and STRING2
   with lengths LENGTH1 and LENGTH2, respectively.

   re_match() matches the compiled pattern in BUFP against the string,
   starting at index START.

   re_search() first tries matching at index START, then it tries to match
   starting from index START + 1, and so on.  The last start position tried
   is START + RANGE.  (Thus RANGE = 0 forces re_search to operate the same
   way as re_match().)

   The parameter STOP of re_{match,search}_2 specifies that no match exceeding
   the first STOP characters of the concatenation of the strings should be
   concerned.

   If REGS is not NULL, and BUFP->no_sub is not set, the offsets of the match
   and all groups is stored in REGS.  (For the "_2" variants, the offsets are
   computed relative to the concatenation, not relative to the individual
   strings.)

   On success, re_match* functions return the length of the match, re_search*
   return the position of the start of the match.  They return -1 on
   match failure, -2 on error.  */

regoff_t re_match(struct re_pattern_buffer *bufp,
                  const char *string,
                  Idx length,
                  Idx start,
                  struct re_registers *regs)
{
    return re_search_stub(bufp, string, length, start, 0, length, regs, true);
}
#ifdef _LIBC
weak_alias (__re_match, re_match)
#endif

regoff_t
re_search (struct re_pattern_buffer *bufp, const char *string, Idx length,
	   Idx start, regoff_t range, struct re_registers *regs)
{
  Idx stub_stop_position = length;
  int stub_drop_on_error = 0; /* Represents 'false' for boolean flag */

  return re_search_stub (bufp, string, length, start, range, stub_stop_position, regs,
			 stub_drop_on_error);
}
#ifdef _LIBC
weak_alias (__re_search, re_search)
#endif

regoff_t
re_match_2 (struct re_pattern_buffer *bufp, const char *string1, Idx length1,
	    const char *string2, Idx length2, Idx start,
	    struct re_registers *regs, Idx stop)
{
  return re_search_2_stub (bufp, string1, length1, string2, length2,
			   start, 0, regs, stop, 1);
}
#ifdef _LIBC
weak_alias (__re_match_2, re_match_2)
#endif

regoff_t
re_search_2 (struct re_pattern_buffer *bufp, const char *string1, Idx length1,
	     const char *string2, Idx length2, Idx start, regoff_t range,
	     struct re_registers *regs, Idx stop)
{
  if (bufp == NULL || regs == NULL)
    {
      return -1;
    }

  return re_search_2_stub (bufp, string1, length1, string2, length2,
			   start, range, regs, stop, 0);
}
#ifdef _LIBC
weak_alias (__re_search_2, re_search_2)
#endif

static regoff_t
re_search_2_stub (struct re_pattern_buffer *bufp, const char *string1,
		  Idx length1, const char *string2, Idx length2, Idx start,
		  regoff_t range, struct re_registers *regs,
		  Idx stop, bool ret_len)
{
  const char *str_to_search;
  regoff_t rval;
  Idx total_len;
  char *temp_concat_buf = NULL;

  if (__glibc_unlikely (length1 < 0 || length2 < 0 || stop < 0
			 || INT_ADD_WRAPV (length1, length2, &total_len)))
    return -2;

  if (length1 == 0)
    {
      str_to_search = string2;
    }
  else if (length2 == 0)
    {
      str_to_search = string1;
    }
  else /* Both length1 > 0 and length2 > 0, concatenation required. */
    {
      temp_concat_buf = re_malloc (char, total_len);

      if (__glibc_unlikely (temp_concat_buf == NULL))
	return -2;

#ifdef _LIBC
      memcpy (__mempcpy (temp_concat_buf, string1, length1), string2, length2);
#else
      memcpy (temp_concat_buf, string1, length1);
      memcpy (temp_concat_buf + length1, string2, length2);
#endif
      str_to_search = temp_concat_buf;
    }

  rval = re_search_stub (bufp, str_to_search, total_len, start, range, stop, regs,
			 ret_len);

  re_free (temp_concat_buf);
  return rval;
}

/* The parameters have the same meaning as those of re_search.
   Additional parameters:
   If RET_LEN is true the length of the match is returned (re_match style);
   otherwise the position of the match is returned.  */

static regoff_t
re_search_stub (struct re_pattern_buffer *bufp, const char *string, Idx length,
		Idx start, regoff_t range, Idx stop, struct re_registers *regs,
		bool ret_len)
{
  reg_errcode_t result;
  regmatch_t *pmatch = NULL;
  Idx effective_nregs;
  regoff_t rval = -2;
  int eflags = 0;
  re_dfa_t *dfa = NULL;

  if (__glibc_unlikely (bufp == NULL))
    return -2;

  dfa = (re_dfa_t *)bufp->buffer;
  if (__glibc_unlikely (dfa == NULL || dfa->lock == NULL))
    return -2;

  if (__glibc_unlikely (start < 0 || start > length))
    return -1;

  regoff_t search_range_end_candidate;
  if (range >= 0)
    {
      if ((regoff_t)length - start < range)
        search_range_end_candidate = length;
      else
        search_range_end_candidate = start + range;
    }
  else
    {
      if (start < -(regoff_t)range)
        search_range_end_candidate = 0;
      else
        search_range_end_candidate = start + range;
    }

  lock_lock (dfa->lock);

  eflags |= (bufp->not_bol) ? REG_NOTBOL : 0;
  eflags |= (bufp->not_eol) ? REG_NOTEOL : 0;

  if (start != search_range_end_candidate && bufp->fastmap != NULL && !bufp->fastmap_accurate)
    re_compile_fastmap (bufp);

  struct re_registers *actual_regs = regs;
  if (bufp->no_sub)
    actual_regs = NULL;

  if (actual_regs == NULL)
    {
      effective_nregs = 1;
    }
  else
    {
      if (__glibc_unlikely (bufp->regs_allocated == REGS_FIXED && actual_regs->num_regs <= bufp->re_nsub))
        {
          effective_nregs = actual_regs->num_regs;
          if (__glibc_unlikely (effective_nregs < 1))
            {
              effective_nregs = 1;
              actual_regs = NULL;
            }
        }
      else
        {
          effective_nregs = bufp->re_nsub + 1;
        }
    }

  pmatch = re_malloc (regmatch_t, effective_nregs);
  if (__glibc_unlikely (pmatch == NULL))
    goto cleanup_and_exit;

  result = re_search_internal (bufp, string, length, start, search_range_end_candidate, stop,
			       effective_nregs, pmatch, eflags);

  if (result != REG_NOERROR)
    {
      rval = (result == REG_NOMATCH) ? -1 : -2;
    }
  else
    {
      rval = 0;

      if (actual_regs != NULL)
        {
          bufp->regs_allocated = re_copy_regs (actual_regs, pmatch, effective_nregs,
                                               bufp->regs_allocated);
          if (__glibc_unlikely (bufp->regs_allocated == REGS_UNALLOCATED))
            rval = -2;
        }

      if (__glibc_likely (rval == 0))
        {
          if (ret_len)
            rval = pmatch[0].rm_eo - pmatch[0].rm_so;
          else
            rval = pmatch[0].rm_so;
        }
    }

cleanup_and_exit:
  re_free (pmatch);
  lock_unlock (dfa->lock);
  return rval;
}

static unsigned
re_allocate_initial(struct re_registers *regs, Idx need_regs)
{
  regs->start = re_malloc(regoff_t, need_regs);
  if (__glibc_unlikely(regs->start == NULL))
    return REGS_UNALLOCATED;

  regs->end = re_malloc(regoff_t, need_regs);
  if (__glibc_unlikely(regs->end == NULL))
    {
      re_free(regs->start);
      return REGS_UNALLOCATED;
    }
  regs->num_regs = need_regs;
  return REGS_REALLOCATE;
}

static unsigned
re_reallocate_conditional(struct re_registers *regs, Idx need_regs)
{
  if (__glibc_unlikely(need_regs > regs->num_regs))
    {
      regoff_t *new_start = re_realloc(regs->start, regoff_t, need_regs);
      if (__glibc_unlikely(new_start == NULL))
        return REGS_UNALLOCATED;

      regoff_t *new_end = re_realloc(regs->end, regoff_t, need_regs);
      if (__glibc_unlikely(new_end == NULL))
        {
          re_free(new_start);
          return REGS_UNALLOCATED;
        }

      regs->start = new_start;
      regs->end = new_end;
      regs->num_regs = need_regs;
    }
  return REGS_REALLOCATE;
}

static unsigned
re_copy_regs (struct re_registers *regs, regmatch_t *pmatch, Idx nregs,
	      int regs_allocated)
{
  Idx need_regs = nregs + 1;
  unsigned rval;

  if (regs_allocated == REGS_UNALLOCATED)
    {
      rval = re_allocate_initial(regs, need_regs);
      if (__glibc_unlikely(rval == REGS_UNALLOCATED))
        return rval;
    }
  else if (regs_allocated == REGS_REALLOCATE)
    {
      rval = re_reallocate_conditional(regs, need_regs);
      if (__glibc_unlikely(rval == REGS_UNALLOCATED))
        return rval;
    }
  else /* regs_allocated == REGS_FIXED */
    {
      DEBUG_ASSERT (regs_allocated == REGS_FIXED);
      DEBUG_ASSERT (nregs <= regs->num_regs);
      rval = REGS_FIXED;
    }

  Idx i;
  for (i = 0; i < nregs; ++i)
    {
      regs->start[i] = pmatch[i].rm_so;
      regs->end[i] = pmatch[i].rm_eo;
    }
  for ( ; i < regs->num_regs; ++i)
    regs->start[i] = regs->end[i] = -1;

  return rval;
}

/* Set REGS to hold NUM_REGS registers, storing them in STARTS and
   ENDS.  Subsequent matches using PATTERN_BUFFER and REGS will use
   this memory for recording register information.  STARTS and ENDS
   must be allocated using the malloc library routine, and must each
   be at least NUM_REGS * sizeof (regoff_t) bytes long.

   If NUM_REGS == 0, then subsequent matches should allocate their own
   register data.

   Unless this function is called, the first search or match using
   PATTERN_BUFFER will allocate its own register data, without
   freeing the old data.  */

void
re_set_registers (struct re_pattern_buffer *bufp, struct re_registers *regs,
		  __re_size_t num_regs, regoff_t *starts, regoff_t *ends)
{
  if (bufp == NULL || regs == NULL)
    {
      return;
    }

  if (num_regs)
    {
      bufp->regs_allocated = REGS_REALLOCATE;
      regs->num_regs = num_regs;
      regs->start = starts;
      regs->end = ends;
    }
  else
    {
      bufp->regs_allocated = REGS_UNALLOCATED;
      regs->num_regs = 0;
      regs->start = regs->end = NULL;
    }
}
#ifdef _LIBC
weak_alias (__re_set_registers, re_set_registers)
#endif

/* Entry points compatible with 4.2 BSD regex library.  We don't define
   them unless specifically requested.  */

#if defined _REGEX_RE_COMP || defined _LIBC
int
# ifdef _LIBC
weak_function
# endif
re_exec (const char *s)
{
  return 0 == regexec (&re_comp_buf, s, 0, NULL, 0);
}
#endif /* _REGEX_RE_COMP */

/* Internal entry point.  */

/* Searches for a compiled pattern PREG in the string STRING, whose
   length is LENGTH.  NMATCH, PMATCH, and EFLAGS have the same
   meaning as with regexec.  LAST_START is START + RANGE, where
   START and RANGE have the same meaning as with re_search.
   Return REG_NOERROR if we find a match, and REG_NOMATCH if not,
   otherwise return the error code.
   Note: We assume front end functions already check ranges.
   (0 <= LAST_START && LAST_START <= LENGTH)  */

static reg_errcode_t
__attribute_warn_unused_result__
re_search_internal (const regex_t *preg, const char *string, Idx length,
		    Idx start, Idx last_start, Idx stop, size_t nmatch,
		    regmatch_t pmatch[], int eflags)
{
  reg_errcode_t err;
  const re_dfa_t *dfa = preg->buffer;
  Idx left_lim, right_lim;
  int incr;
  bool fl_longest_match;
  int match_kind;
  Idx match_first;
  Idx match_last = -1;
  Idx extra_nmatch;
  bool sb;
  int ch;
  re_match_context_t mctx = { .dfa = dfa };
  char *fastmap = ((preg->fastmap != NULL && preg->fastmap_accurate
		    && start != last_start && !preg->can_be_null)
		   ? preg->fastmap : NULL);
  RE_TRANSLATE_TYPE t = preg->translate;

  extra_nmatch = (nmatch > preg->re_nsub) ? nmatch - (preg->re_nsub + 1) : 0;
  nmatch -= extra_nmatch;

  /* Check if the DFA haven't been compiled.  */
  if (__glibc_unlikely (preg->used == 0 || dfa->init_state == NULL
			|| dfa->init_state_word == NULL
			|| dfa->init_state_nl == NULL
			|| dfa->init_state_begbuf == NULL))
    return REG_NOMATCH;

  /* We assume front-end functions already check them.  */
  DEBUG_ASSERT (0 <= last_start && last_start <= length);

  /* If initial states with non-begbuf contexts have no elements,
     the regex must be anchored.  If preg->newline_anchor is set,
     we'll never use init_state_nl, so do not check it.  */
  if (dfa->init_state->nodes.nelem == 0
      && dfa->init_state_word->nodes.nelem == 0
      && (dfa->init_state_nl->nodes.nelem == 0
	  || !preg->newline_anchor))
    {
      if (start != 0 && last_start != 0)
        return REG_NOMATCH;
      start = last_start = 0;
    }

  /* We must check the longest matching, if nmatch > 0.  */
  fl_longest_match = (nmatch != 0 || dfa->nbackref);

  err = re_string_allocate (&mctx.input, string, length, dfa->nodes_len + 1,
			    preg->translate, (preg->syntax & RE_ICASE) != 0,
			    dfa);
  if (__glibc_unlikely (err != REG_NOERROR))
    goto free_return;
  mctx.input.stop = stop;
  mctx.input.raw_stop = stop;
  mctx.input.newline_anchor = preg->newline_anchor;

  err = match_ctx_init (&mctx, eflags, dfa->nbackref * 2);
  if (__glibc_unlikely (err != REG_NOERROR))
    goto free_return;

  /* We will log all the DFA states through which the dfa pass,
     if nmatch > 1, or this dfa has "multibyte node", which is a
     back-reference or a node which can accept multibyte character or
     multi character collating element.  */
  if (nmatch > 1 || dfa->has_mb_node)
    {
      /* Avoid overflow.  */
      if (__glibc_unlikely ((MIN (IDX_MAX, SIZE_MAX / sizeof (re_dfastate_t *))
			     <= mctx.input.bufs_len)))
	{
	  err = REG_ESPACE;
	  goto free_return;
	}

      mctx.state_log = re_malloc (re_dfastate_t *, mctx.input.bufs_len + 1);
      if (__glibc_unlikely (mctx.state_log == NULL))
	{
	  err = REG_ESPACE;
	  goto free_return;
	}
    }

  match_first = start;
  mctx.input.tip_context = (eflags & REG_NOTBOL) ? CONTEXT_BEGBUF
			   : CONTEXT_NEWLINE | CONTEXT_BEGBUF;

  /* Check incrementally whether the input string matches.  */
  incr = (last_start < start) ? -1 : 1;
  left_lim = (last_start < start) ? last_start : start;
  right_lim = (last_start < start) ? start : last_start;
  sb = dfa->mb_cur_max == 1;
  match_kind =
    (fastmap
     ? ((sb || !(preg->syntax & RE_ICASE || t) ? 4 : 0)
	| (start <= last_start ? 2 : 0)
	| (t != NULL ? 1 : 0))
     : 8);

  for (;; match_first += incr)
    {
      err = REG_NOMATCH;
      if (match_first < left_lim || right_lim < match_first)
	goto free_return;

      /* Advance as rapidly as possible through the string, until we
	 find a plausible place to start matching.  This may be done
	 with varying efficiency, so there are various possibilities:
	 only the most common of them are specialized, in order to
	 save on code size.  We use a switch statement for speed.  */
      switch (match_kind)
	{
	case 8:
	  /* No fastmap.  */
	  break;

	case 7:
	  /* Fastmap with single-byte translation, match forward.  */
	  while (__glibc_likely (match_first < right_lim)
		 && !fastmap[t[(unsigned char) string[match_first]]])
	    ++match_first;
	  goto forward_match_found_start_or_reached_end;

	case 6:
	  /* Fastmap without translation, match forward.  */
	  while (__glibc_likely (match_first < right_lim)
		 && !fastmap[(unsigned char) string[match_first]])
	    ++match_first;

	forward_match_found_start_or_reached_end:
	  if (__glibc_unlikely (match_first == right_lim))
	    {
	      ch = match_first >= length
		       ? 0 : (unsigned char) string[match_first];
	      if (!fastmap[t ? t[ch] : ch])
		goto free_return;
	    }
	  break;

	case 4:
	case 5:
	  /* Fastmap without multi-byte translation, match backwards.  */
	  while (match_first >= left_lim)
	    {
	      ch = match_first >= length
		       ? 0 : (unsigned char) string[match_first];
	      if (fastmap[t ? t[ch] : ch])
		break;
	      --match_first;
	    }
	  if (match_first < left_lim)
	    goto free_return;
	  break;

	default:
	  /* In this case, we can't determine easily the current byte,
	     since it might be a component byte of a multibyte
	     character.  Then we use the constructed buffer instead.  */
	  for (;;)
	    {
	      /* If MATCH_FIRST is out of the valid range, reconstruct the
		 buffers.  */
	      __re_size_t offset = match_first - mctx.input.raw_mbs_idx;
	      if (__glibc_unlikely (offset
				    >= (__re_size_t) mctx.input.valid_raw_len))
		{
		  err = re_string_reconstruct (&mctx.input, match_first,
					       eflags);
		  if (__glibc_unlikely (err != REG_NOERROR))
		    goto free_return;

		  offset = match_first - mctx.input.raw_mbs_idx;
		}
	      /* Use buffer byte if OFFSET is in buffer, otherwise '\0'.  */
	      ch = (offset < mctx.input.valid_len
		    ? re_string_byte_at (&mctx.input, offset) : 0);
	      if (fastmap[ch])
		break;
	      match_first += incr;
	      if (match_first < left_lim || match_first > right_lim)
		{
		  err = REG_NOMATCH;
		  goto free_return;
		}
	    }
	  break;
	}

      /* Reconstruct the buffers so that the matcher can assume that
	 the matching starts from the beginning of the buffer.  */
      err = re_string_reconstruct (&mctx.input, match_first, eflags);
      if (__glibc_unlikely (err != REG_NOERROR))
	goto free_return;

#ifdef RE_ENABLE_I18N
     /* Don't consider this char as a possible match start if it part,
	yet isn't the head, of a multibyte character.  */
      if (!sb && !re_string_first_byte (&mctx.input, 0))
	continue;
#endif

      /* It seems to be appropriate one, then use the matcher.  */
      /* We assume that the matching starts from 0.  */
      mctx.state_log_top = mctx.nbkref_ents = mctx.max_mb_elem_len = 0;
      match_last = check_matching (&mctx, fl_longest_match,
				   start <= last_start ? &match_first : NULL);
      if (match_last != -1)
	{
	  if (__glibc_unlikely (match_last == -2))
	    {
	      err = REG_ESPACE;
	      goto free_return;
	    }
	  else
	    {
	      mctx.match_last = match_last;
	      if ((!preg->no_sub && nmatch > 1) || dfa->nbackref)
		{
		  re_dfastate_t *pstate = mctx.state_log[match_last];
		  mctx.last_node = check_halt_state_context (&mctx, pstate,
							     match_last);
		}
	      if ((!preg->no_sub && nmatch > 1 && dfa->has_plural_match)
		  || dfa->nbackref)
		{
		  err = prune_impossible_nodes (&mctx);
		  if (err == REG_NOERROR)
		    break;
		  if (__glibc_unlikely (err != REG_NOMATCH))
		    goto free_return;
		  match_last = -1;
		}
	      else
		break; /* We found a match.  */
	    }
	}

      match_ctx_clean (&mctx);
    }

  DEBUG_ASSERT (match_last != -1);
  DEBUG_ASSERT (err == REG_NOERROR);

  /* Set pmatch[] if we need.  */
  if (nmatch > 0)
    {
      Idx reg_idx;

      /* Initialize registers.  */
      for (reg_idx = 1; reg_idx < nmatch; ++reg_idx)
	pmatch[reg_idx].rm_so = pmatch[reg_idx].rm_eo = -1;

      /* Set the points where matching start/end.  */
      pmatch[0].rm_so = 0;
      pmatch[0].rm_eo = mctx.match_last;
      /* FIXME: This function should fail if mctx.match_last exceeds
	 the maximum possible regoff_t value.  We need a new error
	 code REG_OVERFLOW.  */

      if (!preg->no_sub && nmatch > 1)
	{
	  err = set_regs (preg, &mctx, nmatch, pmatch,
			  dfa->has_plural_match && dfa->nbackref > 0);
	  if (__glibc_unlikely (err != REG_NOERROR))
	    goto free_return;
	}

      /* At last, add the offset to each register, since we slid
	 the buffers so that we could assume that the matching starts
	 from 0.  */
      for (reg_idx = 0; reg_idx < nmatch; ++reg_idx)
	if (pmatch[reg_idx].rm_so != -1)
	  {
#ifdef RE_ENABLE_I18N
	    if (__glibc_unlikely (mctx.input.offsets_needed != 0))
	      {
		pmatch[reg_idx].rm_so =
		  (pmatch[reg_idx].rm_so == mctx.input.valid_len
		   ? mctx.input.valid_raw_len
		   : mctx.input.offsets[pmatch[reg_idx].rm_so]);
		pmatch[reg_idx].rm_eo =
		  (pmatch[reg_idx].rm_eo == mctx.input.valid_len
		   ? mctx.input.valid_raw_len
		   : mctx.input.offsets[pmatch[reg_idx].rm_eo]);
	      }
#else
	    DEBUG_ASSERT (mctx.input.offsets_needed == 0);
#endif
	    pmatch[reg_idx].rm_so += match_first;
	    pmatch[reg_idx].rm_eo += match_first;
	  }
      for (reg_idx = 0; reg_idx < extra_nmatch; ++reg_idx)
	{
	  pmatch[nmatch + reg_idx].rm_so = -1;
	  pmatch[nmatch + reg_idx].rm_eo = -1;
	}

      if (dfa->subexp_map)
	for (reg_idx = 0; reg_idx + 1 < nmatch; reg_idx++)
	  if (dfa->subexp_map[reg_idx] != reg_idx)
	    {
	      pmatch[reg_idx + 1].rm_so
		= pmatch[dfa->subexp_map[reg_idx] + 1].rm_so;
	      pmatch[reg_idx + 1].rm_eo
		= pmatch[dfa->subexp_map[reg_idx] + 1].rm_eo;
	    }
    }

 free_return:
  re_free (mctx.state_log);
  if (dfa->nbackref)
    match_ctx_free (&mctx);
  re_string_destruct (&mctx.input);
  return err;
}

static reg_errcode_t
__attribute_warn_unused_result__
prune_impossible_nodes (re_match_context_t *mctx)
{
  const re_dfa_t *const dfa = mctx->dfa;
  Idx halt_node, match_last;
  reg_errcode_t ret;
  re_dfastate_t **sifted_states;
  re_dfastate_t **lim_states = NULL;
  re_sift_context_t sctx;
  DEBUG_ASSERT (mctx->state_log != NULL);
  match_last = mctx->match_last;
  halt_node = mctx->last_node;

  /* Avoid overflow.  */
  if (__glibc_unlikely (MIN (IDX_MAX, SIZE_MAX / sizeof (re_dfastate_t *))
			<= match_last))
    return REG_ESPACE;

  sifted_states = re_malloc (re_dfastate_t *, match_last + 1);
  if (__glibc_unlikely (sifted_states == NULL))
    {
      ret = REG_ESPACE;
      goto free_return;
    }
  if (dfa->nbackref)
    {
      lim_states = re_malloc (re_dfastate_t *, match_last + 1);
      if (__glibc_unlikely (lim_states == NULL))
	{
	  ret = REG_ESPACE;
	  goto free_return;
	}
      while (1)
	{
	  memset (lim_states, '\0',
		  sizeof (re_dfastate_t *) * (match_last + 1));
	  sift_ctx_init (&sctx, sifted_states, lim_states, halt_node,
			 match_last);
	  ret = sift_states_backward (mctx, &sctx);
	  re_node_set_free (&sctx.limits);
	  if (__glibc_unlikely (ret != REG_NOERROR))
	      goto free_return;
	  if (sifted_states[0] != NULL || lim_states[0] != NULL)
	    break;
	  do
	    {
	      --match_last;
	      if (match_last < 0)
		{
		  ret = REG_NOMATCH;
		  goto free_return;
		}
	    } while (mctx->state_log[match_last] == NULL
		     || !mctx->state_log[match_last]->halt);
	  halt_node = check_halt_state_context (mctx,
						mctx->state_log[match_last],
						match_last);
	}
      ret = merge_state_array (dfa, sifted_states, lim_states,
			       match_last + 1);
      re_free (lim_states);
      lim_states = NULL;
      if (__glibc_unlikely (ret != REG_NOERROR))
	goto free_return;
    }
  else
    {
      sift_ctx_init (&sctx, sifted_states, lim_states, halt_node, match_last);
      ret = sift_states_backward (mctx, &sctx);
      re_node_set_free (&sctx.limits);
      if (__glibc_unlikely (ret != REG_NOERROR))
	goto free_return;
      if (sifted_states[0] == NULL)
	{
	  ret = REG_NOMATCH;
	  goto free_return;
	}
    }
  re_free (mctx->state_log);
  mctx->state_log = sifted_states;
  sifted_states = NULL;
  mctx->last_node = halt_node;
  mctx->match_last = match_last;
  ret = REG_NOERROR;
 free_return:
  re_free (sifted_states);
  re_free (lim_states);
  return ret;
}

/* Acquire an initial state and return it.
   We must select appropriate initial state depending on the context,
   since initial states may have constraints like "\<", "^", etc..  */

static inline re_dfastate_t *
__attribute__ ((always_inline))
acquire_init_state_context (reg_errcode_t *err, const re_match_context_t *mctx,
			    Idx idx)
{
  const re_dfa_t *const dfa = mctx->dfa;
  re_dfastate_t *result = dfa->init_state;

  if (dfa->init_state->has_constraint)
    {
      unsigned int context = re_string_context_at (&mctx->input, idx - 1, mctx->eflags);

      if (IS_WORD_CONTEXT (context))
	{
	  result = dfa->init_state_word;
	}
      else if (IS_BEGBUF_CONTEXT (context) && IS_NEWLINE_CONTEXT (context))
	{
	  result = dfa->init_state_begbuf;
	}
      else if (IS_NEWLINE_CONTEXT (context))
	{
	  result = dfa->init_state_nl;
	}
      else if (IS_BEGBUF_CONTEXT (context))
	{
	  result = re_acquire_state_context (err, dfa,
					     dfa->init_state->entrance_nodes,
					     context);
	}
    }

  return result;
}

/* Check whether the regular expression match input string INPUT or not,
   and return the index where the matching end.  Return -1 if
   there is no match, and return -2 in case of an error.
   FL_LONGEST_MATCH means we want the POSIX longest matching.
   If P_MATCH_FIRST is not NULL, and the match fails, it is set to the
   next place where we may want to try matching.
   Note that the matcher assumes that the matching starts from the current
   index of the buffer.  */

static Idx
__attribute_warn_unused_result__
check_matching (re_match_context_t *mctx, bool fl_longest_match,
		Idx *p_match_first)
{
  const re_dfa_t *const dfa = mctx->dfa;
  reg_errcode_t err;
  Idx match = 0;
  Idx match_last = -1;
  Idx cur_str_idx = re_string_cur_idx (&mctx->input);
  re_dfastate_t *cur_state;
  bool at_init_state = p_match_first != NULL;
  Idx next_start_idx = cur_str_idx;

  err = REG_NOERROR;
  cur_state = acquire_init_state_context (&err, mctx, cur_str_idx);
  /* An initial state must not be NULL (invalid).  */
  if (__glibc_unlikely (cur_state == NULL))
    {
      DEBUG_ASSERT (err == REG_ESPACE);
      return -2;
    }

  if (mctx->state_log != NULL)
    {
      mctx->state_log[cur_str_idx] = cur_state;

      /* Check OP_OPEN_SUBEXP in the initial state in case that we use them
	 later.  E.g. Processing back references.  */
      if (__glibc_unlikely (dfa->nbackref))
	{
	  at_init_state = false;
	  err = check_subexp_matching_top (mctx, &cur_state->nodes, 0);
	  if (__glibc_unlikely (err != REG_NOERROR))
	    return err;

	  if (cur_state->has_backref)
	    {
	      err = transit_state_bkref (mctx, &cur_state->nodes);
	      if (__glibc_unlikely (err != REG_NOERROR))
		return err;
	    }
	}
    }

  /* If the RE accepts NULL string.  */
  if (__glibc_unlikely (cur_state->halt))
    {
      if (!cur_state->has_constraint
	  || check_halt_state_context (mctx, cur_state, cur_str_idx))
	{
	  if (!fl_longest_match)
	    return cur_str_idx;
	  else
	    {
	      match_last = cur_str_idx;
	      match = 1;
	    }
	}
    }

  while (!re_string_eoi (&mctx->input))
    {
      re_dfastate_t *old_state = cur_state;
      Idx next_char_idx = re_string_cur_idx (&mctx->input) + 1;

      if ((__glibc_unlikely (next_char_idx >= mctx->input.bufs_len)
	   && mctx->input.bufs_len < mctx->input.len)
	  || (__glibc_unlikely (next_char_idx >= mctx->input.valid_len)
	      && mctx->input.valid_len < mctx->input.len))
	{
	  err = extend_buffers (mctx, next_char_idx + 1);
	  if (__glibc_unlikely (err != REG_NOERROR))
	    {
	      DEBUG_ASSERT (err == REG_ESPACE);
	      return -2;
	    }
	}

      cur_state = transit_state (&err, mctx, cur_state);
      if (mctx->state_log != NULL)
	cur_state = merge_state_with_log (&err, mctx, cur_state);

      if (cur_state == NULL)
	{
	  /* Reached the invalid state or an error.  Try to recover a valid
	     state using the state log, if available and if we have not
	     already found a valid (even if not the longest) match.  */
	  if (__glibc_unlikely (err != REG_NOERROR))
	    return -2;

	  if (mctx->state_log == NULL
	      || (match && !fl_longest_match)
	      || (cur_state = find_recover_state (&err, mctx)) == NULL)
	    break;
	}

      if (__glibc_unlikely (at_init_state))
	{
	  if (old_state == cur_state)
	    next_start_idx = next_char_idx;
	  else
	    at_init_state = false;
	}

      if (cur_state->halt)
	{
	  /* Reached a halt state.
	     Check the halt state can satisfy the current context.  */
	  if (!cur_state->has_constraint
	      || check_halt_state_context (mctx, cur_state,
					   re_string_cur_idx (&mctx->input)))
	    {
	      /* We found an appropriate halt state.  */
	      match_last = re_string_cur_idx (&mctx->input);
	      match = 1;

	      /* We found a match, do not modify match_first below.  */
	      p_match_first = NULL;
	      if (!fl_longest_match)
		break;
	    }
	}
    }

  if (p_match_first)
    *p_match_first += next_start_idx;

  return match_last;
}

/* Check NODE match the current context.  */

static bool
check_halt_node_context (const re_dfa_t *dfa, Idx node, unsigned int context)
{
  re_token_type_t type = dfa->nodes[node].type;
  unsigned int constraint = dfa->nodes[node].constraint;

  if (type != END_OF_RE) {
    return false;
  }

  if (constraint == 0) {
    return true;
  }

  return !NOT_SATISFY_NEXT_CONSTRAINT(constraint, context);
}

/* Check the halt state STATE match the current context.
   Return 0 if not match, if the node, STATE has, is a halt node and
   match the context, return the node.  */

static Idx
check_halt_state_context (const re_match_context_t *mctx,
			  const re_dfastate_t *state, Idx idx)
{
  DEBUG_ASSERT (state->halt);
  unsigned int context = re_string_context_at (&mctx->input, idx, mctx->eflags);

  for (Idx i = 0; i < state->nodes.nelem; ++i) {
    if (check_halt_node_context (mctx->dfa, state->nodes.elems[i], context)) {
      return state->nodes.elems[i];
    }
  }
  return 0;
}

/* Compute the next node to which "NFA" transit from NODE("NFA" is a NFA
   corresponding to the DFA).
   Return the destination node, and update EPS_VIA_NODES;
   return -1 on match failure, -2 on error.  */

static Idx
proceed_next_node (const re_match_context_t *mctx, Idx nregs, regmatch_t *regs,
		   regmatch_t *prevregs,
		   Idx *pidx, Idx node, re_node_set *eps_via_nodes,
		   struct re_fail_stack_t *fs)
{
  if (__glibc_unlikely(mctx == NULL || pidx == NULL || eps_via_nodes == NULL)) {
      return -2;
  }
  const re_dfa_t *const dfa = mctx->dfa;
  if (__glibc_unlikely(dfa == NULL || dfa->nodes == NULL || dfa->edests == NULL || dfa->nexts == NULL || mctx->state_log == NULL)) {
      return -2;
  }

  if (__glibc_unlikely(node < 0 || node >= dfa->nnodes)) {
      return -2;
  }
  if (__glibc_unlikely(*pidx < 0 || *pidx > mctx->match_last + 1)) {
      return -2;
  }

  if (__glibc_unlikely(mctx->state_log[*pidx] == NULL)) {
      return -2;
  }
  re_node_set *cur_nodes = &mctx->state_log[*pidx]->nodes;

  if (IS_EPSILON_NODE (dfa->nodes[node].type))
    {
      re_node_set *edests = &dfa->edests[node];

      if (! re_node_set_contains (eps_via_nodes, node))
        {
          bool ok = re_node_set_insert (eps_via_nodes, node);
          if (__glibc_unlikely (! ok))
            return -2;
        }

      Idx dest_node = -1;
      Idx second_candidate = -1;

      for (Idx i = 0; i < edests->nelem; i++)
        {
          Idx candidate = edests->elems[i];
          if (re_node_set_contains (cur_nodes, candidate))
            {
              if (dest_node == -1)
                dest_node = candidate;
              else
                {
                  second_candidate = candidate;
                  break;
                }
            }
        }

      if (second_candidate != -1)
        {
          if (re_node_set_contains (eps_via_nodes, dest_node))
            return second_candidate;
          else if (fs != NULL)
            {
              if (push_fail_stack (fs, *pidx, second_candidate, nregs, regs,
                                   prevregs, eps_via_nodes))
                return -2;
            }
        }
      return dest_node;
    }
  else /* Non-epsilon node */
    {
      Idx naccepted = 0;
      re_token_type_t type = dfa->nodes[node].type;

#ifdef RE_ENABLE_I18N
      if (dfa->nodes[node].accept_mb)
	naccepted = check_node_accept_bytes (dfa, node, &mctx->input, *pidx);
      else
#endif /* RE_ENABLE_I18N */
      if (type == OP_BACK_REF)
	{
          if (__glibc_unlikely(regs == NULL)) {
              return -2;
          }
	  Idx subexp_idx = dfa->nodes[node].opr.idx + 1;
          bool backref_valid = true;

	  if (subexp_idx >= nregs || regs[subexp_idx].rm_so == -1 || regs[subexp_idx].rm_eo == -1)
	    {
              backref_valid = false;
	      if (fs != NULL)
		return -1;
              /* If fs is NULL, naccepted remains 0 (initial value) and we proceed. */
	    }
	  else
	    {
	      naccepted = regs[subexp_idx].rm_eo - regs[subexp_idx].rm_so;
	    }

          if (backref_valid && naccepted > 0)
            {
              char *buf = (char *) re_string_get_buffer (&mctx->input);
              if (__glibc_unlikely(buf == NULL)) return -2;

              if (mctx->input.valid_len - *pidx < naccepted
                  || (memcmp (buf + regs[subexp_idx].rm_so, buf + *pidx,
                              naccepted)
                      != 0))
                return -1;
            }

	  if (naccepted == 0)
	    {
	      bool ok = re_node_set_insert (eps_via_nodes, node);
	      if (__glibc_unlikely (! ok))
		return -2;

              if (__glibc_unlikely(dfa->edests[node].nelem == 0)) {
                  return -1;
              }
	      Idx dest_node_br = dfa->edests[node].elems[0];

              if (__glibc_unlikely(mctx->state_log[*pidx] == NULL)) {
                   return -2;
              }
	      if (re_node_set_contains (&mctx->state_log[*pidx]->nodes,
					dest_node_br))
		return dest_node_br;
              return -1;
	    }
	}

      if (naccepted != 0
	  || check_node_accept (mctx, dfa->nodes + node, *pidx))
	{
	  Idx dest_node = dfa->nexts[node];
	  *pidx = (naccepted == 0) ? *pidx + 1 : *pidx + naccepted;

	  if (fs != NULL)
	    {
              if (__glibc_unlikely(*pidx < 0 || *pidx > mctx->match_last + 1)) {
                  return -2;
              }
	      if (__glibc_unlikely(mctx->state_log[*pidx] == NULL) ||
                  !re_node_set_contains (&mctx->state_log[*pidx]->nodes,
					 dest_node))
		return -1;
	    }
	  re_node_set_empty (eps_via_nodes);
	  return dest_node;
	}
    }
  return -1;
}

static reg_errcode_t
__attribute_warn_unused_result__
push_fail_stack (struct re_fail_stack_t *fs, Idx str_idx, Idx dest_node,
		 Idx nregs, regmatch_t *regs, regmatch_t *prevregs,
		 re_node_set *eps_via_nodes)
{
  reg_errcode_t err;
  Idx num = fs->num++;
  if (fs->num == fs->alloc)
    {
      struct re_fail_stack_ent_t *new_array;
      new_array = re_realloc (fs->stack, struct re_fail_stack_ent_t,
                              fs->alloc * 2);
      if (new_array == NULL)
	return REG_ESPACE;
      fs->alloc *= 2;
      fs->stack = new_array;
    }
  fs->stack[num].idx = str_idx;
  fs->stack[num].node = dest_node;
  fs->stack[num].regs = re_malloc (regmatch_t, 2 * nregs);
  if (fs->stack[num].regs == NULL)
    return REG_ESPACE;
  memcpy (fs->stack[num].regs, regs, sizeof (regmatch_t) * nregs);
  memcpy (fs->stack[num].regs + nregs, prevregs, sizeof (regmatch_t) * nregs);
  err = re_node_set_init_copy (&fs->stack[num].eps_via_nodes, eps_via_nodes);
  return err;
}

static Idx
pop_fail_stack (struct re_fail_stack_t *fs, Idx *pidx, Idx nregs,
		regmatch_t *regs, regmatch_t *prevregs,
		re_node_set *eps_via_nodes)
{
  if (fs == NULL || fs->num == 0 || pidx == NULL || regs == NULL || prevregs == NULL || eps_via_nodes == NULL)
    {
      return -1;
    }

  if (nregs < 0)
    {
      return -1;
    }

  struct re_fail_stack_entry_t *current_entry = &fs->stack[--fs->num];

  *pidx = current_entry->idx;

  memcpy(regs, current_entry->regs, sizeof(regmatch_t) * nregs);
  memcpy(prevregs, current_entry->regs + nregs, sizeof(regmatch_t) * nregs);

  re_node_set_free(eps_via_nodes);

  re_free(current_entry->regs);

  *eps_via_nodes = current_entry->eps_via_nodes;

  return current_entry->node;
}


#define DYNARRAY_STRUCT  regmatch_list
#define DYNARRAY_ELEMENT regmatch_t
#define DYNARRAY_PREFIX  regmatch_list_
#include <malloc/dynarray-skeleton.c>

/* Set the positions where the subexpressions are starts/ends to registers
   PMATCH.
   Note: We assume that pmatch[0] is already set, and
   pmatch[i].rm_so == pmatch[i].rm_eo == -1 for 0 < i < nmatch.  */

static reg_errcode_t
__attribute_warn_unused_result__
set_regs (const regex_t *preg, const re_match_context_t *mctx, size_t nmatch,
	  regmatch_t *pmatch, bool fl_backtrack)
{
  const re_dfa_t *dfa = preg->buffer;
  Idx idx, cur_node;
  re_node_set eps_via_nodes;
  struct re_fail_stack_t *fs;
  struct re_fail_stack_t fs_body = { 0, 2, NULL };
  struct regmatch_list prev_match;
  regmatch_list_init (&prev_match);

  DEBUG_ASSERT (nmatch > 1);
  DEBUG_ASSERT (mctx->state_log != NULL);
  if (fl_backtrack)
    {
      fs = &fs_body;
      fs->stack = re_malloc (struct re_fail_stack_ent_t, fs->alloc);
      if (fs->stack == NULL)
	return REG_ESPACE;
    }
  else
    fs = NULL;

  cur_node = dfa->init_node;
  re_node_set_init_empty (&eps_via_nodes);

  if (!regmatch_list_resize (&prev_match, nmatch))
    {
      regmatch_list_free (&prev_match);
      free_fail_stack_return (fs);
      return REG_ESPACE;
    }
  regmatch_t *prev_idx_match = regmatch_list_begin (&prev_match);
  memcpy (prev_idx_match, pmatch, sizeof (regmatch_t) * nmatch);

  for (idx = pmatch[0].rm_so; idx <= pmatch[0].rm_eo ;)
    {
      update_regs (dfa, pmatch, prev_idx_match, cur_node, idx, nmatch);

      if ((idx == pmatch[0].rm_eo && cur_node == mctx->last_node)
	  || (fs && re_node_set_contains (&eps_via_nodes, cur_node)))
	{
	  Idx reg_idx;
	  cur_node = -1;
	  if (fs)
	    {
	      for (reg_idx = 0; reg_idx < nmatch; ++reg_idx)
		if (pmatch[reg_idx].rm_so > -1 && pmatch[reg_idx].rm_eo == -1)
		  {
		    cur_node = pop_fail_stack (fs, &idx, nmatch, pmatch,
					       prev_idx_match, &eps_via_nodes);
		    break;
		  }
	    }
	  if (cur_node < 0)
	    {
	      re_node_set_free (&eps_via_nodes);
	      regmatch_list_free (&prev_match);
	      return free_fail_stack_return (fs);
	    }
	}

      /* Proceed to next node.  */
      cur_node = proceed_next_node (mctx, nmatch, pmatch, prev_idx_match,
				    &idx, cur_node,
				    &eps_via_nodes, fs);

      if (__glibc_unlikely (cur_node < 0))
	{
	  if (__glibc_unlikely (cur_node == -2))
	    {
	      re_node_set_free (&eps_via_nodes);
	      regmatch_list_free (&prev_match);
	      free_fail_stack_return (fs);
	      return REG_ESPACE;
	    }
	  cur_node = pop_fail_stack (fs, &idx, nmatch, pmatch,
				     prev_idx_match, &eps_via_nodes);
	  if (cur_node < 0)
	    {
	      re_node_set_free (&eps_via_nodes);
	      regmatch_list_free (&prev_match);
	      free_fail_stack_return (fs);
	      return REG_NOMATCH;
	    }
	}
    }
  re_node_set_free (&eps_via_nodes);
  regmatch_list_free (&prev_match);
  return free_fail_stack_return (fs);
}

static reg_errcode_t
free_fail_stack_return (struct re_fail_stack_t *fs)
{
  if (fs == NULL)
    {
      return REG_NOERROR;
    }

  Idx fs_idx;
  for (fs_idx = 0; fs_idx < fs->num; ++fs_idx)
    {
      re_node_set_free (&fs->stack[fs_idx].eps_via_nodes);
      re_free (fs->stack[fs_idx].regs);
    }

  re_free (fs->stack);

  return REG_NOERROR;
}

static void
update_regs (const re_dfa_t *dfa, regmatch_t *pmatch,
	     regmatch_t *prev_idx_match, Idx cur_node, Idx cur_idx, Idx nmatch)
{
  int type = dfa->nodes[cur_node].type;
  Idx reg_num;

  if (type == OP_OPEN_SUBEXP)
    {
      reg_num = dfa->nodes[cur_node].opr.idx + 1;
      if (reg_num < nmatch)
	{
	  pmatch[reg_num].rm_so = cur_idx;
	  pmatch[reg_num].rm_eo = -1;
	}
    }
  else if (type == OP_CLOSE_SUBEXP)
    {
      reg_num = dfa->nodes[cur_node].opr.idx + 1;
      if (reg_num < nmatch)
	{
	  const reg_node_t *node = &dfa->nodes[cur_node];
	  int is_non_empty_current_match = (pmatch[reg_num].rm_so < cur_idx);
	  int is_optional_subexp = node->opt_subexp;
	  int had_prev_non_empty_match_for_this_reg = (prev_idx_match[reg_num].rm_so != -1);

	  if (is_non_empty_current_match)
	    {
	      pmatch[reg_num].rm_eo = cur_idx;
	      memcpy (prev_idx_match, pmatch, sizeof (regmatch_t) * nmatch);
	    }
	  else /* Current subexpression match is empty */
	    {
	      if (is_optional_subexp && had_prev_non_empty_match_for_this_reg)
		{
		  memcpy (pmatch, prev_idx_match, sizeof (regmatch_t) * nmatch);
		}
	      else
		{
		  pmatch[reg_num].rm_eo = cur_idx;
		}
	    }
	}
    }
}

/* This function checks the STATE_LOG from the SCTX->last_str_idx to 0
   and sift the nodes in each states according to the following rules.
   Updated state_log will be wrote to STATE_LOG.

   Rules: We throw away the Node 'a' in the STATE_LOG[STR_IDX] if...
     1. When STR_IDX == MATCH_LAST(the last index in the state_log):
	If 'a' isn't the LAST_NODE and 'a' can't epsilon transit to
	the LAST_NODE, we throw away the node 'a'.
     2. When 0 <= STR_IDX < MATCH_LAST and 'a' accepts
	string 's' and transit to 'b':
	i. If 'b' isn't in the STATE_LOG[STR_IDX+strlen('s')], we throw
	   away the node 'a'.
	ii. If 'b' is in the STATE_LOG[STR_IDX+strlen('s')] but 'b' is
	    thrown away, we throw away the node 'a'.
     3. When 0 <= STR_IDX < MATCH_LAST and 'a' epsilon transit to 'b':
	i. If 'b' isn't in the STATE_LOG[STR_IDX], we throw away the
	   node 'a'.
	ii. If 'b' is in the STATE_LOG[STR_IDX] but 'b' is thrown away,
	    we throw away the node 'a'.  */

#define STATE_NODE_CONTAINS(state,node) \
  ((state) != NULL && re_node_set_contains (&(state)->nodes, node))

static reg_errcode_t
sift_states_backward (const re_match_context_t *mctx, re_sift_context_t *sctx)
{
  reg_errcode_t err = REG_NOERROR;
  int null_cnt = 0;
  Idx str_idx;
  re_node_set cur_dest;
  bool cur_dest_initialized = false;

  DEBUG_ASSERT (mctx->state_log != NULL && mctx->state_log[sctx->last_str_idx] != NULL);

  str_idx = sctx->last_str_idx;

  err = re_node_set_init_1 (&cur_dest, sctx->last_node);
  if (__glibc_unlikely (err != REG_NOERROR))
    {
      return err;
    }
  cur_dest_initialized = true;

  err = update_cur_sifted_state (mctx, sctx, str_idx, &cur_dest);
  if (__glibc_unlikely (err != REG_NOERROR))
    {
      // Error occurred, err is set. The loop will be skipped, and cleanup will handle cur_dest.
    }
  else
    {
      while (str_idx > 0 && err == REG_NOERROR)
	    {
	      null_cnt = (sctx->sifted_states[str_idx] == NULL) ? (null_cnt + 1) : 0;

	      if (null_cnt > mctx->max_mb_elem_len)
		    {
		      memset (sctx->sifted_states, 0, sizeof (re_dfastate_t *) * str_idx);
		      err = REG_NOERROR;
		      break;
		    }

	      re_node_set_empty (&cur_dest);
	      --str_idx;

	      if (mctx->state_log[str_idx])
		    {
		      err = build_sifted_states (mctx, sctx, str_idx, &cur_dest);
		    }

	      if (err == REG_NOERROR)
		    {
		      err = update_cur_sifted_state (mctx, sctx, str_idx, &cur_dest);
		    }
	    }
    }

  if (cur_dest_initialized)
    {
      re_node_set_free (&cur_dest);
    }

  return err;
}

static reg_errcode_t
__attribute_warn_unused_result__
build_sifted_states (const re_match_context_t *mctx, re_sift_context_t *sctx,
		     Idx str_idx, re_node_set *cur_dest)
{
  const re_dfa_t *const dfa = mctx->dfa;
  const re_node_set *cur_src = &mctx->state_log[str_idx]->non_eps_nodes;
  Idx i;

  /* Then build the next sifted state.
     We build the next sifted state on 'cur_dest', and update
     'sifted_states[str_idx]' with 'cur_dest'.
     Note:
     'cur_dest' is the sifted state from 'state_log[str_idx + 1]'.
     'cur_src' points the node_set of the old 'state_log[str_idx]'
     (with the epsilon nodes pre-filtered out).  */
  for (i = 0; i < cur_src->nelem; i++)
    {
      Idx prev_node = cur_src->elems[i];
      int naccepted = 0;
      bool ok;
      DEBUG_ASSERT (!IS_EPSILON_NODE (dfa->nodes[prev_node].type));

#ifdef RE_ENABLE_I18N
      /* If the node may accept "multi byte".  */
      if (dfa->nodes[prev_node].accept_mb)
	naccepted = sift_states_iter_mb (mctx, sctx, prev_node,
					 str_idx, sctx->last_str_idx);
#endif /* RE_ENABLE_I18N */

      /* We don't check backreferences here.
	 See update_cur_sifted_state().  */
      if (!naccepted
	  && check_node_accept (mctx, dfa->nodes + prev_node, str_idx)
	  && STATE_NODE_CONTAINS (sctx->sifted_states[str_idx + 1],
				  dfa->nexts[prev_node]))
	naccepted = 1;

      if (naccepted == 0)
	continue;

      if (sctx->limits.nelem)
	{
	  Idx to_idx = str_idx + naccepted;
	  if (check_dst_limits (mctx, &sctx->limits,
				dfa->nexts[prev_node], to_idx,
				prev_node, str_idx))
	    continue;
	}
      ok = re_node_set_insert (cur_dest, prev_node);
      if (__glibc_unlikely (! ok))
	return REG_ESPACE;
    }

  return REG_NOERROR;
}

/* Helper functions.  */

static reg_errcode_t
clean_state_log_if_needed (re_match_context_t *mctx, Idx next_state_log_idx)
{
  Idx current_state_log_top = mctx->state_log_top;

  // Determine if input buffers need to be extended.
  // This is required if the next state log index exceeds the current allocated
  // buffer length or the valid data length, and there's more input available.
  bool needs_bufs_extension = (next_state_log_idx >= mctx->input.bufs_len && mctx->input.bufs_len < mctx->input.len);
  bool needs_valid_extension = (next_state_log_idx >= mctx->input.valid_len && mctx->input.valid_len < mctx->input.len);

  if (needs_bufs_extension || needs_valid_extension)
    {
      reg_errcode_t err = extend_buffers (mctx, next_state_log_idx + 1);
      if (err != REG_NOERROR)
	return err;
    }

  // If the next state log index is beyond the current top,
  // clear the newly introduced state log entries and update the top index.
  if (current_state_log_top < next_state_log_idx)
    {
      // Calculate the number of new entries that need to be cleared.
      Idx num_entries_to_clear = next_state_log_idx - current_state_log_top;

      // Clear the memory for the new state log entries, initializing pointers to NULL.
      // We start clearing from the element *after* current_state_log_top.
      memset (mctx->state_log + current_state_log_top + 1,
              0, // Use 0 to set all bytes to null, effectively making it a NULL pointer.
              sizeof (re_dfastate_t *) * num_entries_to_clear);

      // Update the state log's top index to reflect the new extent.
      mctx->state_log_top = next_state_log_idx;
    }

  return REG_NOERROR;
}

static reg_errcode_t
_merge_single_state (const re_dfa_t *dfa, re_dfastate_t **dst_state_ptr,
		     re_dfastate_t *src_state)
{
  if (*dst_state_ptr == NULL)
    {
      *dst_state_ptr = src_state;
      return REG_NOERROR;
    }
  else if (src_state != NULL)
    {
      re_node_set merged_set;
      reg_errcode_t err;

      err = re_node_set_init_union (&merged_set, &(*dst_state_ptr)->nodes,
				    &src_state->nodes);
      if (__glibc_unlikely (err != REG_NOERROR))
	return err;

      *dst_state_ptr = re_acquire_state (&err, dfa, &merged_set);
      re_node_set_free (&merged_set);
      if (__glibc_unlikely (err != REG_NOERROR))
	return err;
    }
  return REG_NOERROR;
}

static reg_errcode_t
merge_state_array (const re_dfa_t *dfa, re_dfastate_t **dst,
		   re_dfastate_t **src, Idx num)
{
  Idx st_idx;
  for (st_idx = 0; st_idx < num; ++st_idx)
    {
      reg_errcode_t err = _merge_single_state (dfa, &dst[st_idx], src[st_idx]);
      if (__glibc_unlikely (err != REG_NOERROR))
	return err;
    }
  return REG_NOERROR;
}

static reg_errcode_t
update_cur_sifted_state (const re_match_context_t *mctx,
			 re_sift_context_t *sctx, Idx str_idx,
			 re_node_set *dest_nodes)
{
  const re_dfa_t *const dfa = mctx->dfa;
  reg_errcode_t err = REG_NOERROR;

  const re_state_log_entry *log_entry = mctx->state_log[str_idx];
  const re_node_set *candidates = (log_entry == NULL) ? NULL : &log_entry->nodes;

  if (dest_nodes->nelem == 0)
    {
      sctx->sifted_states[str_idx] = NULL;
    }
  else
    {
      if (candidates)
	{
	  err = add_epsilon_src_nodes (dfa, dest_nodes, candidates);
	  if (__glibc_unlikely (err != REG_NOERROR))
	    return err;

	  if (sctx->limits.nelem)
	    {
	      err = check_subexp_limits (dfa, dest_nodes, candidates, &sctx->limits,
					 mctx->bkref_ents, str_idx);
	      if (__glibc_unlikely (err != REG_NOERROR))
		return err;
	    }
	}

      sctx->sifted_states[str_idx] = re_acquire_state (&err, dfa, dest_nodes);
      if (__glibc_unlikely (err != REG_NOERROR))
	return err;
    }

  if (log_entry && log_entry->has_backref)
    {
      err = sift_states_bkref (mctx, sctx, str_idx, candidates);
      if (__glibc_unlikely (err != REG_NOERROR))
	return err;
    }

  return REG_NOERROR;
}

static reg_errcode_t
__attribute_warn_unused_result__
add_epsilon_src_nodes (const re_dfa_t *dfa, re_node_set *dest_nodes,
		       const re_node_set *candidates)
{
  reg_errcode_t err = REG_NOERROR;
  Idx i;

  re_dfastate_t *state = re_acquire_state (&err, dfa, dest_nodes);
  if (__glibc_unlikely (err != REG_NOERROR))
    return err;

  if (!state->inveclosure.alloc)
    {
      err = re_node_set_alloc (&state->inveclosure, dest_nodes->nelem);
      if (__glibc_unlikely (err != REG_NOERROR))
	return REG_ESPACE;
      for (i = 0; i < dest_nodes->nelem; i++)
	{
	  err = re_node_set_merge (&state->inveclosure,
				   dfa->inveclosures + dest_nodes->elems[i]);
	  if (__glibc_unlikely (err != REG_NOERROR))
	    return REG_ESPACE;
	}
    }
  return re_node_set_add_intersect (dest_nodes, candidates,
				    &state->inveclosure);
}

static reg_errcode_t
sub_epsilon_src_nodes (const re_dfa_t *dfa, Idx node, re_node_set *dest_nodes,
                       const re_node_set *candidates)
{
    reg_errcode_t err;
    re_node_set *inv_eclosure = dfa->inveclosures + node;
    re_node_set except_nodes;

    re_node_set_init_empty(&except_nodes);

    for (Idx ecl_idx = 0; ecl_idx < inv_eclosure->nelem; ++ecl_idx)
    {
        Idx cur_node = inv_eclosure->elems[ecl_idx];

        if (cur_node == node)
            continue;

        if (IS_EPSILON_NODE(dfa->nodes[cur_node].type))
        {
            Idx edst1 = dfa->edests[cur_node].elems[0];
            bool meets_epsilon_condition = false;

            if (!re_node_set_contains(inv_eclosure, edst1) && re_node_set_contains(dest_nodes, edst1))
            {
                meets_epsilon_condition = true;
            }

            if (!meets_epsilon_condition && dfa->edests[cur_node].nelem > 1)
            {
                Idx edst2 = dfa->edests[cur_node].elems[1];
                if (edst2 > 0
                    && !re_node_set_contains(inv_eclosure, edst2)
                    && re_node_set_contains(dest_nodes, edst2))
                {
                    meets_epsilon_condition = true;
                }
            }

            if (meets_epsilon_condition)
            {
                err = re_node_set_add_intersect(&except_nodes, candidates,
                                                dfa->inveclosures + cur_node);
                if (__glibc_unlikely(err != REG_NOERROR))
                {
                    re_node_set_free(&except_nodes);
                    return err;
                }
            }
        }
    }

    for (Idx ecl_idx = 0; ecl_idx < inv_eclosure->nelem; ++ecl_idx)
    {
        Idx cur_node = inv_eclosure->elems[ecl_idx];

        if (!re_node_set_contains(&except_nodes, cur_node))
        {
            Idx one_based_idx = re_node_set_contains(dest_nodes, cur_node);
            if (one_based_idx > 0)
            {
                re_node_set_remove_at(dest_nodes, one_based_idx - 1);
            }
        }
    }

    re_node_set_free(&except_nodes);
    return REG_NOERROR;
}

static bool
check_dst_limits (const re_match_context_t *mctx, const re_node_set *limits,
		  Idx dst_node, Idx dst_idx, Idx src_node, Idx src_idx)
{
  const re_dfa_t *const dfa = mctx->dfa;

  const Idx dst_bkref_idx = search_cur_bkref_entry (mctx, dst_idx);
  const Idx src_bkref_idx = search_cur_bkref_entry (mctx, src_idx);

  for (size_t i = 0; i < limits->nelem; ++i)
    {
      const Idx current_limit_elem_idx = limits->elems[i];
      const struct re_backref_cache_entry *current_bkref_entry = &mctx->bkref_ents[current_limit_elem_idx];
      const Idx subexp_idx = dfa->nodes[current_bkref_entry->node].opr.idx;

      const Idx dst_pos = check_dst_limits_calc_pos (mctx, current_limit_elem_idx,
                                                     subexp_idx, dst_node, dst_idx,
                                                     dst_bkref_idx);
      const Idx src_pos = check_dst_limits_calc_pos (mctx, current_limit_elem_idx,
                                                     subexp_idx, src_node, src_idx,
                                                     src_bkref_idx);

      if (src_pos != dst_pos)
        {
          return true;
        }
    }
  return false;
}

static int
check_dst_limits_calc_pos_1 (const re_match_context_t *mctx, int boundaries,
			     Idx subexp_idx, Idx from_node, Idx bkref_idx)
{
  const re_dfa_t *const dfa = mctx->dfa;
  const re_node_set *eclosures = dfa->eclosures + from_node;
  Idx node_idx;

#define BOUNDARY_FLAG_OPEN_SUBEXP  1
#define BOUNDARY_FLAG_CLOSE_SUBEXP 2

#define RESULT_OPEN_SUBEXP_FOUND  -1
#define RESULT_CLOSE_SUBEXP_FOUND  0
#define RESULT_CLOSE_SUBEXP_NOT_FOUND 1
#define RESULT_DEFAULT_NO_OPEN_FOUND 0

  for (node_idx = 0; node_idx < eclosures->nelem; ++node_idx)
    {
      Idx node = eclosures->elems[node_idx];
      switch (dfa->nodes[node].type)
	{
	case OP_BACK_REF:
	  if (bkref_idx != -1)
	    {
	      struct re_backref_cache_entry *ent = mctx->bkref_ents + bkref_idx;
	      do
		{
		  if (ent->node != node)
		    continue;

		  if (subexp_idx < BITSET_WORD_BITS &&
		      !(ent->eps_reachable_subexps_map & ((bitset_word_t) 1 << subexp_idx)))
		    continue;

		  Idx dst_node = dfa->edests[node].elems[0];

		  if (dst_node == from_node)
		    {
		      if (boundaries & BOUNDARY_FLAG_OPEN_SUBEXP)
			return RESULT_OPEN_SUBEXP_FOUND;
		      else
			return RESULT_CLOSE_SUBEXP_FOUND;
		    }

		  int recursive_result =
		    check_dst_limits_calc_pos_1 (mctx, boundaries, subexp_idx,
						 dst_node, bkref_idx);

		  if (recursive_result == RESULT_OPEN_SUBEXP_FOUND)
		    return RESULT_OPEN_SUBEXP_FOUND;

		  if (recursive_result == RESULT_CLOSE_SUBEXP_FOUND &&
                      (boundaries & BOUNDARY_FLAG_CLOSE_SUBEXP))
		    return RESULT_CLOSE_SUBEXP_FOUND;

		  if (subexp_idx < BITSET_WORD_BITS)
		    ent->eps_reachable_subexps_map
		      &= ~((bitset_word_t) 1 << subexp_idx);
		}
	      while (ent++->more);
	    }
	  break;

	case OP_OPEN_SUBEXP:
	  if ((boundaries & BOUNDARY_FLAG_OPEN_SUBEXP) && subexp_idx == dfa->nodes[node].opr.idx)
	    return RESULT_OPEN_SUBEXP_FOUND;
	  break;

	case OP_CLOSE_SUBEXP:
	  if ((boundaries & BOUNDARY_FLAG_CLOSE_SUBEXP) && subexp_idx == dfa->nodes[node].opr.idx)
	    return RESULT_CLOSE_SUBEXP_FOUND;
	  break;

	default:
	    break;
	}
    }

  return (boundaries & BOUNDARY_FLAG_CLOSE_SUBEXP) ? RESULT_CLOSE_SUBEXP_NOT_FOUND : RESULT_DEFAULT_NO_OPEN_FOUND;
#undef BOUNDARY_FLAG_OPEN_SUBEXP
#undef BOUNDARY_FLAG_CLOSE_SUBEXP
#undef RESULT_OPEN_SUBEXP_FOUND
#undef RESULT_CLOSE_SUBEXP_FOUND
#undef RESULT_CLOSE_SUBEXP_NOT_FOUND
#undef RESULT_DEFAULT_NO_OPEN_FOUND
}

enum ReBoundaryFlags
{
  RE_BOUNDARY_NONE = 0,
  RE_BOUNDARY_FROM = 1,
  RE_BOUNDARY_TO   = (1 << 1)
};

static int
check_dst_limits_calc_pos (const re_match_context_t *mctx, Idx limit,
			   Idx subexp_idx, Idx from_node, Idx str_idx,
			   Idx bkref_idx)
{
  const struct re_backref_cache_entry *lim = mctx->bkref_ents + limit;
  int current_boundaries = RE_BOUNDARY_NONE;

  if (str_idx < lim->subexp_from)
    return -1;

  if (str_idx > lim->subexp_to)
    return 1;

  current_boundaries |= (str_idx == lim->subexp_from) ? RE_BOUNDARY_FROM : RE_BOUNDARY_NONE;
  current_boundaries |= (str_idx == lim->subexp_to) ? RE_BOUNDARY_TO : RE_BOUNDARY_NONE;

  if (current_boundaries == RE_BOUNDARY_NONE)
    return 0;

  return check_dst_limits_calc_pos_1 (mctx, current_boundaries, subexp_idx,
				      from_node, bkref_idx);
}

/* Check the limitations of sub expressions LIMITS, and remove the nodes
   which are against limitations from DEST_NODES. */

static Idx
find_subexp_node_in_set (const re_dfa_t *dfa, const re_node_set *nodes,
                        re_token_type_t type, Idx subexp_idx)
{
  for (Idx i = 0; i < nodes->nelem; ++i)
    {
      Idx node = nodes->elems[i];
      if (dfa->nodes[node].type == type && subexp_idx == dfa->nodes[node].opr.idx)
	{
	  return node;
	}
    }
  return -1;
}

static reg_errcode_t
handle_epsilon_source_propagation (const re_dfa_t *dfa, Idx node_to_process,
                                  re_node_set *dest_nodes, const re_node_set *candidates)
{
  reg_errcode_t err = sub_epsilon_src_nodes (dfa, node_to_process, dest_nodes, candidates);
  if (__glibc_unlikely (err != REG_NOERROR))
    {
      return err;
    }
  return REG_NOERROR;
}

static reg_errcode_t
check_subexp_limits (const re_dfa_t *dfa, re_node_set *dest_nodes,
		     const re_node_set *candidates, re_node_set *limits,
		     struct re_backref_cache_entry *bkref_ents, Idx str_idx)
{
  reg_errcode_t err;

  for (Idx lim_idx = 0; lim_idx < limits->nelem; ++lim_idx)
    {
      struct re_backref_cache_entry *ent = bkref_ents + limits->elems[lim_idx];

      if (str_idx <= ent->subexp_from || ent->str_idx < str_idx)
	{
	  continue;
	}

      Idx subexp_idx = dfa->nodes[ent->node].opr.idx;

      if (ent->subexp_to == str_idx)
	{
	  Idx ops_node = find_subexp_node_in_set (dfa, dest_nodes, OP_OPEN_SUBEXP, subexp_idx);
	  Idx cls_node = find_subexp_node_in_set (dfa, dest_nodes, OP_CLOSE_SUBEXP, subexp_idx);

	  if (ops_node >= 0)
	    {
	      err = handle_epsilon_source_propagation (dfa, ops_node, dest_nodes, candidates);
	      if (err != REG_NOERROR)
		{
		  return err;
		}
	    }

	  if (cls_node >= 0)
	    {
	      for (Idx node_idx = 0; node_idx < dest_nodes->nelem; ++node_idx)
		{
		  Idx node = dest_nodes->elems[node_idx];
		  if (!re_node_set_contains (dfa->inveclosures + node, cls_node)
		      && !re_node_set_contains (dfa->eclosures + node, cls_node))
		    {
		      err = handle_epsilon_source_propagation (dfa, node, dest_nodes, candidates);
		      if (err != REG_NOERROR)
			{
			  return err;
			}
		      --node_idx;
		    }
		}
	    }
	}
      else
	{
	  for (Idx node_idx = 0; node_idx < dest_nodes->nelem; ++node_idx)
	    {
	      Idx node = dest_nodes->elems[node_idx];
	      re_token_type_t type = dfa->nodes[node].type;
	      if ((type == OP_CLOSE_SUBEXP || type == OP_OPEN_SUBEXP)
		  && subexp_idx == dfa->nodes[node].opr.idx)
		{
		  err = handle_epsilon_source_propagation (dfa, node, dest_nodes, candidates);
		  if (err != REG_NOERROR)
		    {
		      return err;
		    }
		}
	    }
	}
    }
  return REG_NOERROR;
}

static reg_errcode_t
__attribute_warn_unused_result__
sift_states_bkref (const re_match_context_t *mctx, re_sift_context_t *sctx,
		   Idx str_idx, const re_node_set *candidates)
{
  const re_dfa_t *const dfa = mctx->dfa;
  reg_errcode_t err;
  Idx node_idx, node;
  re_sift_context_t local_sctx;
  Idx first_idx = search_cur_bkref_entry (mctx, str_idx);

  if (first_idx == -1)
    return REG_NOERROR;

  local_sctx.sifted_states = NULL; /* Mark that it hasn't been initialized.  */

  for (node_idx = 0; node_idx < candidates->nelem; ++node_idx)
    {
      Idx enabled_idx;
      re_token_type_t type;
      struct re_backref_cache_entry *entry;
      node = candidates->elems[node_idx];
      type = dfa->nodes[node].type;
      /* Avoid infinite loop for the REs like "()\1+".  */
      if (node == sctx->last_node && str_idx == sctx->last_str_idx)
	continue;
      if (type != OP_BACK_REF)
	continue;

      entry = mctx->bkref_ents + first_idx;
      enabled_idx = first_idx;
      do
	{
	  Idx subexp_len;
	  Idx to_idx;
	  Idx dst_node;
	  bool ok;
	  re_dfastate_t *cur_state;

	  if (entry->node != node)
	    continue;
	  subexp_len = entry->subexp_to - entry->subexp_from;
	  to_idx = str_idx + subexp_len;
	  dst_node = (subexp_len ? dfa->nexts[node]
		      : dfa->edests[node].elems[0]);

	  if (to_idx > sctx->last_str_idx
	      || sctx->sifted_states[to_idx] == NULL
	      || !STATE_NODE_CONTAINS (sctx->sifted_states[to_idx], dst_node)
	      || check_dst_limits (mctx, &sctx->limits, node,
				   str_idx, dst_node, to_idx))
	    continue;

	  if (local_sctx.sifted_states == NULL)
	    {
	      local_sctx = *sctx;
	      err = re_node_set_init_copy (&local_sctx.limits, &sctx->limits);
	      if (__glibc_unlikely (err != REG_NOERROR))
		goto free_return;
	    }
	  local_sctx.last_node = node;
	  local_sctx.last_str_idx = str_idx;
	  ok = re_node_set_insert (&local_sctx.limits, enabled_idx);
	  if (__glibc_unlikely (! ok))
	    {
	      err = REG_ESPACE;
	      goto free_return;
	    }
	  cur_state = local_sctx.sifted_states[str_idx];
	  err = sift_states_backward (mctx, &local_sctx);
	  if (__glibc_unlikely (err != REG_NOERROR))
	    goto free_return;
	  if (sctx->limited_states != NULL)
	    {
	      err = merge_state_array (dfa, sctx->limited_states,
				       local_sctx.sifted_states,
				       str_idx + 1);
	      if (__glibc_unlikely (err != REG_NOERROR))
		goto free_return;
	    }
	  local_sctx.sifted_states[str_idx] = cur_state;
	  re_node_set_remove (&local_sctx.limits, enabled_idx);

	  /* mctx->bkref_ents may have changed, reload the pointer.  */
	  entry = mctx->bkref_ents + enabled_idx;
	}
      while (enabled_idx++, entry++->more);
    }
  err = REG_NOERROR;
 free_return:
  if (local_sctx.sifted_states != NULL)
    {
      re_node_set_free (&local_sctx.limits);
    }

  return err;
}


#ifdef RE_ENABLE_I18N
static int
sift_states_iter_mb (const re_match_context_t *mctx, re_sift_context_t *sctx,
		     Idx node_idx, Idx str_idx, Idx max_str_idx)
{
  const re_dfa_t *const dfa = mctx->dfa;
  int naccepted;
  /* Check the node can accept "multi byte".  */
  naccepted = check_node_accept_bytes (dfa, node_idx, &mctx->input, str_idx);
  if (naccepted > 0 && str_idx + naccepted <= max_str_idx
      && !STATE_NODE_CONTAINS (sctx->sifted_states[str_idx + naccepted],
			       dfa->nexts[node_idx]))
    /* The node can't accept the "multi byte", or the
       destination was already thrown away, then the node
       couldn't accept the current input "multi byte".   */
    naccepted = 0;
  /* Otherwise, it is sure that the node could accept
     'naccepted' bytes input.  */
  return naccepted;
}
#endif /* RE_ENABLE_I18N */


/* Functions for state transition.  */

/* Return the next state to which the current state STATE will transit by
   accepting the current input byte, and update STATE_LOG if necessary.
   Return NULL on failure.
   If STATE can accept a multibyte char/collating element/back reference
   update the destination of STATE_LOG.  */

static re_dfastate_t *
__attribute_warn_unused_result__
transit_state (reg_errcode_t *err, re_match_context_t *mctx,
	       re_dfastate_t *state)
{
  re_dfastate_t **trtable;
  unsigned char ch;

#ifdef RE_ENABLE_I18N
  /* If the current state can accept multibyte.  */
  if (__glibc_unlikely (state->accept_mb))
    {
      *err = transit_state_mb (mctx, state);
      if (__glibc_unlikely (*err != REG_NOERROR))
	return NULL;
    }
#endif /* RE_ENABLE_I18N */

  /* Then decide the next state with the single byte.  */
#if 0
  if (0)
    /* don't use transition table  */
    return transit_state_sb (err, mctx, state);
#endif

  /* Use transition table  */
  ch = re_string_fetch_byte (&mctx->input);
  for (;;)
    {
      trtable = state->trtable;
      if (__glibc_likely (trtable != NULL))
	return trtable[ch];

      trtable = state->word_trtable;
      if (__glibc_likely (trtable != NULL))
	{
	  unsigned int context;
	  context
	    = re_string_context_at (&mctx->input,
				    re_string_cur_idx (&mctx->input) - 1,
				    mctx->eflags);
	  if (IS_WORD_CONTEXT (context))
	    return trtable[ch + SBC_MAX];
	  else
	    return trtable[ch];
	}

      if (!build_trtable (mctx->dfa, state))
	{
	  *err = REG_ESPACE;
	  return NULL;
	}

      /* Retry, we now have a transition table.  */
    }
}

/* Update the state_log if we need */
static re_dfastate_t *
merge_state_with_log (reg_errcode_t *err, re_match_context_t *mctx,
		      re_dfastate_t *next_state)
{
  const re_dfa_t *const dfa = mctx->dfa;
  Idx cur_idx = re_string_cur_idx (&mctx->input);

  if (mctx->state_log[cur_idx] == NULL || cur_idx > mctx->state_log_top)
    {
      mctx->state_log[cur_idx] = next_state;
      if (cur_idx > mctx->state_log_top)
        mctx->state_log_top = cur_idx;
    }
  else
    {
      re_dfastate_t *existing_state = mctx->state_log[cur_idx];
      re_node_set merged_nodes;
      re_node_set *log_nodes = existing_state->entrance_nodes;
      re_node_set *table_nodes = NULL;
      int needs_free = 0;

      if (next_state != NULL)
        {
          table_nodes = next_state->entrance_nodes;
          *err = re_node_set_init_union (&merged_nodes, table_nodes, log_nodes);
          if (__glibc_unlikely (*err != REG_NOERROR))
            return NULL;
          needs_free = 1;
        }
      else
        {
          merged_nodes = *log_nodes;
        }

      unsigned int context = re_string_context_at (&mctx->input, cur_idx - 1, mctx->eflags);
      next_state = re_acquire_state_context (err, dfa, &merged_nodes, context);

      if (needs_free)
        re_node_set_free (&merged_nodes);

      if (__glibc_unlikely (*err != REG_NOERROR))
        return NULL;

      mctx->state_log[cur_idx] = next_state;
    }

  if (__glibc_unlikely (dfa->nbackref) && next_state != NULL)
    {
      *err = check_subexp_matching_top (mctx, &next_state->nodes, cur_idx);
      if (__glibc_unlikely (*err != REG_NOERROR))
	return NULL;

      if (next_state->has_backref)
	{
	  *err = transit_state_bkref (mctx, &next_state->nodes);
	  if (__glibc_unlikely (*err != REG_NOERROR))
	    return NULL;
	  next_state = mctx->state_log[cur_idx];
	}
    }

  return next_state;
}

/* Skip bytes in the input that correspond to part of a
   multi-byte match, then look in the log for a state
   from which to restart matching.  */
static re_dfastate_t *
find_recover_state (reg_errcode_t *err, re_match_context_t *mctx)
{
  re_dfastate_t *current_state = NULL;

  while (*err == REG_NOERROR && current_state == NULL)
    {
      Idx max_log_idx = mctx->state_log_top;
      Idx current_str_idx = re_string_cur_idx (&mctx->input);

      bool log_entry_found_in_iteration = false;
      for (current_str_idx++; current_str_idx <= max_log_idx; current_str_idx++)
        {
          re_string_skip_bytes (&mctx->input, 1);
          if (mctx->state_log[current_str_idx] != NULL)
            {
              log_entry_found_in_iteration = true;
              break;
            }
        }

      if (!log_entry_found_in_iteration)
        {
          return NULL;
        }

      current_state = merge_state_with_log (err, mctx, NULL);
    }

  return current_state;
}

/* Helper functions for transit_state.  */

/* From the node set CUR_NODES, pick up the nodes whose types are
   OP_OPEN_SUBEXP and which have corresponding back references in the regular
   expression. And register them to use them later for evaluating the
   corresponding back references.  */

static reg_errcode_t
check_subexp_matching_top (re_match_context_t *mctx, re_node_set *cur_nodes,
			   Idx str_idx)
{
  const re_dfa_t *const dfa = mctx->dfa;
  reg_errcode_t err = REG_NOERROR;

  for (Idx i = 0; i < cur_nodes->nelem; ++i)
    {
      const Idx current_node_idx = cur_nodes->elems[i];
      const re_node_t *const node_data = &dfa->nodes[current_node_idx];

      const bool is_open_subexp_type = (node_data->type == OP_OPEN_SUBEXP);
      const bool is_idx_within_bitset_bounds = (node_data->opr.idx < BITSET_WORD_BITS);
      
      // Check if the specific subexpression index (node_data->opr.idx)
      // is marked in the DFA's used_bkref_map.
      // This bitwise operation is safe due to the short-circuiting of
      // the '&&' operator below, ensuring 'is_idx_within_bitset_bounds'
      // is true before this expression is evaluated.
      const bool is_backref_used_for_this_idx =
          (dfa->used_bkref_map & ((bitset_word_t) 1 << node_data->opr.idx));

      if (is_open_subexp_type &&
          is_idx_within_bitset_bounds &&
          is_backref_used_for_this_idx)
	{
	  err = match_ctx_add_subtop (mctx, current_node_idx, str_idx);
	  if (__glibc_unlikely (err != REG_NOERROR))
	    {
	      return err;
	    }
	}
    }
  return err;
}

#if 0
/* Return the next state to which the current state STATE will transit by
   accepting the current input byte.  Return NULL on failure.  */

static re_dfastate_t *
transit_state_sb (reg_errcode_t *err, re_match_context_t *mctx,
		  re_dfastate_t *state)
{
  const re_dfa_t *const dfa = mctx->dfa;
  re_node_set next_nodes;
  re_dfastate_t *next_state;
  Idx node_cnt, cur_str_idx = re_string_cur_idx (&mctx->input);
  unsigned int context;

  *err = re_node_set_alloc (&next_nodes, state->nodes.nelem + 1);
  if (__glibc_unlikely (*err != REG_NOERROR))
    return NULL;
  for (node_cnt = 0; node_cnt < state->nodes.nelem; ++node_cnt)
    {
      Idx cur_node = state->nodes.elems[node_cnt];
      if (check_node_accept (mctx, dfa->nodes + cur_node, cur_str_idx))
	{
	  *err = re_node_set_merge (&next_nodes,
				    dfa->eclosures + dfa->nexts[cur_node]);
	  if (__glibc_unlikely (*err != REG_NOERROR))
	    {
	      re_node_set_free (&next_nodes);
	      return NULL;
	    }
	}
    }
  context = re_string_context_at (&mctx->input, cur_str_idx, mctx->eflags);
  next_state = re_acquire_state_context (err, dfa, &next_nodes, context);
  /* We don't need to check errors here, since the return value of
     this function is next_state and ERR is already set.  */

  re_node_set_free (&next_nodes);
  re_string_skip_bytes (&mctx->input, 1);
  return next_state;
}
#endif

#ifdef RE_ENABLE_I18N
static reg_errcode_t
transit_state_mb (re_match_context_t *mctx, re_dfastate_t *pstate)
{
  const re_dfa_t *const dfa = mctx->dfa;
  reg_errcode_t err;
  Idx i;

  for (i = 0; i < pstate->nodes.nelem; ++i)
    {
      re_node_set dest_nodes, *new_nodes;
      Idx cur_node_idx = pstate->nodes.elems[i];
      int naccepted;
      Idx dest_idx;
      unsigned int context;
      re_dfastate_t *dest_state;

      if (!dfa->nodes[cur_node_idx].accept_mb)
	continue;

      if (dfa->nodes[cur_node_idx].constraint)
	{
	  context = re_string_context_at (&mctx->input,
					  re_string_cur_idx (&mctx->input),
					  mctx->eflags);
	  if (NOT_SATISFY_NEXT_CONSTRAINT (dfa->nodes[cur_node_idx].constraint,
					   context))
	    continue;
	}

      /* How many bytes the node can accept?  */
      naccepted = check_node_accept_bytes (dfa, cur_node_idx, &mctx->input,
					   re_string_cur_idx (&mctx->input));
      if (naccepted == 0)
	continue;

      /* The node can accepts 'naccepted' bytes.  */
      dest_idx = re_string_cur_idx (&mctx->input) + naccepted;
      mctx->max_mb_elem_len = ((mctx->max_mb_elem_len < naccepted) ? naccepted
			       : mctx->max_mb_elem_len);
      err = clean_state_log_if_needed (mctx, dest_idx);
      if (__glibc_unlikely (err != REG_NOERROR))
	return err;
      DEBUG_ASSERT (dfa->nexts[cur_node_idx] != -1);
      new_nodes = dfa->eclosures + dfa->nexts[cur_node_idx];

      dest_state = mctx->state_log[dest_idx];
      if (dest_state == NULL)
	dest_nodes = *new_nodes;
      else
	{
	  err = re_node_set_init_union (&dest_nodes,
					dest_state->entrance_nodes, new_nodes);
	  if (__glibc_unlikely (err != REG_NOERROR))
	    return err;
	}
      context = re_string_context_at (&mctx->input, dest_idx - 1,
				      mctx->eflags);
      mctx->state_log[dest_idx]
	= re_acquire_state_context (&err, dfa, &dest_nodes, context);
      if (dest_state != NULL)
	re_node_set_free (&dest_nodes);
      if (__glibc_unlikely (mctx->state_log[dest_idx] == NULL
			    && err != REG_NOERROR))
	return err;
    }
  return REG_NOERROR;
}
#endif /* RE_ENABLE_I18N */

static reg_errcode_t
update_state_log_entry_internal(re_match_context_t *mctx, Idx dest_str_idx,
                                const re_node_set *source_nodes, unsigned int context)
{
  reg_errcode_t err = REG_NOERROR;
  re_dfastate_t *dest_state = mctx->state_log[dest_str_idx];
  re_node_set combined_nodes_storage;
  const re_node_set *nodes_to_add = source_nodes;
  bool needs_free = false;

  if (dest_state != NULL)
    {
      err = re_node_set_init_union(&combined_nodes_storage, dest_state->entrance_nodes, source_nodes);
      if (__glibc_unlikely(err != REG_NOERROR))
        {
          return err;
        }
      nodes_to_add = &combined_nodes_storage;
      needs_free = true;
    }

  mctx->state_log[dest_str_idx]
    = re_acquire_state_context(&err, mctx->dfa, nodes_to_add, context);

  if (needs_free)
    {
      re_node_set_free(&combined_nodes_storage);
    }

  if (__glibc_unlikely(mctx->state_log[dest_str_idx] == NULL && err == REG_NOERROR))
    {
      err = REG_NOMEM;
    }

  return err;
}

static reg_errcode_t
process_single_backref_cache_entry(re_match_context_t *mctx, Idx node_idx, Idx cur_str_idx,
                                     struct re_backref_cache_entry *bkref_ent)
{
  reg_errcode_t err = REG_NOERROR;
  const re_dfa_t *const dfa = mctx->dfa;

  if (bkref_ent->node != node_idx || bkref_ent->str_idx != cur_str_idx)
    {
      return REG_NOERROR;
    }

  Idx subexp_len = bkref_ent->subexp_to - bkref_ent->subexp_from;
  const re_node_set *new_dest_nodes;

  if (subexp_len == 0)
    {
      DEBUG_ASSERT(dfa->edests[node_idx].nelem > 0);
      new_dest_nodes = dfa->eclosures + dfa->edests[node_idx].elems[0];
    }
  else
    {
      DEBUG_ASSERT(dfa->nexts[node_idx] != -1);
      new_dest_nodes = dfa->eclosures + dfa->nexts[node_idx];
    }

  Idx dest_str_idx = cur_str_idx + subexp_len;
  unsigned int dest_context = re_string_context_at(&mctx->input, dest_str_idx - 1, mctx->eflags);

  // Capture prev_nelem at cur_str_idx *before* updating state log for dest_str_idx and before potential recursive calls.
  Idx prev_nelem_at_cur_str = (mctx->state_log[cur_str_idx] == NULL) ? 0 : mctx->state_log[cur_str_idx]->nodes.nelem;

  err = update_state_log_entry_internal(mctx, dest_str_idx, new_dest_nodes, dest_context);
  if (__glibc_unlikely(err != REG_NOERROR))
    {
      return err;
    }

  // Recursively check for epsilon transit if the backreference is zero-length,
  // and if there has been a change at the current string index.
  // The condition `mctx->state_log[cur_str_idx]->nodes.nelem > prev_nelem_at_cur_str`
  // as in the original code, implies `mctx->state_log[cur_str_idx]` is not NULL at this point.
  // Adding an explicit NULL check for robustness.
  if (subexp_len == 0 && mctx->state_log[cur_str_idx] != NULL && mctx->state_log[cur_str_idx]->nodes.nelem > prev_nelem_at_cur_str)
    {
      err = check_subexp_matching_top(mctx, new_dest_nodes, cur_str_idx);
      if (__glibc_unlikely(err != REG_NOERROR))
        {
          return err;
        }

      err = transit_state_bkref(mctx, new_dest_nodes);
      if (__glibc_unlikely(err != REG_NOERROR))
        {
          return err;
        }
    }

  return REG_NOERROR;
}

static reg_errcode_t
transit_state_bkref (re_match_context_t *mctx, const re_node_set *nodes)
{
  const re_dfa_t *const dfa = mctx->dfa;
  reg_errcode_t err = REG_NOERROR;
  Idx cur_str_idx = re_string_cur_idx (&mctx->input);

  for (Idx i = 0; i < nodes->nelem; ++i)
    {
      Idx node_idx = nodes->elems[i];
      const re_token_t *node = dfa->nodes + node_idx;

      if (node->type != OP_BACK_REF)
	    {
	      continue;
	    }

      if (node->constraint)
	    {
	      unsigned int context = re_string_context_at (&mctx->input, cur_str_idx, mctx->eflags);
	      if (NOT_SATISFY_NEXT_CONSTRAINT (node->constraint, context))
	        {
	          continue;
	        }
	    }

      Idx initial_bkref_ents_count = mctx->nbkref_ents;

      err = get_subexp (mctx, node_idx, cur_str_idx);
      if (__glibc_unlikely (err != REG_NOERROR))
	    {
	      return err;
	    }

      for (Idx bkc_idx = initial_bkref_ents_count; bkc_idx < mctx->nbkref_ents; ++bkc_idx)
	    {
	      err = process_single_backref_cache_entry(mctx, node_idx, cur_str_idx, mctx->bkref_ents + bkc_idx);
	      if (__glibc_unlikely(err != REG_NOERROR))
	        {
	          return err;
	        }
	    }
    }
  return REG_NOERROR;
}

/* Enumerate all the candidates which the backreference BKREF_NODE can match
   at BKREF_STR_IDX, and register them by match_ctx_add_entry().
   Note that we might collect inappropriate candidates here.
   However, the cost of checking them strictly here is too high, then we
   delay these checking for prune_impossible_nodes().  */

static reg_errcode_t
__attribute_warn_unused_result__
get_subexp (re_match_context_t *mctx, Idx bkref_node, Idx bkref_str_idx)
{
  const re_dfa_t *const dfa = mctx->dfa;
  Idx subexp_num, sub_top_idx;
  const char *buf = (const char *) re_string_get_buffer (&mctx->input);
  /* Return if we have already checked BKREF_NODE at BKREF_STR_IDX.  */
  Idx cache_idx = search_cur_bkref_entry (mctx, bkref_str_idx);
  if (cache_idx != -1)
    {
      const struct re_backref_cache_entry *entry
	= mctx->bkref_ents + cache_idx;
      do
	if (entry->node == bkref_node)
	  return REG_NOERROR; /* We already checked it.  */
      while (entry++->more);
    }

  subexp_num = dfa->nodes[bkref_node].opr.idx;

  /* For each sub expression  */
  for (sub_top_idx = 0; sub_top_idx < mctx->nsub_tops; ++sub_top_idx)
    {
      reg_errcode_t err;
      re_sub_match_top_t *sub_top = mctx->sub_tops[sub_top_idx];
      re_sub_match_last_t *sub_last;
      Idx sub_last_idx, sl_str, bkref_str_off;

      if (dfa->nodes[sub_top->node].opr.idx != subexp_num)
	continue; /* It isn't related.  */

      sl_str = sub_top->str_idx;
      bkref_str_off = bkref_str_idx;
      /* At first, check the last node of sub expressions we already
	 evaluated.  */
      for (sub_last_idx = 0; sub_last_idx < sub_top->nlasts; ++sub_last_idx)
	{
	  regoff_t sl_str_diff;
	  sub_last = sub_top->lasts[sub_last_idx];
	  sl_str_diff = sub_last->str_idx - sl_str;
	  /* The matched string by the sub expression match with the substring
	     at the back reference?  */
	  if (sl_str_diff > 0)
	    {
	      if (__glibc_unlikely (bkref_str_off + sl_str_diff
				    > mctx->input.valid_len))
		{
		  /* Not enough chars for a successful match.  */
		  if (bkref_str_off + sl_str_diff > mctx->input.len)
		    break;

		  err = clean_state_log_if_needed (mctx,
						   bkref_str_off
						   + sl_str_diff);
		  if (__glibc_unlikely (err != REG_NOERROR))
		    return err;
		  buf = (const char *) re_string_get_buffer (&mctx->input);
		}
	      if (memcmp (buf + bkref_str_off, buf + sl_str, sl_str_diff) != 0)
		/* We don't need to search this sub expression any more.  */
		break;
	    }
	  bkref_str_off += sl_str_diff;
	  sl_str += sl_str_diff;
	  err = get_subexp_sub (mctx, sub_top, sub_last, bkref_node,
				bkref_str_idx);

	  /* Reload buf, since the preceding call might have reallocated
	     the buffer.  */
	  buf = (const char *) re_string_get_buffer (&mctx->input);

	  if (err == REG_NOMATCH)
	    continue;
	  if (__glibc_unlikely (err != REG_NOERROR))
	    return err;
	}

      if (sub_last_idx < sub_top->nlasts)
	continue;
      if (sub_last_idx > 0)
	++sl_str;
      /* Then, search for the other last nodes of the sub expression.  */
      for (; sl_str <= bkref_str_idx; ++sl_str)
	{
	  Idx cls_node;
	  regoff_t sl_str_off;
	  const re_node_set *nodes;
	  sl_str_off = sl_str - sub_top->str_idx;
	  /* The matched string by the sub expression match with the substring
	     at the back reference?  */
	  if (sl_str_off > 0)
	    {
	      if (__glibc_unlikely (bkref_str_off >= mctx->input.valid_len))
		{
		  /* If we are at the end of the input, we cannot match.  */
		  if (bkref_str_off >= mctx->input.len)
		    break;

		  err = extend_buffers (mctx, bkref_str_off + 1);
		  if (__glibc_unlikely (err != REG_NOERROR))
		    return err;

		  buf = (const char *) re_string_get_buffer (&mctx->input);
		}
	      if (buf [bkref_str_off++] != buf[sl_str - 1])
		break; /* We don't need to search this sub expression
			  any more.  */
	    }
	  if (mctx->state_log[sl_str] == NULL)
	    continue;
	  /* Does this state have a ')' of the sub expression?  */
	  nodes = &mctx->state_log[sl_str]->nodes;
	  cls_node = find_subexp_node (dfa, nodes, subexp_num,
				       OP_CLOSE_SUBEXP);
	  if (cls_node == -1)
	    continue; /* No.  */
	  if (sub_top->path == NULL)
	    {
	      sub_top->path = calloc (sizeof (state_array_t),
				      sl_str - sub_top->str_idx + 1);
	      if (sub_top->path == NULL)
		return REG_ESPACE;
	    }
	  /* Can the OP_OPEN_SUBEXP node arrive the OP_CLOSE_SUBEXP node
	     in the current context?  */
	  err = check_arrival (mctx, sub_top->path, sub_top->node,
			       sub_top->str_idx, cls_node, sl_str,
			       OP_CLOSE_SUBEXP);
	  if (err == REG_NOMATCH)
	      continue;
	  if (__glibc_unlikely (err != REG_NOERROR))
	      return err;
	  sub_last = match_ctx_add_sublast (sub_top, cls_node, sl_str);
	  if (__glibc_unlikely (sub_last == NULL))
	    return REG_ESPACE;
	  err = get_subexp_sub (mctx, sub_top, sub_last, bkref_node,
				bkref_str_idx);
	  buf = (const char *) re_string_get_buffer (&mctx->input);
	  if (err == REG_NOMATCH)
	    continue;
	  if (__glibc_unlikely (err != REG_NOERROR))
	    return err;
	}
    }
  return REG_NOERROR;
}

/* Helper functions for get_subexp().  */

/* Check SUB_LAST can arrive to the back reference BKREF_NODE at BKREF_STR.
   If it can arrive, register the sub expression expressed with SUB_TOP
   and SUB_LAST.  */

static reg_errcode_t
get_subexp_sub (re_match_context_t *mctx, const re_sub_match_top_t *sub_top,
		re_sub_match_last_t *sub_last, Idx bkref_node, Idx bkref_str)
{
  reg_errcode_t err_code;

  err_code = check_arrival (mctx, &sub_last->path, sub_last->node,
                            sub_last->str_idx, bkref_node, bkref_str,
                            OP_OPEN_SUBEXP);
  if (err_code != REG_NOERROR)
  {
    return err_code;
  }

  err_code = match_ctx_add_entry (mctx, bkref_node, bkref_str, sub_top->str_idx,
                                  sub_last->str_idx);
  if (__glibc_unlikely (err_code != REG_NOERROR))
  {
    return err_code;
  }

  Idx to_idx = bkref_str + sub_last->str_idx - sub_top->str_idx;
  return clean_state_log_if_needed (mctx, to_idx);
}

/* Find the first node which is '(' or ')' and whose index is SUBEXP_IDX.
   Search '(' if FL_OPEN, or search ')' otherwise.
   TODO: This function isn't efficient...
	 Because there might be more than one nodes whose types are
	 OP_OPEN_SUBEXP and whose index is SUBEXP_IDX, we must check all
	 nodes.
	 E.g. RE: (a){2}  */

static Idx
find_subexp_node (const re_dfa_t *dfa, const re_node_set *nodes,
		  Idx subexp_idx, int type)
{
  if (dfa == NULL || nodes == NULL || dfa->nodes == NULL || nodes->elems == NULL)
    {
      return -1;
    }

  for (size_t cls_idx = 0; cls_idx < nodes->nelem; ++cls_idx)
    {
      Idx cls_node = nodes->elems[cls_idx];
      const re_token_t *node = dfa->nodes + cls_node;
      if (node->type == type && node->opr.idx == subexp_idx)
        {
          return cls_node;
        }
    }

  return -1;
}

/* Check whether the node TOP_NODE at TOP_STR can arrive to the node
   LAST_NODE at LAST_STR.  We record the path onto PATH since it will be
   heavily reused.
   Return REG_NOERROR if it can arrive, REG_NOMATCH if it cannot,
   REG_ESPACE if memory is exhausted.  */

static reg_errcode_t
__attribute_warn_unused_result__
check_arrival (re_match_context_t *mctx, state_array_t *path, Idx top_node,
	       Idx top_str, Idx last_node, Idx last_str, int type)
{
  const re_dfa_t *const dfa = mctx->dfa;
  reg_errcode_t err = REG_NOERROR;
  Idx subexp_num, backup_cur_idx, str_idx, null_cnt;
  re_dfastate_t *cur_state = NULL;
  re_node_set *cur_nodes, next_nodes;
  re_dfastate_t **backup_state_log;
  unsigned int context;

  subexp_num = dfa->nodes[top_node].opr.idx;
  /* Extend the buffer if we need.  */
  if (__glibc_unlikely (path->alloc < last_str + mctx->max_mb_elem_len + 1))
    {
      re_dfastate_t **new_array;
      Idx old_alloc = path->alloc;
      Idx incr_alloc = last_str + mctx->max_mb_elem_len + 1;
      Idx new_alloc;
      if (__glibc_unlikely (IDX_MAX - old_alloc < incr_alloc))
	return REG_ESPACE;
      new_alloc = old_alloc + incr_alloc;
      if (__glibc_unlikely (SIZE_MAX / sizeof (re_dfastate_t *) < new_alloc))
	return REG_ESPACE;
      new_array = re_realloc (path->array, re_dfastate_t *, new_alloc);
      if (__glibc_unlikely (new_array == NULL))
	return REG_ESPACE;
      path->array = new_array;
      path->alloc = new_alloc;
      memset (new_array + old_alloc, '\0',
	      sizeof (re_dfastate_t *) * (path->alloc - old_alloc));
    }

  str_idx = path->next_idx ? path->next_idx : top_str;

  /* Temporary modify MCTX.  */
  backup_state_log = mctx->state_log;
  backup_cur_idx = mctx->input.cur_idx;
  mctx->state_log = path->array;
  mctx->input.cur_idx = str_idx;

  /* Setup initial node set.  */
  context = re_string_context_at (&mctx->input, str_idx - 1, mctx->eflags);
  if (str_idx == top_str)
    {
      err = re_node_set_init_1 (&next_nodes, top_node);
      if (__glibc_unlikely (err != REG_NOERROR))
	return err;
      err = check_arrival_expand_ecl (dfa, &next_nodes, subexp_num, type);
      if (__glibc_unlikely (err != REG_NOERROR))
	{
	  re_node_set_free (&next_nodes);
	  return err;
	}
    }
  else
    {
      cur_state = mctx->state_log[str_idx];
      if (cur_state && cur_state->has_backref)
	{
	  err = re_node_set_init_copy (&next_nodes, &cur_state->nodes);
	  if (__glibc_unlikely (err != REG_NOERROR))
	    return err;
	}
      else
	re_node_set_init_empty (&next_nodes);
    }
  if (str_idx == top_str || (cur_state && cur_state->has_backref))
    {
      if (next_nodes.nelem)
	{
	  err = expand_bkref_cache (mctx, &next_nodes, str_idx,
				    subexp_num, type);
	  if (__glibc_unlikely (err != REG_NOERROR))
	    {
	      re_node_set_free (&next_nodes);
	      return err;
	    }
	}
      cur_state = re_acquire_state_context (&err, dfa, &next_nodes, context);
      if (__glibc_unlikely (cur_state == NULL && err != REG_NOERROR))
	{
	  re_node_set_free (&next_nodes);
	  return err;
	}
      mctx->state_log[str_idx] = cur_state;
    }

  for (null_cnt = 0; str_idx < last_str && null_cnt <= mctx->max_mb_elem_len;)
    {
      re_node_set_empty (&next_nodes);
      if (mctx->state_log[str_idx + 1])
	{
	  err = re_node_set_merge (&next_nodes,
				   &mctx->state_log[str_idx + 1]->nodes);
	  if (__glibc_unlikely (err != REG_NOERROR))
	    {
	      re_node_set_free (&next_nodes);
	      return err;
	    }
	}
      if (cur_state)
	{
	  err = check_arrival_add_next_nodes (mctx, str_idx,
					      &cur_state->non_eps_nodes,
					      &next_nodes);
	  if (__glibc_unlikely (err != REG_NOERROR))
	    {
	      re_node_set_free (&next_nodes);
	      return err;
	    }
	}
      ++str_idx;
      if (next_nodes.nelem)
	{
	  err = check_arrival_expand_ecl (dfa, &next_nodes, subexp_num, type);
	  if (__glibc_unlikely (err != REG_NOERROR))
	    {
	      re_node_set_free (&next_nodes);
	      return err;
	    }
	  err = expand_bkref_cache (mctx, &next_nodes, str_idx,
				    subexp_num, type);
	  if (__glibc_unlikely (err != REG_NOERROR))
	    {
	      re_node_set_free (&next_nodes);
	      return err;
	    }
	}
      context = re_string_context_at (&mctx->input, str_idx - 1, mctx->eflags);
      cur_state = re_acquire_state_context (&err, dfa, &next_nodes, context);
      if (__glibc_unlikely (cur_state == NULL && err != REG_NOERROR))
	{
	  re_node_set_free (&next_nodes);
	  return err;
	}
      mctx->state_log[str_idx] = cur_state;
      null_cnt = cur_state == NULL ? null_cnt + 1 : 0;
    }
  re_node_set_free (&next_nodes);
  cur_nodes = (mctx->state_log[last_str] == NULL ? NULL
	       : &mctx->state_log[last_str]->nodes);
  path->next_idx = str_idx;

  /* Fix MCTX.  */
  mctx->state_log = backup_state_log;
  mctx->input.cur_idx = backup_cur_idx;

  /* Then check the current node set has the node LAST_NODE.  */
  if (cur_nodes != NULL && re_node_set_contains (cur_nodes, last_node))
    return REG_NOERROR;

  return REG_NOMATCH;
}

/* Helper functions for check_arrival.  */

/* Calculate the destination nodes of CUR_NODES at STR_IDX, and append them
   to NEXT_NODES.
   TODO: This function is similar to the functions transit_state*(),
	 however this function has many additional works.
	 Can't we unify them?  */

static reg_errcode_t
__attribute_warn_unused_result__
check_arrival_add_next_nodes (re_match_context_t *mctx, Idx str_idx,
			      re_node_set *cur_nodes, re_node_set *next_nodes)
{
  const re_dfa_t *const dfa = mctx->dfa;
  bool ok;
  Idx cur_idx;
#ifdef RE_ENABLE_I18N
  reg_errcode_t err = REG_NOERROR;
#endif
  re_node_set union_set;
  re_node_set_init_empty (&union_set);
  for (cur_idx = 0; cur_idx < cur_nodes->nelem; ++cur_idx)
    {
      int naccepted = 0;
      Idx cur_node = cur_nodes->elems[cur_idx];
      DEBUG_ASSERT (!IS_EPSILON_NODE (dfa->nodes[cur_node].type));

#ifdef RE_ENABLE_I18N
      /* If the node may accept "multi byte".  */
      if (dfa->nodes[cur_node].accept_mb)
	{
	  naccepted = check_node_accept_bytes (dfa, cur_node, &mctx->input,
					       str_idx);
	  if (naccepted > 1)
	    {
	      re_dfastate_t *dest_state;
	      Idx next_node = dfa->nexts[cur_node];
	      Idx next_idx = str_idx + naccepted;
	      dest_state = mctx->state_log[next_idx];
	      re_node_set_empty (&union_set);
	      if (dest_state)
		{
		  err = re_node_set_merge (&union_set, &dest_state->nodes);
		  if (__glibc_unlikely (err != REG_NOERROR))
		    {
		      re_node_set_free (&union_set);
		      return err;
		    }
		}
	      ok = re_node_set_insert (&union_set, next_node);
	      if (__glibc_unlikely (! ok))
		{
		  re_node_set_free (&union_set);
		  return REG_ESPACE;
		}
	      mctx->state_log[next_idx] = re_acquire_state (&err, dfa,
							    &union_set);
	      if (__glibc_unlikely (mctx->state_log[next_idx] == NULL
				    && err != REG_NOERROR))
		{
		  re_node_set_free (&union_set);
		  return err;
		}
	    }
	}
#endif /* RE_ENABLE_I18N */
      if (naccepted
	  || check_node_accept (mctx, dfa->nodes + cur_node, str_idx))
	{
	  ok = re_node_set_insert (next_nodes, dfa->nexts[cur_node]);
	  if (__glibc_unlikely (! ok))
	    {
	      re_node_set_free (&union_set);
	      return REG_ESPACE;
	    }
	}
    }
  re_node_set_free (&union_set);
  return REG_NOERROR;
}

/* For all the nodes in CUR_NODES, add the epsilon closures of them to
   CUR_NODES, however exclude the nodes which are:
    - inside the sub expression whose number is EX_SUBEXP, if FL_OPEN.
    - out of the sub expression whose number is EX_SUBEXP, if !FL_OPEN.
*/

static reg_errcode_t
check_arrival_expand_ecl (const re_dfa_t *dfa, re_node_set *cur_nodes,
			  Idx ex_subexp, int type)
{
  reg_errcode_t err = REG_NOERROR;
  Idx idx;
  re_node_set new_nodes;

  DEBUG_ASSERT (cur_nodes->nelem);

  err = re_node_set_alloc (&new_nodes, cur_nodes->nelem);
  if (__glibc_unlikely (err != REG_NOERROR))
    return err;

  for (idx = 0; idx < cur_nodes->nelem; ++idx)
    {
      Idx cur_node = cur_nodes->elems[idx];
      const re_node_set *eclosure = dfa->eclosures + cur_node;

      if (find_subexp_node (dfa, eclosure, ex_subexp, type) == -1)
	{
	  err = re_node_set_merge (&new_nodes, eclosure);
	}
      else
	{
	  err = check_arrival_expand_ecl_sub (dfa, &new_nodes, cur_node,
					      ex_subexp, type);
	}

      if (__glibc_unlikely (err != REG_NOERROR))
	{
	  goto cleanup;
	}
    }

  re_node_set_free (cur_nodes);
  *cur_nodes = new_nodes;
  return REG_NOERROR;

cleanup:
  re_node_set_free (&new_nodes);
  return err;
}

/* Helper function for check_arrival_expand_ecl.
   Check incrementally the epsilon closure of TARGET, and if it isn't
   problematic append it to DST_NODES.  */

static reg_errcode_t
__attribute_warn_unused_result__
check_arrival_expand_ecl_sub (const re_dfa_t *dfa, re_node_set *dst_nodes,
			      Idx target, Idx ex_subexp, int type)
{
  Idx cur_node;
  for (cur_node = target; !re_node_set_contains (dst_nodes, cur_node);)
    {
      bool ok;

      if (dfa->nodes[cur_node].type == type
	  && dfa->nodes[cur_node].opr.idx == ex_subexp)
	{
	  if (type == OP_CLOSE_SUBEXP)
	    {
	      ok = re_node_set_insert (dst_nodes, cur_node);
	      if (__glibc_unlikely (! ok))
		return REG_ESPACE;
	    }
	  break;
	}
      ok = re_node_set_insert (dst_nodes, cur_node);
      if (__glibc_unlikely (! ok))
	return REG_ESPACE;
      if (dfa->edests[cur_node].nelem == 0)
	break;
      if (dfa->edests[cur_node].nelem == 2)
	{
	  reg_errcode_t err;
	  err = check_arrival_expand_ecl_sub (dfa, dst_nodes,
					      dfa->edests[cur_node].elems[1],
					      ex_subexp, type);
	  if (__glibc_unlikely (err != REG_NOERROR))
	    return err;
	}
      cur_node = dfa->edests[cur_node].elems[0];
    }
  return REG_NOERROR;
}


/* For all the back references in the current state, calculate the
   destination of the back references by the appropriate entry
   in MCTX->BKREF_ENTS.  */

static reg_errcode_t
__attribute_warn_unused_result__
expand_bkref_cache (re_match_context_t *mctx, re_node_set *cur_nodes,
		    Idx cur_str, Idx subexp_num, int type)
{
  const re_dfa_t *const dfa = mctx->dfa;
  reg_errcode_t err;
  Idx cache_idx_start = search_cur_bkref_entry (mctx, cur_str);
  struct re_backref_cache_entry *ent;

  if (cache_idx_start == -1)
    return REG_NOERROR;

 restart:
  ent = mctx->bkref_ents + cache_idx_start;
  do
    {
      Idx to_idx, next_node;

      /* Is this entry ENT is appropriate?  */
      if (!re_node_set_contains (cur_nodes, ent->node))
	continue; /* No.  */

      to_idx = cur_str + ent->subexp_to - ent->subexp_from;
      /* Calculate the destination of the back reference, and append it
	 to MCTX->STATE_LOG.  */
      if (to_idx == cur_str)
	{
	  /* The backreference did epsilon transit, we must re-check all the
	     node in the current state.  */
	  re_node_set new_dests;
	  reg_errcode_t err2, err3;
	  next_node = dfa->edests[ent->node].elems[0];
	  if (re_node_set_contains (cur_nodes, next_node))
	    continue;
	  err = re_node_set_init_1 (&new_dests, next_node);
	  err2 = check_arrival_expand_ecl (dfa, &new_dests, subexp_num, type);
	  err3 = re_node_set_merge (cur_nodes, &new_dests);
	  re_node_set_free (&new_dests);
	  if (__glibc_unlikely (err != REG_NOERROR || err2 != REG_NOERROR
				|| err3 != REG_NOERROR))
	    {
	      err = (err != REG_NOERROR ? err
		     : (err2 != REG_NOERROR ? err2 : err3));
	      return err;
	    }
	  /* TODO: It is still inefficient...  */
	  goto restart;
	}
      else
	{
	  re_node_set union_set;
	  next_node = dfa->nexts[ent->node];
	  if (mctx->state_log[to_idx])
	    {
	      bool ok;
	      if (re_node_set_contains (&mctx->state_log[to_idx]->nodes,
					next_node))
		continue;
	      err = re_node_set_init_copy (&union_set,
					   &mctx->state_log[to_idx]->nodes);
	      ok = re_node_set_insert (&union_set, next_node);
	      if (__glibc_unlikely (err != REG_NOERROR || ! ok))
		{
		  re_node_set_free (&union_set);
		  err = err != REG_NOERROR ? err : REG_ESPACE;
		  return err;
		}
	    }
	  else
	    {
	      err = re_node_set_init_1 (&union_set, next_node);
	      if (__glibc_unlikely (err != REG_NOERROR))
		return err;
	    }
	  mctx->state_log[to_idx] = re_acquire_state (&err, dfa, &union_set);
	  re_node_set_free (&union_set);
	  if (__glibc_unlikely (mctx->state_log[to_idx] == NULL
				&& err != REG_NOERROR))
	    return err;
	}
    }
  while (ent++->more);
  return REG_NOERROR;
}

/* Build transition table for the state.
   Return true if successful.  */

static bool __attribute_noinline__
build_trtable (const re_dfa_t *dfa, re_dfastate_t *state)
{
  reg_errcode_t err;
  Idx i, j;
  int ch;
  bool need_word_trtable = false;
  bitset_word_t elem, mask;
  Idx ndests; /* Number of the destination states from 'state'.  */
  re_dfastate_t **trtable;
  re_dfastate_t *dest_states[SBC_MAX];
  re_dfastate_t *dest_states_word[SBC_MAX];
  re_dfastate_t *dest_states_nl[SBC_MAX];
  re_node_set follows;
  bitset_t acceptable;

  /* We build DFA states which corresponds to the destination nodes
     from 'state'.  'dests_node[i]' represents the nodes which i-th
     destination state contains, and 'dests_ch[i]' represents the
     characters which i-th destination state accepts.  */
  re_node_set dests_node[SBC_MAX];
  bitset_t dests_ch[SBC_MAX];

  /* Initialize transition table.  */
  state->word_trtable = state->trtable = NULL;

  /* At first, group all nodes belonging to 'state' into several
     destinations.  */
  ndests = group_nodes_into_DFAstates (dfa, state, dests_node, dests_ch);
  if (__glibc_unlikely (ndests <= 0))
    {
      /* Return false in case of an error, true otherwise.  */
      if (ndests == 0)
	{
	  state->trtable = (re_dfastate_t **)
	    calloc (sizeof (re_dfastate_t *), SBC_MAX);
          if (__glibc_unlikely (state->trtable == NULL))
            return false;
	  return true;
	}
      return false;
    }

  err = re_node_set_alloc (&follows, ndests + 1);
  if (__glibc_unlikely (err != REG_NOERROR))
    {
    out_free:
      re_node_set_free (&follows);
      for (i = 0; i < ndests; ++i)
	re_node_set_free (dests_node + i);
      return false;
    }

  bitset_empty (acceptable);

  /* Then build the states for all destinations.  */
  for (i = 0; i < ndests; ++i)
    {
      Idx next_node;
      re_node_set_empty (&follows);
      /* Merge the follows of this destination states.  */
      for (j = 0; j < dests_node[i].nelem; ++j)
	{
	  next_node = dfa->nexts[dests_node[i].elems[j]];
	  if (next_node != -1)
	    {
	      err = re_node_set_merge (&follows, dfa->eclosures + next_node);
	      if (__glibc_unlikely (err != REG_NOERROR))
		goto out_free;
	    }
	}
      dest_states[i] = re_acquire_state_context (&err, dfa, &follows, 0);
      if (__glibc_unlikely (dest_states[i] == NULL && err != REG_NOERROR))
	goto out_free;
      /* If the new state has context constraint,
	 build appropriate states for these contexts.  */
      if (dest_states[i]->has_constraint)
	{
	  dest_states_word[i] = re_acquire_state_context (&err, dfa, &follows,
							  CONTEXT_WORD);
	  if (__glibc_unlikely (dest_states_word[i] == NULL
				&& err != REG_NOERROR))
	    goto out_free;

	  if (dest_states[i] != dest_states_word[i] && dfa->mb_cur_max > 1)
	    need_word_trtable = true;

	  dest_states_nl[i] = re_acquire_state_context (&err, dfa, &follows,
							CONTEXT_NEWLINE);
	  if (__glibc_unlikely (dest_states_nl[i] == NULL && err != REG_NOERROR))
	    goto out_free;
	}
      else
	{
	  dest_states_word[i] = dest_states[i];
	  dest_states_nl[i] = dest_states[i];
	}
      bitset_merge (acceptable, dests_ch[i]);
    }

  if (!__glibc_unlikely (need_word_trtable))
    {
      /* We don't care about whether the following character is a word
	 character, or we are in a single-byte character set so we can
	 discern by looking at the character code: allocate a
	 256-entry transition table.  */
      trtable = state->trtable =
	(re_dfastate_t **) calloc (sizeof (re_dfastate_t *), SBC_MAX);
      if (__glibc_unlikely (trtable == NULL))
	goto out_free;

      /* For all characters ch...:  */
      for (i = 0; i < BITSET_WORDS; ++i)
	for (ch = i * BITSET_WORD_BITS, elem = acceptable[i], mask = 1;
	     elem;
	     mask <<= 1, elem >>= 1, ++ch)
	  if (__glibc_unlikely (elem & 1))
	    {
	      /* There must be exactly one destination which accepts
		 character ch.  See group_nodes_into_DFAstates.  */
	      for (j = 0; (dests_ch[j][i] & mask) == 0; ++j)
		;

	      /* j-th destination accepts the word character ch.  */
	      if (dfa->word_char[i] & mask)
		trtable[ch] = dest_states_word[j];
	      else
		trtable[ch] = dest_states[j];
	    }
    }
  else
    {
      /* We care about whether the following character is a word
	 character, and we are in a multi-byte character set: discern
	 by looking at the character code: build two 256-entry
	 transition tables, one starting at trtable[0] and one
	 starting at trtable[SBC_MAX].  */
      trtable = state->word_trtable =
	(re_dfastate_t **) calloc (sizeof (re_dfastate_t *), 2 * SBC_MAX);
      if (__glibc_unlikely (trtable == NULL))
	goto out_free;

      /* For all characters ch...:  */
      for (i = 0; i < BITSET_WORDS; ++i)
	for (ch = i * BITSET_WORD_BITS, elem = acceptable[i], mask = 1;
	     elem;
	     mask <<= 1, elem >>= 1, ++ch)
	  if (__glibc_unlikely (elem & 1))
	    {
	      /* There must be exactly one destination which accepts
		 character ch.  See group_nodes_into_DFAstates.  */
	      for (j = 0; (dests_ch[j][i] & mask) == 0; ++j)
		;

	      /* j-th destination accepts the word character ch.  */
	      trtable[ch] = dest_states[j];
	      trtable[ch + SBC_MAX] = dest_states_word[j];
	    }
    }

  /* new line */
  if (bitset_contain (acceptable, NEWLINE_CHAR))
    {
      /* The current state accepts newline character.  */
      for (j = 0; j < ndests; ++j)
	if (bitset_contain (dests_ch[j], NEWLINE_CHAR))
	  {
	    /* k-th destination accepts newline character.  */
	    trtable[NEWLINE_CHAR] = dest_states_nl[j];
	    if (need_word_trtable)
	      trtable[NEWLINE_CHAR + SBC_MAX] = dest_states_nl[j];
	    /* There must be only one destination which accepts
	       newline.  See group_nodes_into_DFAstates.  */
	    break;
	  }
    }

  re_node_set_free (&follows);
  for (i = 0; i < ndests; ++i)
    re_node_set_free (dests_node + i);
  return true;
}

/* Group all nodes belonging to STATE into several destinations.
   Then for all destinations, set the nodes belonging to the destination
   to DESTS_NODE[i] and set the characters accepted by the destination
   to DEST_CH[i].  Return the number of destinations if successful,
   -1 on internal error.  */

static bool determine_initial_accepts_bitset(const re_dfa_t *dfa, const re_token_t *node, bitset_t accepts);
static bool apply_node_constraints(const re_dfa_t *dfa, const re_token_t *node, bitset_t accepts);
static reg_errcode_t process_single_node_for_dfa_states(const re_dfa_t *dfa, Idx current_node_idx,
                                                        bitset_t initial_node_accepts_chars,
                                                        re_node_set *dests_node, bitset_t *dests_ch,
                                                        Idx *ndests_ptr);

static bool
determine_initial_accepts_bitset(const re_dfa_t *dfa, const re_token_t *node, bitset_t accepts)
{
  bitset_empty(accepts);

  switch (node->type) {
    case CHARACTER:
      bitset_set(accepts, node->opr.c);
      break;
    case SIMPLE_BRACKET:
      bitset_merge(accepts, node->opr.sbcset);
      break;
    case OP_PERIOD:
#ifdef RE_ENABLE_I18N
      if (dfa->mb_cur_max > 1)
        bitset_merge(accepts, dfa->sb_char);
      else
#endif
        bitset_set_all(accepts);
      if (!(dfa->syntax & RE_DOT_NEWLINE))
        bitset_clear(accepts, '\n');
      if (dfa->syntax & RE_DOT_NOT_NULL)
        bitset_clear(accepts, '\0');
      break;
#ifdef RE_ENABLE_I18N
    case OP_UTF8_PERIOD:
      if (ASCII_CHARS % BITSET_WORD_BITS == 0)
        memset(accepts, -1, ASCII_CHARS / CHAR_BIT);
      else
        bitset_merge(accepts, utf8_sb_map);
      if (!(dfa->syntax & RE_DOT_NEWLINE))
        bitset_clear(accepts, '\n');
      if (dfa->syntax & RE_DOT_NOT_NULL)
        bitset_clear(accepts, '\0');
      break;
#endif
    default:
      return false;
  }
  return true;
}

static bool
apply_node_constraints(const re_dfa_t *dfa, const re_token_t *node, bitset_t accepts)
{
  unsigned int constraint = node->constraint;
  if (!constraint) {
    return true;
  }

  if (constraint & NEXT_NEWLINE_CONSTRAINT) {
    bool accepts_newline = bitset_contain(accepts, NEWLINE_CHAR);
    bitset_empty(accepts);
    if (!accepts_newline) {
      return false;
    }
    bitset_set(accepts, NEWLINE_CHAR);
  }

  if (constraint & NEXT_ENDBUF_CONSTRAINT) {
    bitset_empty(accepts);
    return false;
  }

  if (constraint & NEXT_WORD_CONSTRAINT) {
    if (node->type == CHARACTER && !node->word_char) {
      bitset_empty(accepts);
      return false;
    }
    bitset_word_t any_set = 0;
#ifdef RE_ENABLE_I18N
    if (dfa->mb_cur_max > 1) {
      for (Idx j = 0; j < BITSET_WORDS; ++j)
        any_set |= (accepts[j] &= (dfa->word_char[j] | ~dfa->sb_char[j]));
    } else
#endif
    {
      for (Idx j = 0; j < BITSET_WORDS; ++j)
        any_set |= (accepts[j] &= dfa->word_char[j]);
    }
    if (!any_set) {
      bitset_empty(accepts);
      return false;
    }
  }

  if (constraint & NEXT_NOTWORD_CONSTRAINT) {
    if (node->type == CHARACTER && node->word_char) {
      bitset_empty(accepts);
      return false;
    }
    bitset_word_t any_set = 0;
#ifdef RE_ENABLE_I18N
    if (dfa->mb_cur_max > 1) {
      for (Idx j = 0; j < BITSET_WORDS; ++j)
        any_set |= (accepts[j] &= ~(dfa->word_char[j] & dfa->sb_char[j]));
    } else
#endif
    {
      for (Idx j = 0; j < BITSET_WORDS; ++j)
        any_set |= (accepts[j] &= ~dfa->word_char[j]);
    }
    if (!any_set) {
      bitset_empty(accepts);
      return false;
    }
  }

  return true;
}

static reg_errcode_t
process_single_node_for_dfa_states(const re_dfa_t *dfa, Idx current_node_idx,
                                   bitset_t initial_node_accepts_chars,
                                   re_node_set *dests_node, bitset_t *dests_ch,
                                   Idx *ndests_ptr)
{
  Idx current_ndests_snapshot = *ndests_ptr;
  bitset_t remaining_accepts;
  bitset_copy(remaining_accepts, initial_node_accepts_chars);

  if (bitset_is_empty(remaining_accepts)) {
      return REG_NOERROR;
  }

  for (Idx j = 0; j < current_ndests_snapshot; ++j) {
    bitset_t intersection;
    bitset_word_t has_intersection = 0;
    for (Idx k = 0; k < BITSET_WORDS; ++k) {
      has_intersection |= (intersection[k] = remaining_accepts[k] & dests_ch[j][k]);
    }

    if (!has_intersection) {
      continue;
    }

    bitset_t chars_in_dests_only;
    bitset_word_t dests_j_has_extra_chars = 0;
    for (Idx k = 0; k < BITSET_WORDS; ++k) {
      dests_j_has_extra_chars |= (chars_in_dests_only[k] = dests_ch[j][k] & ~remaining_accepts[k]);
    }

    if (dests_j_has_extra_chars) {
      if (*ndests_ptr >= SBC_MAX) {
          return REG_BADPAT;
      }

      bitset_copy(dests_ch[*ndests_ptr], chars_in_dests_only);
      reg_errcode_t err = re_node_set_init_copy(dests_node + *ndests_ptr, &dests_node[j]);
      if (__glibc_unlikely (err != REG_NOERROR)) {
        return err;
      }
      (*ndests_ptr)++;

      bitset_copy(dests_ch[j], intersection);
    }

    bool ok = re_node_set_insert(&dests_node[j], current_node_idx);
    if (__glibc_unlikely (!ok)) {
      return REG_ESPACE;
    }

    bitset_word_t chars_still_in_remaining = 0;
    for (Idx k = 0; k < BITSET_WORDS; ++k) {
      remaining_accepts[k] = remaining_accepts[k] & ~dests_ch[j][k];
      chars_still_in_remaining |= remaining_accepts[k];
    }

    if (!chars_still_in_remaining) {
      return REG_NOERROR;
    }
  }

  if (!bitset_is_empty(remaining_accepts)) {
      if (*ndests_ptr >= SBC_MAX) {
          return REG_BADPAT;
      }
      bitset_copy(dests_ch[*ndests_ptr], remaining_accepts);
      reg_errcode_t err = re_node_set_init_1(dests_node + *ndests_ptr, current_node_idx);
      if (__glibc_unlikely (err != REG_NOERROR)) {
        return err;
      }
      (*ndests_ptr)++;
  }

  return REG_NOERROR;
}

static Idx
group_nodes_into_DFAstates (const re_dfa_t *dfa, const re_dfastate_t *state,
			    re_node_set *dests_node, bitset_t *dests_ch)
{
  Idx i;
  Idx ndests = 0;
  const re_node_set *cur_nodes = &state->nodes;

  for (i = 0; i < cur_nodes->nelem; ++i)
    {
      const re_token_t *node = &dfa->nodes[cur_nodes->elems[i]];
      bitset_t accepts_chars;

      if (!determine_initial_accepts_bitset(dfa, node, accepts_chars)) {
        continue;
      }

      if (!apply_node_constraints(dfa, node, accepts_chars)) {
        continue;
      }

      if (bitset_is_empty(accepts_chars)) {
        continue;
      }

      reg_errcode_t err = process_single_node_for_dfa_states(dfa,
                                                             cur_nodes->elems[i],
                                                             accepts_chars,
                                                             dests_node,
                                                             dests_ch,
                                                             &ndests);
      if (__glibc_unlikely (err != REG_NOERROR)) {
        Idx j;
        for (j = 0; j < ndests; ++j) {
          re_node_set_free (dests_node + j);
        }
        return -1;
      }
    }

  assume (ndests <= SBC_MAX);
  return ndests;
}

#ifdef RE_ENABLE_I18N
/* Check how many bytes the node 'dfa->nodes[node_idx]' accepts.
   Return the number of the bytes the node accepts.
   STR_IDX is the current index of the input string.

   This function handles the nodes which can accept one character, or
   one collating element like '.', '[a-z]', opposite to the other nodes
   can only accept one byte.  */

# ifdef _LIBC
#  include <locale/weight.h>
# endif

static int
check_node_accept_bytes (const re_dfa_t *dfa, Idx node_idx,
			 const re_string_t *input, Idx str_idx)
{
  const re_token_t *node = dfa->nodes + node_idx;
  int char_len, elem_len;
  Idx i;

  if (__glibc_unlikely (node->type == OP_UTF8_PERIOD))
    {
      unsigned char c = re_string_byte_at (input, str_idx), d;
      if (__glibc_likely (c < 0xc2))
	return 0;

      if (str_idx + 2 > input->len)
	return 0;

      d = re_string_byte_at (input, str_idx + 1);
      if (c < 0xe0)
	return (d < 0x80 || d > 0xbf) ? 0 : 2;
      else if (c < 0xf0)
	{
	  char_len = 3;
	  if (c == 0xe0 && d < 0xa0)
	    return 0;
	}
      else if (c < 0xf8)
	{
	  char_len = 4;
	  if (c == 0xf0 && d < 0x90)
	    return 0;
	}
      else if (c < 0xfc)
	{
	  char_len = 5;
	  if (c == 0xf8 && d < 0x88)
	    return 0;
	}
      else if (c < 0xfe)
	{
	  char_len = 6;
	  if (c == 0xfc && d < 0x84)
	    return 0;
	}
      else
	return 0;

      if (str_idx + char_len > input->len)
	return 0;

      for (i = 1; i < char_len; ++i)
	{
	  d = re_string_byte_at (input, str_idx + i);
	  if (d < 0x80 || d > 0xbf)
	    return 0;
	}
      return char_len;
    }

  char_len = re_string_char_size_at (input, str_idx);
  if (node->type == OP_PERIOD)
    {
      if (char_len <= 1)
	return 0;
      /* FIXME: I don't think this if is needed, as both '\n'
	 and '\0' are char_len == 1.  */
      /* '.' accepts any one character except the following two cases.  */
      if ((!(dfa->syntax & RE_DOT_NEWLINE)
	   && re_string_byte_at (input, str_idx) == '\n')
	  || ((dfa->syntax & RE_DOT_NOT_NULL)
	      && re_string_byte_at (input, str_idx) == '\0'))
	return 0;
      return char_len;
    }

  elem_len = re_string_elem_size_at (input, str_idx);
  if ((elem_len <= 1 && char_len <= 1) || char_len == 0)
    return 0;

  if (node->type == COMPLEX_BRACKET)
    {
      const re_charset_t *cset = node->opr.mbcset;
# ifdef _LIBC
      const unsigned char *pin
	= ((const unsigned char *) re_string_get_buffer (input) + str_idx);
      Idx j;
      uint32_t nrules;
# endif /* _LIBC */
      int match_len = 0;
      wchar_t wc = ((cset->nranges || cset->nchar_classes || cset->nmbchars)
		    ? re_string_wchar_at (input, str_idx) : 0);

      /* match with multibyte character?  */
      for (i = 0; i < cset->nmbchars; ++i)
	if (wc == cset->mbchars[i])
	  {
	    match_len = char_len;
	    goto check_node_accept_bytes_match;
	  }
      /* match with character_class?  */
      for (i = 0; i < cset->nchar_classes; ++i)
	{
	  wctype_t wt = cset->char_classes[i];
	  if (__iswctype (wc, wt))
	    {
	      match_len = char_len;
	      goto check_node_accept_bytes_match;
	    }
	}

# ifdef _LIBC
      nrules = _NL_CURRENT_WORD (LC_COLLATE, _NL_COLLATE_NRULES);
      if (nrules != 0)
	{
	  unsigned int in_collseq = 0;
	  const int32_t *table, *indirect;
	  const unsigned char *weights, *extra;
	  const char *collseqwc;

	  /* match with collating_symbol?  */
	  if (cset->ncoll_syms)
	    extra = (const unsigned char *)
	      _NL_CURRENT (LC_COLLATE, _NL_COLLATE_SYMB_EXTRAMB);
	  for (i = 0; i < cset->ncoll_syms; ++i)
	    {
	      /* The compiler might warn that extra may be used uninitialized,
		 however the loop will be executed iff ncoll_syms is larger
		 than 0,which means extra will be already initialized.  */
	      DIAG_PUSH_NEEDS_COMMENT;
	      DIAG_IGNORE_Os_NEEDS_COMMENT (8, "-Wmaybe-uninitialized");
	      const unsigned char *coll_sym = extra + cset->coll_syms[i];
	      DIAG_POP_NEEDS_COMMENT;
	      /* Compare the length of input collating element and
		 the length of current collating element.  */
	      if (*coll_sym != elem_len)
		continue;
	      /* Compare each bytes.  */
	      for (j = 0; j < *coll_sym; j++)
		if (pin[j] != coll_sym[1 + j])
		  break;
	      if (j == *coll_sym)
		{
		  /* Match if every bytes is equal.  */
		  match_len = j;
		  goto check_node_accept_bytes_match;
		}
	    }

	  if (cset->nranges)
	    {
	      if (elem_len <= char_len)
		{
		  collseqwc = _NL_CURRENT (LC_COLLATE, _NL_COLLATE_COLLSEQWC);
		  in_collseq = __collseq_table_lookup (collseqwc, wc);
		}
	      else
		in_collseq = find_collation_sequence_value (pin, elem_len);
	    }
	  /* match with range expression?  */
	  /* FIXME: Implement rational ranges here, too.  */
	  for (i = 0; i < cset->nranges; ++i)
	    if (cset->range_starts[i] <= in_collseq
		&& in_collseq <= cset->range_ends[i])
	      {
		match_len = elem_len;
		goto check_node_accept_bytes_match;
	      }

	  /* match with equivalence_class?  */
	  if (cset->nequiv_classes)
	    {
	      const unsigned char *cp = pin;
	      table = (const int32_t *)
		_NL_CURRENT (LC_COLLATE, _NL_COLLATE_TABLEMB);
	      weights = (const unsigned char *)
		_NL_CURRENT (LC_COLLATE, _NL_COLLATE_WEIGHTMB);
	      extra = (const unsigned char *)
		_NL_CURRENT (LC_COLLATE, _NL_COLLATE_EXTRAMB);
	      indirect = (const int32_t *)
		_NL_CURRENT (LC_COLLATE, _NL_COLLATE_INDIRECTMB);
	      int32_t idx = findidx (table, indirect, extra, &cp, elem_len);
	      int32_t rule = idx >> 24;
	      idx &= 0xffffff;
	      if (idx > 0)
		{
		  size_t weight_len = weights[idx];
		  for (i = 0; i < cset->nequiv_classes; ++i)
		    {
		      int32_t equiv_class_idx = cset->equiv_classes[i];
		      int32_t equiv_class_rule = equiv_class_idx >> 24;
		      equiv_class_idx &= 0xffffff;
		      if (weights[equiv_class_idx] == weight_len
			  && equiv_class_rule == rule
			  && memcmp (weights + idx + 1,
				     weights + equiv_class_idx + 1,
				     weight_len) == 0)
			{
			  match_len = elem_len;
			  goto check_node_accept_bytes_match;
			}
		    }
		}
	    }
	}
      else
# endif /* _LIBC */
	{
	  /* match with range expression?  */
	  for (i = 0; i < cset->nranges; ++i)
	    {
	      if (cset->range_starts[i] <= wc && wc <= cset->range_ends[i])
		{
		  match_len = char_len;
		  goto check_node_accept_bytes_match;
		}
	    }
	}
    check_node_accept_bytes_match:
      if (!cset->non_match)
	return match_len;
      else
	{
	  if (match_len > 0)
	    return 0;
	  else
	    return (elem_len > char_len) ? elem_len : char_len;
	}
    }
  return 0;
}

# ifdef _LIBC
static unsigned int
find_collation_sequence_value (const unsigned char *mbs, size_t mbs_len)
{
  uint32_t nrules = _NL_CURRENT_WORD (LC_COLLATE, _NL_COLLATE_NRULES);
  if (nrules == 0)
    {
      if (mbs_len == 1)
	{
	  /* No valid character.  Match it as a single byte character.  */
	  const unsigned char *collseq = (const unsigned char *)
	    _NL_CURRENT (LC_COLLATE, _NL_COLLATE_COLLSEQMB);
	  return collseq[mbs[0]];
	}
      return UINT_MAX;
    }
  else
    {
      int32_t idx;
      const unsigned char *extra = (const unsigned char *)
	_NL_CURRENT (LC_COLLATE, _NL_COLLATE_SYMB_EXTRAMB);
      int32_t extrasize = (const unsigned char *)
	_NL_CURRENT (LC_COLLATE, _NL_COLLATE_SYMB_EXTRAMB + 1) - extra;

      for (idx = 0; idx < extrasize;)
	{
	  int mbs_cnt;
	  bool found = false;
	  int32_t elem_mbs_len;
	  /* Skip the name of collating element name.  */
	  idx = idx + extra[idx] + 1;
	  elem_mbs_len = extra[idx++];
	  if (mbs_len == elem_mbs_len)
	    {
	      for (mbs_cnt = 0; mbs_cnt < elem_mbs_len; ++mbs_cnt)
		if (extra[idx + mbs_cnt] != mbs[mbs_cnt])
		  break;
	      if (mbs_cnt == elem_mbs_len)
		/* Found the entry.  */
		found = true;
	    }
	  /* Skip the byte sequence of the collating element.  */
	  idx += elem_mbs_len;
	  /* Adjust for the alignment.  */
	  idx = (idx + 3) & ~3;
	  /* Skip the collation sequence value.  */
	  idx += sizeof (uint32_t);
	  /* Skip the wide char sequence of the collating element.  */
	  idx = idx + sizeof (uint32_t) * (*(int32_t *) (extra + idx) + 1);
	  /* If we found the entry, return the sequence value.  */
	  if (found)
	    return *(uint32_t *) (extra + idx);
	  /* Skip the collation sequence value.  */
	  idx += sizeof (uint32_t);
	}
      return UINT_MAX;
    }
}
# endif /* _LIBC */
#endif /* RE_ENABLE_I18N */

/* Check whether the node accepts the byte which is IDX-th
   byte of the INPUT.  */

static bool
check_node_accept (const re_match_context_t *mctx, const re_token_t *node,
		   Idx idx)
{
  if (mctx == NULL || node == NULL || mctx->dfa == NULL)
    {
      return false;
    }

  unsigned char ch = re_string_byte_at (&mctx->input, idx);

  switch (node->type)
    {
    case CHARACTER:
      if (node->opr.c != ch)
        return false;
      break;

    case SIMPLE_BRACKET:
      if (!bitset_contain (node->opr.sbcset, ch))
        return false;
      break;

#ifdef RE_ENABLE_I18N
    case OP_UTF8_PERIOD:
      if (ch >= ASCII_CHARS)
        return false;
      FALLTHROUGH;
#endif
    case OP_PERIOD:
      if ((ch == '\n' && !(mctx->dfa->syntax & RE_DOT_NEWLINE)) ||
          (ch == '\0' && (mctx->dfa->syntax & RE_DOT_NOT_NULL)))
	return false;
      break;

    default:
      return false;
    }

  if (node->constraint)
    {
      unsigned int context = re_string_context_at (&mctx->input, idx,
						   mctx->eflags);
      if (NOT_SATISFY_NEXT_CONSTRAINT (node->constraint, context))
	return false;
    }

  return true;
}

/* Extend the buffers, if the buffers have run out.  */

static reg_errcode_t
__attribute_warn_unused_result__
extend_buffers (re_match_context_t *mctx, int min_len)
{
  reg_errcode_t ret;
  re_string_t *pstr = &mctx->input;

  /* Avoid overflow.  */
  if (__glibc_unlikely (MIN (IDX_MAX, SIZE_MAX / sizeof (re_dfastate_t *)) / 2
			<= pstr->bufs_len))
    return REG_ESPACE;

  /* Double the lengths of the buffers, but allocate at least MIN_LEN.  */
  ret = re_string_realloc_buffers (pstr,
				   MAX (min_len,
					MIN (pstr->len, pstr->bufs_len * 2)));
  if (__glibc_unlikely (ret != REG_NOERROR))
    return ret;

  if (mctx->state_log != NULL)
    {
      /* And double the length of state_log.  */
      /* XXX We have no indication of the size of this buffer.  If this
	 allocation fail we have no indication that the state_log array
	 does not have the right size.  */
      re_dfastate_t **new_array = re_realloc (mctx->state_log, re_dfastate_t *,
					      pstr->bufs_len + 1);
      if (__glibc_unlikely (new_array == NULL))
	return REG_ESPACE;
      mctx->state_log = new_array;
    }

  /* Then reconstruct the buffers.  */
  if (pstr->icase)
    {
#ifdef RE_ENABLE_I18N
      if (pstr->mb_cur_max > 1)
	{
	  ret = build_wcs_upper_buffer (pstr);
	  if (__glibc_unlikely (ret != REG_NOERROR))
	    return ret;
	}
      else
#endif /* RE_ENABLE_I18N  */
	build_upper_buffer (pstr);
    }
  else
    {
#ifdef RE_ENABLE_I18N
      if (pstr->mb_cur_max > 1)
	build_wcs_buffer (pstr);
      else
#endif /* RE_ENABLE_I18N  */
	{
	  if (pstr->trans != NULL)
	    re_string_translate_buffer (pstr);
	}
    }
  return REG_NOERROR;
}


/* Functions for matching context.  */

/* Initialize MCTX.  */

static reg_errcode_t
__attribute_warn_unused_result__
match_ctx_init (re_match_context_t *mctx, int eflags, Idx n)
{
  mctx->eflags = eflags;
  mctx->match_last = -1;
  if (n > 0)
    {
      /* Avoid overflow.  */
      size_t max_object_size =
	MAX (sizeof (struct re_backref_cache_entry),
	     sizeof (re_sub_match_top_t *));
      if (__glibc_unlikely (MIN (IDX_MAX, SIZE_MAX / max_object_size) < n))
	return REG_ESPACE;

      mctx->bkref_ents = re_malloc (struct re_backref_cache_entry, n);
      mctx->sub_tops = re_malloc (re_sub_match_top_t *, n);
      if (__glibc_unlikely (mctx->bkref_ents == NULL || mctx->sub_tops == NULL))
	return REG_ESPACE;
    }
  /* Already zero-ed by the caller.
     else
       mctx->bkref_ents = NULL;
     mctx->nbkref_ents = 0;
     mctx->nsub_tops = 0;  */
  mctx->abkref_ents = n;
  mctx->max_mb_elem_len = 1;
  mctx->asub_tops = n;
  return REG_NOERROR;
}

/* Clean the entries which depend on the current input in MCTX.
   This function must be invoked when the matcher changes the start index
   of the input, or changes the input string.  */

static void
free_re_sub_match_last_instance(re_sub_match_last_t *last)
{
  if (last == NULL)
    {
      return;
    }
  re_free(last->path.array);
  re_free(last);
}

static void
free_re_sub_match_top_instance(re_sub_match_top_t *top)
{
  if (top == NULL)
    {
      return;
    }

  for (Idx sl_idx = 0; sl_idx < top->nlasts; ++sl_idx)
    {
      free_re_sub_match_last_instance(top->lasts[sl_idx]);
      top->lasts[sl_idx] = NULL;
    }
  re_free(top->lasts);
  top->lasts = NULL;
  top->nlasts = 0;

  if (top->path != NULL)
    {
      re_free(top->path->array);
      re_free(top->path);
      top->path = NULL;
    }
  re_free(top);
}

static void
match_ctx_clean(re_match_context_t *mctx)
{
  if (mctx == NULL)
    {
      return;
    }

  for (Idx st_idx = 0; st_idx < mctx->nsub_tops; ++st_idx)
    {
      free_re_sub_match_top_instance(mctx->sub_tops[st_idx]);
      mctx->sub_tops[st_idx] = NULL;
    }

  re_free(mctx->sub_tops);
  mctx->sub_tops = NULL;
  mctx->nsub_tops = 0;

  mctx->nbkref_ents = 0;
}

/* Free all the memory associated with MCTX.  */

static void
match_ctx_free (re_match_context_t *mctx)
{
  if (mctx == NULL)
    {
      return;
    }

  match_ctx_clean (mctx);
  re_free (mctx->sub_tops);
  re_free (mctx->bkref_ents);
}

/* Add a new backreference entry to MCTX.
   Note that we assume that caller never call this function with duplicate
   entry, and call with STR_IDX which isn't smaller than any existing entry.
*/

static reg_errcode_t
__attribute_warn_unused_result__
match_ctx_add_entry (re_match_context_t *mctx, Idx node, Idx str_idx, Idx from,
		     Idx to)
{
  if (mctx->nbkref_ents >= mctx->abkref_ents)
    {
      struct re_backref_cache_entry* new_entry;
      new_entry = re_realloc (mctx->bkref_ents, struct re_backref_cache_entry,
			      mctx->abkref_ents * 2);
      if (__glibc_unlikely (new_entry == NULL))
	{
	  re_free (mctx->bkref_ents);
	  return REG_ESPACE;
	}
      mctx->bkref_ents = new_entry;
      memset (mctx->bkref_ents + mctx->nbkref_ents, '\0',
	      sizeof (struct re_backref_cache_entry) * mctx->abkref_ents);
      mctx->abkref_ents *= 2;
    }
  if (mctx->nbkref_ents > 0
      && mctx->bkref_ents[mctx->nbkref_ents - 1].str_idx == str_idx)
    mctx->bkref_ents[mctx->nbkref_ents - 1].more = 1;

  mctx->bkref_ents[mctx->nbkref_ents].node = node;
  mctx->bkref_ents[mctx->nbkref_ents].str_idx = str_idx;
  mctx->bkref_ents[mctx->nbkref_ents].subexp_from = from;
  mctx->bkref_ents[mctx->nbkref_ents].subexp_to = to;

  /* This is a cache that saves negative results of check_dst_limits_calc_pos.
     If bit N is clear, means that this entry won't epsilon-transition to
     an OP_OPEN_SUBEXP or OP_CLOSE_SUBEXP for the N+1-th subexpression.  If
     it is set, check_dst_limits_calc_pos_1 will recurse and try to find one
     such node.

     A backreference does not epsilon-transition unless it is empty, so set
     to all zeros if FROM != TO.  */
  mctx->bkref_ents[mctx->nbkref_ents].eps_reachable_subexps_map
    = (from == to ? -1 : 0);

  mctx->bkref_ents[mctx->nbkref_ents++].more = 0;
  if (mctx->max_mb_elem_len < to - from)
    mctx->max_mb_elem_len = to - from;
  return REG_NOERROR;
}

/* Return the first entry with the same str_idx, or -1 if none is
   found.  Note that MCTX->BKREF_ENTS is already sorted by MCTX->STR_IDX.  */

static Idx
search_cur_bkref_entry (const re_match_context_t *mctx, Idx str_idx)
{
  if (mctx == NULL) {
    return -1;
  }

  if (mctx->nbkref_ents > 0 && mctx->bkref_ents == NULL) {
    return -1;
  }

  Idx left = 0;
  Idx right = mctx->nbkref_ents;
  Idx mid;

  while (left < right)
    {
      mid = left + (right - left) / 2;

      if (mctx->bkref_ents[mid].str_idx < str_idx)
	{
	  left = mid + 1;
	}
      else
	{
	  right = mid;
	}
    }

  if (left < mctx->nbkref_ents && mctx->bkref_ents[left].str_idx == str_idx)
    {
      return left;
    }
  else
    {
      return -1;
    }
}

/* Register the node NODE, whose type is OP_OPEN_SUBEXP, and which matches
   at STR_IDX.  */

static reg_errcode_t
__attribute_warn_unused_result__
match_ctx_add_subtop (re_match_context_t *mctx, Idx node, Idx str_idx)
{
  DEBUG_ASSERT (mctx->sub_tops != NULL);
  DEBUG_ASSERT (mctx->asub_tops > 0);
  if (__glibc_unlikely (mctx->nsub_tops == mctx->asub_tops))
    {
      Idx new_asub_tops = mctx->asub_tops * 2;
      re_sub_match_top_t **new_array = re_realloc (mctx->sub_tops,
						   re_sub_match_top_t *,
						   new_asub_tops);
      if (__glibc_unlikely (new_array == NULL))
	return REG_ESPACE;
      mctx->sub_tops = new_array;
      mctx->asub_tops = new_asub_tops;
    }
  mctx->sub_tops[mctx->nsub_tops] = calloc (1, sizeof (re_sub_match_top_t));
  if (__glibc_unlikely (mctx->sub_tops[mctx->nsub_tops] == NULL))
    return REG_ESPACE;
  mctx->sub_tops[mctx->nsub_tops]->node = node;
  mctx->sub_tops[mctx->nsub_tops++]->str_idx = str_idx;
  return REG_NOERROR;
}

/* Register the node NODE, whose type is OP_CLOSE_SUBEXP, and which matches
   at STR_IDX, whose corresponding OP_OPEN_SUBEXP is SUB_TOP.
   Return the new entry if successful, NULL if memory is exhausted.  */

static re_sub_match_last_t *
match_ctx_add_sublast (re_sub_match_top_t *subtop, Idx node, Idx str_idx)
{
  if (subtop->nlasts == subtop->alasts)
    {
      Idx new_alasts = 2 * subtop->alasts + 1;
      
      // Calculate new capacity. A minimal capacity of 1 is ensured by the +1.
      // An integer overflow check for new_alasts could be added here if Idx is small,
      // but for typical usage, this growth strategy is usually safe.
      
      re_sub_match_last_t **new_array = realloc(subtop->lasts, new_alasts * sizeof(re_sub_match_last_t *));
      
      if (new_array == NULL)
        {
          // Reallocation failed. Return NULL to indicate error.
          return NULL;
        }
      
      subtop->lasts = new_array;
      subtop->alasts = new_alasts;
    }
  
  re_sub_match_last_t *new_entry = calloc(1, sizeof(re_sub_match_last_t));
  
  if (new_entry == NULL)
    {
      // Allocation of individual entry failed. Return NULL.
      return NULL;
    }
  
  // Populate the new entry.
  new_entry->node = node;
  new_entry->str_idx = str_idx;
  
  // Add the new entry to the array and update the count.
  subtop->lasts[subtop->nlasts] = new_entry;
  subtop->nlasts++;
  
  return new_entry;
}

static void
sift_ctx_init (re_sift_context_t *sctx, re_dfastate_t **sifted_sts,
	       re_dfastate_t **limited_sts, Idx last_node, Idx last_str_idx)
{
  sctx->sifted_states = sifted_sts;
  sctx->limited_states = limited_sts;
  sctx->last_node = last_node;
  sctx->last_str_idx = last_str_idx;
  re_node_set_init_empty (&sctx->limits);
}
