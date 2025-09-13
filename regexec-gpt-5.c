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

int
regexec (const regex_t *__restrict preg, const char *__restrict string,
         size_t nmatch, regmatch_t pmatch[_REGEX_NELTS (nmatch)], int eflags)
{
  reg_errcode_t err;
  Idx start = 0;
  Idx length = 0;
  re_dfa_t *dfa;
  size_t effective_nmatch;
  regmatch_t *effective_pmatch;

  if ((eflags & ~(REG_NOTBOL | REG_NOTEOL | REG_STARTEND)) != 0)
    return REG_BADPAT;

  if (eflags & REG_STARTEND)
    {
      start = pmatch[0].rm_so;
      length = pmatch[0].rm_eo;
    }
  else
    {
      length = (Idx) strlen (string);
    }

  dfa = preg->buffer;

  effective_nmatch = preg->no_sub ? 0 : nmatch;
  effective_pmatch = preg->no_sub ? NULL : pmatch;

  lock_lock (dfa->lock);
  err = re_search_internal (preg, string, length, start, length,
                            length, effective_nmatch, effective_pmatch, eflags);
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

regoff_t
re_match(struct re_pattern_buffer *bufp, const char *string, Idx length,
         Idx start, struct re_registers *regs)
{
    return re_search_stub(bufp, string, length, start, (Idx)0, length, regs, 1);
}
#ifdef _LIBC
weak_alias (__re_match, re_match)
#endif

regoff_t
re_search(struct re_pattern_buffer *bufp, const char *string, Idx length,
          Idx start, regoff_t range, struct re_registers *regs)
{
    const Idx stop = length;
    return re_search_stub(bufp, string, length, start, range, stop, regs, 0);
}
#ifdef _LIBC
weak_alias (__re_search, re_search)
#endif

regoff_t re_match_2(struct re_pattern_buffer *bufp, const char *string1, Idx length1,
                    const char *string2, Idx length2, Idx start,
                    struct re_registers *regs, Idx stop)
{
    return re_search_2_stub(bufp, string1, length1, string2, length2,
                            start, 0, regs, stop, true);
}
#ifdef _LIBC
weak_alias (__re_match_2, re_match_2)
#endif

regoff_t
re_search_2(struct re_pattern_buffer *bufp, const char *string1, Idx length1,
            const char *string2, Idx length2, Idx start, regoff_t range,
            struct re_registers *regs, Idx stop)
{
  return re_search_2_stub(bufp, string1, length1, string2, length2,
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
  const char *str;
  regoff_t rval;
  Idx len;
  char *concat = NULL;

  if (__glibc_unlikely (length1 < 0 || length2 < 0 || stop < 0
                        || INT_ADD_WRAPV (length1, length2, &len)))
    return -2;

  if (length1 > 0 && length2 > 0)
    {
      concat = re_malloc (char, len);
      if (__glibc_unlikely (concat == NULL))
        return -2;
#ifdef _LIBC
      memcpy (__mempcpy (concat, string1, (size_t) length1), string2, (size_t) length2);
#else
      memcpy (concat, string1, (size_t) length1);
      memcpy (concat + (size_t) length1, string2, (size_t) length2);
#endif
      str = concat;
    }
  else if (length2 > 0)
    {
      str = string2;
    }
  else
    {
      str = string1;
    }

  rval = re_search_stub (bufp, str, len, start, range, stop, regs, ret_len);
  re_free (concat);
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
  Idx nregs = 1;
  regoff_t rval = -2;
  int eflags = 0;
  re_dfa_t *dfa = bufp->buffer;
  Idx last_start = start + range;

  if (__glibc_unlikely (start < 0 || start > length))
    return -1;

  if (__glibc_unlikely (length < last_start
                        || (0 <= range && last_start < start)))
    last_start = length;
  else if (__glibc_unlikely (last_start < 0
                             || (range < 0 && start <= last_start)))
    last_start = 0;

  lock_lock (dfa->lock);

  if (bufp->not_bol)
    eflags |= REG_NOTBOL;
  if (bufp->not_eol)
    eflags |= REG_NOTEOL;

  if (start < last_start && bufp->fastmap != NULL && !bufp->fastmap_accurate)
    re_compile_fastmap (bufp);

  if (__glibc_unlikely (bufp->no_sub))
    regs = NULL;

  if (regs != NULL)
    {
      if (__glibc_unlikely (bufp->regs_allocated == REGS_FIXED
                            && regs->num_regs <= bufp->re_nsub))
        {
          nregs = regs->num_regs;
          if (__glibc_unlikely (nregs < 1))
            {
              regs = NULL;
              nregs = 1;
            }
        }
      else
        nregs = bufp->re_nsub + 1;
    }

  pmatch = re_malloc (regmatch_t, nregs);
  if (__glibc_unlikely (pmatch == NULL))
    goto finish;

  result = re_search_internal (bufp, string, length, start, last_start, stop,
                               nregs, pmatch, eflags);

  rval = 0;
  if (result != REG_NOERROR)
    {
      rval = (result == REG_NOMATCH) ? -1 : -2;
    }
  else if (regs != NULL)
    {
      bufp->regs_allocated = re_copy_regs (regs, pmatch, nregs,
                                           bufp->regs_allocated);
      if (__glibc_unlikely (bufp->regs_allocated == REGS_UNALLOCATED))
        rval = -2;
    }

  if (__glibc_likely (rval == 0))
    {
      if (ret_len)
        {
          DEBUG_ASSERT (pmatch[0].rm_so == start);
          rval = pmatch[0].rm_eo - start;
        }
      else
        {
          rval = pmatch[0].rm_so;
        }
    }

finish:
  if (pmatch != NULL)
    re_free (pmatch);
  lock_unlock (dfa->lock);
  return rval;
}

static unsigned
re_copy_regs (struct re_registers *regs, regmatch_t *pmatch, Idx nregs,
              int regs_allocated)
{
  unsigned rval = REGS_REALLOCATE;
  Idx i;
  Idx need_regs;

  if (regs == NULL || pmatch == NULL)
    return REGS_UNALLOCATED;

  if (nregs < 0)
    return REGS_UNALLOCATED;

  need_regs = nregs + 1;
  if (need_regs <= nregs)
    return REGS_UNALLOCATED;

  switch (regs_allocated)
    {
    case REGS_UNALLOCATED:
      {
        regoff_t *new_start = re_malloc (regoff_t, need_regs);
        regoff_t *new_end = NULL;

        if (new_start == NULL)
          return REGS_UNALLOCATED;

        new_end = re_malloc (regoff_t, need_regs);
        if (new_end == NULL)
          {
            re_free (new_start);
            return REGS_UNALLOCATED;
          }

        regs->start = new_start;
        regs->end = new_end;
        regs->num_regs = need_regs;
      }
      break;

    case REGS_REALLOCATE:
      if (need_regs > regs->num_regs)
        {
          regoff_t *new_start = re_malloc (regoff_t, need_regs);
          regoff_t *new_end = NULL;

          if (new_start == NULL)
            return REGS_UNALLOCATED;

          new_end = re_malloc (regoff_t, need_regs);
          if (new_end == NULL)
            {
              re_free (new_start);
              return REGS_UNALLOCATED;
            }

          re_free (regs->start);
          re_free (regs->end);
          regs->start = new_start;
          regs->end = new_end;
          regs->num_regs = need_regs;
        }
      break;

    default:
      DEBUG_ASSERT (regs_allocated == REGS_FIXED);
      DEBUG_ASSERT (nregs <= regs->num_regs);
      rval = REGS_FIXED;
      break;
    }

  for (i = 0; i < nregs; ++i)
    {
      regs->start[i] = pmatch[i].rm_so;
      regs->end[i] = pmatch[i].rm_eo;
    }
  for (; i < regs->num_regs; ++i)
    {
      regs->start[i] = -1;
      regs->end[i] = -1;
    }

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

void re_set_registers(struct re_pattern_buffer *bufp, struct re_registers *regs,
                      __re_size_t num_regs, regoff_t *starts, regoff_t *ends)
{
    if (bufp == NULL || regs == NULL) {
        return;
    }

    bufp->regs_allocated = REGS_UNALLOCATED;
    regs->num_regs = 0;
    regs->start = NULL;
    regs->end = NULL;

    if (num_regs != 0) {
        bufp->regs_allocated = REGS_REALLOCATE;
        regs->num_regs = num_regs;
        regs->start = starts;
        regs->end = ends;
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
  const re_dfastate_t *const init_state = dfa->init_state;

  if (!init_state->has_constraint)
    return dfa->init_state;

  const unsigned int context =
    re_string_context_at (&mctx->input, idx - 1, mctx->eflags);

  if (IS_WORD_CONTEXT (context))
    return dfa->init_state_word;

  if (IS_ORDINARY_CONTEXT (context))
    return dfa->init_state;

  if (IS_BEGBUF_CONTEXT (context) && IS_NEWLINE_CONTEXT (context))
    return dfa->init_state_begbuf;

  if (IS_NEWLINE_CONTEXT (context))
    return dfa->init_state_nl;

  if (IS_BEGBUF_CONTEXT (context))
    return re_acquire_state_context (err, dfa,
                                     init_state->entrance_nodes,
                                     context);

  return dfa->init_state;
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
check_halt_node_context(const re_dfa_t *dfa, Idx node, unsigned int context)
{
  if (dfa->nodes[node].type != END_OF_RE)
    return false;
  const unsigned int constraint = dfa->nodes[node].constraint;
  return constraint == 0 || !NOT_SATISFY_NEXT_CONSTRAINT(constraint, context);
}

/* Check the halt state STATE match the current context.
   Return 0 if not match, if the node, STATE has, is a halt node and
   match the context, return the node.  */

static Idx
check_halt_state_context (const re_match_context_t *mctx,
                          const re_dfastate_t *state, Idx idx)
{
  Idx i;
  unsigned int context;
  const Idx nelem = (state != NULL) ? state->nodes.nelem : 0;
  const Idx *elems = (state != NULL) ? state->nodes.elems : NULL;

  if (mctx == NULL || state == NULL || elems == NULL || nelem == 0 || !state->halt)
    return 0;

  DEBUG_ASSERT (state->halt);

  context = re_string_context_at (&mctx->input, idx, mctx->eflags);
  for (i = 0; i < nelem; ++i)
    {
      Idx node = elems[i];
      if (check_halt_node_context (mctx->dfa, node, context))
        return node;
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
  const re_dfa_t *const dfa = mctx->dfa;

  if (IS_EPSILON_NODE (dfa->nodes[node].type))
    {
      if (*pidx > mctx->match_last || mctx->state_log[*pidx] == NULL)
        return -1;

      re_node_set *cur_nodes = &mctx->state_log[*pidx]->nodes;
      re_node_set *edests = &dfa->edests[node];

      if (!re_node_set_contains (eps_via_nodes, node))
        {
          bool ok = re_node_set_insert (eps_via_nodes, node);
          if (__glibc_unlikely (! ok))
            return -2;
        }

      Idx dest_node = -1;
      for (Idx i = 0; i < edests->nelem; i++)
        {
          Idx candidate = edests->elems[i];
          if (!re_node_set_contains (cur_nodes, candidate))
            continue;

          if (dest_node == -1)
            dest_node = candidate;
          else
            {
              if (re_node_set_contains (eps_via_nodes, dest_node))
                return candidate;

              if (fs != NULL
                  && push_fail_stack (fs, *pidx, candidate, nregs, regs,
                                      prevregs, eps_via_nodes))
                return -2;

              break;
            }
        }
      return dest_node;
    }

  Idx naccepted = 0;
  re_token_type_t type = dfa->nodes[node].type;

#ifdef RE_ENABLE_I18N
  if (dfa->nodes[node].accept_mb)
    naccepted = check_node_accept_bytes (dfa, node, &mctx->input, *pidx);
  else
#endif
  if (type == OP_BACK_REF)
    {
      Idx subexp_idx = dfa->nodes[node].opr.idx + 1;
      if (subexp_idx < nregs)
        naccepted = regs[subexp_idx].rm_eo - regs[subexp_idx].rm_so;

      if (fs != NULL)
        {
          if (subexp_idx >= nregs
              || regs[subexp_idx].rm_so == -1
              || regs[subexp_idx].rm_eo == -1)
            return -1;

          if (naccepted)
            {
              const unsigned char *buf = re_string_get_buffer (&mctx->input);
              if (mctx->input.valid_len - *pidx < naccepted
                  || memcmp (buf + regs[subexp_idx].rm_so,
                             buf + *pidx, naccepted) != 0)
                return -1;
            }
        }

      if (naccepted == 0)
        {
          bool ok = re_node_set_insert (eps_via_nodes, node);
          if (__glibc_unlikely (! ok))
            return -2;

          if (dfa->edests[node].nelem > 0)
            {
              Idx dest_node = dfa->edests[node].elems[0];
              if (*pidx <= mctx->match_last
                  && mctx->state_log[*pidx] != NULL
                  && re_node_set_contains (&mctx->state_log[*pidx]->nodes,
                                           dest_node))
                return dest_node;
            }
        }
    }

  if (naccepted != 0
      || check_node_accept (mctx, dfa->nodes + node, *pidx))
    {
      Idx dest_node = dfa->nexts[node];
      *pidx = (naccepted == 0) ? *pidx + 1 : *pidx + naccepted;

      if (fs && (*pidx > mctx->match_last || mctx->state_log[*pidx] == NULL
                 || !re_node_set_contains (&mctx->state_log[*pidx]->nodes,
                                           dest_node)))
        return -1;

      re_node_set_empty (eps_via_nodes);
      return dest_node;
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
pop_fail_stack(struct re_fail_stack_t *fs, Idx *pidx, Idx nregs,
               regmatch_t *regs, regmatch_t *prevregs,
               re_node_set *eps_via_nodes)
{
  if (fs == NULL || pidx == NULL || regs == NULL || prevregs == NULL || eps_via_nodes == NULL)
    return -1;
  if (fs->num <= 0)
    return -1;
  if (nregs < 0)
    return -1;

  size_t count = (size_t)nregs;
  if (count > 0 && sizeof(regmatch_t) > 0) {
    if (count > SIZE_MAX / sizeof(regmatch_t))
      return -1;
  }
  size_t bytes = count * sizeof(regmatch_t);

  Idx top = fs->num - 1;

  if (count > 0 && fs->stack[top].regs == NULL)
    return -1;

  fs->num = top;

  *pidx = fs->stack[top].idx;

  if (bytes > 0) {
    memcpy(regs, fs->stack[top].regs, bytes);
    memcpy(prevregs, fs->stack[top].regs + count, bytes);
  }

  re_node_set_free(eps_via_nodes);
  re_free(fs->stack[top].regs);
  *eps_via_nodes = fs->stack[top].eps_via_nodes;

  DEBUG_ASSERT(0 <= fs->stack[top].node);
  Idx node = fs->stack[top].node;

  fs->stack[top].regs = NULL;

  return node;
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
free_fail_stack_return(struct re_fail_stack_t *fs)
{
    if (fs == NULL)
        return REG_NOERROR;

    if (fs->stack != NULL)
    {
        Idx fs_idx;
        for (fs_idx = 0; fs_idx < fs->num; ++fs_idx)
        {
            re_node_set_free(&fs->stack[fs_idx].eps_via_nodes);
            if (fs->stack[fs_idx].regs != NULL)
                re_free(fs->stack[fs_idx].regs);
        }
        re_free(fs->stack);
    }

    return REG_NOERROR;
}

static void
update_regs(const re_dfa_t *dfa, regmatch_t *pmatch,
            regmatch_t *prev_idx_match, Idx cur_node, Idx cur_idx, Idx nmatch)
{
  if (!dfa || !pmatch || nmatch <= 0)
    return;

  int type = dfa->nodes[cur_node].type;

  if (type == OP_OPEN_SUBEXP)
    {
      Idx reg_num = dfa->nodes[cur_node].opr.idx + 1;
      if (reg_num >= 0 && reg_num < nmatch)
        {
          pmatch[reg_num].rm_so = cur_idx;
          pmatch[reg_num].rm_eo = -1;
        }
      return;
    }

  if (type == OP_CLOSE_SUBEXP)
    {
      Idx reg_num = dfa->nodes[cur_node].opr.idx + 1;
      if (reg_num >= 0 && reg_num < nmatch)
        {
          size_t bytes = (size_t) nmatch * sizeof(regmatch_t);
          if (bytes / sizeof(regmatch_t) != (size_t) nmatch)
            return;

          if (pmatch[reg_num].rm_so < cur_idx)
            {
              pmatch[reg_num].rm_eo = cur_idx;
              if (prev_idx_match && bytes)
                memcpy(prev_idx_match, pmatch, bytes);
            }
          else
            {
              if (dfa->nodes[cur_node].opt_subexp
                  && prev_idx_match
                  && prev_idx_match[reg_num].rm_so != -1)
                {
                  if (bytes)
                    memcpy(pmatch, prev_idx_match, bytes);
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
  if (__glibc_unlikely (mctx == NULL || sctx == NULL))
    return REG_NOERROR;

  reg_errcode_t err = REG_NOERROR;
  int null_cnt = 0;
  Idx str_idx = sctx->last_str_idx;
  re_node_set cur_dest;

  DEBUG_ASSERT (mctx->state_log != NULL && mctx->state_log[str_idx] != NULL);
  if (__glibc_unlikely (mctx->state_log == NULL || mctx->state_log[str_idx] == NULL))
    return REG_NOERROR;

  err = re_node_set_init_1 (&cur_dest, sctx->last_node);
  if (__glibc_unlikely (err != REG_NOERROR))
    return err;

  err = update_cur_sifted_state (mctx, sctx, str_idx, &cur_dest);
  if (__glibc_unlikely (err != REG_NOERROR))
    goto cleanup;

  while (str_idx > 0)
    {
      null_cnt = (sctx->sifted_states[str_idx] == NULL) ? (null_cnt + 1) : 0;
      if (null_cnt > mctx->max_mb_elem_len)
        {
          size_t bytes = sizeof (re_dfastate_t *) * (size_t) str_idx;
          if (sctx->sifted_states != NULL && bytes > 0)
            memset (sctx->sifted_states, 0, bytes);
          err = REG_NOERROR;
          goto cleanup;
        }

      re_node_set_empty (&cur_dest);
      --str_idx;

      if (mctx->state_log[str_idx] != NULL)
        {
          err = build_sifted_states (mctx, sctx, str_idx, &cur_dest);
          if (__glibc_unlikely (err != REG_NOERROR))
            goto cleanup;
        }

      err = update_cur_sifted_state (mctx, sctx, str_idx, &cur_dest);
      if (__glibc_unlikely (err != REG_NOERROR))
        goto cleanup;
    }

  err = REG_NOERROR;

cleanup:
  re_node_set_free (&cur_dest);
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
  Idx top = mctx->state_log_top;

  {
    const Idx bufs_len = mctx->input.bufs_len;
    const Idx valid_len = mctx->input.valid_len;
    const Idx total_len = mctx->input.len;
    int need_extend =
      ((next_state_log_idx >= bufs_len && bufs_len < total_len)
       || (next_state_log_idx >= valid_len && valid_len < total_len));

    if (need_extend)
      {
        reg_errcode_t err = extend_buffers (mctx, next_state_log_idx + 1);
        if (__glibc_unlikely (err != REG_NOERROR))
          return err;
      }
  }

  if (top < next_state_log_idx)
    {
      size_t count = (size_t) (next_state_log_idx - top);
      if (count > (size_t)-1 / sizeof (re_dfastate_t *))
        return REG_ESPACE;

      memset (mctx->state_log + top + 1, 0,
              sizeof (re_dfastate_t *) * count);
      mctx->state_log_top = next_state_log_idx;
    }

  return REG_NOERROR;
}

static reg_errcode_t
merge_state_array(const re_dfa_t *dfa, re_dfastate_t **dst,
                  re_dfastate_t **src, Idx num)
{
  if (num <= 0)
    return REG_NOERROR;

  reg_errcode_t err = REG_NOERROR;
  for (Idx st_idx = 0; st_idx < num; ++st_idx)
    {
      re_dfastate_t *dstate = dst[st_idx];
      re_dfastate_t *sstate = src[st_idx];

      if (dstate == NULL)
        {
          dst[st_idx] = sstate;
          continue;
        }

        if (sstate == NULL)
          continue;

        re_node_set merged_set;
        err = re_node_set_init_union(&merged_set, &dstate->nodes, &sstate->nodes);
        if (__glibc_unlikely(err != REG_NOERROR))
          return err;

        re_dfastate_t *new_state = re_acquire_state(&err, dfa, &merged_set);
        re_node_set_free(&merged_set);
        dst[st_idx] = new_state;
        if (__glibc_unlikely(err != REG_NOERROR))
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
  const re_dfastate_t *log_state = mctx->state_log[str_idx];
  const re_node_set *candidates = log_state ? &log_state->nodes : NULL;

  if (dest_nodes->nelem != 0)
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
  else
    {
      sctx->sifted_states[str_idx] = NULL;
    }

  if (log_state && log_state->has_backref)
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
sub_epsilon_src_nodes(const re_dfa_t *dfa, Idx node, re_node_set *dest_nodes,
                      const re_node_set *candidates)
{
    Idx ecl_idx;
    reg_errcode_t err;
    const re_node_set *inv_eclosure = dfa->inveclosures + node;
    re_node_set except_nodes;

    re_node_set_init_empty(&except_nodes);

    for (ecl_idx = 0; ecl_idx < inv_eclosure->nelem; ++ecl_idx)
    {
        Idx cur_node = inv_eclosure->elems[ecl_idx];

        if (cur_node == node)
            continue;

        if (IS_EPSILON_NODE(dfa->nodes[cur_node].type))
        {
            const re_node_set *edests = dfa->edests + cur_node;
            Idx edst1, edst2;
            int edst1_needed, edst2_needed;

            if (edests->nelem < 1)
                continue;

            edst1 = edests->elems[0];
            edst2 = (edests->nelem > 1) ? edests->elems[1] : -1;

            edst1_needed = (!re_node_set_contains(inv_eclosure, edst1)
                            && re_node_set_contains(dest_nodes, edst1));
            edst2_needed = (edst2 > 0
                            && !re_node_set_contains(inv_eclosure, edst2)
                            && re_node_set_contains(dest_nodes, edst2));

            if (edst1_needed || edst2_needed)
            {
                err = re_node_set_add_intersect(&except_nodes, candidates,
                                                dfa->inveclosures + cur_node);
                if (err != REG_NOERROR)
                {
                    re_node_set_free(&except_nodes);
                    return err;
                }
            }
        }
    }

    for (ecl_idx = 0; ecl_idx < inv_eclosure->nelem; ++ecl_idx)
    {
        Idx cur_node = inv_eclosure->elems[ecl_idx];

        if (!re_node_set_contains(&except_nodes, cur_node))
        {
            Idx idxp1 = re_node_set_contains(dest_nodes, cur_node);
            if (idxp1 > 0)
                re_node_set_remove_at(dest_nodes, idxp1 - 1);
        }
    }

    re_node_set_free(&except_nodes);
    return REG_NOERROR;
}

static bool
check_dst_limits (const re_match_context_t *mctx, const re_node_set *limits,
                  Idx dst_node, Idx dst_idx, Idx src_node, Idx src_idx)
{
  const re_dfa_t *dfa;
  Idx dst_bkref_idx, src_bkref_idx;
  Idx lim_idx;

  if (!mctx || !limits)
    return false;

  dfa = mctx->dfa;
  if (!dfa || !mctx->bkref_ents || !limits->elems || !dfa->nodes)
    return false;

  if (limits->nelem <= 0)
    return false;

  dst_bkref_idx = search_cur_bkref_entry (mctx, dst_idx);
  src_bkref_idx = search_cur_bkref_entry (mctx, src_idx);

  for (lim_idx = 0; lim_idx < limits->nelem; ++lim_idx)
    {
      Idx elem;
      const struct re_backref_cache_entry *ent;
      Idx subexp_idx;
      Idx dst_pos, src_pos;

      elem = limits->elems[lim_idx];
      ent = mctx->bkref_ents + elem;
      subexp_idx = dfa->nodes[ent->node].opr.idx;

      dst_pos = check_dst_limits_calc_pos (mctx, elem, subexp_idx,
                                           dst_node, dst_idx, dst_bkref_idx);
      src_pos = check_dst_limits_calc_pos (mctx, elem, subexp_idx,
                                           src_node, src_idx, src_bkref_idx);

      if (src_pos != dst_pos)
        return true;
    }
  return false;
}

static int
check_dst_limits_calc_pos_1 (const re_match_context_t *mctx, int boundaries,
                             Idx subexp_idx, Idx from_node, Idx bkref_idx)
{
  const int OPEN_MASK = 1;
  const int CLOSE_MASK = 2;
  const re_dfa_t *dfa;
  const re_node_set *eclosures;
  Idx node_idx;

  if (!mctx || !mctx->dfa)
    return (boundaries & CLOSE_MASK) ? 1 : 0;

  dfa = mctx->dfa;

  if (from_node < 0)
    return (boundaries & CLOSE_MASK) ? 1 : 0;

  eclosures = dfa->eclosures + from_node;
  if (!eclosures)
    return (boundaries & CLOSE_MASK) ? 1 : 0;

  for (node_idx = 0; node_idx < eclosures->nelem; ++node_idx)
    {
      Idx node = eclosures->elems[node_idx];
      int type = dfa->nodes[node].type;

      switch (type)
        {
        case OP_BACK_REF:
          if (bkref_idx != -1)
            {
              struct re_backref_cache_entry *p = mctx->bkref_ents + bkref_idx;
              for (;; ++p)
                {
                  int skip = 0;
                  bitset_word_t mask = 0;
                  Idx dst;
                  int cpos;

                  if (p->node != node)
                    skip = 1;
                  else if (subexp_idx < BITSET_WORD_BITS)
                    {
                      mask = (bitset_word_t) 1 << subexp_idx;
                      if (!(p->eps_reachable_subexps_map & mask))
                        skip = 1;
                    }

                  if (!skip)
                    {
                      if (dfa->edests[node].nelem > 0)
                        {
                          dst = dfa->edests[node].elems[0];
                          if (dst == from_node)
                            {
                              if (boundaries & OPEN_MASK)
                                return -1;
                              return 0;
                            }

                          cpos = check_dst_limits_calc_pos_1 (mctx, boundaries, subexp_idx, dst, bkref_idx);
                          if (cpos == -1)
                            return -1;
                          if (cpos == 0 && (boundaries & CLOSE_MASK))
                            return 0;

                          if (subexp_idx < BITSET_WORD_BITS)
                            p->eps_reachable_subexps_map &= ~mask;
                        }
                    }

                  if (!p->more)
                    break;
                }
            }
          break;

        case OP_OPEN_SUBEXP:
          if ((boundaries & OPEN_MASK) && subexp_idx == dfa->nodes[node].opr.idx)
            return -1;
          break;

        case OP_CLOSE_SUBEXP:
          if ((boundaries & CLOSE_MASK) && subexp_idx == dfa->nodes[node].opr.idx)
            return 0;
          break;

        default:
          break;
        }
    }

  return (boundaries & CLOSE_MASK) ? 1 : 0;
}

static int
check_dst_limits_calc_pos (const re_match_context_t *mctx, Idx limit,
                           Idx subexp_idx, Idx from_node, Idx str_idx,
                           Idx bkref_idx)
{
  const struct re_backref_cache_entry *lim = &mctx->bkref_ents[limit];

  if (str_idx < lim->subexp_from)
    return -1;

  if (str_idx > lim->subexp_to)
    return 1;

  {
    const int at_from = (str_idx == lim->subexp_from);
    const int at_to = (str_idx == lim->subexp_to);

    if (!at_from && !at_to)
      return 0;

    {
      const int boundaries = (at_from ? 1 : 0) | (at_to ? 2 : 0);
      return check_dst_limits_calc_pos_1 (mctx, boundaries, subexp_idx,
                                          from_node, bkref_idx);
    }
  }
}

/* Check the limitations of sub expressions LIMITS, and remove the nodes
   which are against limitations from DEST_NODES. */

static reg_errcode_t
check_subexp_limits (const re_dfa_t *dfa, re_node_set *dest_nodes,
                     const re_node_set *candidates, re_node_set *limits,
                     struct re_backref_cache_entry *bkref_ents, Idx str_idx)
{
  reg_errcode_t err;
  Idx lim_idx;

  for (lim_idx = 0; lim_idx < limits->nelem; ++lim_idx)
    {
      struct re_backref_cache_entry *ent = &bkref_ents[limits->elems[lim_idx]];
      Idx node_idx;

      if (str_idx <= ent->subexp_from || ent->str_idx < str_idx)
        continue;

      {
        Idx subexp_idx = dfa->nodes[ent->node].opr.idx;

        if (ent->subexp_to == str_idx)
          {
            Idx ops_node = -1;
            Idx cls_node = -1;

            for (node_idx = 0; node_idx < dest_nodes->nelem; ++node_idx)
              {
                Idx node = dest_nodes->elems[node_idx];
                re_token_type_t type = dfa->nodes[node].type;
                if (type == OP_OPEN_SUBEXP
                    && subexp_idx == dfa->nodes[node].opr.idx)
                  ops_node = node;
                else if (type == OP_CLOSE_SUBEXP
                         && subexp_idx == dfa->nodes[node].opr.idx)
                  cls_node = node;
              }

            if (ops_node >= 0)
              {
                err = sub_epsilon_src_nodes (dfa, ops_node, dest_nodes, candidates);
                if (__glibc_unlikely (err != REG_NOERROR))
                  return err;
              }

            if (cls_node >= 0)
              {
                for (node_idx = 0; node_idx < dest_nodes->nelem; ++node_idx)
                  {
                    Idx node = dest_nodes->elems[node_idx];
                    int in_inv = re_node_set_contains (dfa->inveclosures + node, cls_node);
                    int in_ecl = re_node_set_contains (dfa->eclosures + node, cls_node);
                    if (!in_inv && !in_ecl)
                      {
                        err = sub_epsilon_src_nodes (dfa, node, dest_nodes, candidates);
                        if (__glibc_unlikely (err != REG_NOERROR))
                          return err;
                        --node_idx;
                      }
                  }
              }
          }
        else
          {
            for (node_idx = 0; node_idx < dest_nodes->nelem; ++node_idx)
              {
                Idx node = dest_nodes->elems[node_idx];
                re_token_type_t type = dfa->nodes[node].type;
                if ((type == OP_CLOSE_SUBEXP || type == OP_OPEN_SUBEXP)
                    && subexp_idx == dfa->nodes[node].opr.idx)
                  {
                    err = sub_epsilon_src_nodes (dfa, node, dest_nodes, candidates);
                    if (__glibc_unlikely (err != REG_NOERROR))
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

  if (cur_idx > mctx->state_log_top || mctx->state_log[cur_idx] == NULL)
    {
      mctx->state_log[cur_idx] = next_state;
      if (cur_idx > mctx->state_log_top)
        mctx->state_log_top = cur_idx;
    }
  else
    {
      re_dfastate_t *pstate = mctx->state_log[cur_idx];
      re_node_set next_nodes;
      re_node_set *log_nodes = pstate->entrance_nodes;
      re_node_set *table_nodes = NULL;

      if (next_state != NULL)
        {
          table_nodes = next_state->entrance_nodes;
          *err = re_node_set_init_union (&next_nodes, table_nodes, log_nodes);
          if (__glibc_unlikely (*err != REG_NOERROR))
            return NULL;
        }
      else
        next_nodes = *log_nodes;

      {
        unsigned int context = re_string_context_at (&mctx->input, cur_idx - 1, mctx->eflags);
        next_state = mctx->state_log[cur_idx]
          = re_acquire_state_context (err, dfa, &next_nodes, context);
      }

      if (table_nodes != NULL)
        re_node_set_free (&next_nodes);
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
  re_dfastate_t *cur_state = NULL;

  if (err == NULL || mctx == NULL || mctx->state_log == NULL)
    return NULL;

  for (;;)
    {
      Idx max = mctx->state_log_top;
      Idx cur_str_idx = re_string_cur_idx (&mctx->input);

      for (;;)
        {
          if (++cur_str_idx > max)
            return NULL;
          re_string_skip_bytes (&mctx->input, 1);
          if (mctx->state_log[cur_str_idx] != NULL)
            break;
        }

      cur_state = merge_state_with_log (err, mctx, NULL);
      if (*err != REG_NOERROR || cur_state != NULL)
        break;
    }

  return cur_state;
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
  const re_token_t *const nodes = dfa->nodes;
  const bitset_word_t used_bkref_map = dfa->used_bkref_map;
  reg_errcode_t err = REG_NOERROR;

  for (Idx node_idx = 0; node_idx < cur_nodes->nelem; ++node_idx)
    {
      Idx node = cur_nodes->elems[node_idx];
      const re_token_t *t = &nodes[node];

      if (t->type != OP_OPEN_SUBEXP)
        continue;

      Idx idx = t->opr.idx;
      if (idx >= BITSET_WORD_BITS)
        continue;

      bitset_word_t mask = (bitset_word_t) 1 << idx;
      if ((used_bkref_map & mask) == 0)
        continue;

      err = match_ctx_add_subtop (mctx, node, str_idx);
      if (__glibc_unlikely (err != REG_NOERROR))
        return err;
    }
  return REG_NOERROR;
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
transit_state_bkref (re_match_context_t *mctx, const re_node_set *nodes)
{
  const re_dfa_t *const dfa = mctx->dfa;
  reg_errcode_t err;
  Idx i;
  Idx cur_str_idx = re_string_cur_idx (&mctx->input);

  for (i = 0; i < nodes->nelem; ++i)
    {
      Idx node_idx = nodes->elems[i];
      const re_token_t *node = dfa->nodes + node_idx;
      unsigned int context;
      Idx bkc_idx;

      if (node->type != OP_BACK_REF)
        continue;

      if (node->constraint)
        {
          context = re_string_context_at (&mctx->input, cur_str_idx,
                                          mctx->eflags);
          if (NOT_SATISFY_NEXT_CONSTRAINT (node->constraint, context))
            continue;
        }

      bkc_idx = mctx->nbkref_ents;
      err = get_subexp (mctx, node_idx, cur_str_idx);
      if (__glibc_unlikely (err != REG_NOERROR))
        goto free_return;

      DEBUG_ASSERT (dfa->nexts[node_idx] != -1);
      for (; bkc_idx < mctx->nbkref_ents; ++bkc_idx)
        {
          struct re_backref_cache_entry *bkref_ent = mctx->bkref_ents + bkc_idx;
          Idx subexp_len;
          re_node_set *new_dest_nodes;
          Idx dest_str_idx;
          re_dfastate_t *dest_state;
          Idx prev_nelem;

          if (bkref_ent->node != node_idx || bkref_ent->str_idx != cur_str_idx)
            continue;

          subexp_len = bkref_ent->subexp_to - bkref_ent->subexp_from;
          new_dest_nodes = (subexp_len == 0
                            ? dfa->eclosures + dfa->edests[node_idx].elems[0]
                            : dfa->eclosures + dfa->nexts[node_idx]);

          dest_str_idx = cur_str_idx + subexp_len;
          context = re_string_context_at (&mctx->input, dest_str_idx - 1,
                                          mctx->eflags);
          dest_state = mctx->state_log[dest_str_idx];
          prev_nelem = (mctx->state_log[cur_str_idx] == NULL
                        ? 0
                        : mctx->state_log[cur_str_idx]->nodes.nelem);

          if (dest_state == NULL)
            {
              re_dfastate_t *acquired_state
                = re_acquire_state_context (&err, dfa, new_dest_nodes, context);
              mctx->state_log[dest_str_idx] = acquired_state;
              if (__glibc_unlikely (acquired_state == NULL
                                    && err != REG_NOERROR))
                goto free_return;
            }
          else
            {
              re_node_set dest_nodes;
              err = re_node_set_init_union (&dest_nodes,
                                            dest_state->entrance_nodes,
                                            new_dest_nodes);
              if (__glibc_unlikely (err != REG_NOERROR))
                goto free_return;

              {
                re_dfastate_t *acquired_state
                  = re_acquire_state_context (&err, dfa, &dest_nodes, context);
                re_node_set_free (&dest_nodes);
                mctx->state_log[dest_str_idx] = acquired_state;
                if (__glibc_unlikely (acquired_state == NULL
                                      && err != REG_NOERROR))
                  goto free_return;
              }
            }

          if (subexp_len == 0
              && mctx->state_log[cur_str_idx] != NULL
              && mctx->state_log[cur_str_idx]->nodes.nelem > prev_nelem)
            {
              err = check_subexp_matching_top (mctx, new_dest_nodes,
                                               cur_str_idx);
              if (__glibc_unlikely (err != REG_NOERROR))
                goto free_return;
              err = transit_state_bkref (mctx, new_dest_nodes);
              if (__glibc_unlikely (err != REG_NOERROR))
                goto free_return;
            }
        }
    }
  err = REG_NOERROR;
 free_return:
  return err;
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
get_subexp_sub(re_match_context_t *mctx, const re_sub_match_top_t *sub_top,
               re_sub_match_last_t *sub_last, Idx bkref_node, Idx bkref_str)
{
  const Idx last_idx = sub_last->str_idx;
  const Idx top_idx = sub_top->str_idx;

  reg_errcode_t err = check_arrival(mctx, &sub_last->path, sub_last->node,
                                    last_idx, bkref_node, bkref_str,
                                    OP_OPEN_SUBEXP);
  if (__glibc_unlikely(err != REG_NOERROR))
    return err;

  err = match_ctx_add_entry(mctx, bkref_node, bkref_str, top_idx, last_idx);
  if (__glibc_unlikely(err != REG_NOERROR))
    return err;

  return clean_state_log_if_needed(mctx, bkref_str + (last_idx - top_idx));
}

/* Find the first node which is '(' or ')' and whose index is SUBEXP_IDX.
   Search '(' if FL_OPEN, or search ')' otherwise.
   TODO: This function isn't efficient...
	 Because there might be more than one nodes whose types are
	 OP_OPEN_SUBEXP and whose index is SUBEXP_IDX, we must check all
	 nodes.
	 E.g. RE: (a){2}  */

static Idx
find_subexp_node(const re_dfa_t *dfa, const re_node_set *nodes,
                 Idx subexp_idx, int type)
{
    Idx i;

    if (dfa == NULL || nodes == NULL)
        return -1;
    if (dfa->nodes == NULL || nodes->elems == NULL)
        return -1;
    if (nodes->nelem <= 0)
        return -1;

    for (i = 0; i < nodes->nelem; ++i)
    {
        Idx node_index = nodes->elems[i];
        const re_token_t *token;

        if (node_index < 0)
            continue;

        token = &dfa->nodes[node_index];
        if (token->type == type && token->opr.idx == subexp_idx)
            return node_index;
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
  reg_errcode_t err;
  Idx idx;
  re_node_set new_nodes;

  DEBUG_ASSERT (cur_nodes->nelem);

  err = re_node_set_alloc (&new_nodes, cur_nodes->nelem);
  if (__glibc_unlikely (err != REG_NOERROR))
    return err;

  for (idx = 0; idx < cur_nodes->nelem; ++idx)
    {
      Idx cur_node = cur_nodes->elems[idx];
      const re_node_set *eclosure = &dfa->eclosures[cur_node];

      if (find_subexp_node (dfa, eclosure, ex_subexp, type) == -1)
        err = re_node_set_merge (&new_nodes, eclosure);
      else
        err = check_arrival_expand_ecl_sub (dfa, &new_nodes, cur_node,
                                            ex_subexp, type);

      if (__glibc_unlikely (err != REG_NOERROR))
        goto error;
    }

  re_node_set_free (cur_nodes);
  *cur_nodes = new_nodes;
  return REG_NOERROR;

error:
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

static Idx
group_nodes_into_DFAstates (const re_dfa_t *dfa, const re_dfastate_t *state,
			    re_node_set *dests_node, bitset_t *dests_ch)
{
  reg_errcode_t err;
  Idx node_idx, dest_idx, word_idx;
  Idx ndests = 0;
  const re_node_set *cur_nodes = &state->nodes;

  for (node_idx = 0; node_idx < cur_nodes->nelem; ++node_idx)
    {
      const re_token_t *node = &dfa->nodes[cur_nodes->elems[node_idx]];
      const re_token_type_t type = node->type;
      const unsigned int constraint = node->constraint;
      bitset_t accepts;

      bitset_empty (accepts);

      /* Build initial acceptance set for this node. */
      if (type == CHARACTER)
	{
	  bitset_set (accepts, node->opr.c);
	}
      else if (type == SIMPLE_BRACKET)
	{
	  bitset_merge (accepts, node->opr.sbcset);
	}
      else if (type == OP_PERIOD)
	{
#ifdef RE_ENABLE_I18N
	  if (dfa->mb_cur_max > 1)
	    bitset_merge (accepts, dfa->sb_char);
	  else
#endif
	    bitset_set_all (accepts);

	  if (!(dfa->syntax & RE_DOT_NEWLINE))
	    bitset_clear (accepts, '\n');
	  if (dfa->syntax & RE_DOT_NOT_NULL)
	    bitset_clear (accepts, '\0');
	}
#ifdef RE_ENABLE_I18N
      else if (type == OP_UTF8_PERIOD)
	{
	  if (ASCII_CHARS % BITSET_WORD_BITS == 0)
	    memset (accepts, -1, ASCII_CHARS / CHAR_BIT);
	  else
	    bitset_merge (accepts, utf8_sb_map);

	  if (!(dfa->syntax & RE_DOT_NEWLINE))
	    bitset_clear (accepts, '\n');
	  if (dfa->syntax & RE_DOT_NOT_NULL)
	    bitset_clear (accepts, '\0');
	}
#endif
      else
	{
	  continue;
	}

      /* Apply constraints to acceptance set. */
      if (constraint)
	{
	  if (constraint & NEXT_NEWLINE_CONSTRAINT)
	    {
	      const bool accepts_newline = bitset_contain (accepts, NEWLINE_CHAR);
	      bitset_empty (accepts);
	      if (accepts_newline)
		bitset_set (accepts, NEWLINE_CHAR);
	      else
		continue;
	    }

	  if (constraint & NEXT_ENDBUF_CONSTRAINT)
	    {
	      bitset_empty (accepts);
	      continue;
	    }

	  if (constraint & NEXT_WORD_CONSTRAINT)
	    {
	      bitset_word_t any_set = 0;

	      if (type == CHARACTER && !node->word_char)
		{
		  bitset_empty (accepts);
		  continue;
		}

#ifdef RE_ENABLE_I18N
	      if (dfa->mb_cur_max > 1)
		for (word_idx = 0; word_idx < BITSET_WORDS; ++word_idx)
		  any_set |= (accepts[word_idx]
			      &= (dfa->word_char[word_idx] | ~dfa->sb_char[word_idx]));
	      else
#endif
		for (word_idx = 0; word_idx < BITSET_WORDS; ++word_idx)
		  any_set |= (accepts[word_idx] &= dfa->word_char[word_idx]);

	      if (!any_set)
		continue;
	    }

	  if (constraint & NEXT_NOTWORD_CONSTRAINT)
	    {
	      bitset_word_t any_set = 0;

	      if (type == CHARACTER && node->word_char)
		{
		  bitset_empty (accepts);
		  continue;
		}

#ifdef RE_ENABLE_I18N
	      if (dfa->mb_cur_max > 1)
		for (word_idx = 0; word_idx < BITSET_WORDS; ++word_idx)
		  any_set |= (accepts[word_idx]
			      &= ~(dfa->word_char[word_idx] & dfa->sb_char[word_idx]));
	      else
#endif
		for (word_idx = 0; word_idx < BITSET_WORDS; ++word_idx)
		  any_set |= (accepts[word_idx] &= ~dfa->word_char[word_idx]);

	      if (!any_set)
		continue;
	    }
	}

      /* Distribute acceptance set into destination groups. */
      {
	bitset_t remaining;
	bitset_copy (remaining, accepts);

	for (dest_idx = 0; dest_idx < ndests; ++dest_idx)
	  {
	    bitset_t intersec;
	    bitset_t remains;
	    bitset_word_t has_intersec = 0;
	    bitset_word_t has_remains = 0;
	    bitset_word_t has_remaining = 0;

	    if (type == CHARACTER && !bitset_contain (dests_ch[dest_idx], node->opr.c))
	      continue;

	    for (word_idx = 0; word_idx < BITSET_WORDS; ++word_idx)
	      {
		const bitset_word_t w = remaining[word_idx];
		const bitset_word_t d = dests_ch[dest_idx][word_idx];
		const bitset_word_t i = w & d;
		intersec[word_idx] = i;
		has_intersec |= i;
	      }

	    if (!has_intersec)
	      continue;

	    /* Determine if dests_ch[dest_idx] is subset of remaining. */
	    for (word_idx = 0; word_idx < BITSET_WORDS; ++word_idx)
	      {
		const bitset_word_t d = dests_ch[dest_idx][word_idx];
		const bitset_word_t r = remaining[word_idx];
		const bitset_word_t rem = d & ~r;
		remains[word_idx] = rem;
		has_remains |= rem;
	      }

	    if (has_remains)
	      {
		bitset_copy (dests_ch[ndests], remains);
		bitset_copy (dests_ch[dest_idx], intersec);
		err = re_node_set_init_copy (dests_node + ndests, &dests_node[dest_idx]);
		if (__glibc_unlikely (err != REG_NOERROR))
		  goto error_return;
		++ndests;
	      }
	    else
	      {
		/* Replace dest's charset with intersection for consistent updates. */
		bitset_copy (dests_ch[dest_idx], intersec);
	      }

	    if (__glibc_unlikely (!re_node_set_insert (&dests_node[dest_idx], cur_nodes->elems[node_idx])))
	      goto error_return;

	    for (word_idx = 0; word_idx < BITSET_WORDS; ++word_idx)
	      {
		const bitset_word_t new_rem = remaining[word_idx] & ~dests_ch[dest_idx][word_idx];
		has_remaining |= new_rem;
		remaining[word_idx] = new_rem;
	      }

	    if (!has_remaining)
	      break;
	  }

	if (dest_idx == ndests)
	  {
	    bitset_copy (dests_ch[ndests], remaining);
	    err = re_node_set_init_1 (dests_node + ndests, cur_nodes->elems[node_idx]);
	    if (__glibc_unlikely (err != REG_NOERROR))
	      goto error_return;
	    ++ndests;
	  }
      }
    }

  assume (ndests <= SBC_MAX);
  return ndests;

error_return:
  for (dest_idx = 0; dest_idx < ndests; ++dest_idx)
    re_node_set_free (dests_node + dest_idx);
  return -1;
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
    return false;

  const unsigned char ch = re_string_byte_at (&mctx->input, idx);

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
      {
        const unsigned int syntax = mctx->dfa->syntax;
        const bool is_newline_blocked = (ch == '\n' && !(syntax & RE_DOT_NEWLINE));
        const bool is_null_blocked = (ch == '\0' && (syntax & RE_DOT_NOT_NULL));
        if (is_newline_blocked || is_null_blocked)
          return false;
      }
      break;

    default:
      return false;
    }

  if (node->constraint != 0U)
    {
      const unsigned int context = re_string_context_at (&mctx->input, idx,
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
match_ctx_clean (re_match_context_t *mctx)
{
  if (mctx == NULL)
    return;

  if (mctx->sub_tops != NULL && mctx->nsub_tops > 0)
    {
      Idx st_idx;
      for (st_idx = 0; st_idx < mctx->nsub_tops; ++st_idx)
        {
          re_sub_match_top_t *top = mctx->sub_tops[st_idx];
          if (top == NULL)
            {
              mctx->sub_tops[st_idx] = NULL;
              continue;
            }

          if (top->lasts != NULL && top->nlasts > 0)
            {
              Idx sl_idx;
              for (sl_idx = 0; sl_idx < top->nlasts; ++sl_idx)
                {
                  re_sub_match_last_t *last = top->lasts[sl_idx];
                  if (last == NULL)
                    continue;

                  re_free (last->path.array);
                  last->path.array = NULL;
                  re_free (last);
                  top->lasts[sl_idx] = NULL;
                }
            }

          re_free (top->lasts);
          top->lasts = NULL;
          top->nlasts = 0;

          if (top->path != NULL)
            {
              re_free (top->path->array);
              top->path->array = NULL;
              re_free (top->path);
              top->path = NULL;
            }

          re_free (top);
          mctx->sub_tops[st_idx] = NULL;
        }
    }

  mctx->nsub_tops = 0;
  mctx->nbkref_ents = 0;
}

/* Free all the memory associated with MCTX.  */

static void
match_ctx_free(re_match_context_t *mctx)
{
    if (mctx == NULL)
        return;

    match_ctx_clean(mctx);

    if (mctx->sub_tops != NULL) {
        re_free(mctx->sub_tops);
        mctx->sub_tops = NULL;
    }

    if (mctx->bkref_ents != NULL) {
        re_free(mctx->bkref_ents);
        mctx->bkref_ents = NULL;
    }
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
search_cur_bkref_entry(const re_match_context_t *mctx, Idx str_idx)
{
  if (mctx == NULL || mctx->bkref_ents == NULL || mctx->nbkref_ents <= 0)
    return -1;

  Idx count = mctx->nbkref_ents;
  Idx left = 0;
  Idx right = count;

  while (left < right)
    {
      Idx mid = left + (right - left) / 2;
      Idx cur = mctx->bkref_ents[mid].str_idx;

      if (cur < str_idx)
        left = mid + 1;
      else
        right = mid;
    }

  if (left < count && mctx->bkref_ents[left].str_idx == str_idx)
    return left;

  return -1;
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
match_ctx_add_sublast(re_sub_match_top_t *subtop, Idx node, Idx str_idx)
{
  if (subtop == NULL)
    return NULL;

  if (subtop->nlasts == subtop->alasts)
    {
      Idx old_alasts = subtop->alasts;
      Idx new_alasts = old_alasts * 2 + 1;
      if (new_alasts <= old_alasts)
        return NULL;

      re_sub_match_last_t **new_array =
        re_realloc(subtop->lasts, re_sub_match_last_t *, new_alasts);
      if (new_array == NULL)
        return NULL;

      subtop->lasts = new_array;
      subtop->alasts = new_alasts;
    }

  re_sub_match_last_t *new_entry = calloc(1, sizeof(*new_entry));
  if (new_entry == NULL)
    return NULL;

  subtop->lasts[subtop->nlasts] = new_entry;
  new_entry->node = node;
  new_entry->str_idx = str_idx;
  ++subtop->nlasts;

  return new_entry;
}

static void
sift_ctx_init (re_sift_context_t *sctx, re_dfastate_t **sifted_sts,
               re_dfastate_t **limited_sts, Idx last_node, Idx last_str_idx)
{
  if (sctx == NULL)
    return;

  sctx->sifted_states = sifted_sts;
  sctx->limited_states = limited_sts;
  sctx->last_node = last_node;
  sctx->last_str_idx = last_str_idx;
  re_node_set_init_empty (&sctx->limits);
}
