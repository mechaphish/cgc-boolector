/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2012-2015 Aina Niemetz.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorparse.h"
#include "parser/btorbtor.h"
#include "parser/btorsmt.h"
#include "parser/btorsmt2.h"
#include "boolector.h"
#include "btorcore.h"
#include "btoropt.h"
#include "utils/btorstack.h"
#include "utils/btormem.h"


/* return BOOLECTOR_(SAT|UNSAT|UNKNOWN|PARSE_ERROR) */
static int
btor_parse_aux (Btor * btor, 
                const char *smt_stmt,
                BtorCharStack * prefix,
                const BtorParserAPI * parser_api,
                char ** error_msg,
                int * status)
{
  assert (btor);
  assert (smt_stmt);
  assert (parser_api);
  assert (error_msg);
  assert (status);

  BtorParser *parser;
  BtorParseOpt parse_opt;
  BtorParseResult parse_res;
  BoolectorNode *root;
  int i, root_len, res;
  char *emsg;

  res = BOOLECTOR_UNKNOWN;
  *error_msg = 0;
  parse_opt.verbosity = btor->options.verbosity.val;
  parse_opt.incremental = btor->options.incremental.val;
  parse_opt.interactive = btor->options.parse_interactive.val;
  if (btor->options.incremental_in_depth.val)
    {
      parse_opt.incremental |= BTOR_PARSE_MODE_INCREMENTAL_IN_DEPTH;
      parse_opt.window = btor->options.incremental_in_depth.val;
    }
  else if (btor->options.incremental_look_ahead.val)
    {
      parse_opt.incremental |= BTOR_PARSE_MODE_INCREMENTAL_LOOK_AHEAD;
      parse_opt.window = btor->options.incremental_look_ahead.val;
    }
  else if (btor->options.incremental_interval.val)
    {
      parse_opt.incremental |= BTOR_PARSE_MODE_INCREMENTAL_INTERVAL;
      parse_opt.window = btor->options.incremental_interval.val;
    }
  parse_opt.need_model = btor->options.model_gen.val;

  parser = parser_api->init (btor, &parse_opt);
  
  if ((emsg = parser_api->parse (
          parser, prefix, smt_stmt, &parse_res)))
    {
      res = BOOLECTOR_PARSE_ERROR;
      btor->parse_error_msg = btor_strdup (btor->mm, emsg);
      *error_msg = btor->parse_error_msg;
    }
  else
    {
      res = parse_res.result;

      if (!parse_opt.incremental)
        {
          // FIXME this is only used for non-incremental smt1 and btor
          // maybe move root handling into respective parsers??
          /* assert root(s) if not incremental
           * Note: we have to do this via API calls for API tracing!!! */
          for (i = 0; i < parse_res.noutputs; i++)
            {
              root = parse_res.outputs[i];
              root_len = boolector_get_width (btor, root);
              assert (root_len >= 1);
              if (root_len > 1)
                root = boolector_redor (btor, root);
              else
                root = boolector_copy (btor, root);
              boolector_assert (btor, root);
              boolector_release (btor, root);
            }
        }

      BTOR_MSG (btor->msg, 1, "parsed %d inputs and %d outputs",
          parse_res.ninputs, parse_res.noutputs);
      if (parse_res.logic == BTOR_LOGIC_QF_BV)
        BTOR_MSG (btor->msg, 1, "logic QF_BV");
      else
        {
          assert (parse_res.logic == BTOR_LOGIC_QF_AUFBV);
          BTOR_MSG (btor->msg, 1, "logic QF_AUFBV");
        }

      if (parse_res.status == BOOLECTOR_SAT)
        BTOR_MSG (btor->msg, 1, "status sat");
      else if (parse_res.status == BOOLECTOR_UNSAT)
        BTOR_MSG (btor->msg, 1, "status unsat");
      else
        {
          assert (parse_res.status == BOOLECTOR_UNKNOWN);
          BTOR_MSG (btor->msg, 1, "status unknown");
        }

      BTOR_MSG (btor->msg, 2, "added %d outputs (100%)", parse_res.noutputs);
    }

  if (status) *status = parse_res.status;

  /* cleanup */
  parser_api->reset (parser);

  return res;
}

int
btor_parse (Btor * btor, 
            const char * smt_stmt,
            char ** error_msg,
            int * status)
{
  assert (btor);
  assert (smt_stmt);
  assert (error_msg);
  assert (status);

  const BtorParserAPI *parser_api;
  int res;
  BtorCharStack prefix;
  BtorMemMgr *mem;

  mem = btor_new_mem_mgr ();
  BTOR_INIT_STACK (prefix);

  parser_api = btor_smt2_parser_api ();

  res = btor_parse_aux (btor, smt_stmt, &prefix, 
                        parser_api, error_msg, status);

  /* cleanup */
  BTOR_RELEASE_STACK (mem, prefix);
  btor_delete_mem_mgr (mem);

  return res;
}
