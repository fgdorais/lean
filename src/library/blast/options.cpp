/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "library/blast/options.h"

#ifndef LEAN_DEFAULT_BLAST_MAX_DEPTH
#define LEAN_DEFAULT_BLAST_MAX_DEPTH 128
#endif
#ifndef LEAN_DEFAULT_BLAST_INIT_DEPTH
#define LEAN_DEFAULT_BLAST_INIT_DEPTH 1
#endif
#ifndef LEAN_DEFAULT_BLAST_INC_DEPTH
#define LEAN_DEFAULT_BLAST_INC_DEPTH 5
#endif
#ifndef LEAN_DEFAULT_BLAST_TRACE
#define LEAN_DEFAULT_BLAST_TRACE false
#endif
#ifndef LEAN_DEFAULT_BLAST_SUBST
#define LEAN_DEFAULT_BLAST_SUBST true
#endif

namespace lean {
namespace blast {
/* Options */
static name * g_blast_max_depth    = nullptr;
static name * g_blast_init_depth   = nullptr;
static name * g_blast_inc_depth    = nullptr;
static name * g_blast_trace        = nullptr;
static name * g_blast_subst        = nullptr;

unsigned get_blast_max_depth(options const & o) {
    return o.get_unsigned(*g_blast_max_depth, LEAN_DEFAULT_BLAST_MAX_DEPTH);
}
unsigned get_blast_init_depth(options const & o) {
    return o.get_unsigned(*g_blast_init_depth, LEAN_DEFAULT_BLAST_INIT_DEPTH);
}
unsigned get_blast_inc_depth(options const & o) {
    return o.get_unsigned(*g_blast_inc_depth, LEAN_DEFAULT_BLAST_INC_DEPTH);
}
bool get_blast_trace(options const & o) {
    return o.get_bool(*g_blast_trace, LEAN_DEFAULT_BLAST_TRACE);
}
bool get_blast_subst(options const & o) {
    return o.get_bool(*g_blast_subst, LEAN_DEFAULT_BLAST_SUBST);
}

config::config(options const & o) {
    m_max_depth  = get_blast_max_depth(o);
    m_init_depth = get_blast_init_depth(o);
    m_inc_depth  = get_blast_inc_depth(o);
    m_trace      = get_blast_trace(o);
    m_subst      = get_blast_subst(o);
}

LEAN_THREAD_PTR(config, g_config);

scope_config::scope_config(options const & o):
    m_old(g_config),
    m_config(o) {
    g_config = &m_config;
}

scope_config::~scope_config() {
    g_config = m_old;
}

config const & get_config() {
    lean_assert(g_config);
    return *g_config;
}

void initialize_options() {
    g_blast_max_depth  = new name{"blast", "max_depth"};
    g_blast_init_depth = new name{"blast", "init_depth"};
    g_blast_inc_depth  = new name{"blast", "inc_depth"};
    g_blast_trace      = new name{"blast", "trace"};
    g_blast_subst      = new name{"blast", "subst"};

    register_unsigned_option(*blast::g_blast_max_depth, LEAN_DEFAULT_BLAST_MAX_DEPTH,
                             "(blast) max search depth for blast");
    register_unsigned_option(*blast::g_blast_init_depth, LEAN_DEFAULT_BLAST_INIT_DEPTH,
                             "(blast) initial search depth for blast (remark: blast uses iteration deepening)");
    register_unsigned_option(*blast::g_blast_inc_depth, LEAN_DEFAULT_BLAST_INC_DEPTH,
                             "(blast) search depth increment for blast (remark: blast uses iteration deepening)");
    register_bool_option(*blast::g_blast_trace, LEAN_DEFAULT_BLAST_TRACE,
                         "(blast) trace");
    register_bool_option(*blast::g_blast_subst, LEAN_DEFAULT_BLAST_SUBST,
                         "(blast) enable subst action");
}
void finalize_options() {
    delete g_blast_max_depth;
    delete g_blast_init_depth;
    delete g_blast_inc_depth;
    delete g_blast_trace;
    delete g_blast_subst;
}
}}