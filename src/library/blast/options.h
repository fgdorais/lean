/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/sexpr/options.h"

namespace lean {
namespace blast {
/** \brief Blast configuration object. */
struct config {
    unsigned                   m_max_depth;
    unsigned                   m_init_depth;
    unsigned                   m_inc_depth;
    bool                       m_trace;
    bool                       m_subst;
    config(options const & o);
};

struct scope_config {
    config * m_old;
    config m_config;
public:
    scope_config(options const & o);
    ~scope_config();
};

config const & get_config();

void initialize_options();
void finalize_options();
}}