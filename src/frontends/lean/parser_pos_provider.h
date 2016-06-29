/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <utility>
#include <memory>
#include "util/rb_map.h"
#include "kernel/pos_info_provider.h"

namespace lean {
typedef rb_map<unsigned, pos_info, unsigned_cmp> pos_info_table;

/* Remark the parser object is also a pos_info_provider */
class parser;

class scope_parser_pos_info_provider {
    parser * m_old_p;
public:
    scope_parser_pos_info_provider(parser & p);
    ~scope_parser_pos_info_provider();
};

pos_info_provider * get_parser_pos_info_provider();

/* Temporary object for providing position information.
   It is only used for exceptions such as parser_nested_exception.
   The idea is to avoid storing the whole parser object in these exceptions. */
class parser_pos_provider : public pos_info_provider {
    pos_info_table m_pos_table;
    std::string    m_strm_name;
    pos_info       m_pos;
public:
    parser_pos_provider(pos_info_table const & pos_table, std::string const & strm_name, pos_info const & some_pos);
    virtual ~parser_pos_provider();
    virtual optional<pos_info> get_pos_info(expr const & e) const;
    virtual pos_info get_some_pos() const;
    virtual char const * get_file_name() const;
};
}
