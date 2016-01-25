#ifndef __HELPER_H
#define __HELPER_H

#include <mathsat.h>
#include <gmp.h>
#include <stdbool.h>

msat_term msat_helper_make_congruence(msat_env e,const char* modulus,msat_term t1,msat_term t2);
char* msat_helper_get_number(msat_env e,msat_term t);
char* msat_helper_is_congruence(msat_env e,msat_term t);
bool msat_helper_term_is_error(msat_term t);

#endif
