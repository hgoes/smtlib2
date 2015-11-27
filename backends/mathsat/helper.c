#include "helper.h"

msat_term msat_helper_make_congruence(msat_env e,const char* modulus,msat_term t1,msat_term t2) {
  mpz_t mod;
  mpz_init_set_str(mod,modulus,10);
  return msat_make_int_modular_congruence(e,mod,t1,t2);
}

char* msat_helper_get_number(msat_env e,msat_term t) {
  mpq_t out;
  mpq_init(out);
  msat_term_to_number(e,t,out);
  return mpq_get_str(NULL,10,out);
}

char* msat_helper_is_congruence(msat_env e,msat_term t) {
  mpz_t out;
  mpz_init(out);
  int res = msat_term_is_int_modular_congruence(e,t,out);
  if(res) {
    return mpz_get_str(NULL,10,out);
  } else {
    return NULL;
  }
}

bool msat_helper_term_is_error(msat_term t) {
  return MSAT_ERROR_TERM(t);
}
