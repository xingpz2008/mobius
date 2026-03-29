#include "seal/seal.h"
#include "seal/util/polyarithsmallmod.h" 
#include "seal/util/rlwe.h"              
#include "seal/util/common.h"
#include "seal/util/iterator.h"

using namespace seal;
using namespace seal::util;
using namespace std;


inline size_t get_poly_count(const SEALContext& context) {
    return context.key_context_data()->parms().poly_modulus_degree();
}

void total_dec(
    const SEALContext &context,
    const Ciphertext &ct,
    const Plaintext &p0,
    const Plaintext &p1,
    Plaintext &m_result);

void partial_dec(
    const SEALContext &context,
    const Ciphertext &ct,
    const SecretKey &sk_share,
    Plaintext &p_share,
    uint64_t B_ct = 4096,      
    uint64_t t_queries = 1,      
    uint64_t alpha = 128,
    bool add_noise = true);

void split_secret_key(
    const SEALContext &context,
    const SecretKey &sk,
    SecretKey &sk0,
    SecretKey &sk1);