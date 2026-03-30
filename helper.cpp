#include "helper.h"
#include <iostream>
#include <vector>
#include <iomanip>
#include <random>
#include <cmath>

using namespace seal;
using namespace seal::util;
using namespace std;

void split_secret_key(
    const SEALContext &context,
    const SecretKey &sk,
    SecretKey &sk0,
    SecretKey &sk1)
{
    auto &context_data = *context.key_context_data();
    auto &parms = context_data.parms();
    auto &coeff_modulus = parms.coeff_modulus();
    size_t coeff_count = parms.poly_modulus_degree();
    size_t coeff_mod_size = coeff_modulus.size();
    
    sk0.data().resize(coeff_count * coeff_mod_size);
    sk1.data().resize(coeff_count * coeff_mod_size);
    sk0.parms_id() = sk.parms_id();
    sk1.parms_id() = sk.parms_id();

    auto prng = parms.random_generator()->create();
    sample_poly_uniform(prng, parms, sk0.data().data());

    auto ntt_tables = context_data.small_ntt_tables();
    RNSIter sk0_iter_transform(sk0.data().data(), coeff_count);
    ntt_negacyclic_harvey(sk0_iter_transform, coeff_mod_size, ntt_tables);

    ConstRNSIter s_iter(sk.data().data(), coeff_count);
    RNSIter s0_iter(sk0.data().data(), coeff_count);
    RNSIter s1_iter(sk1.data().data(), coeff_count);

    SEAL_ITERATE(iter(s_iter, s0_iter, s1_iter, coeff_modulus), coeff_mod_size,
        [&](auto I) {
            sub_poly_coeffmod(get<0>(I), get<1>(I), coeff_count, get<3>(I), get<2>(I));
        }
    );
}

void partial_dec(
    const SEALContext &context,
    const Ciphertext &ct,
    const SecretKey &sk_share,
    Plaintext &p_share,
    uint64_t B_ct,       
    uint64_t t_queries,     
    uint64_t alpha,
    bool add_noise,
    bool use_gaussian) // <--- Added flag for distribution selection
{
    if (ct.size() != 2) throw logic_error("Ciphertext size must be 2");

    auto &context_data = *context.get_context_data(ct.parms_id());
    auto &parms = context_data.parms();
    auto &coeff_modulus = parms.coeff_modulus();
    size_t coeff_count = parms.poly_modulus_degree();
    size_t coeff_mod_size = coeff_modulus.size();

    p_share.parms_id() = parms_id_zero;
    p_share.resize(coeff_count * coeff_mod_size);
    p_share.parms_id() = ct.parms_id();
    p_share.scale() = ct.scale(); 

    ConstRNSIter c1_iter(ct.data(1), coeff_count);
    ConstRNSIter s_share_iter(sk_share.data().data(), coeff_count);
    RNSIter dest_iter(p_share.data(), coeff_count);

    SEAL_ITERATE(iter(c1_iter, s_share_iter, dest_iter, coeff_modulus), coeff_mod_size,
        [&](auto I) {
            dyadic_product_coeffmod(get<0>(I), get<1>(I), coeff_count, get<3>(I), get<2>(I));
        }
    );

    if (add_noise){
        auto noise_poly = allocate_poly(coeff_count, coeff_mod_size, MemoryManager::GetPool());
    
        uint64_t N_dim = coeff_count; 

        // 1. Calculate the theoretical standard deviation required by the Smudging Lemma.
        // Formula: sigma_fld = B_ct * sqrt(t_queries * N * (alpha - 1))
        double sigma_fld = B_ct * std::sqrt(t_queries * N_dim * (alpha - 1));

        if (use_gaussian) {
            // ====================================================================
            // GAUSSIAN DISTRIBUTION (Strictly aligns with theoretical proofs)
            // ====================================================================
            std::random_device rd;
            std::mt19937_64 gen(rd()); 
            std::normal_distribution<double> gaussian_dist(0.0, sigma_fld);

            for (size_t i = 0; i < coeff_count; i++) {
                // Sample from the Gaussian distribution and round to a 64-bit integer
                double sample = gaussian_dist(gen);
                int64_t noise_val = static_cast<int64_t>(std::round(sample));
                
                // Embed the noise into the RNS format for each prime modulus
                for (size_t j = 0; j < coeff_mod_size; j++) {
                    uint64_t qi = parms.coeff_modulus()[j].value();
                    uint64_t rns_val = (noise_val < 0) ? 
                                    (qi - ((uint64_t)(-noise_val) % qi)) % qi : 
                                    ((uint64_t)noise_val % qi);
                    noise_poly.get()[j * coeff_count + i] = rns_val;
                }
            }
        } else {
            // ====================================================================
            // UNIFORM DISTRIBUTION (Optimized for Engineering & Constant-time)
            // ====================================================================
            // To achieve the equivalent standard deviation, we scale the boundary 
            // by sqrt(3) ~ 1.73205. Variance of Uniform [-B, B] is B^2 / 3.
            uint64_t B_noise = static_cast<uint64_t>(std::round(sigma_fld * 1.73205)); 
            auto prng = parms.random_generator()->create();

            for (size_t i = 0; i < coeff_count; i++) {
                // Uniformly sample within [-B_noise, B_noise]
                int64_t noise_val = (prng->generate() % (2 * B_noise + 1)) - B_noise;
                
                for (size_t j = 0; j < coeff_mod_size; j++) {
                    uint64_t qi = parms.coeff_modulus()[j].value();
                    uint64_t rns_val = (noise_val < 0) ? 
                                    (qi - ((uint64_t)(-noise_val) % qi)) % qi : 
                                    ((uint64_t)noise_val % qi);
                    noise_poly.get()[j * coeff_count + i] = rns_val;
                }
            }
        }

        auto ntt_tables = context_data.small_ntt_tables();
        RNSIter noise_iter(noise_poly.get(), coeff_count); 
        ntt_negacyclic_harvey(noise_iter, coeff_mod_size, ntt_tables);

        SEAL_ITERATE(iter(dest_iter, noise_iter, dest_iter, coeff_modulus), coeff_mod_size,
            [&](auto I) {
                add_poly_coeffmod(get<0>(I), get<1>(I), coeff_count, get<3>(I), get<2>(I));
            }
        );
    }
}

void total_dec(
    const SEALContext &context,
    const Ciphertext &ct,
    const Plaintext &p0,
    const Plaintext &p1,
    Plaintext &m_result)
{
    auto &context_data = *context.get_context_data(ct.parms_id());
    auto &parms = context_data.parms();
    auto &coeff_modulus = parms.coeff_modulus();
    size_t coeff_count = parms.poly_modulus_degree();
    size_t coeff_mod_size = coeff_modulus.size();

    m_result.resize(coeff_count * coeff_mod_size);
    m_result.parms_id() = ct.parms_id();
    m_result.scale() = ct.scale();

    ConstRNSIter c0_iter(ct.data(0), coeff_count);
    ConstRNSIter p0_iter(p0.data(), coeff_count);
    ConstRNSIter p1_iter(p1.data(), coeff_count);
    RNSIter dest_iter(m_result.data(), coeff_count);

    SEAL_ITERATE(iter(c0_iter, p0_iter, p1_iter, dest_iter, coeff_modulus), coeff_mod_size,
        [&](auto I) {
            add_poly_coeffmod(get<0>(I), get<1>(I), coeff_count, get<4>(I), get<3>(I));
            add_poly_coeffmod(get<3>(I), get<2>(I), coeff_count, get<4>(I), get<3>(I));
        }
    );
}