#include "helper.h"
#include "seal/seal.h"
#include "seal/util/ntt.h"
#include "seal/util/polyarithsmallmod.h"
#include "seal/util/iterator.h"
#include <gmp.h> 
#include <iostream>
#include <vector>
#include <cmath>
#include <chrono>
#include <sstream>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <cstring>
#include <cstdlib> 
#include <iomanip>

using namespace seal;
using namespace seal::util; 
using namespace std;
using namespace std::chrono;

size_t bytes_sent = 0;
size_t bytes_recv = 0;

void send_data(int sock, const string& data) {
    size_t size = data.size();
    send(sock, &size, sizeof(size), 0);
    size_t sent = 0;
    while (sent < size) {
        ssize_t s = send(sock, data.c_str() + sent, size - sent, 0);
        if (s < 0) throw runtime_error("Network send error");
        sent += s;
    }
    bytes_sent += sizeof(size) + size;
}

string recv_data(int sock) {
    size_t size = 0;
    if (recv(sock, &size, sizeof(size), MSG_WAITALL) <= 0) 
        throw runtime_error("Network recv error or connection closed");
    
    string data(size, '\0');
    size_t received = 0;
    while (received < size) {
        ssize_t r = recv(sock, &data[received], size - received, 0);
        if (r < 0) throw runtime_error("Network recv error");
        received += r;
    }
    bytes_recv += sizeof(size) + size;
    return data;
}

template <typename T>
void send_seal_object(int sock, const T& obj) {
    stringstream ss;
    obj.save(ss);
    send_data(sock, ss.str());
}

template <typename T>
void recv_seal_object(int sock, const SEALContext& context, T& obj) {
    string data = recv_data(sock);
    stringstream ss(data);
    obj.load(context, ss);
}


void refresh_ciphertext(int sock, Ciphertext &ct_in, const SEALContext &context, 
                        Evaluator &evaluator, Encryptor &encryptor, const SecretKey &sk1, 
                        uint64_t B_ct, uint64_t t_queries, uint64_t alpha, int &bootstrap_count, 
                        double &network_latency_ms) { // 【新增】传入引用，累加网络耗时
    
    auto &context_data_low = *context.get_context_data(ct_in.parms_id());
    auto &context_data_top = *context.first_context_data();
    size_t coeff_count = context_data_low.parms().poly_modulus_degree();
    size_t coeff_mod_size_low = context_data_low.parms().coeff_modulus().size();
    size_t coeff_mod_size_top = context_data_top.parms().coeff_modulus().size();

    Plaintext plain_u_low, plain_u_fresh;  
    plain_u_low.resize(coeff_count * coeff_mod_size_low);
    plain_u_fresh.resize(coeff_count * coeff_mod_size_top);

    uint64_t B_u = 10000;
    auto prng = context_data_low.parms().random_generator()->create();

    for (size_t i = 0; i < coeff_count; ++i) {
        int64_t u_val = (prng->generate() % (2 * B_u + 1)) - B_u; 
        for (size_t j = 0; j < coeff_mod_size_low; ++j) {
            uint64_t q_j = context_data_low.parms().coeff_modulus()[j].value();
            plain_u_low.data()[j * coeff_count + i] = (u_val < 0) ? (q_j - ((uint64_t)(-u_val) % q_j)) % q_j : ((uint64_t)u_val % q_j);
        }
        for (size_t j = 0; j < coeff_mod_size_top; ++j) {
            uint64_t q_j = context_data_top.parms().coeff_modulus()[j].value();
            plain_u_fresh.data()[j * coeff_count + i] = (u_val < 0) ? (q_j - ((uint64_t)(-u_val) % q_j)) % q_j : ((uint64_t)u_val % q_j);
        }
    }

    auto ntt_tables_low = context_data_low.small_ntt_tables();
    RNSIter plain_u_low_iter(plain_u_low.data(), coeff_count);
    ntt_negacyclic_harvey(plain_u_low_iter, coeff_mod_size_low, ntt_tables_low);
    plain_u_low.parms_id() = ct_in.parms_id(); 
    plain_u_low.scale() = ct_in.scale(); 

    Ciphertext ct_hat;
    evaluator.add_plain(ct_in, plain_u_low, ct_hat);

    auto ntt_tables_top = context_data_top.small_ntt_tables();
    RNSIter plain_u_fresh_iter(plain_u_fresh.data(), coeff_count);
    ntt_negacyclic_harvey(plain_u_fresh_iter, coeff_mod_size_top, ntt_tables_top);
    plain_u_fresh.parms_id() = context_data_top.parms_id();
    plain_u_fresh.scale() = ct_in.scale(); 

    Ciphertext ct_u_fresh;
    encryptor.encrypt(plain_u_fresh, ct_u_fresh);

    Plaintext p0_share;
    partial_dec(context, ct_hat, sk1, p0_share, B_ct, t_queries, alpha);


    auto net_start = high_resolution_clock::now();
    
    send_data(sock, "REFRESH");
    send_seal_object(sock, ct_hat);
    send_seal_object(sock, p0_share);
    send_seal_object(sock, ct_u_fresh);

    Ciphertext ct_final;
    recv_seal_object(sock, context, ct_final); 
    
    auto net_end = high_resolution_clock::now();
    network_latency_ms += duration_cast<nanoseconds>(net_end - net_start).count() / 1e6;

    ct_in = ct_final; 
    bootstrap_count++;
}



void run_server1(int port, uint64_t B_ct, uint64_t t_queries, uint64_t alpha) {
    cout << "\n[Server 1] Starting up... listening on port " << port << endl;
    
    int server_fd = socket(AF_INET, SOCK_STREAM, 0);
    int opt = 1;
    setsockopt(server_fd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));
    
    struct sockaddr_in address;
    memset(&address, 0, sizeof(address)); 
    address.sin_family = AF_INET;
    address.sin_addr.s_addr = INADDR_ANY;
    address.sin_port = htons(port);
    
    if (::bind(server_fd, (struct sockaddr*)&address, sizeof(address)) < 0) exit(EXIT_FAILURE);
    if (listen(server_fd, 1) < 0) exit(EXIT_FAILURE);

    cout << "[Server 1] Waiting for Server 2 to connect..." << endl;
    struct sockaddr_in client_addr;
    socklen_t client_addr_len = sizeof(client_addr);
    int sock = accept(server_fd, (struct sockaddr*)&client_addr, &client_addr_len);
    cout << "[Server 1] Server 2 connected!" << endl;

    EncryptionParameters parms(scheme_type::ckks);
    size_t poly_modulus_degree = 8192;
    parms.set_poly_modulus_degree(poly_modulus_degree);
    parms.set_coeff_modulus(CoeffModulus::Create(poly_modulus_degree, { 60, 40, 40, 60 }));
    SEALContext context(parms);
    KeyGenerator keygen(context);
    auto sk = keygen.secret_key();
    PublicKey pk; keygen.create_public_key(pk);
    RelinKeys rlk; keygen.create_relin_keys(rlk);
    
    SecretKey sk1, sk2;
    split_secret_key(context, sk, sk1, sk2);
    Decryptor decryptor(context, sk);

    stringstream parms_stream;
    parms.save(parms_stream);
    send_data(sock, parms_stream.str());
    send_seal_object(sock, pk);
    send_seal_object(sock, sk2);

    Encryptor encryptor(context, pk);
    Evaluator evaluator(context);
    CKKSEncoder encoder(context);
    double scale = pow(2.0, 40);

    double val_x = 1.02;  
    double val_y = 0.98;
    Plaintext p1, p2;
    encoder.encode(val_x, scale, p1);
    encoder.encode(val_y, scale, p2);
    Ciphertext base_x, base_y;
    encryptor.encrypt(p1, base_x);
    encryptor.encrypt(p2, base_y);

    int num_slots = poly_modulus_degree / 2; // 4096

    cout << "\n================ [Size Profiling] ================" << endl;

    auto print_size = [](string name, size_t bytes) {
        double kb = bytes / 1024.0;
        double mb = kb / 1024.0;
        if (mb > 1.0) 
            cout << "  - " << left << setw(20) << name << ": " << mb << " MB" << endl;
        else 
            cout << "  - " << left << setw(20) << name << ": " << kb << " KB" << endl;
    };

    // 1. 测量各类密钥大小
    print_size("SecretKey (sk)", sk.save_size(compr_mode_type::none));
    print_size("SecretKey Share(sk1)", sk1.save_size(compr_mode_type::none));
    print_size("PublicKey (pk)", pk.save_size(compr_mode_type::none));
    print_size("RelinKeys (rlk)", rlk.save_size(compr_mode_type::none));

    // 2. 测量新鲜密文大小
    print_size("Fresh Ciphertext", base_x.save_size(compr_mode_type::none));

    // 3. 测量做完 1 次乘法并 Rescale 后的密文大小
    Ciphertext ct_after_mul;
    evaluator.multiply(base_x, base_y, ct_after_mul);
    print_size("Ciphertext (size 3)", ct_after_mul.save_size(compr_mode_type::none)); // 乘法后维度膨胀

    evaluator.relinearize_inplace(ct_after_mul, rlk);
    print_size("Ciphertext (Relin)", ct_after_mul.save_size(compr_mode_type::none));  // 降维回 size 2

    evaluator.rescale_to_next_inplace(ct_after_mul);
    print_size("Ciphertext (Rescaled)", ct_after_mul.save_size(compr_mode_type::none)); // 消耗一个素数，变小
    cout << "==================================================\n" << endl;

    auto run_benchmark = [&](string name, int num_iters, double expected_result, double tolerance, auto func) {
        cout << "\n[*] Running " << name << " Benchmark..." << endl;
        bytes_sent = 0; bytes_recv = 0;
        int bs_count = 0;
        double protocol_latency_ms = 0.0; 
        Ciphertext ct_final;
        
        auto t_start = high_resolution_clock::now();
        for (int i = 0; i < num_iters; i++) {
            Ciphertext ct_x = base_x; 
            Ciphertext ct_y = base_y;
            func(ct_x, ct_y, bs_count, ct_final, protocol_latency_ms); 
        }
        auto t_end = high_resolution_clock::now();
        
        Plaintext pt_res;
        decryptor.decrypt(ct_final, pt_res);
        vector<double> vec_res;
        encoder.decode(pt_res, vec_res);
        double actual_result = vec_res[0];
        double error = abs(expected_result - actual_result);

        double total_runtime_ms = duration_cast<nanoseconds>(t_end - t_start).count() / 1e6;
        double computing_cost_s1_ms = total_runtime_ms - protocol_latency_ms; 
        double comm_volume_kb = (bytes_sent + bytes_recv) / 1024.0;
        long total_data_points = (long)num_iters * num_slots;
        
        cout << "[Metrics] ======== " << name << " ========" << endl;
        cout << "  - Config:             " << num_iters << " iterations x " << num_slots << " slots = " << total_data_points << " points" << endl;
        cout << "  - Bootstraps Fired:   " << bs_count << " times" << endl;
        
        cout << "  ---------------- [TOTAL COST] ------------------" << endl;
        cout << "  - S1 Computing Cost:  " << computing_cost_s1_ms << " ms" << endl;
        cout << "  - Protocol Latency:   " << protocol_latency_ms << " ms (Network I/O + S2 Wait)" << endl;
        cout << "  - Total Runtime (E2E):" << total_runtime_ms << " ms" << endl;
        cout << "  - Comm Volume (Sent): " << bytes_sent / 1024.0 << " KB" << endl;
        cout << "  - Comm Volume (Recv): " << bytes_recv / 1024.0 << " KB" << endl;
        
        cout << "  -------------- [AMORTIZED COST] ----------------" << endl;
        cout << "  - \033[1;36mAmortized Compute:\033[0m  " << computing_cost_s1_ms / total_data_points << " ms / point" << endl;
        cout << "  - \033[1;32mAmortized Runtime:\033[0m  " << total_runtime_ms / total_data_points << " ms / point" << endl;
        cout << "  - \033[1;33mAmortized Comm:   \033[0m  " << comm_volume_kb / total_data_points << " KB / point" << endl;
        
        cout << "  ---------------- [CORRECTNESS] -----------------" << endl;
        cout << "  - Ground Truth:       " << expected_result << endl;
        cout << "  - Decrypted Result:   " << actual_result << endl;
        cout << "  - Max Abs Error:      " << error << endl;
        if (error <= tolerance) cout << "  - Status:             \033[1;32mPASS\033[0m" << endl;
        else cout << "  - Status:             \033[1;31mWARNING (Noise exceeds tolerance)\033[0m" << endl;
        cout << "==================================================" << endl;
    };


    double expected_smul = val_x * val_y;
    run_benchmark("SMUL (Secure Multiply)", 100, expected_smul, 0.01, 
    [&](Ciphertext &ct_x, Ciphertext &ct_y, int &bs_count, Ciphertext &ct_res, double &net_time) {
        evaluator.multiply(ct_x, ct_y, ct_res);
        evaluator.relinearize_inplace(ct_res, rlk);
        evaluator.rescale_to_next_inplace(ct_res);
        if (ct_res.coeff_modulus_size() <= 2) refresh_ciphertext(sock, ct_res, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time);
    });


    double expected_scmp = pow(val_x - val_y, 4);
    run_benchmark("SCMP (Secure Compare)", 10, expected_scmp, 0.05, 
    [&](Ciphertext &ct_x, Ciphertext &ct_y, int &bs_count, Ciphertext &ct_res, double &net_time) {
        Ciphertext ct_z;
        evaluator.sub(ct_x, ct_y, ct_z);
        Ciphertext ct_z2;
        evaluator.square(ct_z, ct_z2);
        evaluator.relinearize_inplace(ct_z2, rlk);
        evaluator.rescale_to_next_inplace(ct_z2);
        if (ct_z2.coeff_modulus_size() <= 2) refresh_ciphertext(sock, ct_z2, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time);

        evaluator.square(ct_z2, ct_res); 
        evaluator.relinearize_inplace(ct_res, rlk);
        evaluator.rescale_to_next_inplace(ct_res);
        if (ct_res.coeff_modulus_size() <= 2) refresh_ciphertext(sock, ct_res, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time);
    });


    double expected_ssba = pow(val_x, 8);
    run_benchmark("SSBA (Secure Sign & Abs)", 10, expected_ssba, 0.05, 
    [&](Ciphertext &ct_x, Ciphertext &ct_y, int &bs_count, Ciphertext &ct_res, double &net_time) {
        Ciphertext ct_z2, ct_z3;
        evaluator.square(ct_x, ct_z2);
        evaluator.relinearize_inplace(ct_z2, rlk);
        evaluator.rescale_to_next_inplace(ct_z2);
        if (ct_z2.coeff_modulus_size() <= 2) refresh_ciphertext(sock, ct_z2, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time);

        evaluator.square(ct_z2, ct_z3); 
        evaluator.relinearize_inplace(ct_z3, rlk);
        evaluator.rescale_to_next_inplace(ct_z3);
        if (ct_z3.coeff_modulus_size() <= 2) refresh_ciphertext(sock, ct_z3, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time);

        evaluator.square(ct_z3, ct_res); 
        evaluator.relinearize_inplace(ct_res, rlk);
        evaluator.rescale_to_next_inplace(ct_res);
        if (ct_res.coeff_modulus_size() <= 2) refresh_ciphertext(sock, ct_res, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time);
    });


    double expected_sdiv = val_x;
    for (int i = 0; i < 3; i++) expected_sdiv = pow(expected_sdiv, 4); 
    expected_sdiv = pow(expected_sdiv, 2); 

    run_benchmark("SDIV (Secure Division)", 5, expected_sdiv, 0.5, 
    [&](Ciphertext &ct_x, Ciphertext &ct_y, int &bs_count, Ciphertext &ct_res, double &net_time) {
        Ciphertext ct_z = ct_x; 
        for (int i = 0; i < 3; i++) {
            Ciphertext term1, term2;
            evaluator.square(ct_z, term1); 
            evaluator.relinearize_inplace(term1, rlk);
            evaluator.rescale_to_next_inplace(term1);
            if (term1.coeff_modulus_size() <= 2) refresh_ciphertext(sock, term1, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time);

            evaluator.square(term1, term2); 
            evaluator.relinearize_inplace(term2, rlk);
            evaluator.rescale_to_next_inplace(term2);
            if (term2.coeff_modulus_size() <= 2) refresh_ciphertext(sock, term2, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time);
            ct_z = term2;
        }
        evaluator.square(ct_z, ct_res); 
        evaluator.relinearize_inplace(ct_res, rlk);
        evaluator.rescale_to_next_inplace(ct_res);
        if (ct_res.coeff_modulus_size() <= 2) refresh_ciphertext(sock, ct_res, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time);
    });

    send_data(sock, "DONE");
    close(sock);
    close(server_fd);
}

void run_server2(const string& ip, int port, uint64_t B_ct, uint64_t t_queries, uint64_t alpha) {
    cout << "\n[Server 2] Connecting to Server 1 at " << ip << ":" << port << "..." << endl;
    
    int sock;
    struct sockaddr_in serv_addr;
    memset(&serv_addr, 0, sizeof(serv_addr));
    serv_addr.sin_family = AF_INET;
    serv_addr.sin_port = htons(port);
    inet_pton(AF_INET, ip.c_str(), &serv_addr.sin_addr);
    
    while (true) {
        sock = socket(AF_INET, SOCK_STREAM, 0);
        if (connect(sock, (struct sockaddr *)&serv_addr, sizeof(serv_addr)) >= 0) {
            break; 
        }
        close(sock); 
        usleep(500000); 
    }
    
    cout << "[Server 2] Connected!" << endl;

    string parms_data = recv_data(sock);
    stringstream parms_stream(parms_data);
    EncryptionParameters parms;
    parms.load(parms_stream);
    SEALContext context(parms);

    PublicKey pk; recv_seal_object(sock, context, pk);
    SecretKey sk2; recv_seal_object(sock, context, sk2);

    Encryptor encryptor(context, pk);
    Evaluator evaluator(context);

    cout << "\n[Server 2] Waiting for Protocol Commands..." << endl;

    while (true) {
        string cmd = recv_data(sock);
        if (cmd == "DONE") {
            cout << "[Server 2] Received DONE. Exiting..." << endl;
            break;
        }
        if (cmd == "REFRESH") {
            Ciphertext ct_hat, ct_u_fresh;
            Plaintext p0_share;
            recv_seal_object(sock, context, ct_hat);
            recv_seal_object(sock, context, p0_share);
            recv_seal_object(sock, context, ct_u_fresh);

            Plaintext p1_share;
            partial_dec(context, ct_hat, sk2, p1_share, B_ct, t_queries, alpha, false);

            Plaintext plain_masked_ntt;
            total_dec(context, ct_hat, p0_share, p1_share, plain_masked_ntt);

            auto &context_data_low = *context.get_context_data(ct_hat.parms_id());
            auto &context_data_top = *context.first_context_data();
            size_t coeff_count = context_data_low.parms().poly_modulus_degree();
            size_t coeff_mod_size_low = context_data_low.parms().coeff_modulus().size();
            size_t coeff_mod_size_top = context_data_top.parms().coeff_modulus().size();

            auto ntt_tables_low = context_data_low.small_ntt_tables();
            RNSIter plain_ntt_iter(plain_masked_ntt.data(), coeff_count);
            inverse_ntt_negacyclic_harvey(plain_ntt_iter, coeff_mod_size_low, ntt_tables_low);

            Plaintext plain_masked_fresh;
            plain_masked_fresh.resize(coeff_count * coeff_mod_size_top);

            vector<uint64_t> q_low(coeff_mod_size_low);
            for(size_t j = 0; j < coeff_mod_size_low; j++) q_low[j] = context_data_low.parms().coeff_modulus()[j].value();

            vector<uint64_t> Q_top(coeff_mod_size_top);
            for(size_t j = 0; j < coeff_mod_size_top; j++) Q_top[j] = context_data_top.parms().coeff_modulus()[j].value();

            mpz_t M, half_M;
            mpz_init_set_ui(M, 1);
            for(size_t j = 0; j < coeff_mod_size_low; j++){
                mpz_t q_z; mpz_init(q_z);
                mpz_import(q_z, 1, -1, sizeof(uint64_t), 0, 0, &q_low[j]); 
                mpz_mul(M, M, q_z);
                mpz_clear(q_z);
            }
            mpz_init(half_M);
            mpz_fdiv_q_ui(half_M, M, 2);

            mpz_t* W = new mpz_t[coeff_mod_size_low];
            for(size_t j = 0; j < coeff_mod_size_low; j++){
                mpz_init(W[j]);
                mpz_t q_z, M_j, M_j_mod, inv;
                mpz_init(q_z); mpz_import(q_z, 1, -1, sizeof(uint64_t), 0, 0, &q_low[j]);
                mpz_init(M_j); mpz_divexact(M_j, M, q_z);
                mpz_init(M_j_mod); mpz_mod(M_j_mod, M_j, q_z);
                mpz_init(inv); mpz_invert(inv, M_j_mod, q_z); 
                mpz_mul(W[j], M_j, inv);
                mpz_mod(W[j], W[j], M); 
                mpz_clear(q_z); mpz_clear(M_j); mpz_clear(M_j_mod); mpz_clear(inv);
            }

            for (size_t i = 0; i < coeff_count; ++i) {
                mpz_t X, temp;
                mpz_init_set_ui(X, 0);
                mpz_init(temp);

                for (size_t j = 0; j < coeff_mod_size_low; ++j) {
                    uint64_t x_j = plain_masked_ntt.data()[j * coeff_count + i];
                    mpz_t x_z; mpz_init(x_z); mpz_import(x_z, 1, -1, sizeof(uint64_t), 0, 0, &x_j);
                    mpz_mul(temp, W[j], x_z);
                    mpz_add(X, X, temp);
                    mpz_clear(x_z);
                }
                mpz_mod(X, X, M); 
                if (mpz_cmp(X, half_M) > 0) mpz_sub(X, X, M); 

                for (size_t m = 0; m < coeff_mod_size_top; ++m) {
                    mpz_t Q_z, rem;
                    mpz_init(Q_z); mpz_import(Q_z, 1, -1, sizeof(uint64_t), 0, 0, &Q_top[m]);
                    mpz_init(rem);
                    mpz_fdiv_r(rem, X, Q_z); 
                    uint64_t y_m = 0;
                    if (mpz_sgn(rem) != 0) mpz_export(&y_m, nullptr, -1, sizeof(uint64_t), 0, 0, rem);
                    plain_masked_fresh.data()[m * coeff_count + i] = y_m;
                    mpz_clear(Q_z); mpz_clear(rem);
                }
                mpz_clear(X); mpz_clear(temp);
            }

            mpz_clear(M); mpz_clear(half_M);
            for(size_t j = 0; j < coeff_mod_size_low; j++) mpz_clear(W[j]);
            delete[] W; 

            auto ntt_tables_top = context_data_top.small_ntt_tables();
            RNSIter plain_masked_fresh_iter(plain_masked_fresh.data(), coeff_count);
            ntt_negacyclic_harvey(plain_masked_fresh_iter, coeff_mod_size_top, ntt_tables_top);
            plain_masked_fresh.parms_id() = context_data_top.parms_id();
            plain_masked_fresh.scale() = ct_hat.scale(); 

            Ciphertext ct_masked_fresh;
            encryptor.encrypt(plain_masked_fresh, ct_masked_fresh);

            ct_masked_fresh.scale() = ct_hat.scale();
            Ciphertext ct_final;
            evaluator.sub(ct_masked_fresh, ct_u_fresh, ct_final);

            send_seal_object(sock, ct_final);
        }
    }
    close(sock);
}


int main(int argc, char* argv[]) {
    if (argc < 2) {
        cerr << "Usage for Server 1: " << argv[0] << " 1 [port] [B_ct] [t_queries] [alpha]" << endl;
        cerr << "Usage for Server 2: " << argv[0] << " 2 [ip] [port] [B_ct] [t_queries] [alpha]" << endl;
        return 1;
    }

    int role = atoi(argv[1]);
    uint64_t default_B_ct = 4096, default_t_queries = 1, default_alpha = 128;

    if (role == 1) {
        int port = (argc >= 3) ? atoi(argv[2]) : 12346;
        uint64_t B_ct      = (argc >= 4) ? stoull(argv[3]) : default_B_ct;
        uint64_t t_queries = (argc >= 5) ? stoull(argv[4]) : default_t_queries;
        uint64_t alpha     = (argc >= 6) ? stoull(argv[5]) : default_alpha;
        run_server1(port, B_ct, t_queries, alpha);
    } 
    else if (role == 2) {
        string ip = (argc >= 3) ? argv[2] : "127.0.0.1";
        int port = (argc >= 4) ? atoi(argv[3]) : 12346;
        uint64_t B_ct      = (argc >= 5) ? stoull(argv[4]) : default_B_ct;
        uint64_t t_queries = (argc >= 6) ? stoull(argv[5]) : default_t_queries;
        uint64_t alpha     = (argc >= 7) ? stoull(argv[6]) : default_alpha;
        run_server2(ip, port, B_ct, t_queries, alpha);
    }
    return 0;
}