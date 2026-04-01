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

// ========== S1 端：用于在第一次 Refresh 时打印详细的细化 Breakdown ==========
static bool s1_is_first_refresh = true;

void refresh_ciphertext(int sock, Ciphertext &ct_in, const SEALContext &context, 
                        Evaluator &evaluator, Encryptor &encryptor, const SecretKey &sk1, 
                        uint64_t B_ct, uint64_t t_queries, uint64_t alpha, int &bootstrap_count, 
                        double &network_latency_ms, double &partial_dec_latency_ms, bool use_gaussian) { 
    
    auto t_noise_start = high_resolution_clock::now();

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

    auto t_noise_end = high_resolution_clock::now();

    Plaintext p0_share;
    auto pdec_start = high_resolution_clock::now();
    partial_dec(context, ct_hat, sk1, p0_share, B_ct, t_queries, alpha, true, use_gaussian);
    auto pdec_end = high_resolution_clock::now();
    partial_dec_latency_ms += duration_cast<nanoseconds>(pdec_end - pdec_start).count() / 1e6;

    // === 细化阶段：将序列化、网络发送、网络接收、反序列化 拆开计时 ===
    auto net_start_total = high_resolution_clock::now();

    auto t_ser_start = high_resolution_clock::now();
    stringstream ss1, ss2, ss3;
    ct_hat.save(ss1); p0_share.save(ss2); ct_u_fresh.save(ss3);
    string s_ct_hat = ss1.str(); string s_p0_share = ss2.str(); string s_ct_u_fresh = ss3.str();
    auto t_ser_end = high_resolution_clock::now();

    auto t_tx_start = high_resolution_clock::now();
    send_data(sock, "REFRESH");
    send_data(sock, s_ct_hat); send_data(sock, s_p0_share); send_data(sock, s_ct_u_fresh);
    auto t_tx_end = high_resolution_clock::now();

    auto t_rx_start = high_resolution_clock::now();
    string s_ct_final = recv_data(sock);
    auto t_rx_end = high_resolution_clock::now();

    auto t_deser_start = high_resolution_clock::now();
    Ciphertext ct_final;
    stringstream ss_final(s_ct_final);
    ct_final.load(context, ss_final);
    auto t_deser_end = high_resolution_clock::now();

    auto net_end_total = high_resolution_clock::now();
    // 依然保持原有的宏观网络延时累加（涵盖从准备发送到解析完成的所有网络交互步骤）
    network_latency_ms += duration_cast<nanoseconds>(net_end_total - net_start_total).count() / 1e6;

    if (s1_is_first_refresh) {
        cout << "\n  ==== [Server 1] 1st Refresh Breakdown ====" << endl;
        cout << "    |-- [S1] Noise Gen & Enc u:          " << duration_cast<nanoseconds>(t_noise_end - t_noise_start).count() / 1e6 << " ms" << endl;
        cout << "    |-- [S1] Partial Decrypt:            " << duration_cast<nanoseconds>(pdec_end - pdec_start).count() / 1e6 << " ms" << endl;
        cout << "    |-- [S1] Object Serialization (Save):   " << duration_cast<nanoseconds>(t_ser_end - t_ser_start).count() / 1e6 << " ms" << endl;
        cout << "    |-- [S1] Socket Send:                " << duration_cast<nanoseconds>(t_tx_end - t_tx_start).count() / 1e6 << " ms" << endl;
        cout << "    |-- [S1] Socket Wait + Recv:         " << duration_cast<nanoseconds>(t_rx_end - t_rx_start).count() / 1e6 << " ms (Includes S2 processing time!)" << endl;
        cout << "    |-- [S1] Object Deserialization (Load): " << duration_cast<nanoseconds>(t_deser_end - t_deser_start).count() / 1e6 << " ms" << endl;
        cout << "  =========================================================" << endl;
        s1_is_first_refresh = false;
    }

    ct_in = ct_final; 
    bootstrap_count++;
}

void run_server1(int port, size_t poly_modulus_degree, long target_data_volume, bool use_gaussian, uint64_t B_ct, uint64_t t_queries, uint64_t alpha) {
    cout << "\n[Server 1] Starting up... listening on port " << port << endl;
    cout << "[Server 1] Config -> N: " << poly_modulus_degree << ", Gaussian Noise: " << (use_gaussian ? "ON" : "OFF") << endl;
    
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

    auto t_setup_start = high_resolution_clock::now();

    EncryptionParameters parms(scheme_type::ckks);
    parms.set_poly_modulus_degree(poly_modulus_degree);

    int max_security_bit_count = 0;
    if (poly_modulus_degree == 8192) max_security_bit_count = 218;
    else if (poly_modulus_degree == 16384) max_security_bit_count = 438;
    else if (poly_modulus_degree == 32768) max_security_bit_count = 881;
    else throw invalid_argument("Unsupported poly_modulus_degree for 128-bit security");

    int num_40_bit_primes = (max_security_bit_count - 120) / 40;
    
    vector<int> bit_sizes;
    bit_sizes.push_back(60); 
    for (int i = 0; i < num_40_bit_primes; i++) {
        bit_sizes.push_back(40); 
    }
    bit_sizes.push_back(60);

    cout << "[Server 1] Dynamically generated Modulus Chain: {60";
    for (int i=0; i < num_40_bit_primes; i++) cout << ", 40";
    cout << ", 60} (Total: " << 120 + num_40_bit_primes * 40 << " bits)" << endl;

    parms.set_coeff_modulus(CoeffModulus::Create(poly_modulus_degree, bit_sizes));
    SEALContext context(parms);
    KeyGenerator keygen(context);
    auto sk = keygen.secret_key();
    PublicKey pk; keygen.create_public_key(pk);
    RelinKeys rlk; keygen.create_relin_keys(rlk);
    
    SecretKey sk1, sk2;
    split_secret_key(context, sk, sk1, sk2);
    
    auto t_setup_end = high_resolution_clock::now();
    double setup_time_ms = duration_cast<nanoseconds>(t_setup_end - t_setup_start).count() / 1e6;
    cout << "\n[Metrics] Setup Time (Keys Generation & Splitting): " << setup_time_ms << " ms" << endl;

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

    auto t_enc_start = high_resolution_clock::now();
    encryptor.encrypt(p1, base_x);
    encryptor.encrypt(p2, base_y);
    auto t_enc_end = high_resolution_clock::now();
    double enc_time_ms = duration_cast<nanoseconds>(t_enc_end - t_enc_start).count() / 1e6;
    cout << "[Metrics] Encryption Time (2 Ciphertexts): " << enc_time_ms << " ms\n" << endl;

    int num_slots = poly_modulus_degree / 2;

    cout << "================ [Size Profiling] ================" << endl;
    auto print_size = [](string name, size_t bytes) {
        double kb = bytes / 1024.0;
        double mb = kb / 1024.0;
        if (mb > 1.0) 
            cout << "  - " << left << setw(20) << name << ": " << mb << " MB" << endl;
        else 
            cout << "  - " << left << setw(20) << name << ": " << kb << " KB" << endl;
    };

    print_size("SecretKey (sk)", sk.save_size(compr_mode_type::none));
    print_size("SecretKey Share(sk1)", sk1.save_size(compr_mode_type::none));
    print_size("PublicKey (pk)", pk.save_size(compr_mode_type::none));
    print_size("RelinKeys (rlk)", rlk.save_size(compr_mode_type::none));
    print_size("Fresh Ciphertext", base_x.save_size(compr_mode_type::none));

    Ciphertext ct_after_mul;
    evaluator.multiply(base_x, base_y, ct_after_mul);
    print_size("Ciphertext (size 3)", ct_after_mul.save_size(compr_mode_type::none)); 

    evaluator.relinearize_inplace(ct_after_mul, rlk);
    print_size("Ciphertext (Relin)", ct_after_mul.save_size(compr_mode_type::none));  

    evaluator.rescale_to_next_inplace(ct_after_mul);
    print_size("Ciphertext (Rescaled)", ct_after_mul.save_size(compr_mode_type::none)); 

    int required_iters = std::ceil((double)target_data_volume / num_slots);

    cout << "\n================ [Batch Processing Setup] ================" << endl;
    cout << "  - Target Data Volume:   " << target_data_volume << " points" << endl;
    cout << "  - Slots per Ciphertext: " << num_slots << " points (N=" << poly_modulus_degree << ")" << endl;
    cout << "  - Required Iterations:  " << required_iters << " batches" << endl;
    cout << "==========================================================" << endl;

    auto match_level_and_scale = [&](Ciphertext &ct_target, const Ciphertext &ct_ref) {
        if (ct_target.parms_id() != ct_ref.parms_id()) {
            evaluator.mod_switch_to_inplace(ct_target, ct_ref.parms_id());
        }
        ct_target.scale() = ct_ref.scale(); 
    };

    auto run_benchmark = [&](string name, int num_iters, double expected_result, double tolerance, auto func) {
        cout << "\n[*] Running " << name << " Benchmark..." << endl;
        bytes_sent = 0; bytes_recv = 0;
        int bs_count = 0;
        double protocol_latency_ms = 0.0; 
        double partial_dec_latency_ms = 0.0; 
        Ciphertext ct_final;
        
        auto t_start = high_resolution_clock::now();
        for (int i = 0; i < num_iters; i++) {
            Ciphertext ct_x = base_x; 
            Ciphertext ct_y = base_y;
            func(ct_x, ct_y, bs_count, ct_final, protocol_latency_ms, partial_dec_latency_ms); 
        }
        auto t_end = high_resolution_clock::now();
        
        auto t_dec_start = high_resolution_clock::now();
        Plaintext pt_res;
        decryptor.decrypt(ct_final, pt_res);
        auto t_dec_end = high_resolution_clock::now();
        double dec_latency_ms = duration_cast<nanoseconds>(t_dec_end - t_dec_start).count() / 1e6;

        vector<double> vec_res;
        encoder.decode(pt_res, vec_res);
        double actual_result = vec_res[0];
        double error = abs(expected_result - actual_result);

        double total_runtime_ms = duration_cast<nanoseconds>(t_end - t_start).count() / 1e6;
        double computing_cost_s1_ms = total_runtime_ms - protocol_latency_ms; 
        double comm_volume_sent_kb = bytes_sent / 1024.0;
        double comm_volume_recv_kb = bytes_recv / 1024.0;
        long total_data_points = (long)num_iters * num_slots;
        
        double total_dec_ms = dec_latency_ms * num_iters;
        double overall_total_ms = total_runtime_ms + total_dec_ms;

        cout << "[Metrics] ======== " << name << " ========" << endl;
        cout << "  - Config:             " << num_iters << " iterations x " << num_slots << " slots = " << total_data_points << " points" << endl;
        
        cout << "  ---- [TOTAL COST FOR " << target_data_volume << " POINTS] ----" << endl;
        cout << "  - Total Bootstraps:   " << bs_count << " times" << endl;
        cout << "  - Total S1 Compute:   " << computing_cost_s1_ms << " ms" << endl;
        cout << "  - Total S1 PartialDec:" << partial_dec_latency_ms << " ms" << endl;
        cout << "  - Total Decrypt(Dec): " << total_dec_ms << " ms" << endl;
        cout << "  - Total Protocol Wait:" << protocol_latency_ms << " ms (Incl. S2 Wait)" << endl;
        cout << "  - \033[1;32mTotal Runtime:\033[0m      " << overall_total_ms << " ms" << endl;
        cout << "  - \033[1;33mTotal Comm (Sent):\033[0m  " << comm_volume_sent_kb << " KB" << endl;
        cout << "  - \033[1;33mTotal Comm (Recv):\033[0m  " << comm_volume_recv_kb << " KB" << endl;
        
        cout << "  ---------------- [AMORTIZED COST (Per Item)] ----------------" << endl;
        cout << "  - Amortized Compute:  " << computing_cost_s1_ms / total_data_points << " ms / point" << endl;
        cout << "  - Amortized PDec:     " << partial_dec_latency_ms / total_data_points << " ms / point" << endl;
        cout << "  - Amortized Dec:      " << total_dec_ms / total_data_points << " ms / point" << endl;
        cout << "  - Amortized Net Wait: " << protocol_latency_ms / total_data_points << " ms / point" << endl;
        cout << "  - Amortized Runtime:  " << overall_total_ms / total_data_points << " ms / point" << endl;
        cout << "  - Amortized Comm(Tx): " << comm_volume_sent_kb / total_data_points << " KB / point" << endl;
        cout << "  - Amortized Comm(Rx): " << comm_volume_recv_kb / total_data_points << " KB / point" << endl;
        
    };

    cout << "\n================ [Microbenchmarks] ================" << endl;
    Ciphertext ct_test = base_x;
    Plaintext pt_share;
    auto t_pdec_start = high_resolution_clock::now();
    partial_dec(context, ct_test, sk1, pt_share, B_ct, t_queries, alpha, true, use_gaussian);
    auto t_pdec_end = high_resolution_clock::now();
    cout << "  - S1 PartialDec Time (Full Size CT): " << duration_cast<nanoseconds>(t_pdec_end - t_pdec_start).count() / 1e6 << " ms" << endl;

    Plaintext pt_test_res;
    auto t_dec_start_micro = high_resolution_clock::now();
    decryptor.decrypt(ct_test, pt_test_res);
    auto t_dec_end_micro = high_resolution_clock::now();
    cout << "  - Standard Dec Time:  " << duration_cast<nanoseconds>(t_dec_end_micro - t_dec_start_micro).count() / 1e6 << " ms" << endl;
    
    // 6. 测单次完整 Refresh Ciphertext 的时间 (包含网络通信开销)
    Ciphertext ct_ref_test = ct_test;
    while (ct_ref_test.coeff_modulus_size() > 2) { // 降维触发自举条件
        evaluator.mod_switch_to_next_inplace(ct_ref_test);
    }
    int dummy_bs_count = 0;
    double dummy_net_time = 0.0, dummy_pdec_time = 0.0;
    
    // 记录刷新前的通信量
    size_t before_refresh_sent = bytes_sent;
    size_t before_refresh_recv = bytes_recv;

    // 重新开启首刷打印开关（用于下面的 Refresh）
    s1_is_first_refresh = true;

    auto t_ref_start = high_resolution_clock::now();
    refresh_ciphertext(sock, ct_ref_test, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, dummy_bs_count, dummy_net_time, dummy_pdec_time, use_gaussian);
    auto t_ref_end = high_resolution_clock::now();
    
    // 计算本次产生的通信量
    double single_sent_kb = (bytes_sent - before_refresh_sent) / 1024.0;
    double single_recv_kb = (bytes_recv - before_refresh_recv) / 1024.0;

    double full_refresh_ms = duration_cast<nanoseconds>(t_ref_end - t_ref_start).count() / 1e6;
    
    cout << "\n  - Full Refresh Time (S1 Total):  " << full_refresh_ms << " ms" << endl;
    cout << "    |-- Single Refresh Comm (Sent): " << single_sent_kb << " KB" << endl;
    cout << "    |-- Single Refresh Comm (Recv): " << single_recv_kb << " KB" << endl;
    cout << "===================================================" << endl;

    double expected_sadd = val_x + val_y;
    run_benchmark("SADD (Secure Addition)", required_iters, expected_sadd, 0.01, 
    [&](Ciphertext &ct_x, Ciphertext &ct_y, int &bs_count, Ciphertext &ct_res, double &net_time, double &pdec_time) {
        evaluator.add(ct_x, ct_y, ct_res);
    });

    double expected_smul = val_x * val_y;
    run_benchmark("SMUL (Secure Multiply)", required_iters, expected_smul, 0.01, 
    [&](Ciphertext &ct_x, Ciphertext &ct_y, int &bs_count, Ciphertext &ct_res, double &net_time, double &pdec_time) {
        evaluator.multiply(ct_x, ct_y, ct_res);
        evaluator.relinearize_inplace(ct_res, rlk);
        evaluator.rescale_to_next_inplace(ct_res);
        refresh_ciphertext(sock, ct_res, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
    });

    // =========================================================
    // [Real] SCMP (Minimax Sign Approximation & Step Function)
    // =========================================================
    double expected_scmp = (val_x > val_y) ? 1.0 : 0.0; 
    run_benchmark("SCMP (Secure Compare)", required_iters, expected_scmp, 0.1, 
    [&](Ciphertext &ct_x, Ciphertext &ct_y, int &bs_count, Ciphertext &ct_res, double &net_time, double &pdec_time) {
        Ciphertext ct_z;
        evaluator.sub(ct_x, ct_y, ct_z); 
        
        Ciphertext z2, z3, z5, z7, z_down1 = ct_z;
        evaluator.square(ct_z, z2); evaluator.relinearize_inplace(z2, rlk); evaluator.rescale_to_next_inplace(z2);
        if (z2.coeff_modulus_size() <= 2) refresh_ciphertext(sock, z2, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
        
        match_level_and_scale(z_down1, z2);
        evaluator.multiply(z2, z_down1, z3); evaluator.relinearize_inplace(z3, rlk); evaluator.rescale_to_next_inplace(z3);
        if (z3.coeff_modulus_size() <= 2) refresh_ciphertext(sock, z3, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
        
        Ciphertext z2_down1 = z2; match_level_and_scale(z2_down1, z3);
        evaluator.multiply(z3, z2_down1, z5); evaluator.relinearize_inplace(z5, rlk); evaluator.rescale_to_next_inplace(z5);
        if (z5.coeff_modulus_size() <= 2) refresh_ciphertext(sock, z5, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
        
        Ciphertext z2_down2 = z2; match_level_and_scale(z2_down2, z5);
        evaluator.multiply(z5, z2_down2, z7); evaluator.relinearize_inplace(z7, rlk); evaluator.rescale_to_next_inplace(z7);
        if (z7.coeff_modulus_size() <= 2) refresh_ciphertext(sock, z7, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);

        auto multiply_coeff = [&](Ciphertext ct, double coeff) {
            Plaintext pt; encoder.encode(coeff, ct.scale(), pt); evaluator.mod_switch_to_inplace(pt, ct.parms_id());
            Ciphertext res; evaluator.multiply_plain(ct, pt, res); evaluator.rescale_to_next_inplace(res); return res;
        };

        Ciphertext t1 = multiply_coeff(ct_z, 3.15), t3 = multiply_coeff(z3, -4.2);
        Ciphertext t5 = multiply_coeff(z5, 2.5), t7 = multiply_coeff(z7, -0.5);
        match_level_and_scale(t1, t7); match_level_and_scale(t3, t7); match_level_and_scale(t5, t7);

        Ciphertext sign_z;
        evaluator.add(t1, t3, sign_z); evaluator.add_inplace(sign_z, t5); evaluator.add_inplace(sign_z, t7);
        if (sign_z.coeff_modulus_size() <= 2) refresh_ciphertext(sock, sign_z, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
        
        Plaintext pt_half; encoder.encode(0.5, sign_z.scale(), pt_half); evaluator.mod_switch_to_inplace(pt_half, sign_z.parms_id());
        Ciphertext step_z; evaluator.multiply_plain(sign_z, pt_half, step_z); evaluator.rescale_to_next_inplace(step_z);
        if (step_z.coeff_modulus_size() <= 2) refresh_ciphertext(sock, step_z, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
        
        Plaintext pt_half_add; encoder.encode(0.5, step_z.scale(), pt_half_add); evaluator.mod_switch_to_inplace(pt_half_add, step_z.parms_id());
        evaluator.add_plain(step_z, pt_half_add, ct_res);
        if (ct_res.coeff_modulus_size() <= 2) refresh_ciphertext(sock, ct_res, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
    });

    // =========================================================
    // [Real] SSBA (Secure Sign Bit-Acquisition)
    // =========================================================
    double expected_ssba = abs(val_x); 
    run_benchmark("SSBA (Secure Sign & Abs)", required_iters, expected_ssba, 0.1, 
    [&](Ciphertext &ct_x, Ciphertext &ct_y, int &bs_count, Ciphertext &ct_res, double &net_time, double &pdec_time) {
        Ciphertext z2, z3, z5, z7, z_down1 = ct_x;
        evaluator.square(ct_x, z2); evaluator.relinearize_inplace(z2, rlk); evaluator.rescale_to_next_inplace(z2);
        if (z2.coeff_modulus_size() <= 2) refresh_ciphertext(sock, z2, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
        
        match_level_and_scale(z_down1, z2);
        evaluator.multiply(z2, z_down1, z3); evaluator.relinearize_inplace(z3, rlk); evaluator.rescale_to_next_inplace(z3);
        if (z3.coeff_modulus_size() <= 2) refresh_ciphertext(sock, z3, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
        
        Ciphertext z2_down1 = z2; match_level_and_scale(z2_down1, z3);
        evaluator.multiply(z3, z2_down1, z5); evaluator.relinearize_inplace(z5, rlk); evaluator.rescale_to_next_inplace(z5);
        if (z5.coeff_modulus_size() <= 2) refresh_ciphertext(sock, z5, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
        
        Ciphertext z2_down2 = z2; match_level_and_scale(z2_down2, z5);
        evaluator.multiply(z5, z2_down2, z7); evaluator.relinearize_inplace(z7, rlk); evaluator.rescale_to_next_inplace(z7);
        if (z7.coeff_modulus_size() <= 2) refresh_ciphertext(sock, z7, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);

        auto multiply_coeff = [&](Ciphertext ct, double coeff) {
            Plaintext pt; encoder.encode(coeff, ct.scale(), pt); evaluator.mod_switch_to_inplace(pt, ct.parms_id());
            Ciphertext res; evaluator.multiply_plain(ct, pt, res); evaluator.rescale_to_next_inplace(res); return res;
        };

        Ciphertext t1 = multiply_coeff(ct_x, 3.15), t3 = multiply_coeff(z3, -4.2);
        Ciphertext t5 = multiply_coeff(z5, 2.5), t7 = multiply_coeff(z7, -0.5);
        match_level_and_scale(t1, t7); match_level_and_scale(t3, t7); match_level_and_scale(t5, t7);

        Ciphertext sign_x;
        evaluator.add(t1, t3, sign_x); evaluator.add_inplace(sign_x, t5); evaluator.add_inplace(sign_x, t7);
        if (sign_x.coeff_modulus_size() <= 2) refresh_ciphertext(sock, sign_x, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
        
        Plaintext pt_minus_half; encoder.encode(-0.5, sign_x.scale(), pt_minus_half); evaluator.mod_switch_to_inplace(pt_minus_half, sign_x.parms_id());
        Ciphertext ct_sx; evaluator.multiply_plain(sign_x, pt_minus_half, ct_sx); evaluator.rescale_to_next_inplace(ct_sx);
        if (ct_sx.coeff_modulus_size() <= 2) refresh_ciphertext(sock, ct_sx, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
        
        Plaintext pt_half; encoder.encode(0.5, ct_sx.scale(), pt_half); evaluator.mod_switch_to_inplace(pt_half, ct_sx.parms_id());
        evaluator.add_plain_inplace(ct_sx, pt_half); 
        
        Plaintext pt_minus_two; encoder.encode(-2.0, ct_sx.scale(), pt_minus_two); evaluator.mod_switch_to_inplace(pt_minus_two, ct_sx.parms_id());
        Ciphertext ct_1_minus_2sx; evaluator.multiply_plain(ct_sx, pt_minus_two, ct_1_minus_2sx); evaluator.rescale_to_next_inplace(ct_1_minus_2sx);
        if (ct_1_minus_2sx.coeff_modulus_size() <= 2) refresh_ciphertext(sock, ct_1_minus_2sx, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
        
        Plaintext pt_one; encoder.encode(1.0, ct_1_minus_2sx.scale(), pt_one); evaluator.mod_switch_to_inplace(pt_one, ct_1_minus_2sx.parms_id());
        evaluator.add_plain_inplace(ct_1_minus_2sx, pt_one);
        
        Ciphertext ct_x_down = ct_x;
        match_level_and_scale(ct_x_down, ct_1_minus_2sx);
        evaluator.multiply(ct_1_minus_2sx, ct_x_down, ct_res);
        evaluator.relinearize_inplace(ct_res, rlk);
        evaluator.rescale_to_next_inplace(ct_res);

        if (ct_res.coeff_modulus_size() <= 2) refresh_ciphertext(sock, ct_res, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
    });

    // =========================================================
    // [Real] SDIV (Deep Goldschmidt Division for Bootstrapping)
    // =========================================================
    double expected_sdiv = val_x / val_y; 
    run_benchmark("SDIV (Deep Goldschmidt Division)", required_iters, expected_sdiv, 0.5, 
    [&](Ciphertext &ct_x, Ciphertext &ct_y, int &bs_count, Ciphertext &ct_res, double &net_time, double &pdec_time) {
        Ciphertext curr_x = ct_x;
        Ciphertext curr_y = ct_y;
        
        int div_iterations = 8; 

        for (int i = 0; i < div_iterations; i++) {
            Plaintext pt_2;
            encoder.encode(2.0, curr_y.scale(), pt_2);
            evaluator.mod_switch_to_inplace(pt_2, curr_y.parms_id());
            
            Ciphertext w;
            evaluator.negate(curr_y, w);
            evaluator.add_plain_inplace(w, pt_2); 
            
            Ciphertext next_x;
            Ciphertext curr_x_aligned = curr_x;
            
            match_level_and_scale(curr_x_aligned, w);
            evaluator.multiply(curr_x_aligned, w, next_x);
            evaluator.relinearize_inplace(next_x, rlk);
            evaluator.rescale_to_next_inplace(next_x);
            
            Ciphertext next_y;
            evaluator.multiply(curr_y, w, next_y);
            evaluator.relinearize_inplace(next_y, rlk);
            evaluator.rescale_to_next_inplace(next_y);
            
            curr_x = next_x;
            curr_y = next_y;
            
            if (curr_x.coeff_modulus_size() <= 2 || curr_y.coeff_modulus_size() <= 2) {
                refresh_ciphertext(sock, curr_x, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
                refresh_ciphertext(sock, curr_y, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
            }
        }
        ct_res = curr_x; 
    });

    double expected_sed = pow(val_x - val_y, 2);
    run_benchmark("SED (Secure Euclidean Distance)", required_iters, expected_sed, 0.01, 
    [&](Ciphertext &ct_x, Ciphertext &ct_y, int &bs_count, Ciphertext &ct_res, double &net_time, double &pdec_time) {
        Ciphertext ct_sub;
        evaluator.sub(ct_x, ct_y, ct_sub); 
        
        evaluator.square(ct_sub, ct_res);  
        evaluator.relinearize_inplace(ct_res, rlk);
        evaluator.rescale_to_next_inplace(ct_res);
        refresh_ciphertext(sock, ct_res, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
    });

    // =========================================================
    // [Real] SMAX (Secure Maximum via Minimax Routing)
    // =========================================================
    double expected_real_u = (val_x > val_y) ? 1.0 : 0.0;
    double expected_smax = expected_real_u * (val_x - val_y) + val_y; 

    run_benchmark("SMAX (Secure Max)", required_iters, expected_smax, 0.1, 
    [&](Ciphertext &ct_x, Ciphertext &ct_y, int &bs_count, Ciphertext &ct_res, double &net_time, double &pdec_time) {
        Ciphertext ct_sub;
        evaluator.sub(ct_x, ct_y, ct_sub); 
        
        Ciphertext z2, z3, z5, z7, z_down1 = ct_sub;
        evaluator.square(ct_sub, z2); evaluator.relinearize_inplace(z2, rlk); evaluator.rescale_to_next_inplace(z2);
        if (z2.coeff_modulus_size() <= 2) refresh_ciphertext(sock, z2, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
        
        match_level_and_scale(z_down1, z2);
        evaluator.multiply(z2, z_down1, z3); evaluator.relinearize_inplace(z3, rlk); evaluator.rescale_to_next_inplace(z3);
        if (z3.coeff_modulus_size() <= 2) refresh_ciphertext(sock, z3, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
        
        Ciphertext z2_down1 = z2; match_level_and_scale(z2_down1, z3);
        evaluator.multiply(z3, z2_down1, z5); evaluator.relinearize_inplace(z5, rlk); evaluator.rescale_to_next_inplace(z5);
        if (z5.coeff_modulus_size() <= 2) refresh_ciphertext(sock, z5, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
        
        Ciphertext z2_down2 = z2; match_level_and_scale(z2_down2, z5);
        evaluator.multiply(z5, z2_down2, z7); evaluator.relinearize_inplace(z7, rlk); evaluator.rescale_to_next_inplace(z7);
        if (z7.coeff_modulus_size() <= 2) refresh_ciphertext(sock, z7, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
        
        auto multiply_coeff = [&](Ciphertext ct, double coeff) {
            Plaintext pt; encoder.encode(coeff, ct.scale(), pt); evaluator.mod_switch_to_inplace(pt, ct.parms_id());
            Ciphertext res; evaluator.multiply_plain(ct, pt, res); evaluator.rescale_to_next_inplace(res); return res;
        };

        Ciphertext t1 = multiply_coeff(ct_sub, 3.15), t3 = multiply_coeff(z3, -4.2);
        Ciphertext t5 = multiply_coeff(z5, 2.5), t7 = multiply_coeff(z7, -0.5);
        match_level_and_scale(t1, t7); match_level_and_scale(t3, t7); match_level_and_scale(t5, t7);

        Ciphertext sign_z;
        evaluator.add(t1, t3, sign_z); evaluator.add_inplace(sign_z, t5); evaluator.add_inplace(sign_z, t7);
        if (sign_z.coeff_modulus_size() <= 2) refresh_ciphertext(sock, sign_z, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
        
        Plaintext pt_half; encoder.encode(0.5, sign_z.scale(), pt_half); evaluator.mod_switch_to_inplace(pt_half, sign_z.parms_id());
        Ciphertext ct_u; evaluator.multiply_plain(sign_z, pt_half, ct_u); evaluator.rescale_to_next_inplace(ct_u); 
        if (ct_u.coeff_modulus_size() <= 2) refresh_ciphertext(sock, ct_u, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);
        
        Plaintext pt_half_add; encoder.encode(0.5, ct_u.scale(), pt_half_add); evaluator.mod_switch_to_inplace(pt_half_add, ct_u.parms_id());
        evaluator.add_plain_inplace(ct_u, pt_half_add); 

        Ciphertext ct_sub_down = ct_sub;
        match_level_and_scale(ct_sub_down, ct_u);
        
        Ciphertext ct_mul;
        evaluator.multiply(ct_u, ct_sub_down, ct_mul);
        evaluator.relinearize_inplace(ct_mul, rlk);
        evaluator.rescale_to_next_inplace(ct_mul);
        if (ct_mul.coeff_modulus_size() <= 2) refresh_ciphertext(sock, ct_mul, context, evaluator, encryptor, sk1, B_ct, t_queries, alpha, bs_count, net_time, pdec_time, use_gaussian);

        Ciphertext ct_y_down = ct_y;
        match_level_and_scale(ct_y_down, ct_mul);
        evaluator.add(ct_mul, ct_y_down, ct_res);
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

    bool is_first_refresh = true; 

    while (true) {
        string cmd = recv_data(sock);
        if (cmd == "DONE") {
            cout << "[Server 2] Received DONE. Exiting..." << endl;
            break;
        }
        if (cmd == "REFRESH") {
            auto t_start_s2 = high_resolution_clock::now();

            // === 细化阶段：将网络接收和反序列化拆开 ===
            auto t_rx_start = high_resolution_clock::now();
            string s_ct_hat = recv_data(sock);
            string s_p0_share = recv_data(sock);
            string s_ct_u_fresh = recv_data(sock);
            auto t_rx_end = high_resolution_clock::now();

            auto t_deser_start = high_resolution_clock::now();
            Ciphertext ct_hat, ct_u_fresh;
            Plaintext p0_share;
            stringstream ss1(s_ct_hat), ss2(s_p0_share), ss3(s_ct_u_fresh);
            ct_hat.load(context, ss1);
            p0_share.load(context, ss2);
            ct_u_fresh.load(context, ss3);
            auto t_deser_end = high_resolution_clock::now();

            Plaintext p1_share;
            partial_dec(context, ct_hat, sk2, p1_share, B_ct, t_queries, alpha, false, false);
            
            auto t_pdec_end = high_resolution_clock::now();

            Plaintext plain_masked_ntt;
            total_dec(context, ct_hat, p0_share, p1_share, plain_masked_ntt);

            auto t_comb_end = high_resolution_clock::now();

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

            auto t_lift_end = high_resolution_clock::now();

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
            
            auto t_enc_end = high_resolution_clock::now();

            // === 细化阶段：将 S2 的序列化和发送拆开 ===
            auto t_ser_start = high_resolution_clock::now();
            stringstream ss_final;
            ct_final.save(ss_final);
            string s_ct_final = ss_final.str();
            auto t_ser_end = high_resolution_clock::now();

            auto t_tx_start = high_resolution_clock::now();
            send_data(sock, s_ct_final);
            auto t_tx_end = high_resolution_clock::now();

            if (is_first_refresh) {
                cout << "\n  ==== [Server 2] 1st Refresh Breakdown ====" << endl;
                cout << "    |-- [S2] Socket Recv:                " << duration_cast<nanoseconds>(t_rx_end - t_rx_start).count() / 1e6 << " ms" << endl;
                cout << "    |-- [S2] Object Deserialization (Load): " << duration_cast<nanoseconds>(t_deser_end - t_deser_start).count() / 1e6 << " ms" << endl;
                cout << "    |-- [S2] Partial Decrypt:            " << duration_cast<nanoseconds>(t_pdec_end - t_deser_end).count() / 1e6 << " ms" << endl;
                cout << "    |-- [S2] Combine Shares:             " << duration_cast<nanoseconds>(t_comb_end - t_pdec_end).count() / 1e6 << " ms" << endl;
                cout << "    |-- [S2] GMP Mod Lifting:            " << duration_cast<nanoseconds>(t_lift_end - t_comb_end).count() / 1e6 << " ms" << endl;
                cout << "    |-- [S2] Encrypt & Sub:              " << duration_cast<nanoseconds>(t_enc_end - t_lift_end).count() / 1e6 << " ms" << endl;
                cout << "    |-- [S2] Object Serialization (Save):   " << duration_cast<nanoseconds>(t_ser_end - t_ser_start).count() / 1e6 << " ms" << endl;
                cout << "    |-- [S2] Socket Send:                " << duration_cast<nanoseconds>(t_tx_end - t_tx_start).count() / 1e6 << " ms" << endl;
                cout << "  =========================================================" << endl;
                is_first_refresh = false;
            }
        }
    }
    close(sock);
}

int main(int argc, char* argv[]) {
    if (argc < 2) {
        cerr << "Usage for Server 1: " << argv[0] << " 1 [port] [N] [target_data_volume] [use_gaussian(1/0)] [B_ct] [t_queries] [alpha]" << endl;
        cerr << "Usage for Server 2: " << argv[0] << " 2 [ip] [port] [B_ct] [t_queries] [alpha]" << endl;
        return 1;
    }

    int role = atoi(argv[1]);
    uint64_t default_t_queries = 128, default_alpha = 128;

    if (role == 1) {
        int port = (argc >= 3) ? atoi(argv[2]) : 12346;
        size_t N = (argc >= 4) ? stoull(argv[3]) : 16384;
        long target_data_volume = (argc >= 5) ? (1ULL << stoull(argv[4])) : (1 << 21);
        bool use_gaussian = (argc >= 6) ? (atoi(argv[5]) != 0) : true;
        
        double seal_sigma = 3.2;
        uint64_t dynamic_B_ct = static_cast<uint64_t>(std::round(6.0 * seal_sigma * std::sqrt(N)));
        
        uint64_t default_B_ct = dynamic_B_ct + 500; 
        
        uint64_t B_ct      = (argc >= 7) ? stoull(argv[6]) : default_B_ct;
        uint64_t t_queries = (argc >= 8) ? stoull(argv[7]) : default_t_queries;
        uint64_t alpha     = (argc >= 9) ? stoull(argv[8]) : default_alpha;
        
        cout << "[Config] Dynamically calculated B_ct for N=" << N << " is: " << B_ct << endl;
        run_server1(port, N, target_data_volume, use_gaussian, B_ct, t_queries, alpha);
    } 
    else if (role == 2) {
        string ip = (argc >= 3) ? argv[2] : "127.0.0.1";
        int port = (argc >= 4) ? atoi(argv[3]) : 12346;
        
        uint64_t fallback_B_ct = static_cast<uint64_t>(std::round(12.0 * 3.2 * std::sqrt(8192))) + 500;
        
        uint64_t B_ct      = (argc >= 5) ? stoull(argv[4]) : fallback_B_ct;
        uint64_t t_queries = (argc >= 6) ? stoull(argv[5]) : default_t_queries;
        uint64_t alpha     = (argc >= 7) ? stoull(argv[6]) : default_alpha;
        
        run_server2(ip, port, B_ct, t_queries, alpha);
    }
    return 0;
}