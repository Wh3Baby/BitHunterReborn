#include <iostream>
#include <string>
#include <cstdint>
#include <stdexcept>
#include <vector>
#include <random>
#include <cassert>
#include <cstring>
#include <climits>
#include <curl/curl.h>
#include <sqlite3.h>
#include <thread>        
#include <chrono>
#include "nlohmann/json.hpp"
using json = nlohmann::json;

// -------------------------------------------------------------
// Константы secp256k1
// -------------------------------------------------------------
static const uint8_t secp256k1_p[32] = {
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xfe,
    0xff,0xff,0xfc,0x2f,0x00,0x00,0x00,0x00,
    0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
};

static const uint8_t secp256k1_n[32] = {
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
    0xff,0xff,0xff,0xfe,0xba,0xae,0xdc,0xe6,
    0xaf,0x48,0xa0,0x3b,0xbf,0xd2,0x5e,0x8c,
    0xd0,0x36,0x41,0x41,0x02,0x7e,0x9e,0x59
};

static const uint8_t secp256k1_Gx[32] = {
    0x79,0xbe,0x66,0x7e,0xf9,0xdc,0xbb,0xac,
    0x55,0xa0,0x62,0x95,0xce,0x87,0x0b,0x07,
    0x02,0x9b,0xfc,0xdb,0x2d,0xce,0x28,0xd9,
    0x59,0xf2,0x81,0x5b,0x16,0xf8,0x17,0x98
};

static const uint8_t secp256k1_Gy[32] = {
    0x48,0x3a,0xda,0x77,0x26,0xa3,0xc4,0x65,
    0x5d,0xa4,0xfb,0xfc,0x0e,0x11,0x08,0xa8,
    0xfd,0x17,0xb4,0x48,0xa6,0x85,0x54,0x19,
    0x9c,0x47,0xd0,0x8f,0xfb,0x10,0xd4,0xb8
};

// -------------------------------------------------------------
// Функции для работы с большими числами и эллиптической арифметикой
// -------------------------------------------------------------
static void bn_copy(uint8_t r[32], const uint8_t a[32]) {
    std::memcpy(r, a, 32);
}

static int bn_cmp(const uint8_t a[32], const uint8_t b[32]) {
    for (int i = 0; i < 32; i++) {
        if (a[i] < b[i]) return -1;
        else if (a[i] > b[i]) return 1;
    }
    return 0;
}

static int bn_is_zero(const uint8_t a[32]) {
    for (int i = 0; i < 32; i++) {
        if (a[i] != 0) return 0;
    }
    return 1;
}

static void bn_add_modn(uint8_t r[32], const uint8_t a[32], const uint8_t b[32]) {
    unsigned int carry = 0;
    for (int i = 31; i >= 0; i--) {
        unsigned int sum = a[i] + b[i] + carry;
        r[i] = (uint8_t)sum;
        carry = sum >> 8;
    }
    while (carry || bn_cmp(r, secp256k1_n) >= 0) {
        unsigned int borrow = 0;
        for (int i = 31; i >= 0; i--) {
            unsigned int diff = (unsigned int)r[i] - secp256k1_n[i] - borrow;
            r[i] = (uint8_t)diff;
            borrow = (diff >> 31) & 1;
        }
    }
}

static void bn_add_modp(uint8_t r[32], const uint8_t a[32], const uint8_t b[32]) {
    unsigned int carry = 0;
    for (int i = 31; i >= 0; i--) {
        unsigned int sum = a[i] + b[i] + carry;
        r[i] = (uint8_t)sum;
        carry = sum >> 8;
    }
    if (bn_cmp(r, secp256k1_p) >= 0) {
        unsigned int borrow = 0;
        for (int i = 31; i >= 0; i--) {
            unsigned int diff = (unsigned int)r[i] - secp256k1_p[i] - borrow;
            r[i] = (uint8_t)diff;
            borrow = (diff >> 31) & 1;
        }
    }
}

static void bn_sub_modp(uint8_t r[32], const uint8_t a[32], const uint8_t b[32]) {
    int borrow = 0;
    for (int i = 31; i >= 0; i--) {
        int diff = (int)a[i] - b[i] - borrow;
        borrow = diff < 0 ? 1 : 0;
        r[i] = (uint8_t)(diff & 0xff);
    }
    if (borrow) {
        unsigned int carry = 0;
        for (int i = 31; i >= 0; i--) {
            unsigned int sum = r[i] + secp256k1_p[i] + carry;
            r[i] = (uint8_t)sum;
            carry = sum >> 8;
        }
    }
}

static void bn_mul(uint8_t r[64], const uint8_t a[32], const uint8_t b[32]) {
    memset(r, 0, 64);
    for (int i = 31; i >= 0; i--) {
        unsigned int carry = 0;
        for (int j = 31; j >= 0; j--) {
            unsigned long long sum = (unsigned long long)r[i + j + 1] + (unsigned long long)a[i] * (unsigned long long)b[j] + carry;
            r[i + j + 1] = (uint8_t)sum;
            carry = (unsigned int)(sum >> 8);
        }
        r[i] = (uint8_t)carry;
    }
}

static void bn_mod(uint8_t r[32], const uint8_t in[64], const uint8_t p[32]) {
    uint8_t tmp[64]; memcpy(tmp, in, 64);
    while (true) {
        int cmp = 0;
        for (int i = 0; i < 32; i++) {
            if (tmp[i] < p[i]) { cmp = -1; break; }
            else if (tmp[i] > p[i]) { cmp = 1; break; }
        }
        if (cmp < 0) break;
        unsigned int borrow = 0;
        for (int i = 31; i >= 0; i--) {
            unsigned int diff = (unsigned int)tmp[i + 32] - (unsigned int)p[i] - borrow;
            tmp[i + 32] = (uint8_t)diff;
            borrow = (diff >> 31) & 1;
        }
    }
    memcpy(r, tmp + 32, 32);
}

static void bn_mul_modp(uint8_t r[32], const uint8_t a[32], const uint8_t b[32]) {
    uint8_t mulres[64];
    bn_mul(mulres, a, b);
    bn_mod(r, mulres, secp256k1_p);
}

static void bn_copy32(uint8_t r[32], const uint8_t a[32]) {
    memcpy(r, a, 32);
}

static const uint8_t secp256k1_p_minus_2[32] = {
  0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
  0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xfe,
  0xff,0xff,0xfc,0x2d,0x00,0x00,0x00,0x00,
  0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
};

static void bn_modexp(uint8_t r[32], const uint8_t base[32], const uint8_t exp[32], const uint8_t m[32]) {
    uint8_t res[32]; memset(res, 0, 32); res[31] = 1;
    uint8_t cur[32]; bn_copy32(cur, base);

    for (int i = 0; i < 32; i++) {
        uint8_t e = exp[31 - i];
        for (int bit = 0; bit < 8; bit++) {
            if (e & 1) {
                bn_mul_modp(res, res, cur);
            }
            bn_mul_modp(cur, cur, cur);
            e >>= 1;
        }
    }
    bn_copy32(r, res);
}

static void mod_inv(const uint8_t in[32], uint8_t out[32], const uint8_t p[32]) {
    bn_modexp(out, in, secp256k1_p_minus_2, p);
}

// -------------------------------------------------------------
// Арифметика точек
// -------------------------------------------------------------
static void point_double(uint8_t X[32], uint8_t Y[32]);
static void point_add(uint8_t X1[32], uint8_t Y1[32], const uint8_t X2[32], const uint8_t Y2[32]);

static bool point_mul_G(const uint8_t d[32], uint8_t outx[32], uint8_t outy[32]) {
    if (bn_is_zero(d)) return false;
    if (bn_cmp(d, secp256k1_n) >= 0) return false;

    uint8_t X[32], Y[32];
    memset(X, 0, 32);
    memset(Y, 0, 32);

    uint8_t Gx[32]; memcpy(Gx, secp256k1_Gx, 32);
    uint8_t Gy[32]; memcpy(Gy, secp256k1_Gy, 32);

    for (int i = 0; i < 32; i++) {
        uint8_t byte = d[i];
        for (int bit = 7; bit >= 0; bit--) {
            point_double(X, Y);
            if ((byte >> bit) & 1) {
                point_add(X, Y, Gx, Gy);
            }
        }
    }

    if (bn_is_zero(X) && bn_is_zero(Y)) return false;
    memcpy(outx, X, 32);
    memcpy(outy, Y, 32);
    return true;
}

static void point_double(uint8_t X[32], uint8_t Y[32]) {
    if (bn_is_zero(Y)) {
        memset(X, 0, 32);
        memset(Y, 0, 32);
        return;
    }

    uint8_t s[32], t1[32], t2[32], inv[32];

    bn_mul_modp(t1, X, X);
    {
        uint8_t three[32]; memset(three, 0, 32); three[31] = 3;
        bn_mul_modp(t1, t1, three);
    }

    {
        uint8_t two[32]; memset(two, 0, 32); two[31] = 2;
        bn_mul_modp(t2, Y, two);
    }

    mod_inv(t2, inv, secp256k1_p);
    bn_mul_modp(s, t1, inv);

    bn_mul_modp(t1, s, s);
    {
        uint8_t two[32]; memset(two, 0, 32); two[31] = 2;
        uint8_t twoX[32];
        bn_mul_modp(twoX, X, two);
        bn_sub_modp(t1, t1, twoX);
    }
    uint8_t X3[32]; bn_copy(X3, t1);

    uint8_t xmxx3[32];
    bn_sub_modp(xmxx3, X, X3);
    bn_mul_modp(t1, s, xmxx3);

    uint8_t Y3[32];
    bn_sub_modp(Y3, t1, Y);

    bn_copy(X, X3);
    bn_copy(Y, Y3);
}

static void point_add(uint8_t X1[32], uint8_t Y1[32], const uint8_t X2[32], const uint8_t Y2[32]) {
    if (bn_is_zero(X1) && bn_is_zero(Y1)) {
        bn_copy(X1, X2);
        bn_copy(Y1, Y2);
        return;
    }
    if (bn_is_zero(X2) && bn_is_zero(Y2)) {
        return;
    }
    if (bn_cmp(X1, X2) == 0 && bn_cmp(Y1, Y2) == 0) {
        point_double(X1, Y1);
        return;
    }

    uint8_t dx[32], dy[32], inv[32], lam[32];
    bn_sub_modp(dx, X2, X1);
    bn_sub_modp(dy, Y2, Y1);

    mod_inv(dx, inv, secp256k1_p);
    bn_mul_modp(lam, dy, inv);

    uint8_t lam2[32];
    bn_mul_modp(lam2, lam, lam);

    uint8_t X3[32], Y3[32];
    {
        uint8_t tmp[32];
        bn_sub_modp(tmp, lam2, X1);
        bn_sub_modp(X3, tmp, X2);
    }

    uint8_t x1mx3[32];
    bn_sub_modp(x1mx3, X1, X3);
    bn_mul_modp(Y3, lam, x1mx3);
    bn_sub_modp(Y3, Y3, Y1);

    bn_copy(X1, X3);
    bn_copy(Y1, Y3);
}

// -------------------------------------------------------------
// SHA-256
// -------------------------------------------------------------
#include <array>

static inline uint32_t rotr32(uint32_t x, uint32_t n) {
    return (x >> n) | (x << (32 - n));
}

static void sha256_transform(uint32_t state[8], const uint8_t block[64]) {
    static const uint32_t K[64] = {
        0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,
        0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
        0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,
        0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
        0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,
        0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
        0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,
        0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
        0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,
        0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
        0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,
        0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
        0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,
        0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
        0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,
        0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
    };
    uint32_t W[64];
    for (int i = 0; i < 16; i++) {
        W[i] = (block[i * 4] << 24) | (block[i * 4 + 1] << 16) | (block[i * 4 + 2] << 8) | (block[i * 4 + 3]);
    }
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = rotr32(W[i - 15], 7) ^ rotr32(W[i - 15], 18) ^ (W[i - 15] >> 3);
        uint32_t s1 = rotr32(W[i - 2], 17) ^ rotr32(W[i - 2], 19) ^ (W[i - 2] >> 10);
        W[i] = W[i - 16] + s0 + W[i - 7] + s1;
    }

    uint32_t a = state[0], b = state[1], c = state[2], d = state[3];
    uint32_t e = state[4], f = state[5], g = state[6], h = state[7];

    for (int i = 0; i < 64; i++) {
        uint32_t S1 = rotr32(e, 6) ^ rotr32(e, 11) ^ rotr32(e, 25);
        uint32_t ch = (e & f) ^ ((~e) & g);
        uint32_t temp1 = h + S1 + ch + K[i] + W[i];
        uint32_t S0 = rotr32(a, 2) ^ rotr32(a, 13) ^ rotr32(a, 22);
        uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
        uint32_t temp2 = S0 + maj;

        h = g; g = f; f = e; e = d + temp1;
        d = c; c = b; b = a; a = temp1 + temp2;
    }

    state[0] += a; state[1] += b; state[2] += c; state[3] += d;
    state[4] += e; state[5] += f; state[6] += g; state[7] += h;
}

static void sha256(const uint8_t* data, size_t len, uint8_t out[32]) {
    uint32_t state[8] = {
        0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,
        0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19
    };

    uint64_t bitlen = (uint64_t)len * 8;
    uint8_t block[64];
    size_t i = 0;
    for (; i + 64 <= len; i += 64) {
        sha256_transform(state, data + i);
    }
    size_t r = len - i;
    memcpy(block, data + i, r);
    block[r] = 0x80;
    memset(block + r + 1, 0, 64 - (r + 1));
    if (r >= 56) {
        sha256_transform(state, block);
        memset(block, 0, 64);
    }
    for (int j = 0; j < 8; j++) {
        block[63 - j] = (uint8_t)((bitlen >> (8 * j)) & 0xff);
    }
    sha256_transform(state, block);

    for (int j = 0; j < 8; j++) {
        out[j * 4] = (uint8_t)(state[j] >> 24);
        out[j * 4 + 1] = (uint8_t)(state[j] >> 16);
        out[j * 4 + 2] = (uint8_t)(state[j] >> 8);
        out[j * 4 + 3] = (uint8_t)(state[j]);
    }
}

// -------------------------------------------------------------
// RIPEMD-160
// -------------------------------------------------------------
static inline uint32_t rotl32(uint32_t x, uint32_t n) {
    return (x << n) | (x >> (32 - n));
}

static uint32_t F(uint32_t j, uint32_t x, uint32_t y, uint32_t z) {
    if (j <= 15) return x ^ y ^ z;
    else if (j <= 31) return (x & y) | (~x & z);
    else if (j <= 47) return (x | ~y) ^ z;
    else if (j <= 63) return (x & z) | (y & ~z);
    else return x ^ (y | ~z);
}

static int r[80] = {
  0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,
  7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8,
  3,10,14,4,9,15,8,1,2,7,0,6,13,11,5,12,
  1,9,11,10,0,8,12,4,13,3,7,15,14,5,6,2,
  4,0,5,9,7,12,2,10,14,1,3,8,11,6,15,13
};

static int rr[80] = {
  5,14,7,0,9,2,11,4,13,6,15,8,1,10,3,12,
  6,11,3,7,0,13,5,10,14,15,8,12,4,9,1,2,
  15,5,1,3,7,14,6,9,11,8,12,2,10,14,4,13,
  8,6,4,1,3,11,15,0,5,12,2,13,9,7,10,14,
  12,15,10,4,1,5,8,7,6,2,13,14,0,3,9,11
};

static int s[80] = {
  11,14,15,12,5,8,7,9,11,13,14,15,6,7,9,8,
  7,6,8,13,11,9,7,15,7,12,15,9,11,7,13,12,
  11,13,6,7,14,9,13,15,14,8,13,6,5,12,7,5,
  11,12,14,15,14,15,9,8,9,14,5,6,8,6,5,15,
  12,9,12,5,14,6,8,13,6,5,15,13,11,11,15,5
};

static int ss[80] = {
  8,9,9,11,13,15,15,5,7,7,8,11,14,14,12,6,
  9,13,15,7,12,8,9,11,7,7,12,7,6,15,13,11,
  9,7,15,11,8,6,6,14,12,13,5,14,13,13,7,5,
  15,5,8,11,14,14,6,14,6,9,12,9,12,5,15,8,
  8,5,12,9,12,5,14,6,8,13,6,5,15,5,14,11
};

static uint32_t K[5] = { 0x00000000,0x5a827999,0x6ed9eba1,0x8f1bbcdc,0xa953fd4e };
static uint32_t KK[5] = { 0x50a28be6,0x5c4dd124,0x6d703ef3,0x7a6d76e9,0x00000000 };

static void ripemd160_compress(uint32_t h[5], const uint8_t block[64]) {
    uint32_t X[16];
    for (int i = 0; i < 16; i++) {
        X[i] = (block[i * 4]) | (block[i * 4 + 1] << 8) | (block[i * 4 + 2] << 16) | (block[i * 4 + 3] << 24);
    }

    uint32_t a = h[0], b = h[1], c = h[2], d = h[3], e = h[4];
    uint32_t A = a, B = b, C = c, D = d, E = e;

    for (int j = 0; j < 80; j++) {
        int div = j / 16;
        uint32_t t = a + F(j, b, c, d) + X[r[j]] + (div == 0 ? K[0] : div == 1 ? K[1] : div == 2 ? K[2] : div == 3 ? K[3] : K[4]);
        t = rotl32(t, s[j]) + e; a = e; e = d; d = rotl32(c, 10); c = b; b = t;
    }

    for (int j = 0; j < 80; j++) {
        int div = j / 16;
        uint32_t t = A + F(79 - j, B, C, D) + X[rr[j]] + (div == 0 ? KK[0] : div == 1 ? KK[1] : div == 2 ? KK[2] : div == 3 ? KK[3] : KK[4]);
        t = rotl32(t, ss[j]) + E; A = E; E = D; D = rotl32(C, 10); C = B; B = t;
    }

    uint32_t tmp = h[1] + c + D;
    h[1] = h[2] + d + E;
    h[2] = h[3] + e + A;
    h[3] = h[4] + a + B;
    h[4] = h[0] + b + C;
    h[0] = tmp;
}

static void ripemd160(const uint8_t* msg, size_t len, uint8_t out[20]) {
    uint32_t h[5] = { 0x67452301,0xefcdab89,0x98badcfe,0x10325476,0xc3d2e1f0 };

    uint64_t bitlen = (uint64_t)len * 8;
    size_t pad_len = (len % 64 < 56) ? (56 - (len % 64)) : (64 - (len % 64) + 56);
    std::vector<uint8_t> buf(len + pad_len + 8);
    memcpy(buf.data(), msg, len);
    buf[len] = 0x80;
    memset(buf.data() + len + 1, 0, pad_len - 1);
    for (int i = 0; i < 8; i++) {
        buf[len + pad_len + i] = (uint8_t)(bitlen >> (8 * i));
    }

    for (size_t i = 0; i < buf.size(); i += 64) {
        ripemd160_compress(h, buf.data() + i);
    }

    for (int i = 0; i < 5; i++) {
        out[i * 4] = (uint8_t)(h[i]);
        out[i * 4 + 1] = (uint8_t)(h[i] >> 8);
        out[i * 4 + 2] = (uint8_t)(h[i] >> 16);
        out[i * 4 + 3] = (uint8_t)(h[i] >> 24);
    }
}

// -------------------------------------------------------------
// Base58Check Encoding
// -------------------------------------------------------------
static const char* b58_alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";

static std::string base58check_encode(const uint8_t* data, size_t len) {
    int zeros = 0;
    while (zeros < (int)len && data[zeros] == 0) zeros++;

    std::vector<uint8_t> buf; buf.reserve(len * 2);
    for (size_t i = 0; i < len; i++) {
        int carry = data[i];
        for (size_t j = 0; j < buf.size(); j++) {
            int val = buf[j] * 256 + carry;
            buf[j] = (uint8_t)(val % 58);
            carry = val / 58;
        }
        while (carry) {
            buf.push_back((uint8_t)(carry % 58));
            carry /= 58;
        }
    }

    std::string result(zeros, '1');
    for (int i = (int)buf.size() - 1; i >= 0; i--) {
        result.push_back(b58_alphabet[buf[i]]);
    }
    return result;
}

// -------------------------------------------------------------
// SQLite база
// -------------------------------------------------------------
class Database {
public:
    Database(const std::string& path) {
        if (sqlite3_open(path.c_str(), &db_) != SQLITE_OK) {
            throw std::runtime_error("Cannot open database");
        }
        const char* create_table_sql =
            "CREATE TABLE IF NOT EXISTS addresses ("
            " privkey TEXT,"
            " address TEXT PRIMARY KEY,"
            " balance INTEGER"
            ");";
        char* errMsg = nullptr;
        if (sqlite3_exec(db_, create_table_sql, 0, 0, &errMsg) != SQLITE_OK) {
            std::string err = errMsg;
            sqlite3_free(errMsg);
            throw std::runtime_error("Cannot create table: " + err);
        }
    }
    ~Database() {
        if (db_) sqlite3_close(db_);
    }
    bool insert_or_update_address(const std::string& privkey, const std::string& address, int64_t balance) {
        const char* sql = "INSERT OR REPLACE INTO addresses (privkey,address,balance) VALUES (?,?,?);";
        sqlite3_stmt* stmt;
        if (sqlite3_prepare_v2(db_, sql, -1, &stmt, nullptr) != SQLITE_OK) {
            return false;
        }
        sqlite3_bind_text(stmt, 1, privkey.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 2, address.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_int64(stmt, 3, balance);
        bool result = (sqlite3_step(stmt) == SQLITE_DONE);
        sqlite3_finalize(stmt);
        return result;
    }

private:
    sqlite3* db_;
};

// -------------------------------------------------------------
// HTTP и парсинг multiaddr ответа
// -------------------------------------------------------------
struct CurlWriteData {
    std::string data;
};

static size_t write_cb(void* contents, size_t size, size_t nmemb, void* userp) {
    size_t realsize = size * nmemb;
    CurlWriteData* mem = (CurlWriteData*)userp;
    mem->data.append((char*)contents, realsize);
    return realsize;
}

static bool get_multiaddr_balances(const std::vector<std::string>& addresses, std::vector<int64_t>& balances) {
    if (addresses.empty()) return true;

    std::string url = "https://blockchain.info/multiaddr?active=";
    for (size_t i = 0; i < addresses.size(); i++) {
        if (i > 0) url += "|";
        url += addresses[i];
    }

    CURL* curl = curl_easy_init();
    if (!curl) return false;

    // Добавляем CORS заголовки
    struct curl_slist* headers = nullptr;
    headers = curl_slist_append(headers, "Origin: https://example.com");
    headers = curl_slist_append(headers, "Access-Control-Request-Method: GET");
    headers = curl_slist_append(headers, "Access-Control-Allow-Origin: *");
    curl_easy_setopt(curl, CURLOPT_HTTPHEADER, headers);

    curl_easy_setopt(curl, CURLOPT_URL, url.c_str());
    curl_easy_setopt(curl, CURLOPT_USERAGENT, "curl/7.68.0");
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 0L);
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYHOST, 0L);

    CurlWriteData chunk;
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, write_cb);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, (void*)&chunk);

    CURLcode res = curl_easy_perform(curl);
    curl_easy_cleanup(curl);
    curl_slist_free_all(headers);

    if (res != CURLE_OK) {
        return false;
    }

    balances.clear();
    balances.reserve(addresses.size());

    try {
        // Парсим полученный JSON
        json j = json::parse(chunk.data);

        // Проверяем, есть ли массив "addresses"
        if (!j.contains("addresses") || !j["addresses"].is_array()) {
            // Если нет массива addresses - помечаем все -1
            for (size_t i = 0; i < addresses.size(); i++) balances.push_back(-1);
            return true;
        }

        const auto& arr = j["addresses"];
        // В идеале количество элементов должно совпадать с количеством наших адресов
        // Но в случае несоответствия - мы обработаем ситуацию
        size_t count = arr.size();

        // Создадим map для быстрых сопоставлений адресов с их балансами
        // т.к. порядок может не совпадать (теоретически)
        std::unordered_map<std::string, int64_t> addr_to_balance;
        addr_to_balance.reserve(count);

        for (auto& el : arr) {
            if (!el.contains("address") || !el.contains("final_balance")) {
                // Если нет нужных полей, пропускаем
                continue;
            }

            std::string addr = el["address"].get<std::string>();
            int64_t fb = el["final_balance"].get<int64_t>();
            addr_to_balance[addr] = fb;
        }

        // Теперь для каждого запрошенного адреса достаём баланс
        for (auto& a : addresses) {
            auto it = addr_to_balance.find(a);
            if (it != addr_to_balance.end()) {
                balances.push_back(it->second);
            }
            else {
                // Если адреса нет - -1
                balances.push_back(-1);
            }
        }

        return true;

    }
    catch (const std::exception& e) {
        // Если парсинг упал, выставляем -1
        for (size_t i = 0; i < addresses.size(); i++) balances.push_back(-1);
        return true;
    }
}
// -------------------------------------------------------------
// Генерация публичного ключа из приватного
// -------------------------------------------------------------
static bool secp256k1_point_mul(const uint8_t priv[32], uint8_t pub[33]) {
    uint8_t X[32], Y[32];
    if (!point_mul_G(priv, X, Y)) return false;
    pub[0] = (Y[31] & 1) ? 0x03 : 0x02;
    memcpy(pub + 1, X, 32);
    return true;
}

// -------------------------------------------------------------
// main
// -------------------------------------------------------------
int main() {
    curl_global_init(CURL_GLOBAL_DEFAULT);

    Database db("addresses.db");

    uint8_t base_key[32];
    // Фиксируем первые 25 байт в нули (уязвимый паттерн)
    memset(base_key, 0, 32);

    std::random_device rd;
    std::mt19937_64 gen(rd());
    std::uniform_int_distribution<uint64_t> dist;

    const size_t BATCH_SIZE = 100;
    const auto BATCH_INTERVAL = std::chrono::seconds(10);

    std::vector<std::string> addresses_batch;
    std::vector<std::string> privkeys_batch;
    addresses_batch.reserve(BATCH_SIZE);
    privkeys_batch.reserve(BATCH_SIZE);

    auto last_batch_time = std::chrono::steady_clock::now();

    // Счётчик i будет перебирать все int значения
    // Когда достигнет INT_MAX, сбросим его в 0
    int i = 0;

    while (true) {
        // Генерируем последние 7 байт
        uint64_t rand_part = dist(gen);
        for (int b = 0; b < 7; b++) {
            base_key[25 + b] = (uint8_t)((rand_part >> (8 * b)) & 0xFF);
        }

        while (bn_cmp(base_key, secp256k1_n) >= 0 || bn_is_zero(base_key)) {
            rand_part = dist(gen);
            for (int b = 0; b < 7; b++) {
                base_key[25 + b] = (uint8_t)((rand_part >> (8 * b)) & 0xFF);
            }
        }

        uint8_t priv[32]; memcpy(priv, base_key, 32);

        uint8_t pub[33];
        if (!secp256k1_point_mul(priv, pub)) {
            std::cerr << "Invalid key\n";
            // Переходим к следующей итерации
            // i инкрементируем ниже
        }
        else {
            uint8_t sha_out[32]; sha256(pub, 33, sha_out);
            uint8_t ripe_out[20]; ripemd160(sha_out, 32, ripe_out);

            uint8_t versioned[21];
            versioned[0] = 0x00;
            memcpy(versioned + 1, ripe_out, 20);

            uint8_t check_hash[32];
            sha256(versioned, 21, check_hash);
            sha256(check_hash, 32, check_hash);

            uint8_t final_data[25];
            memcpy(final_data, versioned, 21);
            memcpy(final_data + 21, check_hash, 4);

            std::string address = base58check_encode(final_data, 25);

            // Приватный ключ в hex
            static const char* hexchars = "0123456789abcdef";
            std::string priv_hex; priv_hex.reserve(64);
            for (int k = 0; k < 32; k++) {
                priv_hex.push_back(hexchars[(priv[k] >> 4) & 0xF]);
                priv_hex.push_back(hexchars[priv[k] & 0xF]);
            }

            addresses_batch.push_back(address);
            privkeys_batch.push_back(priv_hex);
        }

        // Проверяем, не пора ли сделать batch-запрос
        auto now = std::chrono::steady_clock::now();
        if (addresses_batch.size() >= BATCH_SIZE || now - last_batch_time >= BATCH_INTERVAL) {
            // Делаем multiaddr запрос
            std::vector<int64_t> balances;
            if (get_multiaddr_balances(addresses_batch, balances)) {
                // Обновляем БД
                for (size_t idx = 0; idx < addresses_batch.size(); idx++) {
                    db.insert_or_update_address(privkeys_batch[idx], addresses_batch[idx], balances[idx]);
                    std::cout << "Address: " << addresses_batch[idx] << " Balance: " << balances[idx] << " PrivKey(hex): " << privkeys_batch[idx] << "\n";
                }
            }
            else {
                // Если не удалось получить - помечаем -1
                for (size_t idx = 0; idx < addresses_batch.size(); idx++) {
                    db.insert_or_update_address(privkeys_batch[idx], addresses_batch[idx], -1);
                    std::cout << "Address: " << addresses_batch[idx] << " Balance: -1 PrivKey(hex): " << privkeys_batch[idx] << "\n";
                }
            }
            addresses_batch.clear();
            privkeys_batch.clear();
            last_batch_time = now;
        }

        // Инкрементируем i
        i++;
        if (i == INT_MAX) {
            // Достигли максимума int, сбрасываем
            i = 0;
        }
    }

    curl_global_cleanup();
    return 0;
}