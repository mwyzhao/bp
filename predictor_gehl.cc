#include "predictor.h"
#include <cstdlib>
#include <cmath>
#include <random>
#include <iostream>

using namespace std;

#define STRG_N 0
#define WEAK_N 1
#define WEAK_T 2
#define STRG_T 3

/////////////////////////////////////////////////////////////
// 2bitsat
/////////////////////////////////////////////////////////////

int BPB[4096]; // 2^12 = 4096 entries, 2-bit field => 8192 bits total

void InitPredictor_2bitsat() {
  for(int i = 0; i < 4096; i++){
    BPB[i] = WEAK_N; // initial state WEAK_N
  }
}

bool GetPrediction_2bitsat(UINT32 PC) {
  return BPB[PC & 0xFFF] > WEAK_N ? TAKEN : NOT_TAKEN;
}

void UpdatePredictor_2bitsat(UINT32 PC, bool resolveDir, bool predDir, UINT32 branchTarget) {
  int ght_index = PC & 0xFFF;
  // update GHT
  BPB[ght_index] += (resolveDir == TAKEN) ? 1 : -1;
  if(BPB[ght_index] < 0){
    BPB[ght_index] = 0;
  }
  if(BPB[ght_index] > 3){
    BPB[ght_index] = 3;
  }
}

/////////////////////////////////////////////////////////////
// 2level
/////////////////////////////////////////////////////////////

/* PC breakdown: ***********
| 31 - 12 | 11 - 3 | 2 - 0 |
----------------------------
|  UNUSED |    BHT |   PHT |
***************************/

int BHT[512]; // 2^0 = 1 table,  2^9 = 512 entries, 6-bit field
int PHT[512]; // 2^3 = 8 tables, 2^6 = 64 entries,  2-bit field

void InitPredictor_2level() {
  for(int i = 0; i < 512; i++){
    BHT[i] = 0; // initial state 6 NOT_TAKEN?
    PHT[i] = WEAK_N; // initial state WEAK_N
  }
}

bool GetPrediction_2level(UINT32 PC) {
  return PHT[BHT[PC >> 3 & 0x1FF] << 3 | (PC & 0x7)] > WEAK_N ? TAKEN : NOT_TAKEN;
}

void UpdatePredictor_2level(UINT32 PC, bool resolveDir, bool predDir, UINT32 branchTarget) {
  int bht_index = PC >> 3 & 0x1FF;
  int pht_index = BHT[bht_index] << 3 | (PC & 0x7);
  // update PHT
  PHT[pht_index] += (resolveDir == TAKEN) ? 1 : -1;
  if(PHT[pht_index] < 0){
    PHT[pht_index] = 0;
  }
  if(PHT[pht_index] > 3){
    PHT[pht_index] = 3;
  }
  // update BHT
  BHT[bht_index] = (BHT[bht_index] << 1 | resolveDir) & 0x3F;
}

/////////////////////////////////////////////////////////////
// openend
/////////////////////////////////////////////////////////////

// O-GEHL

/* NOTE: Values are UINTX and types/sizes/flags are int */
/* NOTE: Maximum "size" values for function inputs/outputs are dictated by input/output type
 * eg. UINT128 type => max size is 128, UINT32 type => max size is 32                        */

/*******************************************************************************************
 * DEFINES AND TYPES
 *******************************************************************************************/

// #define COLL_STAT

#define UINT128 unsigned __int128
// UINT32 and UINT64 defined in utils.h

#define MAX_MEM        131072  // 128k in bytes

#define GHR_SIZE       128     // bounded by UINT128, need custom impl for larger

// SC PARAMETERS AND DEFINITIONS

#define N_SC_TABLES    5
#define ALPHA          2
#define L1             2

#define SCI_SIZE       10
#define SC_SIZE        1024

#define SCTR_SIZE      6

#define SC_THRESH      5
#define TCTR_SIZE      7
#define HASH_BIT_SIZE  3

struct sc_entry {
  UINT32 ctr;
};

/*******************************************************************************************
 * STATISTIC COLLECTION VARIABLES
 *******************************************************************************************/

// int num_wrong_pred[N_TABLES];
// int num_times_used[N_TABLES];
// int num_times_useful[N_TABLES];

/*******************************************************************************************
 * GLOBAL VARIABLES
 *******************************************************************************************/

// GHR max 128 unfortunately, can be extended with hacks
UINT128 ghr;

int sc_sum;
UINT32 sc_thresh;
UINT32 tctr;

sc_entry sc_table[N_SC_TABLES][SC_SIZE];

/*******************************************************************************************
 * UTILITY FUNCTIONS
 *******************************************************************************************/

inline UINT32 get_mask(int size){
  return ((UINT64)1 << size) - 1; // cast to UINT64 for when size = 32
}

inline UINT32 get_msb(UINT32 val, int size){
  return (val >> (size - 1)) & 0x1;
}

inline UINT32 get_weak_taken(int size){
  return (1 << (size - 1));
}

inline UINT32 get_weak_not_taken(int size){
  return (1 << (size - 1)) - 1;
}

// count up saturating counter
UINT32 sat_ctr_inc(UINT32 ctr, int size) {
  UINT32 max = get_mask(size);
  if(ctr == max){
    return ctr;
  }
  else {
    return ctr + 1;
  }
}

// count down saturating counter
UINT32 sat_ctr_dec(UINT32 ctr, int size) {
  UINT32 min = 0;
  if(ctr == min){
    return ctr;
  }
  else {
    return ctr - 1;
  }
}

/*******************************************************************************************
 * IMPLEMENTATION DEPENDENT FUNCTIONS
 *******************************************************************************************/

// get Li aka history length based on Seznec O-GHEL paper
inline UINT32 get_l(int i) { // 1 <= i <= N_TABLES
  return (UINT32)(pow(ALPHA, i-1) * L1 + 0.5);
}

// fold values based on Michaud PPM-like paper
UINT32 fold(UINT128 val, int size, int size_out){
  int num_iter = size / size_out;
  UINT32 val_mask = get_mask(size_out);
  UINT32 val_temp = 0;
  int i;
  for(i = 0; i < num_iter; i++){
    val_temp ^= (UINT32)(val >> i*size_out);
  }
  val_temp ^= (UINT32)(val >> i*size_out) & get_mask(size % size_out);
  return val_temp & val_mask;
}

// get index based on Michaud PPM-like predictor paper
UINT32 get_index(UINT32 pc, int pc_size, UINT128 ghr, int ghr_size, int index_size){
  UINT32 pc_folded = fold((UINT128)pc, pc_size, index_size); // index_size bits
  UINT32 ghr_folded = fold(ghr, ghr_size, index_size);       // index_size bits
  UINT32 ghr_folded_mod = fold(ghr, ghr_size, index_size-1); // index_size-1 bits
  return pc_folded ^ ghr_folded ^ (ghr_folded_mod << 1);
}

// update counter based on dir
UINT32 update_ctr(int dir, UINT32 ctr, int size){
  if(dir){
    return sat_ctr_inc(ctr, size);
  }
  else{
    return sat_ctr_dec(ctr, size);
  }
}

/*******************************************************************************************
 * MAIN PREDICTOR FUNCTIONS
 *******************************************************************************************/

void InitPredictor_openend() {
  ghr = 0; // init to all not taken
  sc_thresh = SC_THRESH; // init threshold
  tctr = get_weak_taken(TCTR_SIZE);
  for(int i = 0; i < N_SC_TABLES; i++){
    for(int j = 0; j < SC_SIZE; j++){
      sc_table[i][j].ctr = get_weak_taken(SCTR_SIZE);
    }
  }
}

bool GetPrediction_openend(UINT32 PC) {
  sc_sum = 0;
  for(int i = 0; i < N_SC_TABLES; i++){
    UINT32 sc_index = get_index(PC, sizeof(PC)*8, ghr, get_l(i+1), SCI_SIZE);
    sc_sum += ((sc_table[i][sc_index].ctr - get_weak_taken(SCTR_SIZE)) << 1) + 1;
  }
  return sc_sum >= 0;
}

void UpdatePredictor_openend(UINT32 PC, bool resolveDir, bool predDir, UINT32 branchTarget) {
  if(predDir != resolveDir || (UINT32)abs(sc_sum) < sc_thresh){
    for(int i = 0; i < N_SC_TABLES; i++){
      int sc_index = get_index(PC, sizeof(PC)*8, ghr, get_l(i+1), SCI_SIZE);
      sc_table[i][sc_index].ctr =
        update_ctr(resolveDir == TAKEN, sc_table[i][sc_index].ctr, SCTR_SIZE);
    }
  }
  if(predDir != resolveDir){
    tctr = sat_ctr_inc(tctr, TCTR_SIZE);
    if(tctr == get_mask(TCTR_SIZE)){
      sc_thresh++;
      tctr = get_weak_taken(TCTR_SIZE);
    }
  }
  if(predDir == resolveDir && (UINT32)abs(sc_sum) < sc_thresh){
    tctr = sat_ctr_dec(tctr, TCTR_SIZE);
    if(tctr == 0){
      sc_thresh--;
      tctr = get_weak_taken(TCTR_SIZE);
    }
  }
  // Update GHR last
  ghr = (ghr << 1) | resolveDir;
}

// Statistic reporting cleanup function
void TermPredictor_openend() {
  ;
}

