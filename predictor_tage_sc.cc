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

// TAGE-SC

/* NOTE: Values are UINTX and types/sizes/flags are int */
/* NOTE: Maximum "size" values for function inputs/outputs are dictated by input/output type
 * eg. UINT128 type => max size is 128, UINT32 type => max size is 32                        */

/*******************************************************************************************
 * DEFINES AND TYPES
 *******************************************************************************************/

// #define COLL_STAT

// GLOBAL DEFINES

#define UINT128 unsigned __int128
// UINT32 and UINT64 defined in utils.h

#define MAX_MEM        131072  // 128k in bytes
#define GHR_SIZE       128     // bounded by UINT128, need custom impl for larger

// TAGE DEFINES

#define N_TABLES       8       // number of tables (min 2, max 8)
#define ALPHA          2       // base for geometric series
#define L1             2       // initial value for geometric series

#define BCTR_SIZE      2       // base prediction counter size
#define GCTR_SIZE      3       // global prediction counter size
#define TAG_SIZE       8       // tag size
#define U_SIZE         2       // useful counter size

#define BTI_SIZE       11      // size of base table index
#define GTI_SIZE       10      // size of global table index
#define BT_SIZE        2048    // 2^BTI_SIZE, number of base table entries
#define GT_SIZE        1024    // 2^GTI_SIZE, number of global table entires

#define UAON_SIZE      4       // use_alt_on_na size
#define TIME_TO_RESET  131072  // branches before u reset

#define ALLOC_CHANCE   3       // chance to alloc entry in table, eg. 4 => 3/4

struct base_entry {
  UINT32 ctr;
};

struct global_entry {
  UINT32 ctr;
  UINT32 tag;
  UINT32 u;
};

// STATISTICAL CORRECTOR (GEHL) DEFINES

#define N_SC_TABLES    5

#define SCTR_SIZE      6

#define SCI_SIZE       10
#define SC_SIZE        1024

#define SC_THRESH      5
#define TCTR_SIZE      7

struct sc_entry {
  UINT32 ctr;
};

/*******************************************************************************************
 * STATISTIC COLLECTION VARIABLES
 *******************************************************************************************/

int num_wrong_pred[N_TABLES];
int num_times_used[N_TABLES];
int num_times_useful[N_TABLES];

/*******************************************************************************************
 * GLOBAL VARIABLES
 *******************************************************************************************/

// GLOBAL

default_random_engine generator;
uniform_int_distribution<int> distribution(1, ALLOC_CHANCE);

// GHR max 128 unfortunately, can be extended with hacks
UINT128 ghr;

// TAGE

// Counter to bias prediction away from using newly initialized predictions
UINT32 use_alt_on_na;

// Prediction and alternate prediction
int pred;
UINT32 pred_table;
UINT32 pred_index;
int altpred;
UINT32 altpred_table;
UINT32 altpred_index;

// Useful reset counter
UINT32 n_branches;
int u_reset_bit;

// TAGE tables
// T0
base_entry base_table[BT_SIZE];
// T1 - TN-1, NOTE: global_table[0] unused
global_entry global_table[N_TABLES][GT_SIZE];

// SC (GEHL)

// GEHL decision making counter
int sc_sum;

// Tage decision tracker
UINT32 prediction_ctr;

// Update counters
UINT32 sc_thresh;
UINT32 tctr;

// GEHL tables
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

// calculate maximum ghr used
inline UINT32 get_max_ghr(){
  return get_l(N_TABLES-1);
}

// calculate memory usage
UINT32 get_mem_usage(){
  UINT32 bt_usage = BT_SIZE * BCTR_SIZE;
  UINT32 gt_usage = (N_TABLES - 1) * GT_SIZE * (GCTR_SIZE + TAG_SIZE + U_SIZE);
  UINT32 sc_usage = N_SC_TABLES * SC_SIZE * SCTR_SIZE;
  UINT32 misc_usage = 1024; // hw implementation safety factor include ghr register, etc.
  return bt_usage + gt_usage + sc_usage + misc_usage;
}

// print resource usage and warnings
void print_usage(){
  UINT32 max_ghr = get_max_ghr();
  if(max_ghr > GHR_SIZE){
    cout << "WARNING: Max GHR used (" << max_ghr << ") ";
    cout << "exceeds max GHR length (" << GHR_SIZE << ")" << endl;
  }
  else{
    cout << "Maximum GHR length used: " << max_ghr << endl;
  }
  UINT32 mem_use = get_mem_usage();
  if(mem_use > MAX_MEM){
    cout << "WARNING: Mem usage (" << mem_use << ") ";
    cout << "exceeds max (" << MAX_MEM << ")" << endl;
  }
  else{
    cout << "Predictor size: " << mem_use << endl;
  }
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
  UINT32 pc_folded = fold((UINT128)pc, pc_size, index_size);
  UINT32 ghr_folded = fold(ghr, ghr_size, index_size);
  return pc_folded ^ ghr_folded;
}

// get tag based on Michaud PPM-like predictor paper
UINT32 get_tag(UINT32 pc, int pc_size, UINT128 ghr, int ghr_size, int index_size){
  UINT32 pc_folded = fold((UINT128)pc, pc_size, index_size); // index_size bits
  UINT32 ghr_folded = fold(ghr, ghr_size, index_size);       // index_size bits
  UINT32 ghr_folded_mod = fold(ghr, ghr_size, index_size-1); // index_size-1 bits
  return pc_folded ^ ghr_folded ^ (ghr_folded_mod << 1);
}

// check if counter value is weak
int low_confidence(UINT32 ctr, int size){
  return ctr == get_weak_not_taken(size) || ctr == get_weak_taken(size);
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
#ifdef COLL_STAT
  // Statistics
  for(int i = 0; i < N_TABLES; i++){
    num_wrong_pred[i] = 0;
    num_times_used[i] = 0;
    num_times_useful[i] = 0;
  }
#endif
  print_usage();
  // GLOBAL
  ghr = 0; // init to all not taken
  // TAGE
  use_alt_on_na = get_weak_taken(UAON_SIZE); // init to weak used
  n_branches = 0; // init u reset counter
  u_reset_bit = U_SIZE - 1; // u_reset_bit goes from U_SIZE-1 to 0
  for(int i = 0; i < BT_SIZE; i++){
    base_table[i].ctr = get_weak_taken(BCTR_SIZE); // init base table entries to weak not taken
  }
  for(int i = 1; i < N_TABLES; i++){
    for(int j = 0; j < GT_SIZE; j++){ // global table entries initialized during update
      global_table[i][j].ctr = 0;
      global_table[i][j].tag = 0;
      global_table[i][j].u   = 0;
    }
  }
  // SC
  sc_thresh = SC_THRESH; // init threshold
  tctr = get_weak_taken(TCTR_SIZE);
  for(int i = 0; i < N_SC_TABLES; i++){
    for(int j = 0; j < SC_SIZE; j++){
      sc_table[i][j].ctr = get_weak_taken(SCTR_SIZE);
    }
  }
}

bool GetPrediction_openend(UINT32 PC) {
  // TAGE
  // Make prediction
  int prediction;
  int prediction_table;
  int pred_made = 0;
  int altpred_made = 0;
  // Find entry with matching tag from longest history table for pred and altpred
  for(int i = N_TABLES-1; i > 0; i--){
    UINT32 index = get_index(PC, sizeof(PC)*8, ghr, get_l(i), GTI_SIZE);
    UINT32 tag = get_tag(PC, sizeof(PC)*8, ghr, get_l(i), TAG_SIZE);
    if(global_table[i][index].tag == tag){
      // if pred already found, then log as altpred
      if(pred_made){
        altpred_made = 1;
        altpred = get_msb(global_table[i][index].ctr, GCTR_SIZE);
        altpred_table = i;
        altpred_index = index;
        // use altpred when pred is fresh and UAON biased to altpred
        if(global_table[pred_table][pred_index].u == 0 &&
           low_confidence(global_table[pred_table][pred_index].ctr, GCTR_SIZE) &&
           get_msb(use_alt_on_na, UAON_SIZE)){
          prediction = altpred;
          prediction_table = altpred_table;
          prediction_ctr = global_table[i][index].ctr;
        }
        break; // exit loop
      }
      // log pred
      pred_made = 1;
      pred = get_msb(global_table[i][index].ctr, GCTR_SIZE);
      pred_table = i;
      pred_index = index;
      prediction = pred;
      prediction_table = pred_table;
      prediction_ctr = global_table[i][index].ctr;
      continue; // continue to find alpred
    }
  }
  // If no pred match found in global tables, use base bimodal table
  if(!pred_made){
    pred_made = 1;
    pred = get_msb(base_table[PC & get_mask(BTI_SIZE)].ctr, BCTR_SIZE);
    pred_table = 0;
    pred_index = PC & get_mask(BTI_SIZE);
    prediction = pred;
    prediction_table = pred_table;
    prediction_ctr = base_table[PC & get_mask(BTI_SIZE)].ctr;
  }
  // If no altpred match found in global tables, use base bimodal table
  if(!altpred_made){
    altpred_made = 1;
    altpred = get_msb(base_table[PC & get_mask(BTI_SIZE)].ctr, BCTR_SIZE);
    altpred_table = 0;
    altpred_index = PC & get_mask(BTI_SIZE);
    // use altpred when pred is fresh and UAON biased to altpred
    if(pred_table != 0 && // lazy eval
       global_table[pred_table][pred_index].u == 0 &&
       low_confidence(global_table[pred_table][pred_index].ctr, GCTR_SIZE) &&
       get_msb(use_alt_on_na, UAON_SIZE)){
      prediction = altpred;
      prediction_table = altpred_table;
      prediction_ctr = base_table[PC & get_mask(BTI_SIZE)].ctr;
    }
  }
  // SC
  // Double check Tage prediction with GEHL
  // find (centered) avg of GEHL entries
  sc_sum = 0;
  for(int i = 0; i < N_SC_TABLES; i++){
    UINT32 sc_index = get_tag(PC, sizeof(PC)*8, ghr, get_l(i+1), SCI_SIZE) ^ prediction_ctr;
    sc_sum += ((sc_table[i][sc_index].ctr - get_weak_taken(SCTR_SIZE)) << 1) + 1;
  }
  // add (centered and scaled) Tage prediction
  int sc_val;
  if(prediction_table == 0){
    sc_val = sc_sum + (((prediction_ctr - get_weak_taken(BCTR_SIZE)) << 1) + 1) * (N_SC_TABLES);
  }
  else{
    sc_val = sc_sum + (((prediction_ctr - get_weak_taken(GCTR_SIZE)) << 1) + 1) * (N_SC_TABLES);
  }
  // return sign as prediction
  prediction = sc_val >= 0;
  return prediction;
}

void UpdatePredictor_openend(UINT32 PC, bool resolveDir, bool predDir, UINT32 branchTarget) {
#ifdef COLL_STAT
  // Statistics
  num_times_used[pred_table]++;
  if(resolveDir != pred){
    num_wrong_pred[pred_table]++;
  }
  if(pred_table != 0){
    if(global_table[pred_table][pred_index].u == get_mask(U_SIZE)){
      num_times_useful[pred_table]++;
    }
  }
#endif
  // TAGE
  // The order of the following update steps can be changed
  // Update base table
  base_table[PC & get_mask(BTI_SIZE)].ctr =
    update_ctr(resolveDir == TAKEN, base_table[PC & get_mask(BTI_SIZE)].ctr, BCTR_SIZE);
  // Update use_alt_on_na
  if(pred_table != 0 &&
     pred != altpred &&
     global_table[pred_table][pred_index].u == 0 &&
     low_confidence(global_table[pred_table][pred_index].ctr, GCTR_SIZE)){
    use_alt_on_na = update_ctr(altpred == resolveDir, use_alt_on_na, UAON_SIZE);
  }
  // Update useful counter
  if(pred_table != 0 && pred != altpred){
    global_table[pred_table][pred_index].u =
      update_ctr(pred == resolveDir, global_table[pred_table][pred_index].u, U_SIZE);
  }
  // "Gracefully" reset u
  // done after update, can also be changed to before update
  // change to cycle through n bits or any other policy
  n_branches++;
  if(n_branches == TIME_TO_RESET){
    for(int i = 1; i < N_TABLES; i++){
      for(int j = 0; j < GT_SIZE; j++){
          global_table[i][j].u &= ~(1 << u_reset_bit); // reset bit with index u_reset_bit
      }
    }
    // reset counters after u reset
    n_branches = 0;
    u_reset_bit--;
    if(u_reset_bit < 0){
      u_reset_bit = U_SIZE - 1;
    }
  }
  // Update prediction counters
  if(pred_table != 0){
    global_table[pred_table][pred_index].ctr =
      update_ctr(resolveDir == TAKEN, global_table[pred_table][pred_index].ctr, GCTR_SIZE);
  }
  // Allocate new table entries
  // when pred was wrong and did not come from longest history table
  if(pred != resolveDir && pred_table < N_TABLES - 1){
    // find first free index of tables with longer history
    int num_free_tables = 0;
    int free_table_index[N_TABLES];
    int free_entry_index[N_TABLES];
    for(int i = pred_table + 1; i < N_TABLES; i++){
      UINT32 index = get_index(PC, sizeof(PC)*8, ghr, get_l(i), GTI_SIZE);
      if(global_table[i][index].u == 0){
        free_table_index[num_free_tables] = i;
        free_entry_index[num_free_tables] = index;
        num_free_tables++;
      }
    }
    // if no free entry found, decrement all u
    if(num_free_tables == 0){
      for(int i = pred_table + 1; i < N_TABLES; i++){
        UINT32 index = get_index(PC, sizeof(PC)*8, ghr, get_l(i), GTI_SIZE);
        global_table[i][index].u = sat_ctr_dec(global_table[i][index].u, U_SIZE);
      }
    }
    // else allocate new entry
    else{
      for(int i = 0; i < num_free_tables; i++){
        // pick table with (ALLOC_CHANCE-1)/ALLOC_CHANCE chance
        if(i < num_free_tables - 1){ // not last table
          if(distribution(generator) == 1){
            continue;
          }
        }
        // if allocated with 2/3 chance or last table, initialize entry
        int table = free_table_index[i];
        int entry = free_entry_index[i];
        global_table[table][entry].ctr = get_weak_taken(GCTR_SIZE);
        global_table[table][entry].tag = get_tag(PC, sizeof(PC)*8, ghr, get_l(table), TAG_SIZE);
        global_table[table][entry].u   = 0;
        break;
      }
    }
  }
  // SC
  // update table entires
  if(predDir != resolveDir || (UINT32)abs(sc_sum) < sc_thresh){
    for(int i = 0; i < N_SC_TABLES; i++){
      int sc_index = get_tag(PC, sizeof(PC)*8, ghr, get_l(i+1), SCI_SIZE) ^ prediction_ctr;
      sc_table[i][sc_index].ctr =
        update_ctr(resolveDir == TAKEN, sc_table[i][sc_index].ctr, SCTR_SIZE);
    }
  }
  // update threshold
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
#ifdef COLL_STAT
  cout << endl;
  cout << "Print predictor statistics here" << endl;
  for(int i = 0; i < N_TABLES; i++){
    cout << "Table " << i << endl;
    cout << "Number of wrong predictions " << num_wrong_pred[i] << endl;
    cout << "Number of times used " << num_times_used[i] << endl;
    cout << "Number of times used and useful " << num_times_useful[i] << endl;
    // cout << "Numbers of times full " << num_times_full[i] << endl;
  }
  cout << endl;
#else
  cout << endl;
  cout << "Statistcs turned off, define COLL_STAT to collect statistics" << endl;
  cout << endl;
#endif
}
