#include "predictor.h"
#include <random>
#include <cstdlib>
#include <cmath>
#include <iostream>
using namespace std;

//general utility classes////////////////////////////////////
template <int WIDTH, int NUM_ENTRIES> class SAT_COUNTER {
public:
    int val[NUM_ENTRIES];
    void init(int init_val) {
        for (int i = 0; i < NUM_ENTRIES; i++) {
            val[i] = init_val;
        }
    }
    int operator [](int i) {
        return val[i];
    }
    void update(int index, bool isTAKEN) {
        if (isTAKEN && val[index] != ctrmax) {
            val[index]++;
        } else if (!isTAKEN && val[index] != ctrmin) {
            val[index]--;
        }
    }
private:
    int ctrmin = -(1 << (WIDTH - 1));
    int ctrmax = -ctrmin - 1;
};

template <int L> class BHT {
public:
    UINT64 val = 0; //initialized as 0
    void update(bool isTAKEN) {
        val = ((val << 1) | isTAKEN) & BHT_MASK;
    }
private:
    const UINT64 BHT_MASK = (1 << L) - 1;
};
/////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////
// 2bitsat
/////////////////////////////////////////////////////////////
static SAT_COUNTER<2,4096> sat_counter_2bit;

void InitPredictor_2bitsat() {
    sat_counter_2bit.init(-1); //weak not-taken
}

bool GetPrediction_2bitsat(UINT32 PC) {
    return sat_counter_2bit[PC & 0xfff] < 0 ? NOT_TAKEN : TAKEN;
}

void UpdatePredictor_2bitsat(UINT32 PC, bool resolveDir, bool predDir, UINT32 branchTarget) {
    sat_counter_2bit.update(PC & 0xfff, resolveDir);
}

/////////////////////////////////////////////////////////////
// 2level
/////////////////////////////////////////////////////////////

static BHT<6> BHT_2level[512]; //6 history bits
static SAT_COUNTER<2,512> sat_counter_2level;

void InitPredictor_2level() {
    sat_counter_2level.init(-1); //weak not-taken
}

bool GetPrediction_2level(UINT32 PC) {
    return sat_counter_2level[((BHT_2level[(PC >> 3) & 0x1ff].val << 3) | (PC & 0x7))] < 0 ? NOT_TAKEN : TAKEN;
}

void UpdatePredictor_2level(UINT32 PC, bool resolveDir, bool predDir, UINT32 branchTarget) {
    sat_counter_2level.update(((BHT_2level[(PC >> 3) & 0x1ff].val << 3) | (PC & 0x7)), resolveDir);
    BHT_2level[(PC >> 3) & 0x1ff].update(resolveDir);
}

/////////////////////////////////////////////////////////////
// openend
/////////////////////////////////////////////////////////////
/*******************************************************************************************
 * pre-defined values and utility functions, directly took from Michael Zhao
 *******************************************************************************************/
#define UINT128 unsigned __int128

#define N_TABLES       8       // number of tables (min 2, max 8)
#define ALPHA          2       // base for geometric series
#define L1             2       // initial value for geometric series

#define BCTR_WIDTH      3       // base prediction counter size
#define GCTR_WIDTH      3       // global prediction counter size
#define TAG_WIDTH       10      // tag size

#define BT_SIZE        4096    // 2^BTI_SIZE, number of base table entries
#define GT_SIZE        1024    // 2^GTI_SIZE, number of global table entires

// fold values based on Michaud PPM-like paper
UINT32 fold(UINT128 val, int size, int size_out){
    int num_iter = (size-1) / size_out + 1;
    UINT32 val_mask = (1 << size_out) - 1;
    UINT32 val_temp = 0;
    for(int i = 0; i < num_iter; i++){
        val_temp ^= (UINT32)(val >> i*size_out);
    }
    return val_temp & val_mask;
}

// get index based on Michaud PPM-like predictor paper
UINT32 get_index(UINT32 pc, UINT128 ghr, int ghr_size, int index_size){
    int pc_size = sizeof(pc)*8;
    UINT32 pc_folded = fold((UINT128)pc, pc_size, index_size);
    UINT32 ghr_folded = fold(ghr, ghr_size, index_size);
    return pc_folded ^ ghr_folded;
}

// get tag based on Michaud PPM-like predictor paper
UINT32 get_tag(UINT32 pc, UINT128 ghr, int ghr_size, int index_size){
    int pc_size = sizeof(pc)*8;
    UINT32 pc_folded = fold((UINT128)pc, pc_size, index_size); // index_size bits
    UINT32 ghr_folded = fold(ghr, ghr_size, index_size);             // index_size bits
    UINT32 ghr_folded_mod = fold(ghr, ghr_size, index_size-1); // index_size-1 bits
    return pc_folded ^ ghr_folded ^ (ghr_folded_mod << 1);
}

/*******************************************************************************************
 * BATAGE data structures
 *******************************************************************************************/
//BATAGE confidence level
#define HIGH_CONF   0
#define MED_CONF    1
#define LOW_CONF    2
#define INV_CONF    3

int get_bitwidth(int num_entries) {
//get index width from total number of entries
    int n = 0;
    while (num_entries >>= 1) ++n;
    return n;
}

class PRED_RESULT {
public:
    bool result;
    int confidence;
    bool isHit;
};

template <int WIDTH, int NUM_ENTRIES> class BASE_TABLE {
public:
    int val[NUM_ENTRIES];
    bool last_predict_result;
    int last_predict_confidence;
    void init(int init_val) {
        for (int i = 0; i < NUM_ENTRIES; i++) {
            val[i] = init_val;
        }
    //for portability, do member variable initialization here
        index_mask = (1 << get_bitwidth(NUM_ENTRIES)) - 1;
        ctrmin = -(1 << (WIDTH - 1));
        ctrmax = -ctrmin - 1;
    }
    int operator [](int i) {
        return val[i];
    }
    void update(UINT32 PC, bool isTAKEN) {
        int index = PC & index_mask;
        if (isTAKEN && val[index] != ctrmax) {
            val[index]++;
        } else if (!isTAKEN && val[index] != ctrmin) {
            val[index]--;
        }
    }
    PRED_RESULT predict(UINT32 PC) {
        PRED_RESULT prediction;
        int index = PC & index_mask;
        prediction.result = val[index] < 0 ? NOT_TAKEN : TAKEN;    
        prediction.confidence = cal_confidence(val[index]);
        prediction.isHit = true;
        return prediction;
    }
private:
    UINT32 index_mask;
    int cal_confidence(int value) {
        int tmp = value*2+1 > 0 ? 4 - value*2 : 6 + value*2;
        return tmp > 0 ? tmp >> 1 : 0;
    }
    int ctrmin;
    int ctrmax;
};


template <int WIDTH, int NUM_ENTRIES, int TAG_WID> class GHT {
public:
    UINT32 tag[NUM_ENTRIES];
    int n0[NUM_ENTRIES];
    int n1[NUM_ENTRIES];
    bool last_predict_result;
    bool last_predict_hit;
    int last_predict_confidence;
    void init() {
        for (int i = 0; i < NUM_ENTRIES; i++) {
            n0[i] = 0;
            n1[i] = 0;
            tag[i] = 0;
        }
        index_mask = (1 << get_bitwidth(NUM_ENTRIES)) - 1;
        dual_ctr_max = (1 << WIDTH) - 1;
    }
    void update(UINT32 PC, UINT128 ghr, int his_len, bool isTAKEN) {
        UINT32 index = get_index(PC, ghr, his_len, get_bitwidth(NUM_ENTRIES));
        UINT32 tag_from_PC = get_tag(PC, ghr, his_len, TAG_WID);
        if (isTAKEN) {
            if (n1[index] < dual_ctr_max) n1[index]++;
            else if (n0[index] > 0) n0[index]--;
        } else {
            if (n0[index] < dual_ctr_max) n0[index]++;
            else if (n1[index] > 0) n1[index]--;
        }
        tag[index] = tag_from_PC; // always update?
    }
    void decay(UINT32 PC, UINT128 ghr, int his_len) {
        UINT32 index = get_index(PC, ghr, his_len, get_bitwidth(NUM_ENTRIES));
        if (n1[index] > n0[index]) n1[index]--; // leaves predictor at low conf
        if (n0[index] > n1[index]) n0[index]--;
    } // does not check tags which makes sense
    PRED_RESULT predict(UINT32 PC, UINT128 ghr, int his_len) {
        PRED_RESULT prediction;
        UINT32 index = get_index(PC, ghr, his_len, get_bitwidth(NUM_ENTRIES));
        UINT32 tag_from_PC = get_tag(PC, ghr, his_len, TAG_WID);
        if (tag_from_PC == tag[index]) { //tag hit
            prediction.result = n0[index] >= n1[index] ? TAKEN : NOT_TAKEN;
            prediction.confidence = cal_confidence(n0[index], n1[index]);
            prediction.isHit = true;
        } else { //tag miss
            prediction.result = TAKEN;
            prediction.confidence = INV_CONF;
            prediction.isHit = false;
        } 
        return prediction;
    }
private:
    int cal_confidence(int t_cnt, int n_cnt) {
        int medium = (t_cnt == (2*n_cnt + 1)) || (n_cnt == (2*t_cnt + 1)) ? 1 : 0;
        int low = (n_cnt < (2*t_cnt + 1)) && (t_cnt < (2*n_cnt + 1)) ? 1 : 0;
        return 2*low+medium;
    }
    UINT32 index_mask;
    int dual_ctr_max;
};

default_random_engine generator;
uniform_int_distribution<int> distribution(1, 4); //PDEC = 1/4

static BASE_TABLE<BCTR_WIDTH, BT_SIZE> base_table; 
static GHT<GCTR_WIDTH, GT_SIZE, TAG_WIDTH> global_table[N_TABLES-1];
static UINT128 ghr;
static int predict_table_id;

void InitPredictor_openend() {
    base_table.init(-1); //weak not-taken
    for (int i = 0; i < N_TABLES-1; i++) global_table[i].init();
    ghr = 0;
}

bool GetPrediction_openend(UINT32 PC) {
    PRED_RESULT best_prediction, tmp_prediction;
    best_prediction.confidence = INV_CONF;
    // iterate through tables starting with longest history
    for (int i = N_TABLES - 2; i >= 0; i--){
        int his_len = L1 << i;
        tmp_prediction = global_table[i].predict(PC, ghr, his_len);
        global_table[i].last_predict_result = tmp_prediction.result;
        global_table[i].last_predict_hit = tmp_prediction.isHit;
        global_table[i].last_predict_confidence = tmp_prediction.confidence;
        if (tmp_prediction.confidence < best_prediction.confidence) { //better confidence 
            best_prediction = tmp_prediction;
            predict_table_id = i + 1;
        }
    }
    // doing base prediction last guarantees longer history in case of equal confidence
    PRED_RESULT base_prediction = base_table.predict(PC);
    base_table.last_predict_result = base_prediction.result;
    base_table.last_predict_confidence = base_prediction.confidence;
    if (base_prediction.confidence < best_prediction.confidence) {
        best_prediction = base_prediction;
        predict_table_id = 0;
    }
    // return prediction with highest confidence and longest history
    return best_prediction.result;
}

void UpdatePredictor_openend(UINT32 PC, bool resolveDir, bool predDir, UINT32 branchTarget) {
    bool result_array[N_TABLES];
    bool hit_array[N_TABLES];
    int confidence_array[N_TABLES];
    int i;
    // initialize base prediction
    result_array[0] = base_table.last_predict_result;
    hit_array[0] = true;
    confidence_array[0] = base_table.last_predict_confidence;
    // initialize global table predictions
    for (i = 1; i < N_TABLES; i++) {
        result_array[i] = global_table[i-1].last_predict_result;
        hit_array[i] = global_table[i-1].last_predict_hit;
        confidence_array[i] = global_table[i-1].last_predict_confidence;
    }
    // update tables Lh > Lp and find Ln
    int findLn = 0;
    int altpred_table_id = 0; // defaults to base table
    for (i = N_TABLES - 1; i >= 1; i--) {
        int ght_index = i - 1;
        if (hit_array[i]) {
            int his_len = L1 << ght_index;
            if (i > predict_table_id) {
                global_table[ght_index].update(PC, ghr, his_len, resolveDir); // no error checking in update
            } else if (i == predict_table_id) {
                // start looking for Ln
                findLn = 1;
                continue;
            }
            if(findLn){
                altpred_table_id = i;
                break;
            }
        }
    }
    //update Lp and Ln
    int predict_index = predict_table_id - 1;
    int altpred_index = altpred_table_id - 1;
    int predict_his_len = L1 << predict_index;
    int altpred_his_len = L1 << altpred_index;
    // Lp == L0
    if (predict_table_id == 0) base_table.update(PC, resolveDir);
    else { // Lp > 0
        if (confidence_array[predict_table_id] != HIGH_CONF || confidence_array[altpred_table_id] != HIGH_CONF || result_array[altpred_table_id] != resolveDir){
            global_table[predict_index].update(PC, ghr, predict_his_len, resolveDir);
        }
        if (confidence_array[predict_table_id] == HIGH_CONF && confidence_array[altpred_table_id] == HIGH_CONF && result_array[altpred_table_id] == resolveDir){
            global_table[predict_index].decay(PC, ghr, predict_his_len);
        }
        if (confidence_array[predict_table_id] != HIGH_CONF) {
            // update Ln
            if (altpred_table_id == 0) {
                base_table.update(PC, resolveDir);
            } else {
                global_table[altpred_index].update(PC, ghr, altpred_his_len, resolveDir);
            }
        }
    }

    // allocate new table entries
    int longest_hitting_entry = 0;
    if (predDir != resolveDir) { //mispredict
        for (i = N_TABLES - 1; i >= 0; i--) {
            if (hit_array[i]) {
                longest_hitting_entry = i;
                break;
            }
        }
        int r = longest_hitting_entry + 1;
        if (longest_hitting_entry != N_TABLES - 1) {
            while (r < N_TABLES) {
                int his_len = L1 << (r-1);
                if (global_table[r-1].last_predict_confidence != HIGH_CONF) {
                    global_table[r-1].update(PC, ghr, his_len, resolveDir);
                    break;
                }
                r++;
            }
        }
        for (i = longest_hitting_entry + 1; i < r; i++) {
            int his_len = L1 << (i-1);
            if (global_table[i-1].last_predict_confidence == HIGH_CONF && distribution(generator) == 1) //PDEC = 1/4
                global_table[i-1].decay(PC, ghr, his_len);
        }
    }

    //update global history register
    ghr = (ghr << 1) | resolveDir;
}

void TermPredictor_openend(){
    ;
}