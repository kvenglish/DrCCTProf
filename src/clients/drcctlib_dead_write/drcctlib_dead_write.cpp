/*
 *  Copyright (c) 2020 Xuhpclab. All rights reserved.
 *  Licensed under the MIT License.
 *  See LICENSE file for more information.
 */

#include <cstddef>

#include "dr_api.h"
#include "drmgr.h"
#include "drreg.h"
#include "drutil.h"
#include "drcctlib.h"
#include <stdio.h>
#include <iostream>
#include <map>
#include <fstream>
#include <sstream>
#include <iomanip>

using namespace std;

#define DRCCTLIB_PRINTF(format, args...) \
    DRCCTLIB_PRINTF_TEMPLATE("dead_write", format, ##args)
#define DRCCTLIB_EXIT_PROCESS(format, args...) \
    DRCCTLIB_CLIENT_EXIT_PROCESS_TEMPLATE("dead_write", format, ##args)

static int tls_idx;

enum {
    INSTRACE_TLS_OFFS_BUF_PTR,
    INSTRACE_TLS_COUNT, /* total number of TLS slots allocated */
};
static reg_id_t tls_seg;
static uint tls_offs;
#define TLS_SLOT(tls_base, enum_val) (void **)((byte *)(tls_base) + tls_offs + (enum_val))
#define BUF_PTR(tls_base, type, offs) *(type **)TLS_SLOT(tls_base, offs)
#define MINSERT instrlist_meta_preinsert
#ifdef ARM_CCTLIB
#    define OPND_CREATE_CCT_INT OPND_CREATE_INT
#else
#    define OPND_CREATE_CCT_INT OPND_CREATE_INT32
#endif

typedef struct _mem_ref_t {
    app_pc addr;
    bool write_state;
} mem_ref_t;

typedef struct _per_thread_t {
    mem_ref_t *cur_buf_list;
    void *cur_buf;
} per_thread_t;

typedef struct access_state_t {
    context_handle_t ctxt_hndl;
    bool write_state;

} access_state_t;

//formating
string divider = "==============================================================";
string writeDiv = "*************************************************************";
string formatGuide = "FORMAT GUIDE\n==================\nDead Store Trace\n***********************\nKilling Store Trace\n====================";


// Global Maps
map<app_pc, access_state_t> memAccessRec;   // <memory address, write state>
map<reg_id_t, access_state_t> regAccessRec; //<register_id, <context_id, write state>>
map<uint64, uint64> deadMemRecord; // <(dead context, killing context), frequency>
map<uint64, uint64> deadRegRecord; // <(dead context, killing context), frequency>

uint64 totMemWrite;
uint64 totRegWrite;

#define TLS_MEM_REF_BUFF_SIZE 100

// Pack 2 32 bit integers into a 64 bit integer
uint64
PackInts(uint32_t high, uint32_t low)
{
    return ((uint64)high) << 32 | low;
}

// Unpack 2 32 bit integers from a 64 bit integer, return as a pair
pair<uint32_t, uint32_t>
UnpackInts(uint64 packed)
{
    uint32_t low = (uint32_t)packed;
    uint32_t high = packed >> 32;
    return pair<uint32_t, uint32_t>(high, low);
}

void
RecordDeadWrite(context_handle_t dead, context_handle_t killing, bool isRegister)
{
    uint64 handles = PackInts(dead, killing);
    // if dead write occured in register, store in register record
    if (isRegister) {
        if (deadRegRecord[handles]) {
            deadRegRecord[handles]++; // increment frequency if exists
        }else {
            deadRegRecord[handles] = 1; // adds if doesn't exist
        }
    }
    // otherwise store in mem record
    else {
        if (deadMemRecord[handles]) {
            deadMemRecord[handles]++;
        } else {
            deadMemRecord[handles] = 1;
        }
    }
}

// Proccess instrumented memory and store information in mem_access_record. If dead write,
// store in dead_mem_record
void
ProcessMemAccess(void *drcontext, context_handle_t cur_ctxt_hndl, mem_ref_t *ref)
{
    if(ref->write_state) totMemWrite++;
    // check if memory location exists in map
    if (memAccessRec.find(ref->addr) != memAccessRec.end()) {
        // checks if current context is a read, or if previous context was a read
        // if so, don't care about previous state, just update
        if (!ref->write_state || !memAccessRec[ref->addr].write_state) {
            memAccessRec[ref->addr].write_state =
                ref->write_state; // write new state (1=write, 0=read)
            memAccessRec[ref->addr].ctxt_hndl = cur_ctxt_hndl; // record new context
                                                               // handle
        }
        // else, since previous state is write and new state is write, record dead write
        // and update state
        else {
            RecordDeadWrite(memAccessRec[ref->addr].ctxt_hndl, cur_ctxt_hndl, 0);
            memAccessRec[ref->addr].ctxt_hndl = cur_ctxt_hndl;
            memAccessRec[ref->addr].write_state = ref->write_state;
        }
    }
    // else if doesn't exist, add it
    else {
        memAccessRec[ref->addr].write_state = ref->write_state;
        memAccessRec[ref->addr].ctxt_hndl = cur_ctxt_hndl;
    }
}


// Process instrumented registers and store information in reg_access_record. If dead
// write, store in dead_reg_record
void
InsertRegCleanCall(int32_t slot, reg_id_t reg_id, int32_t write_state)
{
    if(write_state) totRegWrite++;
    void *drcontext = dr_get_current_drcontext();
    context_handle_t cur_ctxt_hndl = drcctlib_get_context_handle(drcontext, slot);
    // check if memory location exists in map
    if (regAccessRec.find(reg_id) != regAccessRec.end()) {
        // checks if current context is a read, or if previous context was a read
        // if so, don't care about previous state, just update
        if (!write_state || !regAccessRec[reg_id].write_state) {
            regAccessRec[reg_id].write_state = write_state; // write new state (1=write, 0=read)
            regAccessRec[reg_id].ctxt_hndl = cur_ctxt_hndl; // record new context
            // handle
        }
            // else, since previous state is write and new state is write, record dead write
            // and update state
        else {
            RecordDeadWrite(regAccessRec[reg_id].ctxt_hndl, cur_ctxt_hndl, 1);
            regAccessRec[reg_id].ctxt_hndl = cur_ctxt_hndl;
            regAccessRec[reg_id].write_state = write_state;
        }
    }
        // else if doesn't exist, add it
    else {
        regAccessRec[reg_id].write_state = write_state;
        regAccessRec[reg_id].ctxt_hndl = cur_ctxt_hndl;
    }
}

// dr clean call
void
InsertCleancall(int32_t slot, int32_t num)
{
    void *drcontext = dr_get_current_drcontext();
    per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    context_handle_t cur_ctxt_hndl = drcctlib_get_context_handle(drcontext, slot);
    for (int i = 0; i < num; i++) {
        if (pt->cur_buf_list[i].addr != 0) {
            ProcessMemAccess(drcontext, cur_ctxt_hndl, &pt->cur_buf_list[i]);
        }
    }
    BUF_PTR(pt->cur_buf, mem_ref_t, INSTRACE_TLS_OFFS_BUF_PTR) = pt->cur_buf_list;
}

// insert
static void
InstrumentMem(void *drcontext, instrlist_t *ilist, instr_t *where, opnd_t ref, int write)
{
    /* We need two scratch registers */
    reg_id_t reg_mem_ref_ptr, free_reg;
    if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_mem_ref_ptr) !=
            DRREG_SUCCESS ||
        drreg_reserve_register(drcontext, ilist, where, NULL, &free_reg) !=
            DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("InstrumentMem drreg_reserve_register != DRREG_SUCCESS");
    }
    if (!drutil_insert_get_mem_addr(drcontext, ilist, where, ref, free_reg,
                                    reg_mem_ref_ptr)) {
        MINSERT(ilist, where,
                XINST_CREATE_load_int(drcontext, opnd_create_reg(free_reg),
                                      OPND_CREATE_CCT_INT(0)));
    }
    dr_insert_read_raw_tls(drcontext, ilist, where, tls_seg,
                           tls_offs + INSTRACE_TLS_OFFS_BUF_PTR, reg_mem_ref_ptr);
    // store mem_ref_t->addr
    MINSERT(ilist, where,
            XINST_CREATE_store(
                drcontext, OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, addr)),
                opnd_create_reg(free_reg)));

    // store mem_ref_t->size
#ifdef ARM_CCTLIB
    MINSERT(ilist, where,
            XINST_CREATE_load_int(
                drcontext, opnd_create_reg(free_reg),
                OPND_CREATE_CCT_INT(drutil_opnd_mem_size_in_bytes(ref, where))));
    MINSERT(ilist, where,
            XINST_CREATE_store(
                drcontext,
                OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, write_state)),
                opnd_create_reg(write)));
#else
    // insert memory access type
    MINSERT(ilist, where,
            XINST_CREATE_store(
                drcontext,
                OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, write_state)),
                OPND_CREATE_CCT_INT(write)));
#endif

#ifdef ARM_CCTLIB
    MINSERT(ilist, where,
            XINST_CREATE_load_int(drcontext, opnd_create_reg(free_reg),
                                  OPND_CREATE_CCT_INT(sizeof(mem_ref_t))));
    MINSERT(ilist, where,
            XINST_CREATE_add(drcontext, opnd_create_reg(reg_mem_ref_ptr),
                             opnd_create_reg(free_reg)));
#else
    MINSERT(ilist, where,
            XINST_CREATE_add(drcontext, opnd_create_reg(reg_mem_ref_ptr),
                             OPND_CREATE_CCT_INT(sizeof(mem_ref_t))));
#endif
    dr_insert_write_raw_tls(drcontext, ilist, where, tls_seg,
                            tls_offs + INSTRACE_TLS_OFFS_BUF_PTR, reg_mem_ref_ptr);
    /* Restore scratch registers */
    if (drreg_unreserve_register(drcontext, ilist, where, reg_mem_ref_ptr) !=
            DRREG_SUCCESS ||
        drreg_unreserve_register(drcontext, ilist, where, free_reg) != DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("InstrumentMem drreg_unreserve_register != DRREG_SUCCESS");
    }
}

// analysis
void
InstrumentInsCallback(void *drcontext, instr_instrument_msg_t *instrument_msg)
{

    instrlist_t *bb = instrument_msg->bb;
    instr_t *instr = instrument_msg->instr;
    int32_t slot = instrument_msg->slot;
    int num = 0;
    for (int i = 0; i < instr_num_srcs(instr); i++) {
        if (opnd_is_memory_reference(instr_get_src(instr, i))) {
            num++;
            // 0 = read
            InstrumentMem(drcontext, bb, instr, instr_get_src(instr, i), 0);
        }
        else if (opnd_is_reg(instr_get_src(instr, i))) {
            // in case multiple registers in operand
            opnd_t op = instr_get_src(instr, i);
            int num_temp = opnd_num_regs_used(op);
            for (int j = 0; j < num_temp; j++) {
                reg_id_t reg_id = opnd_get_reg_used(op, j); // register id
                // 0 = read
                // insert clean call with read, reg_id, and slot
                dr_insert_clean_call(drcontext, bb, instr, (void *)InsertRegCleanCall,
                                     false, 3, OPND_CREATE_CCT_INT(slot),
                                     OPND_CREATE_CCT_INT(reg_id), OPND_CREATE_CCT_INT(0));
            }
        }
    }
    for (int i = 0; i < instr_num_dsts(instr); i++) {
        if (opnd_is_reg(instr_get_dst(instr, i))) {
            // in case multiple registers in operand
            opnd_t op = instr_get_dst(instr, i);
            int num_temp = opnd_num_regs_used(op);
            for (int j = 0; j < num_temp; j++) {
                reg_id_t reg_id = opnd_get_reg_used(op, 0);
                cout << reg_id << endl;
                if (opnd_is_memory_reference(op)) {
                    // 0 = read
                    // insert clean call with read, reg_id, and slot
                    dr_insert_clean_call(drcontext, bb, instr, (void *)InsertRegCleanCall,
                                         false, 3, OPND_CREATE_CCT_INT(slot),
                                         OPND_CREATE_CCT_INT(reg_id),
                                         OPND_CREATE_CCT_INT(0));
                } else {
                    // 1 = write
                    // insert clean call with write, reg_id, and slot
                    dr_insert_clean_call(drcontext, bb, instr, (void *)InsertRegCleanCall,
                                         false, 3, OPND_CREATE_CCT_INT(slot),
                                         OPND_CREATE_CCT_INT(reg_id),
                                         OPND_CREATE_CCT_INT(1));
                }
           }
        }
        else if (opnd_is_memory_reference(instr_get_dst(instr, i))) {
            num++;
            // 1 = write
            InstrumentMem(drcontext, bb, instr, instr_get_dst(instr, i), 1);
        }
    }

    dr_insert_clean_call(drcontext, bb, instr, (void *)InsertCleancall, false, 2,
                         OPND_CREATE_CCT_INT(slot), OPND_CREATE_CCT_INT(num));
}

static void
ClientThreadStart(void *drcontext)
{
    per_thread_t *pt = (per_thread_t *)dr_thread_alloc(drcontext, sizeof(per_thread_t));
    if (pt == NULL) {
        DRCCTLIB_EXIT_PROCESS("pt == NULL");
    }
    drmgr_set_tls_field(drcontext, tls_idx, (void *)pt);

    pt->cur_buf = dr_get_dr_segment_base(tls_seg);
    pt->cur_buf_list =
        (mem_ref_t *)dr_global_alloc(TLS_MEM_REF_BUFF_SIZE * sizeof(mem_ref_t));
    BUF_PTR(pt->cur_buf, mem_ref_t, INSTRACE_TLS_OFFS_BUF_PTR) = pt->cur_buf_list;
}

static void
ClientThreadEnd(void *drcontext)
{
    per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    dr_global_free(pt->cur_buf_list, TLS_MEM_REF_BUFF_SIZE * sizeof(mem_ref_t));
    dr_thread_free(drcontext, pt, sizeof(per_thread_t));
}

static void
ClientInit(int argc, const char *argv[])
{
}

static string AddrToHex(unsigned long addr){
    stringstream hex_addr;
    hex_addr << "0x" << setfill('0') << setw(sizeof(addr)*2) << std::hex << addr;
    return hex_addr.str();
}

void PrintToFile(uint32_t dead, uint32_t killing, ofstream& fout){

    int lineCount = 0;
    //Dead context's output
    context_t *cct = drcctlib_get_full_cct(dead, 0); // deads's full tree

    context_t *parent = cct->pre_ctxt; // gets parent context of current node
    int parent_handle = cct->pre_ctxt->ctxt_hndl; // parent handle of current node

    fout << cct->ctxt_hndl << ":" << AddrToHex((unsigned long)cct->ip) << ":" << cct->code_asm << ":" << cct->func_name << ":" << cct->file_path << "(" << cct->line_no << ")"
         << endl;
    // prints out node call tree by going up parents
    while (parent_handle != 0) {
        for(int j=0; j<lineCount+1; j++){
            fout << "  ";
        }

        fout << parent->ctxt_hndl << ":" << AddrToHex((unsigned long)parent->ip) << ":" << parent->code_asm << ":" << parent->func_name << ":" << parent->file_path << "(" << parent->line_no << ")"
             << endl;
        // sets next parent, or sets 0 if at ROOT_CTXT
        if (parent_handle != 1) {
            parent = parent->pre_ctxt;
            parent_handle = parent->ctxt_hndl;
        } else {
            parent_handle = 0;
        }
        lineCount++;
    }
    fout << writeDiv << endl << endl;

    lineCount = 0;
    //Killing context output
    cct = drcctlib_get_full_cct(killing, 0); // deads's full tree

    parent = cct->pre_ctxt; // gets parent context of current node
    parent_handle = cct->pre_ctxt->ctxt_hndl; // parent handle of current node

    fout << cct->ctxt_hndl << ":" << cct->code_asm << ":" << cct->func_name << cct->file_path << "(" << cct->line_no << "):\""
         << AddrToHex((unsigned long)cct->ip) << ":" << cct->code_asm << endl;
    // prints out node call tree by going up parents
    while (parent_handle != 0) {
        string dblSpace = "  ";
        for(int j=0; j<lineCount+1; j++){
            fout << "  ";
        }
        fout << parent->ctxt_hndl << ":" << AddrToHex((unsigned long)parent->ip) << ":" << parent->code_asm << ":" << parent->func_name << ":" << parent->file_path << "(" << parent->line_no << ")"
             << endl;

        // sets next parent, or sets 0 if at ROOT_CTXT
        if (parent_handle != 1) {
            parent = parent->pre_ctxt;
            parent_handle = parent->ctxt_hndl;
        } else {
            parent_handle = 0;
        }
        lineCount++;
    }
    fout << divider << endl << endl;
    return;
}

void OutputRegLog(){
    //put dead write map into multimap to sort, because C++ probably sorts better than
    //I do

    int totDeadWrite = 0; //total dead writes

    multimap<uint64, uint64> sorted;
    for(auto& it : deadRegRecord){
        sorted.insert({it.second, it.first}); //add to multimap to sort
        totDeadWrite+=it.second; //sum dead writes while already going through map
    }


    ofstream fout("RegisterDeadWrites.txt");
    fout << "REGISTER DEAD WRITE RECORD" << endl;
    fout << "Total Register Writes: " << totRegWrite << endl;
    fout << "Total Dead Register Writes: " << totDeadWrite << " " << (float) totDeadWrite/totRegWrite*100.00 << "%" << endl << endl;
    fout << "Percentages of Dead Writes Per Record is Percent of All Dead Writes" << endl;
    fout << formatGuide << endl;

    //print top 100
    auto rev_it = sorted.rbegin();

    bool total = false;
    uint32_t dead;
    uint32_t killing;
    for (int i = 1; i < 101; i++) {
        tie(dead, killing) = UnpackInts(rev_it->second);
        //cout << dead << " k: " << killing << endl;
        fout << "NO. " << i << " dead write total is " << rev_it->first
             << " (" << (float) rev_it->first/totDeadWrite*100.00 << ")" << endl;
        fout << divider << endl;
        PrintToFile(dead, killing, fout);

        rev_it++;
    }
}



void OutputMemLog(){
    //put dead write map into multimap to sort, because C++ probably sorts better than
    //I do

    int totDeadWrite = 0; //total dead writes

    multimap<uint64, uint64> sorted;
    for(auto& it : deadMemRecord){
        sorted.insert({it.second, it.first}); //add to multimap to sort
        totDeadWrite+=it.second; //sum dead writes while already going through map
    }


    ofstream fout("MemoryDeadWrites.txt");
    fout << "MEMORY DEAD WRITE RECORD" << endl;
    fout << "Total Memory Writes: " << totMemWrite << endl;
    fout << "Total Dead Memory Writes: " << totDeadWrite << " " << (float) totDeadWrite/totMemWrite*100.00 << "%" << endl << endl;
    fout << "Percentages of Dead Writes Per Record is Percent of All Dead Writes" << endl;
    fout << formatGuide << endl;

    //print top 100
    auto rev_it = sorted.rbegin();

    bool total = false;
    uint32_t dead;
    uint32_t killing;
    for (int i = 1; i < 101; i++) {
        tie(dead, killing) = UnpackInts(rev_it->second);
        //cout << dead << " k: " << killing << endl;

        fout << "NO. " << i << " dead write total is " << rev_it->first
            << " (" << (float) rev_it->first/totDeadWrite*100.00 << ")" << endl;
        fout << divider << endl;
        PrintToFile(dead, killing, fout);
//
//        int lineCount = 0;
//        //Dead context's output
//        context_t *cct = drcctlib_get_full_cct(dead, 0); // deads's full tree
//
//        context_t *parent = cct->pre_ctxt; // gets parent context of current node
//        int parent_handle = cct->pre_ctxt->ctxt_hndl; // parent handle of current node
//
//        // prints out node call tree by going up parents
//        while (parent_handle != 0) {
//            for(int j=0; j<lineCount; j++){
//                fout << "  ";
//            }
//            fout << parent->file_path << ":" << parent->func_name << "(" << parent->line_no << "):\""
//                << AddrToHex((unsigned long)parent->ip) << ")" << parent->code_asm
//                << "\"" << endl;
//
//            // sets next parent, or sets 0 if at ROOT_CTXT
//            if (parent_handle != 1) {
//                parent = parent->pre_ctxt;
//                parent_handle = parent->ctxt_hndl;
//            } else {
//                parent_handle = 0;
//            }
//            lineCount++;
//        }
//        fout << writeDiv << endl << endl;
//
//        lineCount = 0;
//        //Killing context output
//        cct = drcctlib_get_full_cct(killing, 0); // deads's full tree
//
//        parent = cct->pre_ctxt; // gets parent context of current node
//        parent_handle = cct->pre_ctxt->ctxt_hndl; // parent handle of current node
//
//        // prints out node call tree by going up parents
//        while (parent_handle != 0) {
//            string dblSpace = "  ";
//            for(int j=0; j<lineCount; j++){
//                fout << "  ";
//            }
//            fout << parent->file_path << ":" << parent->func_name << "(" << parent->line_no << "):\""
//                 << AddrToHex((unsigned long)parent->ip) << ")" << parent->code_asm
//                 << "\"" << endl;
//
//            // sets next parent, or sets 0 if at ROOT_CTXT
//            if (parent_handle != 1) {
//                parent = parent->pre_ctxt;
//                parent_handle = parent->ctxt_hndl;
//            } else {
//                parent_handle = 0;
//            }
//            lineCount++;
//        }
//        fout << divider << endl << endl;
        rev_it++;
    }

    // out << endl << endl;
}

static void
ClientExit(void)
{
    OutputMemLog();
    OutputRegLog();
    drcctlib_exit();

    if (!dr_raw_tls_cfree(tls_offs, INSTRACE_TLS_COUNT)) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_dead_write dr_raw_tls_calloc fail");
    }
    if (!drmgr_unregister_thread_init_event(ClientThreadStart) ||
        !drmgr_unregister_thread_exit_event(ClientThreadEnd) ||
        !drmgr_unregister_tls_field(tls_idx)) {
        DRCCTLIB_PRINTF("ERROR: drcctlib_dead_write failed to "
                        "unregister in ClientExit");
    }
    drmgr_exit();
    if (drreg_exit() != DRREG_SUCCESS) {
        DRCCTLIB_PRINTF("failed to exit drreg");
    }
    drutil_exit();
}

#ifdef __cplusplus
extern "C" {
#endif

DR_EXPORT void
dr_client_main(client_id_t id, int argc, const char *argv[])
{
    dr_set_client_name("DynamoRIO Client 'drcctlib_dead_write'",
                       "http://dynamorio.org/issues");
    ClientInit(argc, argv);

    if (!drmgr_init()) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_dead_write "
                              "unable to initialize drmgr");
    }
    drreg_options_t ops = { sizeof(ops), 4 /*max slots needed*/, false };
    if (drreg_init(&ops) != DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_dead_write "
                              "unable to initialize drreg");
    }
    if (!drutil_init()) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_dead_write "
                              "unable to initialize drutil");
    }
    drmgr_register_thread_init_event(ClientThreadStart);
    drmgr_register_thread_exit_event(ClientThreadEnd);

    tls_idx = drmgr_register_tls_field();
    if (tls_idx == -1) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_dead_write "
                              "drmgr_register_tls_field fail");
    }
    if (!dr_raw_tls_calloc(&tls_seg, &tls_offs, INSTRACE_TLS_COUNT, 0)) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_dead_write dr_raw_tls_calloc fail");
    }
    drcctlib_init(DRCCTLIB_FILTER_MEM_ACCESS_INSTR, INVALID_FILE, InstrumentInsCallback,
                  false);
    dr_register_exit_event(ClientExit);
}

#ifdef __cplusplus
}
#endif