/*
 *  Copyright (c) 2020 Xuhpclab. All rights reserved.
 *  Licensed under the MIT License.
 *  See LICENSE file for more information.
 */

#include <cstddef>
#include <list>
#include <iostream>
#include <map>
#include <string>
#include <fstream>
#include <sstream>
#include <iomanip>
#include <algorithm>
using namespace std;

#include "dr_api.h"
#include "drmgr.h"
#include "drreg.h"
#include "drutil.h"
#include "drcctlib.h"
#include "drcctlib_hpcviewer_format.h"


#define DRCCTLIB_PRINTF(format, args...) \
    DRCCTLIB_PRINTF_TEMPLATE("memory_with_addr_and_refsize_clean_call", format, ##args)
#define DRCCTLIB_EXIT_PROCESS(format, args...)                                       \
    DRCCTLIB_CLIENT_EXIT_PROCESS_TEMPLATE("memory_with_addr_and_refsize_clean_call", \
                                          format, ##args)

#define TOP_REACH_NUM_SHOW 200

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
    size_t size;
} mem_ref_t;

typedef struct _per_thread_t {
    mem_ref_t *cur_buf_list;
    void *cur_buf;
} per_thread_t;

typedef struct _parent_map {
    char *func;
    list<unsigned long> locs;
    int32_t parent;

} parent_map;

map<context_handle_t, list<unsigned long>> calls;

string divider = "================================================================================";
#define TLS_MEM_REF_BUFF_SIZE 100

// client want to do
void
DoWhatClientWantTodo(void *drcontext, context_handle_t cur_ctxt_hndl, mem_ref_t *ref)
{



    list<unsigned long> mem;
    unsigned long address = (unsigned long)ref->addr; //casts starting address to long

    //Checks if current context 1. exists in global call map and 2. if it exists, if the
    //memory locations exist. Searching for that specific context handle adds it if it
    //doesn't already exist, which is default functionality of map
    //if bytes aren't in list, pushes them to back
    for (long unsigned int i = 0; i < ref->size; i++) {
        if (find(calls[cur_ctxt_hndl].begin(), calls[cur_ctxt_hndl].end(), address) ==
            calls[cur_ctxt_hndl].end()) {
            calls[cur_ctxt_hndl].push_front(address);
        }
        address++;
    }
}

// }

// dr clean call
void
InsertCleancall(int32_t slot, int32_t num)
{
    void *drcontext = dr_get_current_drcontext();
    per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    context_handle_t cur_ctxt_hndl = drcctlib_get_context_handle(drcontext, slot);
    for (int i = 0; i < num; i++) {
        if (pt->cur_buf_list[i].addr != 0) {
            DoWhatClientWantTodo(drcontext, cur_ctxt_hndl, &pt->cur_buf_list[i]);
        }
    }
    BUF_PTR(pt->cur_buf, mem_ref_t, INSTRACE_TLS_OFFS_BUF_PTR) = pt->cur_buf_list;
}

// insert
static void
InstrumentMem(void *drcontext, instrlist_t *ilist, instr_t *where, opnd_t ref)
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
                drcontext, OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, size)),
                opnd_create_reg(free_reg)));
#else
    MINSERT(ilist, where,
            XINST_CREATE_store(
                drcontext, OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, size)),
                OPND_CREATE_CCT_INT(drutil_opnd_mem_size_in_bytes(ref, where))));
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
            InstrumentMem(drcontext, bb, instr, instr_get_src(instr, i));
        }
    }
    for (int i = 0; i < instr_num_dsts(instr); i++) {
        if (opnd_is_memory_reference(instr_get_dst(instr, i))) {
            num++;
            InstrumentMem(drcontext, bb, instr, instr_get_dst(instr, i));
        }
    }

    for (int i = 0; i < instr_num_dsts(instr); i++) {
        if (opnd_is_reg(instr_get_src(instr, i))) {
            num++;
            InstrumentMem(drcontext, bb, instr, instr_get_src(instr, i));
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

static string addr_to_hex(unsigned long addr){
    stringstream hex_addr;
    hex_addr << "0x" << setfill('0') << setw(sizeof(addr)*2) << std::hex << addr;
    return hex_addr.str();
}

static void
ClientExit(void)
{
    // add output module here
    //map<int32_t, list<unsigned long>>::iterator it = calls.begin();

    //Goes through calls map and aggregates the memory footprint of each node up
    //it's call tree
    for(auto& it : calls) {

            //gets full CCT for current node
            context_t *full_cct = drcctlib_get_full_cct(it.first, 0);
            //list<unsigned long>::iterator addr_it = it.second.begin();
            context_t *parent = full_cct->pre_ctxt; //initial parrent context
            int parent_handle = full_cct->pre_ctxt->ctxt_hndl; //initial parent context handle
            while(parent_handle != 0){

                //checks if parent node has the memory bytes assigned, if not, adds them.
                //same functionality as in DoWhatClientWantTodo
            for(auto& addr_it : it.second) {
                if (find(calls[parent_handle].begin(), calls[parent_handle].end(),
                         addr_it) == calls[parent_handle].end()) {
                    calls[parent_handle].push_front(addr_it);
                }


            }
             //sets next parent, or sets 0 if at ROOT_CTXT
            if(parent_handle!=1) {
                parent = parent->pre_ctxt;
                parent_handle = parent->ctxt_hndl;
            }
            else{
                parent_handle = 0;
            }
            //cout << "H: " << parent_handle;
        }
    }
    //put size values into multimap for sorting
    multimap<int, context_handle_t> sorted;
    for (auto& it : calls){
        sorted.insert({it.second.size(), it.first});
    }


    //goes through sorted multimap, and prints out the information for each node
    //code is simply string formatting and pulling each piece of information from the
    //node's context
    auto rev_it = sorted.rbegin();
    ofstream out("footprint.txt");
    out << "Memory footprint of nodes, orderd by size" << endl;
    bool total = false;
    for(int i = 0; i < 200; i++){
        context_t *cct = drcctlib_get_full_cct(rev_it->second, 0); //node's full tree

        int print_num = i-2; //Starts at No. 0 for output, skipping ROOT_CTXT

        //if root_ctxt or _root_ctxt, simply prints out the total memory size. This is because
        //root_ctxt does not require a tree print, line number, etc, as it is always the same information
        if(rev_it->second == 1 || rev_it->second == 2){
            if(!total) {
                out << "The total foot print of program (from " << cct->func_name
                    << ") is " << rev_it->first << " bytes" << endl;
                total = true;
            }
        }
        //if not root context, print out memory info
        else{
            out << "NO. " << print_num << " memory footprint is " << rev_it->first <<
                " bytes for " << cct->func_name << "(" << cct->line_no << "): (" <<
                addr_to_hex((unsigned long)cct->ip) << ")" << endl;
            out << divider << endl;

            context_t *parent = cct->pre_ctxt; //gets parent context of current node
            int parent_handle = cct->pre_ctxt->ctxt_hndl; //parent handle of current node

            //prints out node call tree by going up parents
            while(parent_handle != 0){
                out << parent->func_name << "(" << parent->line_no << "):\"" <<
                    addr_to_hex((unsigned long) parent->ip) << ")" << parent->code_asm << "\"" << endl;

                //sets next parent, or sets 0 if at ROOT_CTXT
                if(parent_handle!=1) {
                    parent = parent->pre_ctxt;
                    parent_handle = parent->ctxt_hndl;
                }
                else{
                    parent_handle = 0;
                }
            }
            out << divider << endl << endl;

        }

        //out << endl << endl;
        rev_it++;

    }

    typedef struct _output_format_t {
        context_handle_t handle;
        uint64_t count;
    } output_format_t;

    output_format_t *output_list =
        (output_format_t *)dr_global_alloc(TOP_REACH_NUM_SHOW * sizeof(output_format_t));


    long counter = 0;
    for(auto& it : sorted){
        while(counter < TOP_REACH_NUM_SHOW) {
            output_list[counter].handle = it.second;
            output_list[counter].count = it.first;
            counter++;
        }
    }


    //Attempt to set HPC format. I don't think it works, but I also don't know if I was connecting
    //it correctly
    vector<HPCRunCCT_t *> hpcRunNodes; //HPC format vector

    //puts sorted nodes and their memory sizes into hpc vectors
    for (long unsigned int i = 0; i < TOP_REACH_NUM_SHOW; i++) {
        HPCRunCCT_t *hpcRunNode = new HPCRunCCT_t();
        hpcRunNode->ctxt_hndl_list.push_back(output_list[i].handle);
        hpcRunNode->metric_list.push_back(output_list[i].count);
        hpcRunNodes.push_back(hpcRunNode);
    }

    //builds/writes hpc file
    build_progress_custom_cct_hpurun_format(hpcRunNodes);
    write_progress_custom_cct_hpurun_format();



    hpcrun_format_exit();
    drcctlib_exit();

if (!dr_raw_tls_cfree(tls_offs, INSTRACE_TLS_COUNT)) {
    DRCCTLIB_EXIT_PROCESS(
        "ERROR: drcctlib_memory_with_addr_and_refsize_clean_call dr_raw_tls_calloc fail");
}
if (!drmgr_unregister_thread_init_event(ClientThreadStart) ||
    !drmgr_unregister_thread_exit_event(ClientThreadEnd) ||
    !drmgr_unregister_tls_field(tls_idx)) {
    DRCCTLIB_PRINTF("ERROR: drcctlib_memory_with_addr_and_refsize_clean_call failed to "
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

    dr_set_client_name(
        "DynamoRIO Client 'drcctlib_memory_footprint'",
        "http://dynamorio.org/issues");
    ClientInit(argc, argv);
    hpcrun_format_init(dr_get_application_name(), false); // init for hpcformat
    hpcrun_create_metric("TOT_MEM_BYTES"); //sets metric for hpcformat

    if (!drmgr_init()) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_memory_with_addr_and_refsize_clean_call "
                              "unable to initialize drmgr");
    }
    drreg_options_t ops = { sizeof(ops), 4 /*max slots needed*/, false };
    if (drreg_init(&ops) != DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_memory_with_addr_and_refsize_clean_call "
                              "unable to initialize drreg");
    }
    if (!drutil_init()) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_memory_with_addr_and_refsize_clean_call "
                              "unable to initialize drutil");
    }
    drmgr_register_thread_init_event(ClientThreadStart);
    drmgr_register_thread_exit_event(ClientThreadEnd);

    tls_idx = drmgr_register_tls_field();
    if (tls_idx == -1) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_memory_with_addr_and_refsize_clean_call "
                              "drmgr_register_tls_field fail");
    }
    if (!dr_raw_tls_calloc(&tls_seg, &tls_offs, INSTRACE_TLS_COUNT, 0)) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_memory_with_addr_and_refsize_clean_call "
                              "dr_raw_tls_calloc fail");
    }
    drcctlib_init(DRCCTLIB_FILTER_MEM_ACCESS_INSTR, INVALID_FILE, InstrumentInsCallback,
                  false);
    dr_register_exit_event(ClientExit);
}

#ifdef __cplusplus
}
#endif
