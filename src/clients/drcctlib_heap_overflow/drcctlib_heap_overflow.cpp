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
#include "drwrap.h"
#include "map"
#include <stdio.h>
#include <iostream>
#include <sstream>
#include <iomanip>
#include "stack"
#include <fstream>
#include <sstream>

using namespace std;

#define DRCCTLIB_PRINTF(format, args...) \
    DRCCTLIB_PRINTF_TEMPLATE("heap_overflow", format, ##args)
#define DRCCTLIB_EXIT_PROCESS(format, args...)                                           \
    DRCCTLIB_CLIENT_EXIT_PROCESS_TEMPLATE("heap_overflow", format, \
                                          ##args)


//Checks if Windows, if yes choose left parameter

#ifdef WINDOWS
#    define IF_WINDOWS_ELSE(x, y) x
#else
#    define IF_WINDOWS_ELSE(x, y) y
#endif

#define MALLOC_ROUTINE_NAME IF_WINDOWS_ELSE("HeapAlloc", "malloc")
#define FREE_ROUTINE_NAME IF_WINDOWS_ELSE("HeapFree", "free")


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

size_t redzone_size;
static void *size_lock; //locks redzone size so size does not get overwritten before post call

typedef struct _zone_info {
    context_handle_t ctxt_hndl;
    app_pc base_addr;
} zone_info;

typedef struct _violation_info {
    context_handle_t vio_ctxt; // violating context
    context_handle_t red_ctxt; // redzone context
    app_pc red_addr; // redzone address
} violation_info;

map<app_pc , zone_info> redzone; // <Redzone address, <redzone context, heap base>>
stack<violation_info> violations; // Stack holding violations

#define TLS_MEM_REF_BUFF_SIZE 100



static void
prewrap_malloc(void *wrapcxt OUT,  void **user_data)
{
    /* malloc(size) or HeapAlloc(heap, flags, size) */
    size_t size = (size_t)drwrap_get_arg(wrapcxt, IF_WINDOWS_ELSE(2, 0));
    *user_data = (void *) size; //save based size, since 0 index means addr+size is after array

    //add 5 to make 5 wide redzone
    drwrap_set_arg(wrapcxt, IF_WINDOWS_ELSE(2, 0), (void*) (size + 5));
     //cout << "Pre Success; Size: " << size << endl;

}


static void
postwrap_malloc(void *wrapctxt , void *user_data)
{
    void *context = drwrap_get_drcontext(wrapctxt); // get drcontext for post
    context_handle_t curr_ctxt =
        drcctlib_get_context_handle(context, 0); // get current context from dr context
    app_pc base_addr = (app_pc)drwrap_get_retval(
        wrapctxt); // get return value of malloc (pointer to base)

    //Create 5 byte wide redzone
    for (int i = 0; i < 5; i++) {
        app_pc redzone_addr = base_addr + (unsigned long)user_data; // redzone address
        redzone[redzone_addr].ctxt_hndl = curr_ctxt; // add context to redzone map
        redzone[redzone_addr].base_addr = base_addr; // add base address to redzone map
        // cout << "Post Success; Size: " << (unsigned long) user_data << " Redzone: " << (unsigned long) redzone_addr << " Base: " << (unsigned long) base_addr << " Context: " << curr_ctxt << endl;
    }
}

static void prewrap_free(void *wrapctxt OUT, void **user_data){
    //grabs the base pointer of area to be freed to be passed to post function.
    // redzone not removed from map until post to confirm free executed properly
    *user_data = (void *)drwrap_get_arg(wrapctxt, IF_WINDOWS_ELSE(0, 0)); // IF_WINDOWS_ELSE not needed, as Handle is the 0th variable. In place for consistency
}

static void postwrap_free(void *wrapctxt, void *user_data){
    for(auto& it : redzone){
        if(it.second.base_addr == (app_pc) user_data){
            int success = redzone.erase(it.first);
            //cout << "Free erase " << success << endl;
        }
    }
}

static void module_load_event(void *drcontext, const module_data_t *mod, bool loaded){
    app_pc freewrap = (app_pc)dr_get_proc_address(mod->handle, FREE_ROUTINE_NAME);
    app_pc mallwrap = (app_pc)dr_get_proc_address(mod->handle, MALLOC_ROUTINE_NAME);
    //cout << mod->handle << endl;
    if(freewrap != NULL) {
        // cout << mod->names.file_name << endl;
        //cout << "Free wrapped" << endl;
        drwrap_wrap(freewrap, prewrap_free, postwrap_free);
    }

    if(mallwrap != NULL){
        drwrap_wrap(mallwrap, prewrap_malloc, postwrap_malloc);
    }

}

// Check memory access against Redzone
void
CheckRedzone(void *drcontext, context_handle_t cur_ctxt_hndl, mem_ref_t *ref)
{
    app_pc addr;

    //checks the entire size of the access reference instead of just the base. This is because
    //even if it is not a direct redzone access, the access is a violation. Just because you use
    //only the first byte of an integer or other memory primitive, if the rest of it extends into
    //an overflow, it can be a security issue
    for(unsigned long i = 0; i < ref->size; i++) {
        addr = ref->addr + i; //violating address/redzone map key
        if (redzone.find(addr) != redzone.end()) {
            context_t *context = drcctlib_get_full_cct(cur_ctxt_hndl, 0);
            /* cout << "Redzone hit, Redzone Info: " << redzone[ref->addr + i].ctxt_hndl
                 << " Address: " << (unsigned long)ref->addr + i << " i: " << i << endl;
               */

            violation_info hold;
            hold.red_addr = addr;
            hold.red_ctxt = redzone[addr].ctxt_hndl;
            hold.vio_ctxt = cur_ctxt_hndl;
            violations.push(hold);
        }

    }
    
}
// dr clean call
void
InsertCleancall(int32_t slot,int32_t num)
{
    void *drcontext = dr_get_current_drcontext();
    per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    context_handle_t cur_ctxt_hndl = drcctlib_get_context_handle(drcontext, slot);
    for (int i = 0; i < num; i++) {
        if (pt->cur_buf_list[i].addr != 0) {
            CheckRedzone(drcontext, cur_ctxt_hndl, &pt->cur_buf_list[i]);
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
            XINST_CREATE_load_int(drcontext, opnd_create_reg(free_reg),
                                  OPND_CREATE_CCT_INT(drutil_opnd_mem_size_in_bytes(ref, where))));
    MINSERT(ilist, where,
            XINST_CREATE_store(drcontext, OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, size)),
                             opnd_create_reg(free_reg)));
#else
    MINSERT(ilist, where,
            XINST_CREATE_store(drcontext, OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, size)),
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

static void
ClientExit(void)
{
    string app_name = dr_get_application_name();
    string filename = "Redzone_Violations_" + (string) dr_get_application_name() + ".txt.";
    ofstream fout(filename);
    int count = 0;
    while(!violations.empty()){
        count++;
        violation_info top = violations.top();
        fout << "Redzone Violation " << count << ": Redzone Context=" << top.red_ctxt
             << " Violating Context=" << top.vio_ctxt << " Address="
             << AddrToHex((unsigned long) top.red_addr) << endl;
        violations.pop();
    }
    drcctlib_exit();

    if (!dr_raw_tls_cfree(tls_offs, INSTRACE_TLS_COUNT)) {
        DRCCTLIB_EXIT_PROCESS(
            "ERROR: drcctlib_heap_overflow dr_raw_tls_calloc fail");
    }
    if (!drmgr_unregister_thread_init_event(ClientThreadStart) ||
        !drmgr_unregister_thread_exit_event(ClientThreadEnd) ||
        !drmgr_unregister_tls_field(tls_idx)) {
        DRCCTLIB_PRINTF("ERROR: drcctlib_heap_overflow failed to "
                        "unregister in ClientExit");
    }
    dr_mutex_destroy(size_lock);
    drwrap_exit();
    drwrap_exit();
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
    dr_set_client_name("DynamoRIO Client 'drcctlib_heap_overflow'",
                       "http://dynamorio.org/issues");
    ClientInit(argc, argv);

    if (!drmgr_init()) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_heap_overflow "
                              "unable to initialize drmgr");
    }
    drreg_options_t ops = { sizeof(ops), 4 /*max slots needed*/, false };
    if (drreg_init(&ops) != DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_heap_overflow "
                              "unable to initialize drreg");
    }
    if (!drutil_init()) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_heap_overflow "
                              "unable to initialize drutil");
    }
    drwrap_init();

    drmgr_register_thread_init_event(ClientThreadStart);
    drmgr_register_thread_exit_event(ClientThreadEnd);

    tls_idx = drmgr_register_tls_field();
    if (tls_idx == -1) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_heap_overflow "
                              "drmgr_register_tls_field fail");
    }
    if (!dr_raw_tls_calloc(&tls_seg, &tls_offs, INSTRACE_TLS_COUNT, 0)) {
        DRCCTLIB_EXIT_PROCESS(
            "ERROR: drcctlib_heap_overflow dr_raw_tls_calloc fail");
    }

    drmgr_register_module_load_event(module_load_event);
    size_lock = dr_mutex_create();

    drcctlib_init(DRCCTLIB_FILTER_MEM_ACCESS_INSTR, INVALID_FILE, InstrumentInsCallback, false);
    dr_register_exit_event(ClientExit);
}

#ifdef __cplusplus
}
#endif