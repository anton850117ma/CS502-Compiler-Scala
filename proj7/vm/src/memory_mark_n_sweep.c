#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include "memory.h"
#include "fail.h"
#include "engine.h"

#if GC_VERSION == GC_MARK_N_SWEEP

static void* memory_start = NULL;
static void* memory_end = NULL;

static uvalue_t* bitmap_start = NULL;

static value_t* heap_start = NULL;
static value_t* heap_end = NULL;
static value_t heap_start_v = 0;
static value_t heap_end_v = 0;
static value_t* heap_first_block = NULL;

#define FREE_LISTS_COUNT 32
static value_t* free_list_heads[FREE_LISTS_COUNT];

#define MIN_BLOCK_SIZE 1
#define HEADER_SIZE 1

// Header management

static value_t header_pack(tag_t tag, value_t size) { //(tag+size)
  return (size << 8) | (value_t)tag;
}

static tag_t header_unpack_tag(value_t header) { //get the tag of the header
  return (tag_t)(header & 0xFF);
}

static value_t header_unpack_size(value_t header) { //remove the tag to get size
  return header >> 8;
}

// Bitmap management

static int bitmap_is_bit_set(value_t* ptr) {
  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  return (bitmap_start[word_index] & ((uvalue_t)1 << bit_index)) != 0; //true == 1, false == 0
}

static void bitmap_set_bit(value_t* ptr) {
  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  bitmap_start[word_index] |= (uvalue_t)1 << bit_index;
}

static void bitmap_clear_bit(value_t* ptr) {
  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  bitmap_start[word_index] &= ~((uvalue_t)1 << bit_index);
}

// Virtual <-> physical address translation

static void* addr_v_to_p(value_t v_addr) {
  return (char*)memory_start + v_addr;
}

static value_t addr_p_to_v(void* p_addr) {
  return (value_t)((char*)p_addr - (char*)memory_start);
}

// Free lists management

static value_t real_size(value_t size) {
  assert(0 <= size);
  return size < MIN_BLOCK_SIZE ? MIN_BLOCK_SIZE : size;
}

static unsigned int free_list_index(value_t size) {
  assert(0 <= size);
  return size >= FREE_LISTS_COUNT ? FREE_LISTS_COUNT - 1 : (unsigned int)size;
}

char* memory_get_identity() {
  return "mark & sweep garbage collector";
}

void memory_setup(size_t total_byte_size) {
  memory_start = malloc(total_byte_size);
  if (memory_start == NULL)
    fail("cannot allocate %zd bytes of memory", total_byte_size);
  memory_end = (char*)memory_start + total_byte_size;
}

void memory_cleanup() {
  assert(memory_start != NULL);
  free(memory_start);

  memory_start = memory_end = NULL;
  bitmap_start = NULL;
  heap_start = heap_end = NULL;
  heap_start_v = heap_end_v = 0;
  for (int l = 0; l < FREE_LISTS_COUNT; ++l)
    free_list_heads[l] = NULL;
}

void* memory_get_start() {
  return memory_start;
}

void* memory_get_end() {
  return memory_end;
}

void memory_set_heap_start(void* ptr) {
  assert(memory_start <= ptr && ptr < memory_end);

  const size_t bh_size =
    (size_t)((char*)memory_end - (char*)ptr) / sizeof(value_t); // this size is the number of value_t

  const size_t bitmap_size = (bh_size - 1) / (VALUE_BITS + 1) + 1;
  const size_t heap_size = bh_size - bitmap_size;

  bitmap_start = ptr;
  memset(bitmap_start, 0, bitmap_size * sizeof(value_t));

  heap_start = (value_t*)bitmap_start + bitmap_size;
  heap_end = heap_start + heap_size;
  assert(heap_end == memory_end);

  heap_start_v = addr_p_to_v(heap_start);
  heap_end_v = addr_p_to_v(heap_end);

  heap_first_block = heap_start + HEADER_SIZE;
  const value_t initial_block_size = (value_t)(heap_end - heap_first_block);
  heap_first_block[-1] = header_pack(tag_None, initial_block_size);
  heap_first_block[0] = 0;

  for (int l = 0; l < FREE_LISTS_COUNT - 1; ++l) 
    free_list_heads[l] = memory_start;
  free_list_heads[FREE_LISTS_COUNT - 1] = heap_first_block;
}

static value_t* allocate(tag_t tag, value_t size) { 
  
  assert(0 <= size);
  value_t true_size = real_size(size);
  value_t* current_ptr = free_list_heads[FREE_LISTS_COUNT-1];
  value_t* pre_ptr = NULL;
 
  while(heap_start <= current_ptr && current_ptr < heap_end){
    value_t current_size = memory_get_block_size(current_ptr);
    if(true_size == current_size || true_size + 1 == current_size){
      //check how to reconnect
      if(pre_ptr == NULL){
        free_list_heads[FREE_LISTS_COUNT-1] = addr_v_to_p(*current_ptr);
      }
      else *pre_ptr = *current_ptr;
      //assgin whole block
      current_ptr[-1] = header_pack(tag, current_size);
      memset(current_ptr, 0, current_size*sizeof(value_t));
      bitmap_set_bit(current_ptr);
      return current_ptr;
    }
    else if(true_size > current_size){
      //find next block
      pre_ptr = current_ptr;
      current_ptr = addr_v_to_p(*current_ptr);
    }
    else if(true_size + 1 < current_size){
      //produce the rest block
      current_ptr[true_size] = header_pack(tag_None, current_size - true_size - 1);
      current_ptr[true_size + 1] = *current_ptr;
      //check how to reconnect
      if(pre_ptr == NULL){
        free_list_heads[FREE_LISTS_COUNT-1] = current_ptr + true_size + 1;
      }
      else *pre_ptr = current_ptr[true_size + 1];
      //assign splited block
      current_ptr[-1] = header_pack(tag, true_size);
      memset(current_ptr, 0, true_size*sizeof(value_t));
      bitmap_set_bit(current_ptr);
      return current_ptr;
    }
  }
  return NULL;
  // TODO
}

static void mark(value_t* block) {
/*
a depth-first traversal of the reachabilty graph may overflow, avoid it by storing the stack in the objects being traced
*/
  value_t block_size = memory_get_block_size(block);
  bitmap_clear_bit(block);
  for(int i = 0; i < block_size; ++i){
    value_t vir_addr = block[i];
    if(((vir_addr & 3) == 0) && (heap_start_v <= vir_addr) && (vir_addr < heap_end_v)){
      value_t* ph_addr = addr_v_to_p(vir_addr);
      if(bitmap_is_bit_set(ph_addr) == 1){ 
        mark(ph_addr);
      }
    }
  }
  // TODO
}

static void sweep() {
/*
traverses the whole heap sequentially, looking for unmarked objects and adding them to the free list.
Notice that unreachable objects cannot become reachable again.
It is therefore possible to sweep objects on demand, to only fulfill the current memory need.
Set free_list_heads all to memory_start
*/
  
  free_list_heads[FREE_LISTS_COUNT-1] = memory_start;
  value_t* sweep_ptr = heap_first_block;

  while(sweep_ptr < heap_end){
    
    tag_t tag_first = memory_get_block_tag(sweep_ptr);   
    int bit_first = bitmap_is_bit_set(sweep_ptr);

    if((tag_first == tag_None) || (tag_first != tag_None && bit_first == 1)){ //can be col
      value_t total_size = memory_get_block_size(sweep_ptr);
      value_t* next_sweep = sweep_ptr + total_size + 1; //next block

      while(next_sweep < heap_end){ 
        tag_t tag_second = memory_get_block_tag(next_sweep);
        int bit_second = bitmap_is_bit_set(next_sweep);

        if((tag_second == tag_None) || (tag_second != tag_None && bit_second == 1)){
          total_size += memory_get_block_size(next_sweep) + 1;
          next_sweep += memory_get_block_size(next_sweep) + 1;
        }
        else break;
      }
      sweep_ptr[-1] = header_pack(tag_None, total_size); //problem
      sweep_ptr[0] = addr_p_to_v(free_list_heads[FREE_LISTS_COUNT-1]);
      free_list_heads[FREE_LISTS_COUNT-1] = sweep_ptr;
      sweep_ptr = next_sweep;
    }
    else if(tag_first != tag_None && bit_first == 0){
      bitmap_set_bit(sweep_ptr);
      sweep_ptr += memory_get_block_size(sweep_ptr) + 1;
    }
  }  
  // TODO
}

value_t* memory_allocate(tag_t tag, value_t size) {
  value_t* first_try = allocate(tag, size);
  if (first_try != NULL)
    return first_try;

  value_t* lb = engine_get_Lb();
  if (lb != memory_start) mark(lb);
  value_t* ib = engine_get_Ib();
  if (ib != memory_start) mark(ib);
  value_t* ob = engine_get_Ob();
  if (ob != memory_start) mark(ob);

  sweep();

  value_t* second_try = allocate(tag, size);
  if (second_try != NULL)
    return second_try;

  fail("\ncannot allocate %d words of memory, even after GC\n", size);
}

value_t memory_get_block_size(value_t* block) {
  return header_unpack_size(block[-1]);
}

tag_t memory_get_block_tag(value_t* block) {
  return header_unpack_tag(block[-1]);
}

#endif
