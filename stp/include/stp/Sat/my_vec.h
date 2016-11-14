/**************************************************************************************************
MiniSat -- Copyright (c) 2005, Niklas Sorensson
http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/
// Modified to compile with MS Visual Studio 6.0 by Alan Mishchenko

#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <stdint.h>
enum oper{  
  P_UNDEFINED = 0, // 0
  P_SYMBOL, //1
  P_BVCONST, //2
  P_BVNEG, //3
  P_BVCONCAT, //4
  P_BVOR, //5
  P_BVAND, //6
  P_BVXOR, //7
  P_BVNAND, //8
  P_BVNOR, //9
  P_BVXNOR, //10
  P_BVEXTRACT, //11
  P_BVLEFTSHIFT, //12
  P_BVRIGHTSHIFT, //13
  P_BVSRSHIFT, //14
  P_BVVARSHIFT, //15
  P_BVPLUS, //16
  P_BVSUB, //17
  P_BVUMINUS, //18
  P_BVMULTINVERSE, //19
  P_BVMULT, //20
  P_BVDIV, //21
  P_BVMOD, //22
  P_SBVDIV, //23
  P_SBVREM, //24
  P_SBVMOD, //25
  P_BVSX, //26
  P_BVZX, //27

  P_BVXOR_DIV, // 28
  P_BTOW, // 29
  P_BVEQUALL, // 30

  P_ITE, //31
  P_BOOLEXTRACT, //32

  P_BVEQ_C, // 33
  P_BVLE_C, // 34

  P_BVLT, //35
  P_BVLE, //36
  P_BVGT, //37
  P_BVGE, //38
  P_BVSLT, //39
  P_BVSLE, //40
  P_BVSGT, //41
  P_BVSGE, //42
  P_EQ, //43
  P_FALSE, //44
  P_TRUE, //45
  P_NOT, //46
  P_AND, //47
  P_OR, //48
  P_NAND, //49
  P_NOR, //50
  P_XOR, //51
  P_IFF, //52
  P_IMPLIES, //53
  P_PARAMBOOL, //54
  P_READ, //55
  P_WRITE, //56
  P_ARRAY, //57
  P_BITVECTOR, //58
  P_BOOLEAN, //59
  };

// vector of 32-bit intergers (added for 64-bit portability)
struct veci_t {
    int    size;
    int    cap;
    int*   ptr;
};
typedef struct veci_t veci;

static inline void veci_new (veci* v) {
    v->size = 0;
    v->cap  = 4;
    v->ptr  = (int*)malloc(sizeof(int)*v->cap);
}

static inline void   veci_delete (veci* v)          { free(v->ptr);   }
static inline int*   veci_begin  (veci* v)          { return v->ptr;  }
static inline int    veci_size   (veci* v)          { return v->size; }
static inline void   veci_resize (veci* v, int k)   { v->size = k;    } // only safe to shrink !!
static inline void   veci_push   (veci* v, int e)
{
    if (v->size == v->cap) {
        int newsize = v->cap * 2+1;
        v->ptr = (int*)realloc(v->ptr,sizeof(int)*newsize);
        v->cap = newsize; }
    v->ptr[v->size++] = e;
}

// vector of 32- or 64-bit pointers
struct ul{ // structure for upper and lower bound

	int word_num;
	unsigned long int lower;
	unsigned long int upper;
};

struct ws_flag{ // structure for propagator

	int oper; // operation kind
	int inqueue_flag; // wether it is in the propagation queue
        int* bitwids; // bit width
	int* arnum; // the variable number of each argument (right[i])
	struct ul **argu; // lower and upper bound for each argument
	unsigned long int *bound; // param[i]
}; 

struct vecp_t { // structure for vector

    int size;
    int cap;
    int word_num;
    void** ptr;
    
};
typedef struct vecp_t vecp;


static inline void vecp_new (vecp* v) { // new a vector
    v->size = 0;
    v->cap  = 4;
    v->ptr  = (void**)malloc(sizeof(void*)*v->cap);
    v->word_num = -1;
}

static inline void   vecp_delete (vecp* v)          { free(v->ptr); }
static inline void** vecp_begin  (vecp* v)          { return v->ptr;  }
static inline int    vecp_size   (vecp* v)          { return v->size; }
static inline void   vecp_resize (vecp* v, int   k) { v->size = k;  } // only safe to shrink !!

static inline void   vecp_push(vecp* v, void* e)
{
    if (v->size == v->cap) {
        int newsize = v->cap * 2+1;
        v->ptr = (void**)realloc(v->ptr,sizeof(void*)*newsize);
        v->cap = newsize; 
    }
    v->ptr[v->size] = e;
    v->size++;
}

static inline void   vecp_push_prop(vecp* v, struct ws_flag* e)
{
    if (v->size == v->cap) {
        int newsize = v->cap * 2+1;
        v->ptr = (void**)realloc(v->ptr,sizeof(void*)*newsize);
        v->cap = newsize; 
    }
    v->ptr[v->size] = (void *)(((uintptr_t)e) |(uint64_t)2);
    v->size++;
}

static inline void set_word_num (vecp* wl, int a)
{
	wl->word_num =a;
}

static inline int get_word_num(vecp* wl)
{
	return wl->word_num;
}

static inline unsigned long int check_valid_word(unsigned long int l,unsigned long int u)
{
    unsigned long int a;
    a=(~l)|u;
    return a; 
}

