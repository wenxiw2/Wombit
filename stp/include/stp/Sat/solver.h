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


#ifdef _WIN32
#define inline __inline // compatible with MS VS 6.0
#endif

#include "stp/Sat/my_vec.h"
#include <stdint.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>

//=================================================================================================
// Simple types:

// does not work for c++

//int clk;
typedef int  lit;
typedef char  lbool;

#ifdef _WIN32
typedef signed __int64     uint64;   // compatible with MS VS 6.0
#else
typedef unsigned long long uint64;
#endif

// global variable used between the parser and the word-level solver
int varnum; // number of literals (including boolean variables, the bits in the bit-vector, and intermediate variables)
int prop_num; // number of propagators 
int composed_flag; // flag to indicate composed method or decomposed method
int word_num; // number of the bit-vectors
lbool st; // status indicates the formula SAT or UNSAT
int If_Bwlistprop; // swich the solver_propagate function

// features of the machine learning model
int const_num; // number of
int symbool_num; // number of boolean variables
int symvec_num; // number of

int whole_num; // for all bit-vector operations
int form_num; // number of boolean operations
int logic_num; // number of logic operations
int arith_num; // number of arithmetic operations

int eq_num; // number of equaility operations
int ineq_num; // number of inequality operations 
int ite_num;  // number of if-then-else operations
int bitwise_num; // number of bitwise operations (bvand, bvor, bvxor, bvnand, bvnor, bvnxor, beneg)
int sign_num; // number of signed operations (signed extension, arithmetic right shift)
int extcon_num; // number of extraction and concatenation operations
int extend_num; // number of extension operations
int shift_con_num; // number of shift operations by constant number
int shift_noncon_num; // number of shift operations by bit-vector variable
int mult_num; // number of multiplication operations
int bvplus_num; // number of addition operations
int uminus_num; // number of unary minus operations
int bvsub_num; // number of subtraction operations
int mult_con_num; // number of multiplication operation with both non constant operands
int udiv_num; // number of unsigned division operations
int div_num; // number of signed division operations  

int whole_bitwid; // average bit width of all the bit-vector operations
int logic_bitwid; // average bit width of all the logic operations
int arith_bitwid; // average bit width of all the arithmetic operations

static const int   var_Undef = -1;
static const lit   lit_Undef = -2;

static const lbool l_Undef = 0;
static const lbool l_True = 1;
static const lbool l_False = -1;

static inline lit  toLit(int v) { return v + v; }
static inline lit  lit_neg(lit l) { return l ^ 1; }
static inline int  lit_var(lit l) { return l >> 1; }
static inline int  lit_sign(lit l) { return (l & 1); }

//=================================================================================================
// Public interface:

struct solver_t;
typedef struct solver_t solver;

solver* solver_new(void);
void    solver_delete(solver* s);

int    solver_addclause(solver* s, lit* begin, lit* end);
int    solver_simplify(solver* s);
int    solver_solve(solver* s, lit* begin, lit* end);

int     solver_nvars(solver* s);
int     solver_nclauses(solver* s);
int     solver_nconflicts(solver* s);

void    solver_setnvars(solver* s, int n);

struct stats_t {
	uint64   starts, decisions, propagations, inspects, conflicts;
	uint64   clauses, clauses_literals, learnts, learnts_literals, max_literals, tot_literals;
};
//typedef struct stats_t stats;

//=================================================================================================
// Solver representation:

struct clause_t;
typedef struct clause_t clause;

struct solver_t {
	int      size;          // nof variables
	int      cap;           // size of varmaps
	int      wordcap;
	int      propcap;
	int      qhead;         // Head index of queue.
	int      qtail;         // Tail index of queue.
	int      proph;         // head index of propagator queue;
	int      propt;	    // tail index of propagator queue;


	// clauses
	vecp     clauses;       // List of problem constraints. (contains: clause*)
	vecp     learnts;       // List of learnt clauses. (contains: clause*)
	vecp     prop_stock;    // List of the word-level propagators. (contains: propagator*)

	// activities
	double   var_inc;       // Amount to bump next variable with.
	double   var_decay;     // INVERSE decay factor for variable activity: stores 1/decay.
	float    cla_inc;       // Amount to bump next clause with.
	float    cla_decay;     // INVERSE decay factor for clause activity: stores 1/decay.

	vecp*    wlists;        //
	vecp*    word_info;     // store word's upper and lower bound, and contain the word level propagators.
	double*  activity;      // A heuristic measurement of the activity of a variable.
	lbool*   assigns;       // Current values of variables.
	lbool*   fixpoints;
	int*     orderpos;      // Index in variable order.
	int*     index;
	void**   reasons;       //
	int*     levels;        //
	lit*     trail;
	struct ws_flag** prop_que;     // propagator queue;    
	int*     pos;
	int*     varorder;

	clause*  binary;        // A temporary binary clause
	lbool*   tags;          //
	veci     tagged;        // (contains: var)
	veci     stack;         // (contains: var)

	veci     order;         // Variable order. (heap) (contains: var)
	veci     trail_lim;     // Separator indices for different decision levels in 'trail'. (contains: int)
	veci     model;         // If problem is solved, this vector contains the model (contains: lbool).

	int      root_level;    // Level of first proper decision.
	int      simpdb_assigns;// Number of top-level assignments at last 'simplifyDB()'.
	int      simpdb_props;  // Number of propagations before next 'simplifyDB()'.
	double   random_seed;
	double   progress_estimate;
	int      verbosity;     // Verbosity level. 0=silent, 1=some progress report, 2=everything

	stats_t    stats;
};

static inline vecp*   solver_read_wlist(solver* s, lit l) { return &s->wlists[l]; }
static inline void check(int expr) { assert(expr); }

void explanation_generator(solver* s, lit v, struct ws_flag* i, clause** c);
void propagator_solving(solver *s, vecp* confl_vecp);
//=================================================================================================
// Random numbers:


// Returns a random float 0 <= x < 1. Seed must never be 0.
static inline double drand(double* seed) {
	int q;
	*seed *= 1389796;
	q = (int)(*seed / 2147483647);
	*seed -= (double)q * 2147483647;
	return *seed / 2147483647;
}


// Returns a random integer 0 <= x < size. Seed must never be 0.
static inline int irand(double* seed, int size) {
	return (int)(drand(seed) * size);
}


//=================================================================================================
// Predeclarations:

void sort(void** array, int size, int(*comp)(const void *, const void *));

//=================================================================================================
// Clause datatype + minor functions:

struct clause_t {
	int size_learnt;
	int flag;
	lit lits[0];
};

static inline int   clause_size(clause* c) { return c->size_learnt >> 1; }
static inline lit*  clause_begin(clause* c) { return c->lits; }
static inline int   clause_learnt(clause* c) { return c->size_learnt & 1; }
static inline float clause_activity(clause* c) { return *((float*)&c->lits[c->size_learnt >> 1]); }
static inline void  clause_setactivity(clause* c, float a) { *((float*)&c->lits[c->size_learnt >> 1]) = a; }

//=================================================================================================
// Encode literals in clause pointers:
clause* clause_from_lit(lit l) { return (clause*)((unsigned long)l + (unsigned long)l + 1); }
int    clause_is_lit(clause* c) { return ((unsigned long)c & 1); }
lit     clause_read_lit(clause* c) { return (lit)((unsigned long)c >> 1); }

//=================================================================================================
// Simple helpers:

static inline int     solver_dlevel(solver* s) { return veci_size(&s->trail_lim); }
//static inline vecp*   solver_read_wlist     (solver* s, lit l){ return &s->wlists[l]; }
static inline void    vecp_remove(vecp* v, void* e) {
	void** ws = vecp_begin(v);
	int    j = 0;

	for (; ws[j] != e; j++);
	assert(j < vecp_size(v));
	for (; j < vecp_size(v) - 1; j++) ws[j] = ws[j + 1];
	vecp_resize(v, vecp_size(v) - 1);
}


//=================================================================================================
// Variable order functions:

static inline void order_update(solver* s, int v) // updateorder
{
	int*    orderpos = s->orderpos;
	double* activity = s->activity;
	int*    heap = veci_begin(&s->order);
	int     i = orderpos[v];
	int     x = heap[i];
	int     parent = (i - 1) / 2;

	assert(s->orderpos[v] != -1);

	while (i != 0 && activity[x] > activity[heap[parent]]) {
		heap[i] = heap[parent];
		orderpos[heap[i]] = i;
		i = parent;
		parent = (i - 1) / 2;
	}
	heap[i] = x;
	orderpos[x] = i;
}

static inline void order_unassigned(solver* s, int v) // undoorder
{
	int* orderpos = s->orderpos;
	if (orderpos[v] == -1) {
		orderpos[v] = veci_size(&s->order);
		veci_push(&s->order, v);
		order_update(s, v);
	}
}
static int  order_select(solver* s, float random_var_freq) // selectvar
{

	int*    heap;
	double* activity;
	int*    orderpos;
	//int next;

	lbool* values = s->assigns;

	if (drand(&s->random_seed) < random_var_freq) {

		int next = irand(&s->random_seed, s->size);
		assert(next >= 0 && next < s->size);
		if (values[next] == l_Undef) {
			return next;
		}
	}

	// Activity based decision:

	heap = veci_begin(&s->order);
	activity = s->activity;
	orderpos = s->orderpos;
	while (veci_size(&s->order) > 0) {
		int    next = heap[0];
		int    size = veci_size(&s->order) - 1;
		int    x = heap[size];

		veci_resize(&s->order, size);

		orderpos[next] = -1;

		if (size > 0) {
			double act = activity[x];

			int    i = 0;
			int    child = 1;
			while (child < size) {
				if (child + 1 < size && activity[heap[child]] < activity[heap[child + 1]])
					child++;
				assert(child < size);
				if (act >= activity[heap[child]])
					break;
				heap[i] = heap[child];
				orderpos[heap[i]] = i;
				i = child;
				child = 2 * child + 1;
			}
			heap[i] = x;
			orderpos[heap[i]] = i;
		}

		if (values[next] == l_Undef) {

			return next;
		}
	}
	return var_Undef;
}

//=================================================================================================
// Activity functions:

static inline void act_var_rescale(solver* s) {
	double* activity = s->activity;
	int i;
	for (i = 0; i < s->size; i++)
		activity[i] *= 1e-100;
	s->var_inc *= 1e-100;
}

static inline void act_var_bump(solver* s, int v) {
	double* activity = s->activity;
	if ((activity[v] += s->var_inc) > 1e100)
		act_var_rescale(s);

	if (s->orderpos[v] != -1)
		order_update(s, v);

}

static inline void act_var_decay(solver* s) { s->var_inc *= s->var_decay; }  //decay the score for variables

static inline void act_clause_rescale(solver* s) {
	clause** cs = (clause**)vecp_begin(&s->learnts);
	int i;
	for (i = 0; i < vecp_size(&s->learnts); i++) {
		float a = clause_activity(cs[i]);
		clause_setactivity(cs[i], a * (float)1e-20);
	}
	s->cla_inc *= (float)1e-20;
}


static inline void act_clause_bump(solver* s, clause *c) {
	float a = clause_activity(c) + s->cla_inc;
	clause_setactivity(c, a);
	if (a > 1e20) act_clause_rescale(s);
}

static inline void act_clause_decay(solver* s) { s->cla_inc *= s->cla_decay; }


//=================================================================================================
// Clause functions:

static clause* clause_new(solver* s, lit* begin, lit* end, int learnt) {
	int size;
	clause* c;
	int i;

	assert(end - begin > 1);
	assert(learnt >= 0 && learnt < 2);
	size = end - begin;
	c = (clause*)malloc(sizeof(clause) + sizeof(int) + sizeof(lit) * size + learnt * sizeof(float));
	c->size_learnt = (size << 1) | learnt;
	c->flag = 0;
	assert(((unsigned long int)c & 1) == 0);


	for (i = 0; i < size; i++) {
		c->lits[i] = begin[i];
	}


	if (learnt)
		*((float*)&c->lits[size]) = 0.0;

	assert(begin[0] >= 0);
	assert(begin[0] < s->size * 2);
	assert(begin[1] >= 0);
	assert(begin[1] < s->size * 2);

	assert(lit_neg(begin[0]) < s->size * 2);
	assert(lit_neg(begin[1]) < s->size * 2);


	vecp_push(solver_read_wlist(s, lit_neg(begin[0])), (void*)(size > 2 ? c : clause_from_lit(begin[1])));
	vecp_push(solver_read_wlist(s, lit_neg(begin[1])), (void*)(size > 2 ? c : clause_from_lit(begin[0])));

	return c;
}


static void clause_remove(solver* s, clause* c) {

	lit* lits = clause_begin(c);

	assert(lit_neg(lits[0]) < s->size * 2);
	assert(lit_neg(lits[1]) < s->size * 2);

	assert(lits[0] < s->size * 2);

	vecp_remove(solver_read_wlist(s, lit_neg(lits[0])), (void*)(clause_size(c) > 2 ? c : clause_from_lit(lits[1])));
	vecp_remove(solver_read_wlist(s, lit_neg(lits[1])), (void*)(clause_size(c) > 2 ? c : clause_from_lit(lits[0])));

	if (clause_learnt(c)) {
		s->stats.learnts--;
		s->stats.learnts_literals -= clause_size(c);
	}
	else {
		s->stats.clauses--;
		s->stats.clauses_literals -= clause_size(c);
	}

	free(c);

}


static lbool clause_simplify(solver* s, clause* c) {
	lit*   lits = clause_begin(c);
	lbool* values = s->assigns;
	int i;

	assert(solver_dlevel(s) == 0);

	for (i = 0; i < clause_size(c); i++) {
		lbool sig = !lit_sign(lits[i]); sig += sig - 1;
		if (values[lit_var(lits[i])] == sig)
			return l_True;
	}
	return l_False;
}

//=================================================================================================
// Minor (solver) functions:

void solver_setnvars(solver* s, int n) {
	int var;

	if (s->cap < n) {

		while (s->cap < n) s->cap = s->cap * 2 + 1;

		s->wlists = (vecp*)realloc(s->wlists, sizeof(vecp)*s->cap * 2);
		s->activity = (double*)realloc(s->activity, sizeof(double)*s->cap);
		s->assigns = (lbool*)realloc(s->assigns, sizeof(lbool)*s->cap);
		s->orderpos = (int*)realloc(s->orderpos, sizeof(int)*s->cap);
		s->reasons = (void**)realloc(s->reasons, sizeof(clause*)*s->cap);
		s->levels = (int*)realloc(s->levels, sizeof(int)*s->cap);
		s->tags = (lbool*)realloc(s->tags, sizeof(lbool)*s->cap);
		s->trail = (lit*)realloc(s->trail, sizeof(lit)*s->cap);
		s->index = (int*)realloc(s->index, sizeof(int)*s->cap);
		s->pos = (int*)realloc(s->pos, sizeof(int)*s->cap);
		s->varorder = (int*)realloc(s->varorder, sizeof(int)*s->cap);

	}

	for (var = s->size; var < n; var++) {
		vecp_new(&s->wlists[2 * var]);
		vecp_new(&s->wlists[2 * var + 1]);
		s->activity[var] = 0;
		s->assigns[var] = l_Undef;
		s->orderpos[var] = veci_size(&s->order);
		s->reasons[var] = (clause*)0;
		s->levels[var] = 0;
		s->tags[var] = l_Undef;
		s->index[var] = -1;
		s->pos[var] = -1;
		s->varorder[var] = -1;

		veci_push(&s->order, var);
		order_update(s, var);
	}             

	s->size = n > s->size ? n : s->size;
}

void enqueue_prop(solver*s, int var1) {
	int size = s->word_info[var1].size; int i;
	struct ws_flag** begin = (struct ws_flag**)vecp_begin(&s->word_info[var1]);
	for (i = 1;i < size; i++) {                // go through the proagators of this integer var1, to enqueue the fresh propagators
		if (begin[i]->inqueue_flag == -1) {
			s->prop_que[s->propt] = begin[i];	// enqueue the fresh propagator to the propagator queue	
			begin[i]->inqueue_flag = 1;			// mark it as enqueued propagator
			s->propt = (s->propt + 1) % prop_num;
		}
	}
}

void enqueue_prop_pure(solver*s, struct ws_flag *ws) {
	if (ws->inqueue_flag == -1) {
		s->prop_que[s->propt] = ws;	// enqueue the fresh propagator to the propagator queue	
		ws->inqueue_flag = 1;			// mark it as enqueued propagator
		s->propt = (s->propt + 1) % prop_num;
	}
}


void enqueue(solver* s, lit l, void* from, int varorder)  // enqueue function inside the word level propagators
{
	lbool* values = s->assigns;
	int    v = lit_var(l);

	assert(values[v] == l_Undef);
	if (l & 1)
		values[v] = l_False;
	else
		values[v] = l_True;

	s->levels[v] = solver_dlevel(s);
	s->reasons[v] = (void *)(((uintptr_t)from) | (uint64_t)2);
	s->pos[v] = s->qtail;
	s->trail[s->qtail++] = l;
	s->varorder[v] = varorder;
	//order_assigned(s, v);
}

static inline int enqueue_bool(solver* s, lit l, clause* from)   // enqueue function for boolean vars in word level propagator
{
	lbool* values = s->assigns;
	int    v = lit_var(l);

	assert(values[v] == l_Undef);
	if (l & 1)
		values[v] = l_False;
	else
		values[v] = l_True;

	s->levels[v] = solver_dlevel(s);
	s->reasons[v] = from;
	s->pos[v] = s->qtail;
	s->trail[s->qtail++] = l;
	//order_assigned(s, v);

	return true;

}

void enqueue_bit(solver* s, lit l, void* from)   // enqueue function outside the word level propagators (update the uplo)
{
	lbool* values = s->assigns;
	int    v = lit_var(l);

	assert(values[v] == l_Undef);
	if (l & 1)
		values[v] = l_False;
	else
		values[v] = l_True;

	s->levels[v] = solver_dlevel(s);
	s->reasons[v] = (void *)(((uintptr_t)from) | (uint64_t)2);
	s->pos[v] = s->qtail;
	s->trail[s->qtail++] = l;
	//order_assigned(s, v);

	int word_num = get_word_num(solver_read_wlist(s, toLit(v)));

	if (word_num != -1) {
		struct ul *uplw; int index; // unsigned long int ll,uu;

		uplw = (struct ul *)vecp_begin(&s->word_info[word_num])[0];

		if (((uintptr_t)uplw & (uint64_t)1) == 0) {   // integer      			
			index = s->index[v];
			if (values[v] == l_True) {
				uplw->lower = uplw->lower | (((uint64_t)1) << index);
			}
			else {
				uplw->upper = uplw->upper & (~(((uint64_t)1) << index));

			}
		}
		enqueue_prop(s, word_num);
	}
}

// enqueue function outside the word level propagators (update the uplo)
static inline int enqueue_org(solver* s, lit l, clause* from)   
{
	lbool* values = s->assigns;
	int    v = lit_var(l);
	lbool  val = values[v];

	lbool sig = !lit_sign(l); sig += sig - 1;
	if (val != l_Undef) {
		return val == sig;
	}
	else {
		// New fact -- store it.
		int*     levels = s->levels;
		int*     ids = s->index;
		clause** reasons = (clause **)s->reasons;

		values[v] = sig;

		levels[v] = solver_dlevel(s);
		reasons[v] = from;
		s->pos[v] = s->qtail;
		s->trail[s->qtail++] = l;
		//order_assigned(s, v);

		int word_num = get_word_num(solver_read_wlist(s, toLit(v)));


		if (word_num != -1) {
			struct ul *uplw; int index;// unsigned long int ll,uu;

			uplw = (struct ul *) vecp_begin(&s->word_info[word_num])[0];

			if (((uintptr_t)uplw & (uint64_t)1) == 0) {   // integer
				index = ids[v];
				if (values[v] == l_True) {
					uplw->lower = uplw->lower | (((uint64_t)1) << index);
				}
				else {
					uplw->upper = uplw->upper & (~(((uint64_t)1) << index));
				}
			}
			enqueue_prop(s, word_num);
		}
		return true;
	}
}

static inline void assume(solver* s, lit l) {
	assert(s->propt == s->proph);
	assert(s->qtail == s->qhead);
	assert(s->assigns[lit_var(l)] == l_Undef);

	veci_push(&s->trail_lim, s->qtail);

	enqueue_org(s, l, (clause*)0);
}

void solver_canceluntil(solver* s, int level) {

	lit*     trail;
	lbool*   values;
	clause** reasons;
	int      bound;
	int      c;

	if (solver_dlevel(s) <= level)
		return;

	trail = s->trail;
	values = s->assigns;
	reasons = (clause **)s->reasons;
	bound = (veci_begin(&s->trail_lim))[level];
	int* ids = s->index;

	struct ul *uplw; int index; int x, l; int word_num; //unsigned int ll,uu;
	for (c = s->qtail - 1; c >= bound; c--) {
		l = trail[c];
		x = lit_var(l);

		word_num = get_word_num(solver_read_wlist(s, l));

		if (word_num != -1) {
			uplw = (struct ul *)vecp_begin(&s->word_info[word_num])[0];
			if (((uintptr_t)uplw & (uint64_t)1) == 0)   // integer, not the x of ite
			{
				index = ids[x];

				if (values[x] == l_True) {
					uplw->lower = uplw->lower & (~((uint64_t)1 << index));
				}
				else {
					uplw->upper = uplw->upper | ((uint64_t)1 << index);
				}
			}
		}

		values[x] = l_Undef;
		if (reasons[x] != (clause*)0 && (((uintptr_t)reasons[x])&(uint64_t)3) == 0 && reasons[x]->flag != 0) {
			free(reasons[x]);
		}
		else {
			reasons[x] = (clause*)0;
		}
	}

	for (c = s->qhead - 1; c >= bound; c--)
		order_unassigned(s, lit_var(trail[c]));

	struct ws_flag** prop_que = s->prop_que;
	while (s->propt != s->proph) {
		(prop_que[s->proph])->inqueue_flag = -1;
		s->proph = (s->proph + 1) % prop_num;
	}

	s->qhead = s->qtail = bound;
	veci_resize(&s->trail_lim, level);
}

static clause* solver_record_learnt(solver* s, veci* cls) {
	lit*    begin = veci_begin(cls);
	lit*    end = begin + veci_size(cls);
	clause* c = (veci_size(cls) > 1) ? clause_new(s, begin, end, 1) : (clause*)0;

	assert(veci_size(cls) > 0);

	if (c != 0) {
		vecp_push(&s->learnts, c);
		act_clause_bump(s, c);
		s->stats.learnts++;
		s->stats.learnts_literals += veci_size(cls);
	}
	return c;
}


static double solver_progress(solver* s) {
	lbool*  values = s->assigns;
	int*    levels = s->levels;
	int     i;

	double  progress = 0;
	double  F = 1.0 / s->size;
	for (i = 0; i < s->size; i++)
		if (values[i] != l_Undef)
			progress += pow(F, levels[i]);
	return progress / s->size;
}

//=================================================================================================
// Major methods:
static int solver_lit_removable(solver* s, lit l, int minl) {
	lbool*   tags = s->tags;
	clause** reasons = (clause **)s->reasons;
	int*     levels = s->levels;
	int      top = veci_size(&s->tagged);

	assert(lit_var(l) >= 0 && lit_var(l) < s->size);
	assert(reasons[lit_var(l)] != 0);
	veci_resize(&s->stack, 0);
	veci_push(&s->stack, lit_var(l));

	while (veci_size(&s->stack) > 0) {
		clause* c;
		int v = veci_begin(&s->stack)[veci_size(&s->stack) - 1];
		assert(v >= 0 && v < s->size);
		veci_resize(&s->stack, veci_size(&s->stack) - 1);
		assert(reasons[v] != 0);

		if (((uintptr_t)reasons[v] & (uint64_t)3) == 2) {
			explanation_generator(s, v, (struct ws_flag*)((uintptr_t)reasons[v] & (~((uint64_t)3))), &reasons[v]);
		}

		c = reasons[v];

		if (clause_is_lit(c)) {
			int v = lit_var(clause_read_lit(c));

			if (tags[v] == l_Undef && levels[v] != 0) {
				if (reasons[v] != 0 && ((1 << (levels[v] & 31)) & minl)) {
					veci_push(&s->stack, v);
					tags[v] = l_True;
					veci_push(&s->tagged, v);
				}
				else {
					int* tagged = veci_begin(&s->tagged);
					int j;
					for (j = top; j < veci_size(&s->tagged); j++)
						tags[tagged[j]] = l_Undef;
					veci_resize(&s->tagged, top);
					return false;
				}
			}
		}
		else {
			lit*    lits = clause_begin(c);
			int     i, j;

			for (i = 1; i < clause_size(c); i++) {
				int v = lit_var(lits[i]);

				if (tags[v] == l_Undef && levels[v] != 0) {
					if (reasons[v] != 0 && ((1 << (levels[v] & 31)) & minl)) {

						veci_push(&s->stack, lit_var(lits[i]));
						tags[v] = l_True;
						veci_push(&s->tagged, v);
					}
					else {
						int* tagged = veci_begin(&s->tagged);
						for (j = top; j < veci_size(&s->tagged); j++)
							tags[tagged[j]] = l_Undef;
						veci_resize(&s->tagged, top);
						return false;
					}
				}
			}
		}
	}

	return true;
}

static void solver_analyze(solver* s, clause* c, veci* learnt) {
	lit*     trail = s->trail;
	lbool*   tags = s->tags;
	clause** reasons = (clause **)s->reasons;
	int*     levels = s->levels;
	int      cnt = 0;
	lit      p = lit_Undef;
	int      ind = s->qtail - 1;
	lit*     lits;
	int      i, j, minl;
	int*     tagged;
	int v;
	veci_push(learnt, lit_Undef);

	do {
		assert(c != 0);

		if (clause_is_lit(c)) {

			lit q = clause_read_lit(c);
			assert(lit_var(q) >= 0 && lit_var(q) < s->size);

			if (tags[lit_var(q)] == l_Undef && levels[lit_var(q)] > 0) {
				tags[lit_var(q)] = l_True;
				veci_push(&s->tagged, lit_var(q));
				act_var_bump(s, lit_var(q));
				if (levels[lit_var(q)] == solver_dlevel(s)) {
					cnt++;
				}
				else {
					veci_push(learnt, q);
				}
			}
		}
		else {

			if (clause_learnt(c))
				act_clause_bump(s, c);

			lits = clause_begin(c);
			for (j = (p == lit_Undef ? 0 : 1); j < clause_size(c); j++) {
				lit q = lits[j];

				assert(lit_var(q) >= 0 && lit_var(q) < s->size);

				if (tags[lit_var(q)] == l_Undef && levels[lit_var(q)] > 0) {


					tags[lit_var(q)] = l_True;

					veci_push(&s->tagged, lit_var(q));
					act_var_bump(s, lit_var(q));
					if (levels[lit_var(q)] == solver_dlevel(s)) {
						cnt++;
					}
					else
						veci_push(learnt, q);
				}
			}
		}
		while (tags[lit_var(trail[ind--])] == l_Undef);

		p = trail[ind + 1];
		v = lit_var(p);

		// if the reason is fake (a propagator), use the propagator to generate the explanation 
		if (((uintptr_t)reasons[v] & (uint64_t)3) == 2) {
			explanation_generator(s, v, (struct ws_flag*)((uintptr_t)reasons[v] & (~((uint64_t)(3)))), &reasons[v]);
		}

		c = reasons[v];
		cnt--;

	} while (cnt > 0);

	*veci_begin(learnt) = lit_neg(p);

	lits = veci_begin(learnt);
	minl = 0;
	for (i = 1; i < veci_size(learnt); i++) {
		int lev = levels[lit_var(lits[i])];
		minl |= 1 << (lev & 31);
	}


	for (i = j = 1; i < veci_size(learnt); i++) {
		if (reasons[lit_var(lits[i])] == 0 || !solver_lit_removable(s, lits[i], minl))
			lits[j++] = lits[i];
	}

	// update size of learnt + statistics
	s->stats.max_literals += veci_size(learnt);
	veci_resize(learnt, j);
	s->stats.tot_literals += j;

	// clear tags
	tagged = veci_begin(&s->tagged);
	for (i = 0; i < veci_size(&s->tagged); i++)
		tags[tagged[i]] = l_Undef;
	veci_resize(&s->tagged, 0);

#ifdef DEBUG
	for (i = 0; i < s->size; i++)
		assert(tags[i] == l_Undef);
#endif


	if (veci_size(learnt) > 1) {
		int max_i = 1;
		int max = levels[lit_var(lits[1])];
		lit tmp;

		for (i = 2; i < veci_size(learnt); i++)
			if (levels[lit_var(lits[i])] > max) {
				max = levels[lit_var(lits[i])];
				max_i = i;
			}

		tmp = lits[1];
		lits[1] = lits[max_i];
		lits[max_i] = tmp;
	}

#ifdef VERBOSEDEBUG
	{
		int lev = veci_size(learnt) > 1 ? levels[lit_var(lits[1])] : 0;
		printf(" } at level %d\n", lev);
	}
#endif
}


vecp solver_propagate_Bwlistprop(solver* s) {
	lbool*  values = s->assigns;
	clause* confl;
	vecp confl_vecp;
	vecp_new(&confl_vecp);
	lit*    lits;

	do {
		while (vecp_size(&confl_vecp) == 0 && s->qtail - s->qhead > 0) // no conflict and the literal queue is not empty
		{
			lit  p = s->trail[s->qhead++];
			vecp* ws = solver_read_wlist(s, p);

			void** begin = vecp_begin(ws);
			void** end = begin + vecp_size(ws);
			void **i, **j;
			s->stats.propagations++;
			s->simpdb_props--;

			for (i = j = begin; i < end;) {
				if (((uintptr_t)(*i) & (uint64_t)3) != ((uint64_t)2)) {
					if (clause_is_lit((clause*)(*i))) {
						*j++ = *i;
						if (!enqueue_org(s, clause_read_lit((clause*)(*i)), clause_from_lit(p))) {
							confl = s->binary;
							(clause_begin(confl))[1] = lit_neg(p);
							(clause_begin(confl))[0] = clause_read_lit((clause*)(*i++));
							vecp_push(&confl_vecp, confl);
							// Copy the remaining watches:
							while (i < end)
								*j++ = *i++;
						}
					}
					else {
						lit false_lit;
						lbool sig;

						lits = clause_begin((clause*)(*i));

						// Make sure the false literal is data[1]:
						false_lit = lit_neg(p);
						if (lits[0] == false_lit) {
							lits[0] = lits[1];
							lits[1] = false_lit;
						}
						assert(lits[1] == false_lit);

						// If 0th watch is true, then clause is already satisfied.
						sig = !lit_sign(lits[0]); sig += sig - 1;
						if (values[lit_var(lits[0])] == sig) {
							*j++ = *i;
						}
						else {
							// Look for new watch:
							lit* stop = lits + clause_size((clause*)(*i));
							lit* k;
							for (k = lits + 2; k < stop; k++) {
								lbool sig = lit_sign(*k); sig += sig - 1;
								if (values[lit_var(*k)] != sig) {
									lits[1] = *k;
									*k = false_lit;
									vecp_push(solver_read_wlist(s, lit_neg(lits[1])), *i);
									goto next;
								}
							}

							*j++ = *i;
							// Clause is unit under assignment:
							if (!enqueue_org(s, lits[0], (clause*)(*i))) {

								confl = (clause*)(*i++);
								vecp_push(&confl_vecp, confl);
								// Copy the remaining watches:
								while (i < end)
									*j++ = *i++;
							}
						}
					}
				}
				else {
					enqueue_prop_pure(s, (struct ws_flag*)((uintptr_t)(*i) &(~((uint64_t)(3))))); // enqueue the bwlist propagator
					*j++ = *i;
				}
			next:
				i++;
			}
			s->stats.inspects += j - vecp_begin(ws);
			vecp_resize(ws, j - vecp_begin(ws));
		}

		propagator_solving(s, &confl_vecp);
	} while (vecp_size(&confl_vecp) == 0 && s->qtail - s->qhead > 0); // no conflict and the literal queue is not empty

	return confl_vecp;
}

vecp solver_propagate_NonBwlistprop(solver* s) {
	lbool*  values = s->assigns;
	clause* confl;
	vecp confl_vecp;
	vecp_new(&confl_vecp);
	lit*    lits;

	do {
		while (vecp_size(&confl_vecp) == 0 && s->qtail - s->qhead > 0) {
			lit  p = s->trail[s->qhead++];
			vecp* ws = solver_read_wlist(s, p);

			void** begin = vecp_begin(ws);
			void** end = begin + vecp_size(ws);
			void **i, **j;
			s->stats.propagations++;
			s->simpdb_props--;

			for (i = j = begin; i < end;) {
				if (clause_is_lit((clause*)(*i))) {
					*j++ = *i;
					if (!enqueue_org(s, clause_read_lit((clause*)(*i)), clause_from_lit(p))) {
						confl = s->binary;
						(clause_begin(confl))[1] = lit_neg(p);
						(clause_begin(confl))[0] = clause_read_lit((clause*)(*i++));
						vecp_push(&confl_vecp, confl);
						// Copy the remaining watches:
						while (i < end)
							*j++ = *i++;
					}
				}
				else {
					lit false_lit;
					lbool sig;

					lits = clause_begin((clause*)(*i));

					// Make sure the false literal is data[1]:
					false_lit = lit_neg(p);
					if (lits[0] == false_lit) {
						lits[0] = lits[1];
						lits[1] = false_lit;
					}
					assert(lits[1] == false_lit);

					// If 0th watch is true, then clause is already satisfied.
					sig = !lit_sign(lits[0]); sig += sig - 1;
					if (values[lit_var(lits[0])] == sig) {
						*j++ = *i;
					}
					else {
						// Look for new watch:
						lit* stop = lits + clause_size((clause*)(*i));
						lit* k;
						for (k = lits + 2; k < stop; k++) {
							lbool sig = lit_sign(*k); sig += sig - 1;
							if (values[lit_var(*k)] != sig) {
								lits[1] = *k;
								*k = false_lit;
								vecp_push(solver_read_wlist(s, lit_neg(lits[1])), *i);
								goto next;
							}
						}

						*j++ = *i;
						// Clause is unit under assignment:
						if (!enqueue_org(s, lits[0], (clause*)(*i))) {

							confl = (clause*)(*i++);
							vecp_push(&confl_vecp, confl);
							// Copy the remaining watches:
							while (i < end)
								*j++ = *i++;
						}
					}
				}
			next:
				i++;
			}
			s->stats.inspects += j - vecp_begin(ws);
			vecp_resize(ws, j - vecp_begin(ws));
		}

		propagator_solving(s, &confl_vecp);
	} while (vecp_size(&confl_vecp) == 0 && s->qtail - s->qhead > 0); // no conflict and the literal queue is not empty

	return confl_vecp;
}



static inline int clause_cmp(const void* x, const void* y) {
	return clause_size((clause*)x) > 2 && (clause_size((clause*)y) == 2 || clause_activity((clause*)x) < 
		clause_activity((clause*)y)) ? -1 : 1;
}

void solver_reducedb(solver* s) {
	int      i, j;
	double   extra_lim = s->cla_inc / vecp_size(&s->learnts); // Remove any clause below this activity
	clause** learnts = (clause**)vecp_begin(&s->learnts);
	clause** reasons = (clause **)s->reasons;

	sort(vecp_begin(&s->learnts), vecp_size(&s->learnts), &clause_cmp);

	for (i = j = 0; i < vecp_size(&s->learnts) / 2; i++) {
		if (clause_size(learnts[i]) > 2 && reasons[lit_var(*clause_begin(learnts[i]))] != learnts[i]) {
			clause_remove(s, learnts[i]);
		}
		else
			learnts[j++] = learnts[i];
	}
	for (; i < vecp_size(&s->learnts); i++) {
		if (clause_size(learnts[i]) > 2 && reasons[lit_var(*clause_begin(learnts[i]))] != learnts[i] && 
			clause_activity(learnts[i]) < extra_lim) {
			clause_remove(s, learnts[i]);
		}
		else
			learnts[j++] = learnts[i];
	}

	vecp_resize(&s->learnts, j);
}



static lbool solver_search(solver* s, int nof_conflicts, int nof_learnts) {
	int*    levels = s->levels;
	double  var_decay = 0.95;
	double  clause_decay = 0.999;
	double  random_var_freq = 0.02;
	int     conflictC = 0;
	veci    learnt_clause;
	int i;
	assert(s->root_level == solver_dlevel(s));
	s->stats.starts++;
	s->var_decay = (float)(1 / var_decay);
	s->cla_decay = (float)(1 / clause_decay);
	veci_resize(&s->model, 0);
	veci_new(&learnt_clause);
	vecp confl_vecp;

	for (;;) {

		if (If_Bwlistprop) {
			confl_vecp = solver_propagate_Bwlistprop(s);
		}
		else {
			confl_vecp = solver_propagate_NonBwlistprop(s);
		}

		int confl_size = vecp_size(&confl_vecp);
		if (confl_size != 0) {
			// CONFLICT
			clause** confl_begin = (clause **)vecp_begin(&confl_vecp);
			int blevel;  int minlevel = solver_dlevel(s);  clause* learnt_minclau = 0; lit learnt_minlit = 0;

			s->stats.conflicts++; conflictC++;

			if (solver_dlevel(s) == s->root_level) { // top level conflict -> come to the solution of unsat

				veci_delete(&learnt_clause);

				for (i = 0; i < confl_size; i++) {
					if (confl_begin[i]->flag == 1)
						free(confl_begin[i]);
				}

				vecp_delete(&confl_vecp);
				return l_False;
			}

			for (i = 0; i < confl_size; i++) {
				veci_resize(&learnt_clause, 0);

				solver_analyze(s, confl_begin[i], &learnt_clause); // analyze all the conflict clause
				clause* cc = solver_record_learnt(s, &learnt_clause);  // add all the learnt clause to the clause database

				if (confl_begin[i]->flag == 1) {
					free(confl_begin[i]);  // free the conflict clause
				}
				// choose the smallest backjump level based on the learnt clauses
				if (veci_size(&learnt_clause) > 1) {

					if (levels[lit_var(veci_begin(&learnt_clause)[1])] < minlevel) {
						int* learntc_begin = veci_begin(&learnt_clause); // the begin of learnt clause
						minlevel = levels[lit_var(learntc_begin[1])]; // record the minimal level of in the current

						learnt_minclau = cc; // record the learnt clause for the minimal level in current
						learnt_minlit = learntc_begin[0];
					}
				}
				else {
					minlevel = s->root_level;
					learnt_minclau = cc; // record the learnt clause for the minimal level in current
					learnt_minlit = veci_begin(&learnt_clause)[0];

					i++;
					for (; i < confl_size; i++) {
						if (confl_begin[i]->flag == 1) {
							free(confl_begin[i]);
						}
					}
					break;
				}
			}

			vecp_delete(&confl_vecp);  // delete the conflict clause array

			blevel = minlevel;
			blevel = s->root_level > blevel ? s->root_level : blevel;
			solver_canceluntil(s, blevel);
			enqueue_org(s, learnt_minlit, learnt_minclau);
			act_var_decay(s);
			act_clause_decay(s);
		}
		else {
			// NO CONFLICT
			int next;

			if (nof_conflicts >= 0 && conflictC >= nof_conflicts) {
				// Reached bound on number of conflicts:
				s->progress_estimate = solver_progress(s);
				solver_canceluntil(s, s->root_level);
				veci_delete(&learnt_clause);
				vecp_delete(&confl_vecp);
				return l_Undef;
			}

			if (solver_dlevel(s) == 0)
				// Simplify the set of problem clauses:
			{
				solver_simplify(s);
			}

			if (nof_learnts >= 0 && vecp_size(&s->learnts) - s->qtail >= nof_learnts)
				// Reduce the set of learnt clauses:
			{
				solver_reducedb(s);
			}

			// New variable decision:
			s->stats.decisions++;


			next = order_select(s, (float)random_var_freq);

			if (next == var_Undef) {
				// Model found:
				lbool* values = s->assigns;
				int i;
				for (i = 0; i < s->size; i++) {

					veci_push(&s->model, (int)values[i]);
				}

				solver_canceluntil(s, s->root_level);
				veci_delete(&learnt_clause);
				vecp_delete(&confl_vecp);
				return l_True;
			}
			assume(s, lit_neg(toLit(next)));
			vecp_delete(&confl_vecp);
		}
	}

	return l_Undef; // cannot happen
}

//=================================================================================================
// External solver functions:

solver* solver_new(void) {
	solver* s = (solver*)malloc(sizeof(solver));

	// initialize vectors
	vecp_new(&s->clauses);
	vecp_new(&s->learnts);
	vecp_new(&s->prop_stock);
	veci_new(&s->order);
	veci_new(&s->trail_lim);
	veci_new(&s->tagged);
	veci_new(&s->stack);
	veci_new(&s->model);


	// initialize arrays
	s->wlists = 0;
	s->word_info = 0;
	s->activity = 0;
	s->assigns = 0;
	s->index = 0;
	s->orderpos = 0;
	s->reasons = 0;
	s->levels = 0;
	s->tags = 0;
	s->trail = 0;
	s->prop_que = 0;
	s->pos = 0;
	s->varorder = 0;


	// initialize other vars
	s->size = 0;
	s->cap = 0;
	s->wordcap = 0;
	s->propcap = 0;
	s->qhead = 0;
	s->qtail = 0;
	s->propt = 0;
	s->proph = 0;
	s->cla_inc = 1;
	s->cla_decay = 1;
	s->var_inc = 1;
	s->var_decay = 1;
	s->root_level = 0;
	s->simpdb_assigns = 0;
	s->simpdb_props = 0;
	s->random_seed = 91648253;
	s->progress_estimate = 0;
	s->binary = (clause*)malloc(sizeof(clause) + sizeof(lit) * 2);
	s->binary->size_learnt = (2 << 1);
	s->verbosity = 0;

	s->stats.starts = 0;
	s->stats.decisions = 0;
	s->stats.propagations = 0;
	s->stats.inspects = 0;
	s->stats.conflicts = 0;
	s->stats.clauses = 0;
	s->stats.clauses_literals = 0;
	s->stats.learnts = 0;
	s->stats.learnts_literals = 0;
	s->stats.max_literals = 0;
	s->stats.tot_literals = 0;

	return s;
}



void solver_delete(solver* s) {
	int i;
	for (i = 0; i < vecp_size(&s->clauses); i++)
		free(vecp_begin(&s->clauses)[i]);

	for (i = 0; i < vecp_size(&s->learnts); i++)
		free(vecp_begin(&s->learnts)[i]);

	// delete vectors
	vecp_delete(&s->clauses);
	vecp_delete(&s->learnts);
	veci_delete(&s->order);
	veci_delete(&s->trail_lim);
	veci_delete(&s->tagged);
	veci_delete(&s->stack);
	veci_delete(&s->model);
	free(s->binary);

	struct ws_flag *prop;
	for (i = 0; i < (&s->prop_stock)->size; i++) // free propagator stock
	{
		prop = (struct ws_flag *)((&s->prop_stock)->ptr[i]);
		free(prop->bitwids);
		free(prop->arnum);
		free(prop->argu);
		if (prop->bound != 0)
			free(prop->bound);
		free(prop);
	}
	vecp_delete(&s->prop_stock);

	// delete arrays
	if (s->wlists != 0) {
		int i;
		for (i = 0; i < s->size * 2; i++)
			vecp_delete(&s->wlists[i]);

		for (i = 0; i < word_num; i++) {
			void** word = (&s->word_info[i])->ptr;
			if (word[0] != 0 && word[0] != (struct ul*)1)
				free(word[0]); // free the lower and upper bound structure
			free(word);
		}

		// if one is different from null, all are
		if (s->word_info != 0)
			free(s->word_info);
		free(s->wlists);
		free(s->activity);
		free(s->assigns);
		free(s->orderpos);
		free(s->reasons);
		free(s->levels);
		free(s->trail);
		free(s->prop_que);
		free(s->tags);
		free(s->index);
		free(s->pos);
		free(s->varorder);
	}

	free(s);
}


int solver_addclause(solver* s, lit* begin, lit* end) {
	lit *i, *j;
	lbool* values;
	lit last;

	if (begin == end) { return false; }

	values = s->assigns;

	// delete duplicates
	last = lit_Undef;
	for (i = j = begin; i < end; i++) {

		lbool sig = !lit_sign(*i); sig += sig - 1;
		if (*i == lit_neg(last) || sig == values[lit_var(*i)])
			return true;
		else if (*i != last && values[lit_var(*i)] == l_Undef)
			last = *j++ = *i;
	}

	if (j == begin)          // empty clause
	{
		return false;
	}
	else if (j - begin == 1) // unit clause
	{
		return enqueue_org(s, *begin, (clause*)0);
	}

	vecp_push(&s->clauses, clause_new(s, begin, j, 0));

	s->stats.clauses++;
	s->stats.clauses_literals += j - begin;
	//printf("s->stats.clauses %d",s->stats.clauses);

	return true;
}

int   solver_simplify(solver* s) {
	clause** reasons;
	int type;

	assert(solver_dlevel(s) == 0);

	vecp confl_vecp;

	confl_vecp = solver_propagate_Bwlistprop(s);
	if (vecp_size(&confl_vecp) != 0) {
		vecp_delete(&confl_vecp);
		return false;
	}
	vecp_delete(&confl_vecp);

	if (s->qhead == s->simpdb_assigns || s->simpdb_props > 0)
		return true;

	reasons = (clause **)s->reasons;
	for (type = 0; type < 2; type++) {
		vecp*    cs = type ? &s->learnts : &s->clauses;
		clause** cls = (clause**)vecp_begin(cs);

		int i, j;
		for (j = i = 0; i < vecp_size(cs); i++) {

			if (reasons[lit_var(*clause_begin(cls[i]))] != cls[i] &&
				clause_simplify(s, cls[i]) == l_True) {
				clause_remove(s, cls[i]);
			}
			else
				cls[j++] = cls[i];
		}
		vecp_resize(cs, j);
	}

	s->simpdb_assigns = s->qhead;
	// (shouldn't depend on 'stats' really, but it will do for now)
	s->simpdb_props = (int)(s->stats.clauses_literals + s->stats.learnts_literals);

	return true;
}


int  solver_solve(solver* s, lit* begin, lit* end) {
	double  nof_conflicts = 100;
	double  nof_learnts = (solver_nclauses(s)) / 3;

	lbool   status = l_Undef;
	lbool*  values = s->assigns;
	lit*    i;

	for (i = begin; i < end; i++) {
		switch (lit_sign(*i) ? -values[lit_var(*i)] : values[lit_var(*i)]) {
		case l_True:/* l_True: */
			break;
		case l_Undef: /* l_Undef */
			assume(s, *i);
			vecp confl_vecp;
			confl_vecp = solver_propagate_NonBwlistprop(s);
			if (vecp_size(&confl_vecp) == 0) {
				vecp_delete(&confl_vecp);
				break;
			}
			vecp_delete(&confl_vecp);
			// falltrough
		case l_False: /* l_False */
			solver_canceluntil(s, 0);
			return false;
		}
	}

	s->root_level = solver_dlevel(s);


	while (status == l_Undef) {
		status = solver_search(s, (int)nof_conflicts, (int)nof_learnts);
		nof_conflicts *= 1.5;
		nof_learnts *= 1.1;
	}

	solver_canceluntil(s, 0);
	return status != l_False;
}

int solver_nvars(solver* s) {
	return s->size;
}


int solver_nclauses(solver* s) {
	return vecp_size(&s->clauses);
}


int solver_nconflicts(solver* s) {
	return (int)s->stats.conflicts;
}

//=================================================================================================
// Sorting functions (sigh):

static inline void selectionsort(void** array, int size, int(*comp)(const void *, const void *)) {
	int     i, j, best_i;
	void*   tmp;

	for (i = 0; i < size - 1; i++) {
		best_i = i;
		for (j = i + 1; j < size; j++) {
			if (comp(array[j], array[best_i]) < 0)
				best_i = j;
		}
		tmp = array[i]; array[i] = array[best_i]; array[best_i] = tmp;
	}
}


static void sortrnd(void** array, int size, int(*comp)(const void *, const void *), double* seed) {
	if (size <= 15)
		selectionsort(array, size, comp);

	else {
		void*       pivot = array[irand(seed, size)];
		void*       tmp;
		int         i = -1;
		int         j = size;

		for (;;) {
			do i++; while (comp(array[i], pivot) < 0);
			do j--; while (comp(pivot, array[j]) < 0);

			if (i >= j) break;

			tmp = array[i]; array[i] = array[j]; array[j] = tmp;
		}

		sortrnd(array, i, comp, seed);
		sortrnd(&array[i], size - i, comp, seed);
	}
}

void sort(void** array, int size, int(*comp)(const void *, const void *)) {
	double seed = 91648253;
	sortrnd(array, size, comp, &seed);
}



//==================== Extended by Wenxi Wang on 19/11/2014 =====================

clause* explan_generate(lit* begin, int num)  //clause generate for explanations
{
	clause* c;
	if (num == 2) {
		c = clause_from_lit(begin[1]);
	}
	else {
		int i;

		c = (clause*)malloc(sizeof(clause) + sizeof(int) + sizeof(lit)*num);
		c->size_learnt = num << 1;
		c->flag = 1;
		for (i = 0;i < num;i++) {
			c->lits[i] = begin[i];

		}
	}

	return c;
}

clause* confl_generate(lit* begin, int num)  //clause generate for conflict clauses
{
	clause* c;

	int i;

	c = (clause*)malloc(sizeof(clause) + sizeof(int) + sizeof(lit)*num);
	c->size_learnt = num << 1;
	c->flag = 1;
	for (i = 0;i < num;i++) {
		c->lits[i] = begin[i];
	}

	return c;
}

// enqueuue the positive literals to the literal queue with the propagator (*wsf) as the fake explanation
void enque_pos(solver* s, int bitwid, int var1, unsigned long int z, struct ws_flag *wsf, int varorder) {
	int i;
	while (z) {
		i = bitwid - __builtin_ffsll(z);
		enqueue(s, toLit(var1 + i), wsf, varorder);
		z &= (z - (uint64_t)1);
	}
}

// enqueuue the negtive literals to the literal queue with the propagator (*wsf) as the fake explanation
void enque_neg(solver* s, int bitwid, int var1, unsigned long int z, struct ws_flag *wsf, int varorder) {
	int i;
	while (z) {
		i = bitwid - __builtin_ffsll(z);
		enqueue(s, lit_neg(toLit(var1 + i)), wsf, varorder);
		z &= (z - (uint64_t)1);
	}
}

/*propagators, do the proapgation, if there is no conflict: enqueue the fixed literals; otherwise: return the conflict clause */

int conjunction(solver *s, int var1, int var2, int var3, struct ul* uplw1, struct ul* uplw2, struct ul* uplw3, 
	vecp* confl, int bitwid, unsigned long int ax, unsigned long int ay, struct ws_flag *wsf) {
	unsigned long int xl, xu, yl, yu, zl, zu;
	unsigned long int zlp, zup;

	if (var1 != -2) {
		xl = uplw1->lower;
		xu = uplw1->upper;
	}
	else {
		xl = ax;
		xu = ax;
	}

	if (var2 != -2) {
		yl = uplw2->lower;
		yu = uplw2->upper;
	}
	else {
		yl = ay;
		yu = ay;
	}

	zl = uplw3->lower;
	zu = uplw3->upper;


	zlp = zl | (xl & yl);
	zup = zu & xu & yu;

	unsigned long int che = check_valid_word(zlp, zup);

	if (che != (uint64_t)(-1)) {
		veci lits1;
		veci_new(&lits1);
		lbool* values = s->assigns;

		che = ~che; int i; int v3;
		while (che) {
			i = bitwid - __builtin_ffsl(che);
			v3 = var3 + i;

			if (values[v3] == l_True) {
				if ((var1 == -2 && ((ax >> (bitwid - 1 - i)) & (uint64_t)1) == (uint64_t)0) || 
					(var2 == -2 && ((ay >> (bitwid - 1 - i)) & (uint64_t)1) == (uint64_t)0)) {
					veci_push(&lits1, lit_neg(toLit(v3)));
				}
				else {
					if (var1 != -2)  // find the literals that first cause the conflict
					{
						int v1 = var1 + i;
						if (var2 != -2) {
							int v2 = var2 + i;
							if (values[v1] == l_False) {
								if (values[v2] == l_False) {
									if (s->pos[v1] < s->pos[v2]) {
										veci_push(&lits1, lit_neg(toLit(v3)));
										veci_push(&lits1, toLit(v1));
									}
									else {
										veci_push(&lits1, lit_neg(toLit(v3)));
										veci_push(&lits1, toLit(v2));
									}
								}
								else {
									veci_push(&lits1, lit_neg(toLit(v3)));
									veci_push(&lits1, toLit(v1));
								}
							}
							else {
								veci_push(&lits1, lit_neg(toLit(v3)));
								veci_push(&lits1, toLit(v2));
							}
						}
						else {
							veci_push(&lits1, lit_neg(toLit(v3)));
							veci_push(&lits1, toLit(v1));
						}
					}
					else {
						veci_push(&lits1, lit_neg(toLit(v3)));

						assert(s->assigns[var2 + i] == l_False);
						veci_push(&lits1, toLit(var2 + i));
					}
				}
			}
			else {
				veci_push(&lits1, toLit(v3));
				if (var2 != -2) {
					assert(s->assigns[var2 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
				if (var1 != -2) {
					assert(s->assigns[var1 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var1 + i)));
				}
			}


			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}

		veci_delete(&lits1);
		return 0;
	}

	unsigned long int xlp, xup, ylp, yup;

	xlp = xl | zl;
	xup = xu & ~((~zu) & yl);
	ylp = yl | zl;
	yup = yu & ~((~zu) & xl);


	unsigned long int z;

	z = xlp^xl;
	if (z) {
		uplw1->lower = xlp;
		enque_pos(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);

	}

	z = xup^xu;
	if (z) {
		uplw1->upper = xup;
		enque_neg(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = ylp^yl;
	if (z) {
		uplw2->lower = ylp;
		enque_pos(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = yup^yu;
	if (z) {
		uplw2->upper = yup;
		enque_neg(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = zlp^zl;
	if (z) {
		uplw3->lower = zlp;
		enque_pos(s, bitwid, var3, z, wsf, 3);
		enqueue_prop(s, uplw3->word_num);
	}

	z = zup^zu;
	if (z) {
		uplw3->upper = zup;
		enque_neg(s, bitwid, var3, z, wsf, 3);
		enqueue_prop(s, uplw3->word_num);
	}
	return 1;
}

int conjunction_neg(solver *s, int var1, int var2, int var3, struct ul* uplw1, struct ul* uplw2, struct ul* uplw3, 
	vecp* confl, int bitwid, unsigned long int ax, unsigned long int ay, struct ws_flag *wsf) {
	unsigned long int xl, xu, yl, yu, zl, zu;
	unsigned long int zlp, zup;

	if (var1 != -2) {
		xl = uplw1->lower;
		xu = uplw1->upper;
	}
	else {
		xl = ax;
		xu = ax;
	}

	if (var2 != -2) {
		yl = uplw2->lower;
		yu = uplw2->upper;
	}
	else {
		yl = ay;
		yu = ay;
	}

	zl = uplw3->lower;
	zu = uplw3->upper;

	zlp = zl | ~(xu & yu);
	zup = zu & ~(xl & yl);

	unsigned long int che = check_valid_word(zlp, zup);

	if (che != (uint64_t)(-1)) {
		veci lits1;
		veci_new(&lits1);
		lbool* values = s->assigns;

		che = ~che; int i; int v3;
		while (che) {
			i = bitwid - __builtin_ffsl(che);
			v3 = var3 + i;

			if (values[v3] == l_False) {
				if ((var1 == -2 && ((ax >> (bitwid - 1 - i)) & (uint64_t)1) == (uint64_t)0) || 
					(var2 == -2 && ((ay >> (bitwid - 1 - i)) & (uint64_t)1) == (uint64_t)0)) {
					veci_push(&lits1, toLit(v3));
				}
				else {
					if (var1 != -2) {
						int v1 = var1 + i;
						if (var2 != -2) {
							int v2 = var2 + i;
							if (values[v1] == l_False) {
								if (values[v2] == l_False) {
									if (s->pos[v1] < s->pos[v2]) {
										veci_push(&lits1, toLit(v3));
										veci_push(&lits1, toLit(v1));
									}
									else {
										veci_push(&lits1, toLit(v3));
										veci_push(&lits1, toLit(v2));
									}
								}
								else {
									veci_push(&lits1, toLit(v3));
									veci_push(&lits1, toLit(v1));
								}
							}
							else {
								veci_push(&lits1, toLit(v3));
								veci_push(&lits1, toLit(v2));
							}
						}
						else {
							veci_push(&lits1, toLit(v3));
							veci_push(&lits1, toLit(v1));
						}
					}
					else {
						veci_push(&lits1, toLit(v3));

						assert(s->assigns[var2 + i] == l_False);
						veci_push(&lits1, toLit(var2 + i));
					}
				}
			}
			else {
				veci_push(&lits1, lit_neg(toLit(v3)));
				if (var2 != -2) {
					assert(s->assigns[var2 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
				if (var1 != -2) {
					assert(s->assigns[var1 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var1 + i)));
				}
			}


			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}

		veci_delete(&lits1);
		return 0;
	}

	unsigned long int xlp, xup, ylp, yup;

	xlp = xl | (~zu);
	xup = xu &  ~(zl & yl);
	ylp = yl | (~zu);
	yup = yu &  ~(zl & xl);

	unsigned long int z;

	z = xlp^xl;
	if (z) {
		uplw1->lower = xlp;
		enque_pos(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);

	}

	z = xup^xu;
	if (z) {
		uplw1->upper = xup;
		enque_neg(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = ylp^yl;
	if (z) {
		uplw2->lower = ylp;
		enque_pos(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = yup^yu;
	if (z) {
		uplw2->upper = yup;
		enque_neg(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = zlp^zl;
	if (z) {
		uplw3->lower = zlp;
		enque_pos(s, bitwid, var3, z, wsf, 3);
		enqueue_prop(s, uplw3->word_num);
	}

	z = zup^zu;
	if (z) {
		uplw3->upper = zup;
		enque_neg(s, bitwid, var3, z, wsf, 3);
		enqueue_prop(s, uplw3->word_num);
	}
	return 1;
}


int bit_toword(solver *s, int var, int var_word, struct ul *uplw, vecp* confl, int bitwid, struct ws_flag *wsf) {
	unsigned long int wl, wu, wlp, wup;
	lbool x = 0;

	wl = uplw->lower;
	wu = uplw->upper;

	if (var == -1) // const_true, fix wl to 1
	{
		wup = wu;
		if (bitwid == 64)
			wlp = (uint64_t)(-1);

		else
			wlp = ~((uint64_t)(-1) << bitwid);
	}
	else if (var == -2) // const_false, fix wu to 0
	{
		wlp = wl;
		wup = (uint64_t)0;
	}
	else {
		x = s->assigns[var];
		if (x == l_True) // fix wl to 1
		{
			wup = wu;
			if (bitwid == 64)
				wlp = (uint64_t)(-1);
			else
				wlp = ~((uint64_t)(-1) << bitwid);
		}
		else if (x == l_False) // fix wu to 0
		{
			wlp = wl;
			wup = (uint64_t)0;
		}
		else {
			unsigned long int wuu;
			if (bitwid != 64)
				wuu = ~(wu | ((uint64_t)(-1) << bitwid));
			else
				wuu = ~wu;
			unsigned long int wll = wl;
			if (wll != (uint64_t)0 && wuu != (uint64_t)0) // some bit in word fixed to 1, while some fixed to 0
			{
				veci lits1;
				veci_new(&lits1);

				int i, j;
				while (wll) {
					i = bitwid - __builtin_ffsl(wll);

					assert(s->assigns[var_word + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var_word + i)));
					while (wuu) {
						j = bitwid - __builtin_ffsl(wuu);

						assert(s->assigns[var_word + j] == l_False);
						veci_push(&lits1, toLit(var_word + j));

						wuu &= (wuu - (uint64_t)1);

						vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
						veci_resize(&lits1, 1);
					}

					wll &= (wll - (uint64_t)1);
					veci_resize(&lits1, 0);
				}

				veci_delete(&lits1);
				return 0;
			}
			else if (wll != (uint64_t)0) // fix var to true
			{
				assert(s->assigns[var] == l_Undef);
				enqueue_bit(s, toLit(var), wsf);

				if (bitwid == 64)  // propagate var_word, fix to 1
					wlp = (uint64_t)(-1);
				else
					wlp = ~((uint64_t)(-1) << bitwid);

				unsigned long int z = wl ^ wlp;
				if (z) {
					uplw->lower = wlp;
					enque_pos(s, bitwid, var_word, z, wsf, 2);
					enqueue_prop(s, uplw->word_num);
				}

				return 1;
			}
			else if (wuu != (uint64_t)0) // fix var to false	
			{
				assert(s->assigns[var] == l_Undef);
				enqueue_bit(s, lit_neg(toLit(var)), wsf);

				wup = (uint64_t)0; // propagate var_word, fix to 0

				unsigned long int z = wup ^ wu;
				if (z) {
					uplw->upper = wup;
					enque_neg(s, bitwid, var_word, z, wsf, 2);
					enqueue_prop(s, uplw->word_num);
				}

				return 1;
			}
			else
				return 1;
		}
	}

	// var is fixed, propagate word
	unsigned long int che;

	che = check_valid_word(wlp, wup);

	if (che != (uint64_t)(-1)) {
		veci lits1;
		veci_new(&lits1);

		che = ~che; int i;

		if (var > 0) {
			// x= s->assigns[var]; x is assigned before
			if (x == l_True) {
				assert(s->assigns[var] == l_True);
				veci_push(&lits1, lit_neg(toLit(var)));
				while (che) {
					i = bitwid - __builtin_ffsl(che);

					assert(s->assigns[var_word + i] == l_False);
					veci_push(&lits1, toLit(var_word + i));

					che &= (che - (uint64_t)1);
					vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
					veci_resize(&lits1, 1);
				}
			}
			else // x == l_False
			{
				assert(s->assigns[var] == l_False);
				veci_push(&lits1, toLit(var));
				while (che) {
					i = bitwid - __builtin_ffsl(che);

					assert(s->assigns[var_word + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var_word + i)));

					che &= (che - (uint64_t)1);
					vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
					veci_resize(&lits1, 1);
				}
			}
		}
		else {
			if (var == -1) {
				while (che) {
					i = bitwid - __builtin_ffsl(che);

					assert(s->assigns[var_word + i] == l_False);
					veci_push(&lits1, toLit(var_word + i));

					che &= (che - (uint64_t)1);
					vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
					veci_resize(&lits1, 0);
				}
			}
			else // var == -2
			{
				while (che) {
					i = bitwid - __builtin_ffsl(che);

					assert(s->assigns[var_word + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var_word + i)));

					che &= (che - (uint64_t)1);
					vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
					veci_resize(&lits1, 0);
				}
			}
		}

		veci_delete(&lits1);
		return 0;
	}

	unsigned long int z;

	z = wlp^wl;
	if (z) {
		uplw->lower = wlp;
		enque_pos(s, bitwid, var_word, z, wsf, 2);
		enqueue_prop(s, uplw->word_num);

	}

	z = wup^wu;
	if (z) {
		uplw->upper = wup;
		enque_neg(s, bitwid, var_word, z, wsf, 2);
		enqueue_prop(s, uplw->word_num);
	}

	return 1;
}

int exclusiveor(solver *s, int var1, int var2, int var3, struct ul* uplw1, struct ul* uplw2, struct ul* uplw3, 
	vecp* confl, int bitwid, unsigned long int ax, unsigned long int ay, struct ws_flag *wsf) {
	unsigned long int xl, xu, yl, yu, zl, zu;
	unsigned long int zlp, zup;

	if (var1 != -2) {
		xl = uplw1->lower;
		xu = uplw1->upper;
	}
	else {
		xl = ax;
		xu = ax;
	}

	if (var2 != -2) {
		yl = uplw2->lower;
		yu = uplw2->upper;
	}
	else {
		yl = ay;
		yu = ay;
	}

	zl = uplw3->lower;
	zu = uplw3->upper;

	zlp = zl | (~xu & yl) | (xl & ~yu);
	zup = zu&(xu | yu)&(~(xl&yl));

	unsigned long int che = check_valid_word(zlp, zup);

	if (che != (uint64_t)(-1)) {
		veci lits1;
		veci_new(&lits1);
		lbool* values = s->assigns;

		che = ~che;
		while (che) {
			int i = bitwid - __builtin_ffsl(che);
			int v3 = var3 + i;

			if (values[v3] == l_True) {
				veci_push(&lits1, lit_neg(toLit(v3)));
				if (var1 != -2) {
					int v1 = var1 + i;
					if (values[v1] == l_True)

						veci_push(&lits1, lit_neg(toLit(v1)));
					else {
						assert(s->assigns[v1] == l_False);
						veci_push(&lits1, toLit(v1));
					}

				}
				if (var2 != -2) {
					int v2 = var2 + i;
					if (values[v2] == l_True)
						veci_push(&lits1, lit_neg(toLit(v2)));
					else {
						assert(s->assigns[v2] == l_False);
						veci_push(&lits1, toLit(v2));
					}
				}
			}
			else {
				veci_push(&lits1, toLit(v3));
				if (var1 != -2) {
					int v1 = var1 + i;
					if (values[v1] == l_True)
						veci_push(&lits1, lit_neg(toLit(v1)));
					else {
						assert(s->assigns[v1] == l_False);
						veci_push(&lits1, toLit(v1));
					}

				}
				if (var2 != -2) {
					int v2 = var2 + i;
					if (values[v2] == l_True)
						veci_push(&lits1, lit_neg(toLit(v2)));
					else {
						assert(s->assigns[v2] == l_False);
						veci_push(&lits1, toLit(v2));

					}

				}
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}

		veci_delete(&lits1);
		return 0;
	}

	unsigned long int xlp, xup, ylp, yup;

	xlp = xl | (~zu &yl) | (zl& ~yu);
	xup = xu & (zu | yu) & (~(yl & zl));
	ylp = yl | (~zu &xl) | (zl& ~xu);
	yup = yu&(zu | xu)&(~(xl&zl));

	unsigned long int z;  //int count=0; 

	z = xlp^xl;
	if (z) {
		uplw1->lower = xlp;
		enque_pos(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = xup^xu;
	if (z) {
		uplw1->upper = xup;
		enque_neg(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = ylp^yl;
	if (z) {
		uplw2->lower = ylp;
		enque_pos(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = yup^yu;
	if (z) {
		uplw2->upper = yup;
		enque_neg(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = zlp^zl;
	if (z) {
		uplw3->lower = zlp;
		enque_pos(s, bitwid, var3, z, wsf, 3);
		enqueue_prop(s, uplw3->word_num);
	}

	z = zup^zu;
	if (z) {
		uplw3->upper = zup;
		enque_neg(s, bitwid, var3, z, wsf, 3);
		enqueue_prop(s, uplw3->word_num);
	}
	return 1;
}

int exclusiveor_neg(solver *s, int var1, int var2, int var3, struct ul* uplw1, struct ul* uplw2, struct ul* uplw3, 
	vecp* confl, int bitwid, unsigned long int ax, unsigned long int ay, struct ws_flag *wsf) {
	unsigned long int xl, xu, yl, yu, zl, zu;
	unsigned long int zlp, zup;

	if (var1 != -2) {
		xl = uplw1->lower;
		xu = uplw1->upper;
	}
	else {
		xl = ax;
		xu = ax;
	}

	if (var2 != -2) {
		yl = uplw2->lower;
		yu = uplw2->upper;
	}
	else {
		yl = ay;
		yu = ay;
	}

	zl = uplw3->lower;
	zu = uplw3->upper;

	zlp = zl | ~(xu | yu) | (xl & yl);
	zup = zu &~((~xu & yl) | (~yu & xl));

	unsigned long int che = check_valid_word(zlp, zup);

	if (che != (uint64_t)(-1)) {
		veci lits1;
		veci_new(&lits1);
		lbool* values = s->assigns;

		che = ~che;
		while (che) {
			int i = bitwid - __builtin_ffsl(che);
			int v3 = var3 + i;

			if (values[v3] == l_True) {
				veci_push(&lits1, lit_neg(toLit(v3)));
				if (var1 != -2) {
					int v1 = var1 + i;
					if (values[v1] == l_True)
						veci_push(&lits1, lit_neg(toLit(v1)));
					else {
						assert(s->assigns[v1] == l_False);
						veci_push(&lits1, toLit(v1));
					}

				}
				if (var2 != -2) {
					int v2 = var2 + i;
					if (values[v2] == l_True)
						veci_push(&lits1, lit_neg(toLit(v2)));

					else {
						assert(s->assigns[v2] == l_False);
						veci_push(&lits1, toLit(v2));
					}
				}
			}
			else {
				veci_push(&lits1, toLit(v3));
				if (var1 != -2) {
					int v1 = var1 + i;
					if (values[v1] == l_True)
						veci_push(&lits1, lit_neg(toLit(v1)));
					else {
						assert(s->assigns[v1] == l_False);
						veci_push(&lits1, toLit(v1));
					}

				}
				if (var2 != -2) {
					int v2 = var2 + i;
					if (values[v2] == l_True)
						veci_push(&lits1, lit_neg(toLit(v2)));
					else {
						assert(s->assigns[v2] == l_False);
						veci_push(&lits1, toLit(v2));

					}

				}
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}

		veci_delete(&lits1);
		return 0;
	}

	unsigned long int xlp, xup, ylp, yup;

	xlp = xl | ~(zu | yu) | (zl & yl);
	xup = xu & ~((~zu & yl) | (~yu & zl));
	ylp = yl | ~(zu | xu) | (zl & xl);
	yup = yu & ~((~zu & xl) | (~xu & zl));

	unsigned long int z;  //int count=0; 

	z = xlp^xl;
	if (z) {
		uplw1->lower = xlp;
		enque_pos(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = xup^xu;
	if (z) {
		uplw1->upper = xup;
		enque_neg(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = ylp^yl;
	if (z) {
		uplw2->lower = ylp;
		enque_pos(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = yup^yu;
	if (z) {
		uplw2->upper = yup;
		enque_neg(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = zlp^zl;
	if (z) {
		uplw3->lower = zlp;
		enque_pos(s, bitwid, var3, z, wsf, 3);
		enqueue_prop(s, uplw3->word_num);
	}

	z = zup^zu;
	if (z) {
		uplw3->upper = zup;
		enque_neg(s, bitwid, var3, z, wsf, 3);
		enqueue_prop(s, uplw3->word_num);
	}
	return 1;
}


int exclusiveor_div(solver *s, int var1, int var2, struct ul* uplw1, struct ul* uplw2, vecp *confl, int bitwid, 
	unsigned long int az, struct ws_flag *wsf) {
	//printf("exclusiveor_div\n");
	unsigned long int xl, xu, yl, yu, zl, zu;
	unsigned long int zlp, zup;

	xl = uplw1->lower;
	xu = uplw1->upper;

	yl = uplw2->lower;
	yu = uplw2->upper;

	zl = az;
	zu = az;

	zlp = zl | (~xu & yl) | (xl & ~yu);
	zup = zu&(xu | yu)&(~(xl&yl));

	unsigned long int che = check_valid_word(zlp, zup);

	if (che != (uint64_t)(-1)) {
		veci lits1;
		veci_new(&lits1);
		lbool* values = s->assigns;

		che = ~che;
		while (che) {
			int i = bitwid - __builtin_ffsl(che);

			if ((az >> (bitwid - 1 - i)) & (uint64_t)1) {
				if (var1 != -2) {
					int v1 = var1 + i;
					if (values[v1] == l_True)
						veci_push(&lits1, lit_neg(toLit(v1)));
					else {
						assert(s->assigns[v1] == l_False);
						veci_push(&lits1, toLit(v1));

					}

				}
				if (var2 != -2) {
					int v2 = var2 + i;
					if (values[v2] == l_True)
						veci_push(&lits1, lit_neg(toLit(v2)));
					else {
						assert(s->assigns[v2] == l_False);
						veci_push(&lits1, toLit(v2));
					}
				}
			}
			else {
				if (var1 != -2) {
					int v1 = var1 + i;
					if (values[v1] == l_True)
						veci_push(&lits1, lit_neg(toLit(v1)));
					else {
						assert(s->assigns[v1] == l_False);
						veci_push(&lits1, toLit(v1));

					}

				}
				if (var2 != -2) {
					int v2 = var2 + i;
					if (values[v2] == l_True)
						veci_push(&lits1, lit_neg(toLit(v2)));
					else {
						assert(s->assigns[v2] == l_False);
						veci_push(&lits1, toLit(v2));
					}

				}
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}

		veci_delete(&lits1);
		return 0;
	}

	unsigned long int xlp, xup, ylp, yup;

	xlp = xl | (~zu &yl) | (zl& ~yu);
	xup = xu & (zu | yu) & (~(yl & zl));
	ylp = yl | (~zu &xl) | (zl& ~xu);
	yup = yu&(zu | xu)&(~(xl&zl));

	unsigned long int z;

	z = xlp^xl;
	if (z) {
		uplw1->lower = xlp;
		enque_pos(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = xup^xu;
	if (z) {
		uplw1->upper = xup;
		enque_neg(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);

	}

	z = ylp^yl;
	if (z) {
		uplw2->lower = ylp;
		enque_pos(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = yup^yu;
	if (z) {
		uplw2->upper = yup;
		enque_neg(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);

	}

	return 0;
}

int disjunction(solver *s, int var1, int var2, int var3, struct ul* uplw1, struct ul* uplw2, struct ul* uplw3, 
	vecp* confl, int bitwid, unsigned long int ax, unsigned long int ay, struct ws_flag *wsf) {
	unsigned long int xl, xu, yl, yu, zl, zu;
	unsigned long int zlp, zup;

	if (var1 != -2) {
		xl = uplw1->lower;
		xu = uplw1->upper;
	}
	else {
		xl = ax;
		xu = ax;
	}

	if (var2 != -2) {
		yl = uplw2->lower;
		yu = uplw2->upper;
	}
	else {
		yl = ay;
		yu = ay;
	}

	zl = uplw3->lower;
	zu = uplw3->upper;

	zlp = zl | xl | yl;
	zup = zu&(xu | yu);

	unsigned long int che = check_valid_word(zlp, zup);

	if (che != (uint64_t)(-1)) {
		veci lits1;
		veci_new(&lits1);
		lbool* values = s->assigns;

		che = ~che;

		while (che) {
			int i = bitwid - __builtin_ffsl(che);
			int v3 = var3 + i;

			if (values[v3] == l_True) {
				veci_push(&lits1, lit_neg(toLit(v3)));
				if (var1 != -2) {
					assert(s->assigns[var1 + i] == l_False);
					veci_push(&lits1, toLit(var1 + i));
				}
				if (var2 != -2) {
					assert(s->assigns[var2 + i] == l_False);
					veci_push(&lits1, toLit(var2 + i));
				}
			}
			else {
				if ((var1 == -2 && ((ax >> (bitwid - 1 - i)) & (uint64_t)1) == (uint64_t)1) 
					|| (var2 == -2 && ((ay >> (bitwid - 1 - i)) & (uint64_t)1) == (uint64_t)1)) {
					veci_push(&lits1, toLit(v3));
				}
				else {

					veci_push(&lits1, toLit(v3)); // find the literals that first cause the conflict

					if (var1 != -2) {
						int v1 = var1 + i;
						if (var2 != -2) {
							int v2 = var2 + i;
							if (values[v1] == l_True) {
								if (values[v2] == l_True) {
									if (s->pos[v1] < s->pos[v2]) {
										assert(s->assigns[v3] == l_False);
										veci_push(&lits1, toLit(v3));
										assert(s->assigns[v1] == l_True);
										veci_push(&lits1, lit_neg(toLit(v1)));
									}
									else {
										assert(s->assigns[v3] == l_False);
										veci_push(&lits1, toLit(v3));
										assert(s->assigns[v2] == l_True);
										veci_push(&lits1, lit_neg(toLit(v2)));
									}
								}
								else {
									assert(s->assigns[v3] == l_False);
									veci_push(&lits1, toLit(v3));
									assert(s->assigns[v1] == l_True);
									veci_push(&lits1, lit_neg(toLit(v1)));
								}
							}
							else {
								assert(s->assigns[v3] == l_False);
								veci_push(&lits1, toLit(v3));
								assert(s->assigns[v2] == l_True);
								veci_push(&lits1, lit_neg(toLit(v2)));
							}
						}
						else {
							assert(s->assigns[v3] == l_False);
							veci_push(&lits1, toLit(v3));
							assert(s->assigns[v1] == l_True);
							veci_push(&lits1, lit_neg(toLit(v1)));
						}
					}
					else {
						assert(s->assigns[v3] == l_False);
						veci_push(&lits1, toLit(v3));

						assert(s->assigns[var2 + i] == l_True);
						veci_push(&lits1, lit_neg(toLit(var2 + i)));
					}
				}
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}

		veci_delete(&lits1);
		return 0;
	}

	unsigned long int xlp, xup, ylp, yup;

	xlp = xl | ((~yu)&zl);
	xup = xu & zu;
	ylp = yl | ((~xu)&zl);
	yup = yu & zu;

	unsigned long int z;    //int count=0;

	z = xlp^xl;
	if (z) {
		uplw1->lower = xlp;
		enque_pos(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = xup^xu;
	if (z) {
		uplw1->upper = xup;
		enque_neg(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = ylp^yl;
	if (z) {
		uplw2->lower = ylp;
		enque_pos(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = yup^yu;
	if (z) {
		uplw2->upper = yup;
		enque_neg(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}


	z = zlp^zl;
	if (z) {
		uplw3->lower = zlp;

		enque_pos(s, bitwid, var3, z, wsf, 3);
		enqueue_prop(s, uplw3->word_num);
	}

	z = zup^zu;
	if (z) {
		uplw3->upper = zup;
		enque_neg(s, bitwid, var3, z, wsf, 3);
		enqueue_prop(s, uplw3->word_num);
	}

	return 1;
}

int disjunction_neg(solver *s, int var1, int var2, int var3, struct ul* uplw1, struct ul* uplw2, struct ul* uplw3, 
	vecp* confl, int bitwid, unsigned long int ax, unsigned long int ay, struct ws_flag *wsf) {
	unsigned long int xl, xu, yl, yu, zl, zu;
	unsigned long int zlp, zup;

	if (var1 != -2) {
		xl = uplw1->lower;
		xu = uplw1->upper;
	}
	else {
		xl = ax;
		xu = ax;
	}

	if (var2 != -2) {
		yl = uplw2->lower;
		yu = uplw2->upper;
	}
	else {
		yl = ay;
		yu = ay;
	}

	zl = uplw3->lower;
	zu = uplw3->upper;

	zlp = zl | ~(xu | yu);
	zup = zu &~(xl | yl);

	unsigned long int che = check_valid_word(zlp, zup);

	if (che != (uint64_t)(-1)) {
		veci lits1;
		veci_new(&lits1);
		lbool* values = s->assigns;

		che = ~che;

		while (che) {
			int i = bitwid - __builtin_ffsl(che);
			int v3 = var3 + i;

			if (values[v3] == l_False) {
				veci_push(&lits1, toLit(v3));
				if (var1 != -2) {
					assert(s->assigns[var1 + i] == l_False);
					veci_push(&lits1, toLit(var1 + i));
				}
				if (var2 != -2) {
					assert(s->assigns[var2 + i] == l_False);
					veci_push(&lits1, toLit(var2 + i));
				}
			}
			else {
				if ((var1 == -2 && ((ax >> (bitwid - 1 - i)) & (uint64_t)1) == (uint64_t)1) || 
					(var2 == -2 && ((ay >> (bitwid - 1 - i)) & (uint64_t)1) == (uint64_t)1)) {
					veci_push(&lits1, lit_neg(toLit(v3)));
				}
				else {

					veci_push(&lits1, lit_neg(toLit(v3)));

					if (var1 != -2) {
						int v1 = var1 + i;
						if (var2 != -2) {
							int v2 = var2 + i;
							if (values[v1] == l_True) {
								if (values[v2] == l_True) {
									if (s->pos[v1] < s->pos[v2]) {
										veci_push(&lits1, lit_neg(toLit(v3)));
										veci_push(&lits1, lit_neg(toLit(v1)));
									}
									else {
										veci_push(&lits1, lit_neg(toLit(v3)));
										veci_push(&lits1, lit_neg(toLit(v2)));
									}
								}
								else {
									veci_push(&lits1, lit_neg(toLit(v3)));
									veci_push(&lits1, lit_neg(toLit(v1)));
								}
							}
							else {
								veci_push(&lits1, lit_neg(toLit(v3)));
								veci_push(&lits1, lit_neg(toLit(v2)));
							}
						}
						else {
							veci_push(&lits1, lit_neg(toLit(v3)));
							veci_push(&lits1, lit_neg(toLit(v1)));
						}
					}
					else {
						veci_push(&lits1, lit_neg(toLit(v3)));

						assert(s->assigns[var2 + i] == l_True);
						veci_push(&lits1, lit_neg(toLit(var2 + i)));
					}
				}
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}

		veci_delete(&lits1);
		return 0;
	}

	unsigned long int xlp, xup, ylp, yup;

	xlp = xl | ~(yu | zu);
	xup = xu & ~zl;
	ylp = yl | ~(xu | zu);
	yup = yu & ~zl;

	unsigned long int z;    //int count=0;

	z = xlp^xl;
	if (z) {
		uplw1->lower = xlp;
		enque_pos(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = xup^xu;
	if (z) {
		uplw1->upper = xup;
		enque_neg(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = ylp^yl;
	if (z) {
		uplw2->lower = ylp;
		enque_pos(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = yup^yu;
	if (z) {
		uplw2->upper = yup;
		enque_neg(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}


	z = zlp^zl;
	if (z) {
		uplw3->lower = zlp;
		enque_pos(s, bitwid, var3, z, wsf, 3);
		enqueue_prop(s, uplw3->word_num);
	}

	z = zup^zu;
	if (z) {
		uplw3->upper = zup;
		enque_neg(s, bitwid, var3, z, wsf, 3);
		enqueue_prop(s, uplw3->word_num);
	}

	return 1;
}

int ifstatement(solver *s, int var1, int var2, int var3, int var4, struct ul *uplw1, struct ul *uplw2, struct ul *uplw3, 
	struct ul *uplw4,
	vecp* confl, int bitwid, unsigned long int ay, unsigned long int az, struct ws_flag* wsf) {
	lbool* values = s->assigns;

	unsigned long int xl, xu, yl, yu, zl, zu, wl, wu;
	unsigned long int wlp, wup;

	xl = uplw1->lower;
	xu = uplw1->upper;

	if (var2 != -2) {
		yl = uplw2->lower;
		yu = uplw2->upper;
	}
	else {
		yl = ay;
		yu = ay;
	}

	if (var3 != -2) {
		zl = uplw3->lower;
		zu = uplw3->upper;
	}
	else {
		zl = az;
		zu = az;
	}

	wl = uplw4->lower;
	wu = uplw4->upper;

	wlp = wl | (xl&yl) | ((~xu)&zl) | (yl&zl);  //use xlp, xup to make the propagator idemponent, since x might be fixed

	wup = wu& (~((xl&(~yu)) | ((~xu)&(~zu)) | ((~yu)&(~zu))));

	unsigned long int che = check_valid_word(wlp, wup);
	if (che != (uint64_t)(-1)) {
		veci lits1;
		veci_new(&lits1);

		che = ~che; int i; int v4; int v1;

		while (che) {
			i = bitwid - __builtin_ffsl(che);
			v4 = var4 + i; v1 = var1 + i; lbool x = values[v1];

			if (values[v4] == l_False) {
				veci_push(&lits1, toLit(v4));
				if (x == l_True) {
					veci_push(&lits1, lit_neg(toLit(v1)));
					if (var2 != -2) {
						assert(s->assigns[var2 + i] == l_True);
						veci_push(&lits1, lit_neg(toLit(var2 + i)));
					}
				}
				else if (x == l_False) {
					veci_push(&lits1, toLit(v1));
					if (var3 != -2) {
						assert(s->assigns[var3 + i] == l_True);
						veci_push(&lits1, lit_neg(toLit(var3 + i)));
					}
				}
				else {
					if (var2 != -2) {
						assert(s->assigns[var2 + i] == l_True);
						veci_push(&lits1, lit_neg(toLit(var2 + i)));
					}
					if (var3 != -2) {
						assert(s->assigns[var3 + i] == l_True);
						veci_push(&lits1, lit_neg(toLit(var3 + i)));
					}
				}
			}
			else {
				veci_push(&lits1, lit_neg(toLit(v4)));
				if (x == l_True) {
					veci_push(&lits1, lit_neg(toLit(v1)));
					if (var2 != -2) {
						assert(s->assigns[var2 + i] == l_False);
						veci_push(&lits1, toLit(var2 + i));
					}
				}
				else if (x == l_False) {
					veci_push(&lits1, toLit(v1));
					if (var3 != -2) {
						assert(s->assigns[var3 + i] == l_False);
						veci_push(&lits1, toLit(var3 + i));
					}
				}
				else {
					if (var2 != -2) {
						assert(s->assigns[var2 + i] == l_False);
						veci_push(&lits1, toLit(var2 + i));
					}
					if (var3 != -2) {
						assert(s->assigns[var3 + i] == l_False);
						veci_push(&lits1, toLit(var3 + i));
					}
				}
			}

			che &= (che - (int64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}
		veci_delete(&lits1);
		return 0;
	}

	unsigned long int xlp, xup, ylp, yup, zlp, zup;

	xlp = xl | (wl&(~zu)) | ((~wu)&zl);
	xup = xu&(~((wl&(~yu)) | ((~wu)&yl)));
	ylp = yl | (wl&(xl | (~zu)));
	yup = yu&(~((~wu)&(xl | zl)));
	zlp = zl | (wl&((~xu) | (~yu)));
	zup = zu&(~((~wu)&((~xu) | yl)));

	unsigned long int z;

	z = xlp^xl;
	if (z) {
		uplw1->lower = xlp;
		enque_pos(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = xup^xu;
	if (z) {
		uplw1->upper = xup;
		enque_neg(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = ylp^yl;
	if (z) {
		uplw2->lower = ylp;
		enque_pos(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = yup^yu;
	if (z) {
		uplw2->upper = yup;
		enque_neg(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = zlp^zl;
	if (z) {
		uplw3->lower = zlp;
		enque_pos(s, bitwid, var3, z, wsf, 3);
		enqueue_prop(s, uplw3->word_num);
	}

	z = zup^zu;
	if (z) {
		uplw3->upper = zup;
		enque_neg(s, bitwid, var3, z, wsf, 3);
		enqueue_prop(s, uplw3->word_num);
	}

	z = wlp^wl;
	if (z) {
		uplw4->lower = wlp;
		enque_pos(s, bitwid, var4, z, wsf, 4);
		enqueue_prop(s, uplw4->word_num);
	}

	z = wup^wu;
	if (z) {
		uplw4->upper = wup;
		enque_neg(s, bitwid, var4, z, wsf, 4);
		enqueue_prop(s, uplw4->word_num);
	}
	return 1;
}

int negation(solver *s, int var1, int var2, struct ul *uplw1, struct ul *uplw2, vecp* confl, int bitwid, 
	unsigned long int ax, struct ws_flag* wsf) {
	unsigned long int xl, xu, yl, yu;
	unsigned long int xlp, xup;

	if (var1 != -2) {
		xl = uplw1->lower;
		xu = uplw1->upper;

	}
	else {
		xl = ax;
		xu = ax;
	}

	yl = uplw2->lower;
	yu = uplw2->upper;

	unsigned long int mask;
	if (bitwid == 64)
		mask = (uint64_t)(-1);
	else
		mask = ~((uint64_t)(-1) << bitwid); // 0000001111111;

	xlp = (xl | (~yu)) & mask;
	xup = xu & (~yl);

	unsigned long int che = check_valid_word(xlp, xup);

	if (che != (uint64_t)(-1)) {
		veci lits1;
		veci_new(&lits1);

		che = ~che; int i;
		while (che) {
			i = bitwid - __builtin_ffsl(che);

			if (var1 != -2) {
				int v1 = var1 + i;
				if (s->assigns[v1] == l_True) {
					veci_push(&lits1, lit_neg(toLit(v1)));

					assert(s->assigns[var2 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
				else {
					veci_push(&lits1, toLit(v1));

					assert(s->assigns[var2 + i] == l_False);
					veci_push(&lits1, toLit(var2 + i));
				}
			}
			else {
				int v2 = var2 + i;
				if (s->assigns[v2] == l_True) {
					veci_push(&lits1, lit_neg(toLit(v2)));
				}
				else {
					assert(s->assigns[v2] == l_False);
					veci_push(&lits1, toLit(v2));
				}
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}

		veci_delete(&lits1);
		return 0;
	}

	unsigned long int ylp, yup;

	ylp = (yl | (~xu)) & mask;
	yup = yu & (~xl);

	unsigned long int z;

	z = xlp^xl;
	if (z) {
		uplw1->lower = xlp;
		enque_pos(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = xup^xu;
	if (z) {
		uplw1->upper = xup;
		enque_neg(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = ylp^yl;
	if (z) {
		uplw2->lower = ylp;
		enque_pos(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = yup^yu;
	if (z) {
		uplw2->upper = yup;
		enque_neg(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}
	return 1;
}

int leftshift(solver *s, int var1, int var2, struct ul *uplw1, struct ul *uplw2, int shiftbits, vecp* confl, int bitwid, 
	unsigned long int ax, struct ws_flag* wsf) {
	unsigned long int xl, xu, yl, yu;
	unsigned long int ylp, yup;
	unsigned long int mask;

	if (var1 != -2) {
		xl = uplw1->lower;
		xu = uplw1->upper;
	}
	else {
		xl = ax;
		xu = ax;
	}

	yl = uplw2->lower;
	yu = uplw2->upper;

	mask = (~((uint64_t)(-1) << (bitwid - shiftbits))) << shiftbits; // 0000 1111111111100

	ylp = ((xl << shiftbits) | yl) & mask;
	yup = (xu << shiftbits)&yu;


	unsigned long int che;   int confl_flag = 0;
	veci lits1;
	veci_new(&lits1);

	che = check_valid_word(ylp, yup);
	if (che != (uint64_t)(-1)) {
		confl_flag = 1;

		che = ~che; int i;
		while (che) {
			i = bitwid - __builtin_ffsl(che);

			if (var1 != -2) {
				int v2 = var2 + i;
				if (s->assigns[v2] == l_True) {
					veci_push(&lits1, lit_neg(toLit(v2)));

					assert(s->assigns[var1 + i + shiftbits] == l_False);
					veci_push(&lits1, toLit(var1 + i + shiftbits));
				}
				else {
					veci_push(&lits1, toLit(v2));

					assert(s->assigns[var1 + i + shiftbits] == l_True);
					veci_push(&lits1, lit_neg(toLit(var1 + i + shiftbits)));
				}
			}
			else {
				int v2 = var2 + i;
				if (s->assigns[v2] == l_False) {
					veci_push(&lits1, toLit(v2));
				}
				else {
					assert(s->assigns[v2] == l_True);
					veci_push(&lits1, lit_neg(toLit(v2)));
				}
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}
	}

	che = check_valid_word(yl, yup);
	che = ~che; che = che & (~((uint64_t)(-1) << shiftbits));
	if (che) {
		confl_flag = 1;

		while (che) {
			assert(s->assigns[var2 + bitwid - __builtin_ffsl(che)] == l_True);
			veci_push(&lits1, lit_neg(toLit(var2 + bitwid - __builtin_ffsl(che))));

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}
	}

	if (confl_flag) {
		veci_delete(&lits1);
		return 0;
	}
	else {
		veci_delete(&lits1);
	}

	unsigned long int xlp, xup;
	mask = (~((uint64_t)(-1) << shiftbits)) << (bitwid - shiftbits);   // 0000 1100000000000
	xlp = xl | (yl >> shiftbits);
	xup = ((yu >> shiftbits) | mask) & xu;

	unsigned long int z;

	z = xlp^xl;
	if (z) {
		uplw1->lower = xlp;
		enque_pos(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = xup^xu;
	if (z) {
		uplw1->upper = xup;
		enque_neg(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = ylp^yl;
	if (z) {
		uplw2->lower = ylp;
		enque_pos(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = yup^yu;
	if (z) {
		uplw2->upper = yup;
		enque_neg(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}
	return 1;
}

int rightshift(solver *s, int var1, int var2, struct ul *uplw1, struct ul *uplw2, int shiftbits, vecp* confl, int bitwid, 
	unsigned long int ax, struct ws_flag* wsf) {
	unsigned long int xl, xu, yl, yu;
	unsigned long int ylp, yup;

	if (var1 != -2) {
		xl = uplw1->lower;
		xu = uplw1->upper;
	}
	else {
		xl = ax;
		xu = ax;
	}

	yl = uplw2->lower;
	yu = uplw2->upper;

	unsigned long int mask1 = (~((uint64_t)(-1) << (bitwid - shiftbits)));  // 0000 001111111   

	unsigned long int mask2 = (~((uint64_t)(-1) << (shiftbits)));         // 0000 000000011

	ylp = ((xl >> shiftbits) | yl)&mask1;
	yup = (xu >> shiftbits)&yu;

	unsigned long int che;  int confl_flag = 0;

	veci lits1;
	veci_new(&lits1);

	che = check_valid_word(ylp, yup);
	if (che != (uint64_t)(-1)) {
		confl_flag = 1;
		che = ~che;
		while (che) {
			int i = bitwid - __builtin_ffsl(che);

			if (var1 != -2) {
				int v1 = var1 + i - shiftbits;
				if (s->assigns[v1] == l_True) {
					veci_push(&lits1, lit_neg(toLit(v1)));

					assert(s->assigns[var2 + i] == l_False);
					veci_push(&lits1, toLit(var2 + i));
				}
				else {
					assert(s->assigns[v1] == l_False);
					veci_push(&lits1, toLit(v1));

					assert(s->assigns[var2 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
			}
			else {
				int v2 = var2 + i;
				if (s->assigns[v2] == l_True)
					veci_push(&lits1, lit_neg(toLit(v2)));
				else {
					assert(s->assigns[v2] == l_False);
					veci_push(&lits1, toLit(v2));
				}
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}
	}

	unsigned long int mask4 = mask2 << (bitwid - shiftbits); // 0000 110000000  
	che = check_valid_word(yl, yup);
	che = ~che; che = che & mask4;
	if (che) {
		confl_flag = 1;
		while (che) {
			assert(s->assigns[var2 + bitwid - __builtin_ffsl(che)] == l_True);
			veci_push(&lits1, lit_neg(toLit(var2 + bitwid - __builtin_ffsl(che))));

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}
	}

	if (confl_flag) {
		veci_delete(&lits1);
		return 0;
	}
	else {
		veci_delete(&lits1);
	}

	unsigned long int xlp, xup;
	unsigned long int mask;
	if (bitwid == 64) {
		mask = (uint64_t)(-1);
	}
	else {
		mask = ~((uint64_t)(-1) << bitwid);
	}

	xlp = (xl | (yl << shiftbits)) & mask;
	xup = ((yu << shiftbits) | mask2)&xu;

	unsigned long int z;

	z = xlp^xl;
	if (z) {
		uplw1->lower = xlp;
		enque_pos(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = xup^xu;
	if (z) {
		uplw1->upper = xup;
		enque_neg(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = ylp^yl;
	if (z) {
		uplw2->lower = ylp;
		enque_pos(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = yup^yu;
	if (z) {
		uplw2->upper = yup;
		enque_neg(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}
	return 1;
}

int bvsrshift(solver *s, int var1, int var2, struct ul *uplw1, struct ul *uplw2, int shiftbits, vecp* confl, int bitwid,
	unsigned long int ax, struct ws_flag* wsf) // arithmetic right shift
{
	lbool* values = s->assigns;
	int word_num1 = 0, word_num2 = 0;

	unsigned long int xl, xu, yl, yu;
	unsigned long int xlp, xup, ylp, yup;
	unsigned long int mask1, mask2;

	if (var1 != -2) {
		word_num1 = uplw1->word_num;
		xl = uplw1->lower;
		xu = uplw1->upper;
	}
	else {
		xl = ax;
		xu = ax;
	}

	word_num2 = uplw2->word_num;
	yl = uplw2->lower;
	yu = uplw2->upper;


	mask1 = (~((uint64_t)(-1) << (bitwid - shiftbits)));  // 0000 0011111111
	mask2 = (~((uint64_t)(-1) << (shiftbits)));         // 0000 0000000011

	if (var1 != -2) {
		if (values[var1] == l_False) {
			if (bitwid == 64) {
				ylp = ((xl >> shiftbits) | yl)&mask1;
				yup = (xu >> shiftbits)&yu;
				xlp = xl | (yl << shiftbits);
				xup = ((yu << shiftbits) | mask2) &xu;
			}
			else {
				unsigned long int mask = ~((uint64_t)(-1) << bitwid); // 0000 111111111
				ylp = ((xl >> shiftbits) | yl)&mask1;
				yup = (xu >> shiftbits)&yu;
				xlp = (xl | (yl << shiftbits)) &mask;
				xup = ((yu << shiftbits) | mask2) &xu;
			}
		}
		else if (values[var1] == l_Undef) {
			//undef
			unsigned long int yll = yl >> (bitwid - 1 - shiftbits);
			unsigned long int yuu;

			if (shiftbits + 1 == 64)
				yuu = ~(yu >> (bitwid - 1 - shiftbits));
			else
				yuu = ~((yu >> (bitwid - 1 - shiftbits)) | ((uint64_t)(-1) << (shiftbits + 1)));
			if (yll != (uint64_t)0 && yuu != (uint64_t)0) // y_i is fixed to 1, while y_j is fixed to 0; conflict!
			{
				veci lits1;
				veci_new(&lits1);

				while (yll) {
					int i = shiftbits + 1 - __builtin_ffsl(yll);

					veci_push(&lits1, lit_neg(toLit(var2 + i)));
					while (yuu) {
						int j = shiftbits + 1 - __builtin_ffsl(yuu);

						assert(s->assigns[var2 + j] == l_False);
						veci_push(&lits1, toLit(var2 + j));

						yuu &= (yuu - (uint64_t)1);

						vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
						veci_resize(&lits1, 1);
					}

					yll &= (yll - (uint64_t)1);
					veci_resize(&lits1, 0);
				}

				// check the rest if there is conflict
				unsigned long int mask4 = mask2 << (bitwid - shiftbits); // 0000 110000000
				if (bitwid == 64) {
					ylp = (xl >> shiftbits) | yl;
					yup = ((xu >> shiftbits) | mask4)&yu;
					xlp = xl | (yl << shiftbits);
					xup = ((yu << shiftbits) | mask2) &xu;
				}
				else {
					unsigned long int mask = ~((uint64_t)(-1) << bitwid); // 0000 1111111111
					ylp = (xl >> shiftbits) | yl;
					yup = ((xu >> shiftbits) | mask4)&yu;
					xlp = (xl | (yl << shiftbits)) & mask;
					xup = ((yu << shiftbits) | mask2) &xu;
				}

				unsigned long int che = check_valid_word(xlp, xup);

				if (che != (uint64_t)(-1)) {
					veci lits1;
					veci_new(&lits1);

					che = ~che; int i;

					while (che) {
						i = bitwid - __builtin_ffsl(che);

						int v1 = var1 + i;
						if (values[v1] == l_True) {
							veci_push(&lits1, lit_neg(toLit(v1)));
							assert(s->assigns[var2 + i + shiftbits] == l_False);
							veci_push(&lits1, toLit(var2 + i + shiftbits));
						}
						else {
							assert(s->assigns[v1] == l_False);
							veci_push(&lits1, toLit(v1));
							assert(s->assigns[var2 + i + shiftbits] == l_True);
							veci_push(&lits1, lit_neg(toLit(var2 + i + shiftbits)));
						}

						che &= (che - (uint64_t)1);
						vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
						veci_resize(&lits1, 0);
					}
				}
				veci_delete(&lits1);
				return 0;
			}
			else {
				if (yll != (uint64_t)0) // exit y_i fixed to 1
				{
					unsigned long int mask3 = (~((uint64_t)(-1) << (shiftbits + 1))); // 0000 00000011(1)
					unsigned long int mask4 = mask3 << (bitwid - 1 - shiftbits); // 0000 11(1)000000
					if (bitwid == 64) {
						ylp = ((xl >> shiftbits) | yl) | mask4;
						yup = ((xu >> shiftbits)&yu) | mask4;
						xlp = xl | (yl << shiftbits) | ((uint64_t)1 << (bitwid - 1));
						xup = ((yu << shiftbits) | mask2) &xu;
					}
					else {
						unsigned long int mask = ~((uint64_t)(-1) << bitwid); // 0000 111111111
						ylp = ((xl >> shiftbits) | yl) | mask4;
						yup = ((xu >> shiftbits)&yu) | mask4;
						xlp = (xl | (yl << shiftbits) | ((uint64_t)1 << (bitwid - 1))) &mask;
						xup = ((yu << shiftbits) | mask2) &xu;
					}
				}
				else if (yuu != (uint64_t)0) // exit y_i fixed to 0
				{
					unsigned long int mask_headx = ~((uint64_t)1 << (bitwid - 1));
					unsigned long int mask_heady = ~((uint64_t)1 << (bitwid - 1 - shiftbits));
					if (bitwid == 64) {
						ylp = ((xl >> shiftbits) | yl)&mask1;
						yup = (xu >> shiftbits)&yu & mask_heady;
						xlp = xl | (yl << shiftbits);
						xup = ((yu << shiftbits) | mask2) &xu & mask_headx;
					}
					else {
						unsigned long int mask = ~((uint64_t)(-1) << bitwid); // 0000 111111111

						ylp = ((xl >> shiftbits) | yl)&mask1;
						yup = (xu >> shiftbits)&yu & mask_heady;
						xlp = (xl | (yl << shiftbits)) &mask;
						xup = ((yu << shiftbits) | mask2) &xu & mask_headx;
					}
				}
				else // still dont know
				{
					unsigned long int mask4 = mask2 << (bitwid - shiftbits); // 0000 110000000
					if (bitwid == 64) {
						ylp = (xl >> shiftbits) | yl;
						yup = ((xu >> shiftbits) | mask4)&yu;
						xlp = xl | (yl << shiftbits);
						xup = ((yu << shiftbits) | mask2) &xu;
					}
					else {
						unsigned long int mask = ~((uint64_t)(-1) << bitwid); // 0000 1111111111
						ylp = (xl >> shiftbits) | yl;
						yup = ((xu >> shiftbits) | mask4)&yu;
						xlp = (xl | (yl << shiftbits)) & mask;
						xup = ((yu << shiftbits) | mask2) &xu;
					}
				}
			}
		}
		else {
			//true
			unsigned long int mask4 = mask2 << (bitwid - shiftbits); // 0000 110000000
			if (bitwid == 64) {
				ylp = ((xl >> shiftbits) | yl) | mask4;
				yup = ((xu >> shiftbits)&yu) | mask4;
				xlp = xl | (yl << shiftbits);
				xup = ((yu << shiftbits) | mask2) &xu;
			}
			else {
				unsigned long int mask = ~((uint64_t)(-1) << bitwid); // 0000 111111111
				ylp = ((xl >> shiftbits) | yl) | mask4;
				yup = ((xu >> shiftbits)&yu) | mask4;
				xlp = (xl | (yl << shiftbits)) &mask;
				xup = ((yu << shiftbits) | mask2) &xu;
			}
		}
	}
	else {        //x is constant number

		if ((ax >> (bitwid - 1)))  // get the first bit of x
		{
			//true
			unsigned long int mask4 = mask2 << (bitwid - shiftbits); // 0000 110000000
			if (bitwid == 64) {
				ylp = ((xl >> shiftbits) | yl) | mask4;
				yup = ((xu >> shiftbits)&yu) | mask4;
				xlp = xl | (yl << shiftbits);
				xup = ((yu << shiftbits) | mask2) &xu;
			}
			else {
				unsigned long int mask = ~((uint64_t)(-1) << bitwid); // 0000 111111111
				ylp = ((xl >> shiftbits) | yl) | mask4;
				yup = ((xu >> shiftbits)&yu) | mask4;
				xlp = (xl | (yl << shiftbits)) &mask;
				xup = ((yu << shiftbits) | mask2) &xu;
			}
		}
		else {
			//false
			if (bitwid == 64) {
				ylp = ((xl >> shiftbits) | yl)&mask1;
				yup = (xu >> shiftbits)&yu;
				xlp = xl | (yl << shiftbits);
				xup = ((yu << shiftbits) | mask2) &xu;
			}
			else {
				unsigned long int mask = ~((uint64_t)(-1) << bitwid); // 0000 111111111
				ylp = ((xl >> shiftbits) | yl)&mask1;
				yup = (xu >> shiftbits)&yu;
				xlp = (xl | (yl << shiftbits)) &mask;
				xup = ((yu << shiftbits) | mask2) &xu;
			}
		}
	}

	int confl_flag = 0;
	unsigned long int che;

	che = check_valid_word(xlp, xup);

	veci lits1;
	veci_new(&lits1);

	if (che != (uint64_t)(-1)) {
		confl_flag = 1;

		che = ~che; int i;
		while (che) {
			i = bitwid - __builtin_ffsl(che);

			if (var1 != -2) {
				int v1 = var1 + i;
				if (values[v1] == l_True) {
					veci_push(&lits1, lit_neg(toLit(v1)));

					assert(s->assigns[var2 + i + shiftbits] == l_False);
					veci_push(&lits1, toLit(var2 + i + shiftbits));
				}
				else {
					veci_push(&lits1, toLit(v1));

					assert(s->assigns[var2 + i + shiftbits] == l_True);
					veci_push(&lits1, lit_neg(toLit(var2 + i + shiftbits)));
				}
			}
			else {
				int v2 = var2 + i + shiftbits;
				if (values[v2] == l_True)
					veci_push(&lits1, lit_neg(toLit(v2)));
				else {
					assert(s->assigns[v2] == l_False);
					veci_push(&lits1, toLit(v2));
				}
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}
	}

	unsigned long int mask4 = mask2 << (bitwid - shiftbits); // 0000 110000000    
	che = check_valid_word(yl, yup);
	che = ~che; che = che & mask4;
	if (che) {
		confl_flag = 1;
		while (che) {
			assert(s->assigns[var2 + bitwid - __builtin_ffsl(che)] == l_True);
			veci_push(&lits1, lit_neg(toLit(var2 + bitwid - __builtin_ffsl(che))));
			if (var1 != -2) {
				assert(s->assigns[var1] == l_False);
				veci_push(&lits1, toLit(var1));
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);

		}
	}

	che = check_valid_word(ylp, yu);
	che = ~che; che = che & mask4;
	if (che) {
		confl_flag = 1;

		while (che) {
			assert(s->assigns[var2 + bitwid - __builtin_ffsl(che)] == l_False);
			veci_push(&lits1, toLit(var2 + bitwid - __builtin_ffsl(che)));
			if (var1 != -2) {
				assert(s->assigns[var1] == l_True);
				veci_push(&lits1, lit_neg(toLit(var1)));
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}
	}

	if (confl_flag) {
		veci_delete(&lits1);
		return 0;
	}
	else {
		veci_delete(&lits1);
	}

	unsigned long int z;

	z = xlp^xl;
	if (z) {
		uplw1->lower = xlp;
		enque_pos(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, word_num1);
	}

	z = xup^xu;
	if (z) {
		uplw1->upper = xup;
		enque_neg(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, word_num1);
	}

	z = ylp^yl;
	if (z) {
		uplw2->lower = ylp;
		enque_pos(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, word_num2);
	}

	z = yup^yu;
	if (z) {
		uplw2->upper = yup;
		enque_neg(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, word_num2);
	}
	return 1;
}


int zero_extend(solver *s, int var1, int var2, struct ul *uplw1, struct ul *uplw2, vecp* confl, int addbits, int orgbits, 
	unsigned long int ax, struct ws_flag * wsf) {
	int modibits = addbits + orgbits;

	unsigned long int xl, xu, yl, yu;
	unsigned long int ylp, yup;

	if (var1 != -2) {
		xl = uplw1->lower;
		xu = uplw1->upper;
	}
	else {
		xl = ax;
		xu = ax;
	}

	yl = uplw2->lower;
	yu = uplw2->upper;

	unsigned long int mask1 = ~((uint64_t)(-1) << (orgbits)); // 0000 11111111 of x

	ylp = (xl | yl) & mask1;
	yup = xu & yu;

	unsigned long int che;  int confl_flag = 0;
	veci lits1;
	veci_new(&lits1);

	che = check_valid_word(ylp, yup);
	if (che != (uint64_t)(-1)) {
		confl_flag = 1;

		che = ~che;
		while (che) {
			int i = modibits - __builtin_ffsl(che);
			int v2 = var2 + i;
			if (var1 != -2) {
				int v1 = var1 + i - addbits;
				if (s->assigns[v1] == l_True) {
					veci_push(&lits1, lit_neg(toLit(v1)));

					assert(s->assigns[v2] == l_False);
					veci_push(&lits1, toLit(v2));
				}
				else {
					veci_push(&lits1, toLit(v1));

					assert(s->assigns[v2] == l_True);
					veci_push(&lits1, lit_neg(toLit(v2)));
				}
			}
			else {
				if (s->assigns[v2] == l_True) {
					veci_push(&lits1, lit_neg(toLit(v2)));
				}
				else {
					assert(s->assigns[v2] == l_False);
					veci_push(&lits1, toLit(v2));
				}
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}

	}

	unsigned long int mask2 = ~((uint64_t)(-1) << addbits); // 0000 000011111111
	unsigned long int mask3 = mask2 << orgbits;    // 0000 111111110000 

	che = check_valid_word(yl, yup);
	che = ~che; che = che & mask3;
	if (che) {
		confl_flag = 1;
		while (che) {
			assert(s->assigns[var2 + modibits - __builtin_ffsl(che)] == l_True);

			veci_push(&lits1, lit_neg(toLit(var2 + modibits - __builtin_ffsl(che))));
			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}

	}

	if (confl_flag) {
		veci_delete(&lits1);
		return 0;
	}
	else {
		veci_delete(&lits1);
	}

	unsigned long int xlp = ylp;
	unsigned long int xup = yup;

	unsigned long int z;

	z = xlp^xl;
	if (z) {
		uplw1->lower = xlp;
		enque_pos(s, orgbits, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = xup^xu;
	if (z) {
		uplw1->upper = xup;
		enque_neg(s, orgbits, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = ylp^yl;
	if (z) {
		uplw2->lower = ylp;
		enque_pos(s, modibits, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = yup^yu;
	if (z) {
		uplw2->upper = yup;
		enque_neg(s, modibits, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}
	return 1;
}

int sign_extend(solver *s, int var1, int var2, struct ul *uplw1, struct ul *uplw2, vecp* confl, int addbits, int orgbits, 
	unsigned long int ax, struct ws_flag* wsf) {
	int modibits = addbits + orgbits;

	lbool* values = s->assigns;

	unsigned long int xl, xu, yl, yu;
	unsigned long int xlp, xup, ylp, yup;

	if (var1 != -2) {
		xl = uplw1->lower;
		xu = uplw1->upper;
	}
	else {
		xl = ax;
		xu = ax;
	}

	yl = uplw2->lower;
	yu = uplw2->upper;

	if (var1 != -2) {
		if (values[var1] == l_True) {
			unsigned long int mask1 = ~((uint64_t)(-1) << addbits); // 0000 000011111111
			unsigned long int mask2 = mask1 << orgbits;    // 0000 111111110000 
			unsigned long int mask3 = ~((uint64_t)(-1) << orgbits);// 0000 000000001111
			//true

			xlp = xl | (yl & mask3);
			ylp = xlp | mask2;
			xup = xu & yu;
			yup = xup | mask2;

		}
		else if (values[var1] == l_Undef) {
			unsigned long int yll = yl >> (orgbits - 1);
			unsigned long int yuu;
			if (addbits + 1 == 64)
				yuu = ~(yu >> (orgbits - 1));
			else
				yuu = ~((yu >> (orgbits - 1)) | ((uint64_t)(-1) << (addbits + 1)));
			if (yll != (uint64_t)0 && yuu != (uint64_t)0) // y_i is fixed to 1, while y_j is fixed to 0
			{
				veci lits1;
				veci_new(&lits1);

				while (yll) {
					int i = addbits + 1 - __builtin_ffsl(yll);

					assert(s->assigns[var2 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var2 + i)));
					while (yuu) {
						int j = addbits + 1 - __builtin_ffsl(yuu);

						assert(s->assigns[var2 + j] == l_False);
						veci_push(&lits1, toLit(var2 + j));

						yuu &= (yuu - (uint64_t)1);

						vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
						veci_resize(&lits1, 1);
					}

					yll &= (yll - (uint64_t)1);
					veci_resize(&lits1, 0);
				}

				unsigned long int mask3 = ~((uint64_t)(-1) << orgbits);// 0000 000000001111
				// see if there is confl in the rest of the bits x_0 .. x_n

				xlp = xl | (yl & mask3);
				ylp = xlp;
				xup = xu & yu;
				yup = xup;

				unsigned long int che; lbool *values = s->assigns;
				che = check_valid_word(ylp, yup);
				if (che != (uint64_t)(-1)) {
					che = ~che;
					while (che) {
						int i = modibits - __builtin_ffsl(che);

						int v1 = var1 + i - addbits;
						if (values[v1] == l_True) {
							veci_push(&lits1, lit_neg(toLit(v1)));
							assert(s->assigns[var2 + i] == l_False);
							veci_push(&lits1, toLit(var2 + i));

						}
						else {
							assert(s->assigns[v1] == l_False);
							veci_push(&lits1, toLit(v1));

							assert(s->assigns[var2 + i] == l_True);
							veci_push(&lits1, lit_neg(toLit(var2 + i)));
						}

						che &= (che - (uint64_t)1);
						vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
						veci_resize(&lits1, 0);
					}
				}

				veci_delete(&lits1);
				return 0;
			}
			else {
				if (yll != (uint64_t)0) // exit y_i fixed to 1
				{
					unsigned long int mask1 = ~((uint64_t)(-1) << addbits); // 0000 000011111111
					unsigned long int mask2 = mask1 << orgbits;    // 0000 111111110000 
					unsigned long int mask3 = ~((uint64_t)(-1) << orgbits);// 0000 000000001111
					//fix x_0 to true

					xlp = xl | (yl & mask3) | ((uint64_t)1 << (orgbits - 1));
					ylp = xlp | mask2;
					xup = xu & yu;
					yup = xup | mask2;
				}
				else if (yuu != (uint64_t)0) // exit y_i fixed to 0
				{
					unsigned long int mask3 = ~((uint64_t)(-1) << orgbits);
					//fix x to false
					xlp = xl | (yl & mask3);
					ylp = xlp;
					xup = xu & yu & (~((uint64_t)1 << (orgbits - 1)));
					yup = xup;
				}
				else // still dont know
				{
					unsigned long int mask1 = ~((uint64_t)(-1) << addbits); // 0000 000011111111
					unsigned long int mask2 = mask1 << orgbits;    // 0000 111111110000 
					unsigned long int mask3 = ~((uint64_t)(-1) << orgbits);// 0000 000000001111
					//undef

					xlp = xl | (yl & mask3);
					ylp = yl | xl;
					xup = xu & yu;
					yup = yu & (xu | mask2);
				}
			}

		}
		else {
			unsigned long int mask3 = ~((uint64_t)(-1) << orgbits);
			//false
			xlp = xl | (yl & mask3);
			ylp = xlp;
			xup = xu & yu;
			yup = xup;

		}
	}
	else {
		if ((ax >> (orgbits - 1))) {
			unsigned long int mask1 = ~((uint64_t)(-1) << addbits);  // 0000 000011111111
			unsigned long int mask2 = mask1 << orgbits;     // 0000 111111110000 
			unsigned long int mask3 = ~((uint64_t)(-1) << orgbits); // 0000 000000001111

			xlp = xl | (yl & mask3);
			ylp = xlp | mask2;
			xup = xu & yu;
			yup = xup | mask2;

		}
		else {
			unsigned long int mask3 = ~((uint64_t)(-1) << orgbits);

			xlp = xl | (yl & mask3);
			ylp = xlp;
			xup = xu & yu;
			yup = xup;
		}
	}

	veci lits1;
	veci_new(&lits1);
	int confl_flag = 0;

	unsigned long int che;
	che = check_valid_word(ylp, yup);
	if (che != (uint64_t)(-1)) {
		confl_flag = 1;
		che = ~che;

		while (che) {
			int i = modibits - __builtin_ffsl(che);

			if (var1 != -2) {
				int v1 = var1 + i - addbits;
				if (values[v1] == l_True) {
					veci_push(&lits1, lit_neg(toLit(v1)));

					assert(s->assigns[var2 + i] == l_False);
					veci_push(&lits1, toLit(var2 + i));

				}
				else {
					veci_push(&lits1, toLit(v1));

					assert(s->assigns[var2 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}

			}
			else {
				int v2 = var2 + i;
				if (values[v2] == l_True) {
					veci_push(&lits1, lit_neg(toLit(v2)));
				}
				else {
					assert(s->assigns[v2] == l_False);
					veci_push(&lits1, toLit(v2));
				}
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);

		}
	}

	unsigned long int mask1 = ~((uint64_t)(-1) << addbits); // 0000 000011111111
	unsigned long int mask2 = mask1 << orgbits;    // 0000 111111110000 

	che = check_valid_word(yl, yup);
	che = ~che; che = che & mask2;
	if (che) {
		confl_flag = 1;

		while (che) {
			assert(s->assigns[var2 + modibits - __builtin_ffsl(che)] == l_True);
			veci_push(&lits1, lit_neg(toLit(var2 + modibits - __builtin_ffsl(che))));
			if (var1 != -2) {
				assert(s->assigns[var1] == l_False);
				veci_push(&lits1, toLit(var1));
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);

		}
	}

	che = check_valid_word(ylp, yu);
	che = ~che; che = che & mask2;
	if (che) {
		confl_flag = 1;

		while (che) {
			assert(s->assigns[var2 + modibits - __builtin_ffsl(che)] == l_False);
			veci_push(&lits1, toLit(var2 + modibits - __builtin_ffsl(che)));
			if (var1 != -2) {
				assert(s->assigns[var1] == l_True);
				veci_push(&lits1, lit_neg(toLit(var1)));
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}
	}

	if (confl_flag)

	{
		veci_delete(&lits1);
		return 0;
	}
	else {
		veci_delete(&lits1);
	}

	unsigned long int z;

	z = xlp^xl;

	if (z) {
		uplw1->lower = xlp;
		enque_pos(s, orgbits, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = xup^xu;

	if (z) {
		uplw1->upper = xup;
		enque_neg(s, orgbits, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = ylp^yl;

	if (z) {
		uplw2->lower = ylp;
		enque_pos(s, modibits, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = yup^yu;

	if (z) {
		uplw2->upper = yup;
		enque_neg(s, modibits, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}
	return 1;
}

int bvconcat(solver *s, int var1, int var2, int var3, struct ul *uplw1, struct ul *uplw2, struct ul *uplw3, vecp* confl, 
	int bitwid, int subwid1, int subwid2, unsigned long int ax, unsigned long int ay, struct ws_flag* wsf) {
	unsigned long int xl, xu, yl, yu, zl, zu;
	unsigned long int zlp, zup;

	if (var1 != -2) {
		xl = uplw1->lower;
		xu = uplw1->upper;
	}
	else {
		xl = ax;
		xu = ax;
	}

	if (var2 != -2) {
		yl = uplw2->lower;
		yu = uplw2->upper;
	}
	else {
		yl = ay;
		yu = ay;
	}

	zl = uplw3->lower;
	zu = uplw3->upper;

	zlp = zl | ((xl << subwid2) | yl);
	zup = zu & ((xu << subwid2) | yu);

	unsigned long int che = check_valid_word(zlp, zup);
	if (che != (uint64_t)(-1)) {
		veci lits1;
		veci_new(&lits1);

		che = ~che; int i; int v3;

		while (che) {
			i = bitwid - __builtin_ffsl(che);
			v3 = var3 + i;

			if (s->assigns[v3] == l_True) {
				veci_push(&lits1, lit_neg(toLit(v3)));
				if (i < subwid1 && var1 != -2) {
					assert(s->assigns[var1 + i] == l_False);
					veci_push(&lits1, toLit(var1 + i));
				}
				if (i >= subwid1 && var2 != -2) {
					assert(s->assigns[var2 + i - subwid1] == l_False);
					veci_push(&lits1, toLit(var2 + i - subwid1));
				}
			}
			else {
				assert(s->assigns[v3] == l_False);
				veci_push(&lits1, toLit(v3));

				if (i < subwid1 && var1 != -2) {
					assert(s->assigns[var1 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var1 + i)));
				}
				if (i >= subwid1 && var2 != -2) {
					assert(s->assigns[var2 + i - subwid1] == l_True);
					veci_push(&lits1, lit_neg(toLit(var2 + i - subwid1)));
				}
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}

		veci_delete(&lits1);
		return 0;
	}

	unsigned long int xlp, xup, ylp, yup;
	unsigned long int mask = ~(((uint64_t)(-1)) << ((uint64_t)(subwid2)));  // 00000111111(subwid2)
	xlp = xl | (zl >> subwid2);
	xup = xu & (zu >> subwid2);
	ylp = yl | (zl & mask);
	yup = yu & (zu & mask);

	unsigned long int z;

	z = xlp^xl;
	if (z) {
		uplw1->lower = xlp;
		enque_pos(s, subwid1, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = xup^xu;
	if (z) {
		uplw1->upper = xup;
		enque_neg(s, subwid1, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}


	z = ylp^yl;
	if (z) {
		uplw2->lower = ylp;
		enque_pos(s, subwid2, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = yup^yu;
	if (z) {
		uplw2->upper = yup;
		enque_neg(s, subwid2, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = zlp^zl;
	if (z) {
		uplw3->lower = zlp;
		enque_pos(s, bitwid, var3, z, wsf, 3);
		enqueue_prop(s, uplw3->word_num);
	}

	z = zup^zu;
	if (z) {
		uplw3->upper = zup;
		enque_neg(s, bitwid, var3, z, wsf, 3);
		enqueue_prop(s, uplw3->word_num);
	}
	return 1;
}


int extract(solver *s, int var1, int var2, struct ul *uplw1, struct ul *uplw2, vecp* confl, int bitwid, int subwid1, 
	int subwid2, unsigned long int ax, struct ws_flag* wsf) {
	unsigned long int xl, xu, yl, yu;
	unsigned long int ylp, yup;

	if (var1 != -2) {
		xl = uplw1->lower;
		xu = uplw1->upper;
	}
	else {
		xl = ax;
		xu = ax;
	}

	yl = uplw2->lower;
	yu = uplw2->upper;

	int bit2 = subwid1 - subwid2 + 1;

	unsigned long int mask1;

	if (bit2 == 64)
		mask1 = (uint64_t)(-1);
	else
		mask1 = ~(((uint64_t)(-1)) << bit2);    // 0000000001111111(bit2)

	ylp = ((xl >> subwid2) | yl) & mask1;
	yup = (xu >> subwid2) & yu;

	unsigned long int che = check_valid_word(ylp, yup);

	if (che != ((uint64_t)(-1))) {
		veci lits1;
		veci_new(&lits1);

		che = ~che; int i; int v2;

		while (che) {

			i = bit2 - __builtin_ffsl(che);
			v2 = var2 + i;
			if (s->assigns[v2] == l_True) {
				veci_push(&lits1, lit_neg(toLit(v2)));
				if (var1 != -2) {
					assert(s->assigns[var1 + i + bitwid - subwid1 - 1] == l_False);
					veci_push(&lits1, toLit(var1 + i + bitwid - subwid1 - 1));
				}
			}
			else {
				veci_push(&lits1, toLit(v2));
				if (var1 != -2) {
					assert(s->assigns[var1 + i + bitwid - subwid1 - 1] == l_True);
					veci_push(&lits1, lit_neg(toLit(var1 + i + bitwid - subwid1 - 1)));
				}
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);

		}

		veci_delete(&lits1);
		return 0;
	}

	unsigned long int xlp, xup;

	unsigned long int mask3 = ~(mask1 << subwid2); // 1111111(subwid1)000000000(subwid2)1111111 
	xlp = xl | (yl << subwid2);
	xup = ((yu << subwid2) | mask3) & xu;

	unsigned long int z;

	z = xlp^xl;
	if (z) {
		uplw1->lower = xlp;
		enque_pos(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = xup^xu;
	if (z) {
		uplw1->upper = xup;
		enque_neg(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = ylp^yl;
	if (z) {
		uplw2->lower = ylp;
		enque_pos(s, bit2, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = yup^yu;
	if (z) {
		uplw2->upper = yup;
		enque_neg(s, bit2, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}
	return 1;
}


int inequall(solver *s, int var1, int var2, int var3, struct ul *uplw1, struct ul *uplw2, vecp *confl, int bitwid, 
	unsigned long int ax, unsigned long int ay, struct ws_flag* wsf) {
	unsigned long int xlp, xup, ylp, yup;

	if (var1 != -2) {
		xlp = uplw1->lower;
		xup = uplw1->upper;
	}
	else {
		xlp = ax;
		xup = ax;
	}

	if (var2 != -2) {
		ylp = uplw2->lower;
		yup = uplw2->upper;
	}
	else {
		ylp = ay;
		yup = ay;
	}

	if (check_valid_word(xlp | ylp, xup&yup) != (uint64_t)(-1)) // if some bits of x and y have already inequall
	{
		return 0;
	}

	if (xlp == xup && xlp == ylp && ylp == yup) {
		veci lits1;
		veci_new(&lits1);

		int i;
		if (var1 != -2) {
			if (var2 != -2) {
				for (i = bitwid - 1; i >= 0; xlp >>= 1, i--) {
					if ((xlp &(uint64_t)1)) {
						assert(s->assigns[var1 + i] == l_True);
						veci_push(&lits1, lit_neg(toLit(var1 + i)));

						assert(s->assigns[var2 + i] == l_True);
						veci_push(&lits1, lit_neg(toLit(var2 + i)));
					}
					else {
						assert(s->assigns[var1 + i] == l_False);
						veci_push(&lits1, toLit(var1 + i));

						assert(s->assigns[var2 + i] == l_False);
						veci_push(&lits1, toLit(var2 + i));
					}
				}
			}
			else {
				for (i = bitwid - 1; i >= 0; xlp >>= 1, i--) {
					if ((xlp &(uint64_t)1)) {
						assert(s->assigns[var1 + i] == l_True);
						veci_push(&lits1, lit_neg(toLit(var1 + i)));
					}
					else {
						assert(s->assigns[var1 + i] == l_False);
						veci_push(&lits1, toLit(var1 + i));
					}

				}
			}
		}
		else {
			if (var2 != -2) {
				for (i = bitwid - 1; i >= 0; ylp >>= 1, i--) {
					if ((ylp &(uint64_t)1)) {
						assert(s->assigns[var2 + i] == l_True);
						veci_push(&lits1, lit_neg(toLit(var2 + i)));
					}
					else {
						assert(s->assigns[var2 + i] == l_False);
						veci_push(&lits1, toLit(var2 + i));
					}

				}
			}
		}
		assert(s->assigns[var3] == l_False);
		veci_push(&lits1, toLit(var3));
		vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
		veci_delete(&lits1);
		return 0;
	}

	if (ylp == yup && yup == xup && xlp != xup) {
		unsigned long int z = xlp^xup;
		if (__builtin_popcountl(z) == 1) {
			uplw1->upper = xlp;
			int j = bitwid - __builtin_ffsl(z);
			enqueue(s, lit_neg(toLit(var1 + j)), wsf, 1);
			enqueue_prop(s, uplw1->word_num);
			return 0;
		}
	}
	else if (ylp == yup && yup == xlp && xlp != xup) {
		unsigned long int z = xlp^xup;
		if (__builtin_popcountl(z) == 1) {
			uplw1->lower = xup;
			int j = bitwid - __builtin_ffsl(z);
			enqueue(s, toLit(var1 + j), wsf, 1);
			enqueue_prop(s, uplw1->word_num);
			return 0;
		}
	}
	else if (xlp == xup && xup == yup && ylp != yup) {
		unsigned long int z = ylp^yup;
		if (__builtin_popcountl(z) == 1) {
			uplw2->upper = ylp;
			int j = bitwid - __builtin_ffsl(z);
			enqueue(s, lit_neg(toLit(var2 + j)), wsf, 2);
			enqueue_prop(s, uplw2->word_num);
			return 0;
		}
	}
	else if (xlp == xup && xup == ylp && ylp != yup) {
		unsigned long int z = ylp^yup;
		if (__builtin_popcountl(z) == 1) {
			uplw2->lower = yup;
			int j = bitwid - __builtin_ffsl(z);
			enqueue(s, toLit(var2 + j), wsf, 2);
			enqueue_prop(s, uplw2->word_num);
			return 0;
		}
	}
	return 0;
}


int equall(solver *s, int var1, int var2, int var3, struct ul *uplw1, struct ul *uplw2, vecp *confl, int bitwid, 
	unsigned long int ax, unsigned long int ay, struct ws_flag* wsf) {
	unsigned long int xl, xu, yl, yu;
	unsigned long int xlp, xup, ylp, yup;

	if (var1 != -2) {
		xl = uplw1->lower;
		xu = uplw1->upper;
	}
	else {
		xl = ax;
		xu = ax;
	}

	if (var2 != -2) {
		yl = uplw2->lower;
		yu = uplw2->upper;
	}
	else {
		yl = ay;
		yu = ay;
	}

	xlp = xl | yl;
	ylp = xlp;
	xup = xu&yu;
	yup = xup;

	unsigned long int che = check_valid_word(xlp, xup);
	if (che != (uint64_t)(-1)) {
		veci lits1;
		veci_new(&lits1);
		lbool* values = s->assigns;

		che = ~che; int i;
		while (che) {
			i = bitwid - __builtin_ffsl(che);

			if (var1 != -2) {
				int v1 = var1 + i;
				if (var2 != -2) {
					if (values[v1] == l_True) {
						assert(s->assigns[v1] == l_True);
						veci_push(&lits1, lit_neg(toLit(v1)));

						assert(s->assigns[var2 + i] == l_False);
						veci_push(&lits1, toLit(var2 + i));
					}
					else {
						assert(s->assigns[v1] == l_False);
						veci_push(&lits1, toLit(v1));

						assert(s->assigns[var2 + i] == l_True);
						veci_push(&lits1, lit_neg(toLit(var2 + i)));
					}
				}
				else {
					if (values[v1] == l_True) {
						assert(s->assigns[v1] == l_True);
						veci_push(&lits1, lit_neg(toLit(v1)));
					}
					else {
						assert(s->assigns[v1] == l_False);
						veci_push(&lits1, toLit(v1));
					}

				}
			}
			else {
				if (var2 != -2) {
					int v2 = var2 + i;
					if (values[v2] == l_True) {
						veci_push(&lits1, lit_neg(toLit(v2)));
					}
					else {
						assert(s->assigns[v2] == l_False);
						veci_push(&lits1, toLit(v2));
					}
				}
			}

			assert(s->assigns[var3] == l_True);
			veci_push(&lits1, lit_neg(toLit(var3)));

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}

		veci_delete(&lits1);
		return 0;
	}

	unsigned long int z;

	z = xlp^xl;
	if (z) {
		uplw1->lower = xlp;
		//assert(s->assigns[var3] == l_True);	
		enque_pos(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = xup^xu;
	if (z) {
		uplw1->upper = xup;
		//assert(s->assigns[var3] == l_True);	
		enque_neg(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = ylp^yl;
	if (z) {
		uplw2->lower = ylp;
		//assert(s->assigns[var3] == l_True);	
		enque_pos(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = yup^yu;
	if (z) {
		uplw2->upper = yup;
		//assert(s->assigns[var3] == l_True);	
		enque_neg(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	return 0;

}

int bvequall(solver *s, int var1, int var2, struct ul *uplw1, struct ul *uplw2, vecp *confl, int bitwid, 
	unsigned long int ax, unsigned long int ay, struct ws_flag* wsf) // var2 is never constant
{
	unsigned long int xl, xu, yl, yu;
	unsigned long int xlp, xup, ylp, yup;

	if (var1 != -2) {
		xl = uplw1->lower;
		xu = uplw1->upper;
	}
	else {
		xl = ax;
		xu = ax;
	}

	yl = ay;
	yu = ay;

	xlp = xl | yl;
	ylp = xlp;
	xup = xu&yu;
	yup = xup;

	unsigned long int che = check_valid_word(xlp, xup);
	if (che != (uint64_t)(-1)) {
		veci lits1;
		veci_new(&lits1);
		lbool* values = s->assigns;

		che = ~che; int i;
		while (che) {
			i = bitwid - __builtin_ffsl(che);

			if (var1 != -2) {
				int v1 = var1 + i;
				if (values[v1] == l_True) {
					assert(s->assigns[v1] == l_True);
					veci_push(&lits1, lit_neg(toLit(v1)));

					assert(s->assigns[var2 + i] == l_False);
					veci_push(&lits1, toLit(var2 + i));
				}
				else {
					assert(s->assigns[v1] == l_False);
					veci_push(&lits1, toLit(v1));

					assert(s->assigns[var2 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
			}
			else {
				int v2 = var2 + i;
				if (values[v2] == l_True) {
					veci_push(&lits1, lit_neg(toLit(v2)));
				}
				else {
					assert(s->assigns[v2] == l_False);
					veci_push(&lits1, toLit(v2));
				}
			}

			che &= (che - (uint64_t)1);
			vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
			veci_resize(&lits1, 0);
		}

		veci_delete(&lits1);
		return 0;
	}

	unsigned long int z;

	z = xlp^xl;
	if (z) {
		uplw1->lower = xlp;
		enque_pos(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = xup^xu;
	if (z) {
		uplw1->upper = xup;
		enque_neg(s, bitwid, var1, z, wsf, 1);
		enqueue_prop(s, uplw1->word_num);
	}

	z = ylp^yl;
	if (z) {
		uplw2->lower = ylp;
		enque_pos(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	z = yup^yu;
	if (z) {
		uplw2->upper = yup;
		enque_neg(s, bitwid, var2, z, wsf, 2);
		enqueue_prop(s, uplw2->word_num);
	}

	return 0;
}


int undef_equall(solver *s, int var1, int var2, int var3, struct ul *uplw1, struct ul *uplw2, int bitwid, 
	unsigned long int ax, unsigned long int ay, struct ws_flag* wsf) {
	unsigned long int xlp, xup, ylp, yup;

	int word_num3 = get_word_num(solver_read_wlist(s, toLit(var3)));

	if (var1 != -2) {
		xlp = uplw1->lower;
		xup = uplw1->upper;
	}
	else {
		xlp = ax;
		xup = ax;
	}

	if (var2 != -2) {
		ylp = uplw2->lower;
		yup = uplw2->upper;
	}
	else {
		ylp = ay;
		yup = ay;
	}


	if (xlp == xup && ylp == yup && xlp == ylp) {
		enqueue(s, toLit(var3), wsf, 3);
		enqueue_prop(s, word_num3);
		return 0;
	}

	unsigned long int che = check_valid_word(xlp | ylp, xup&yup);
	if (che != (uint64_t)(-1)) {
		veci lits1;
		veci_new(&lits1);


		veci_push(&lits1, lit_neg(toLit(var3)));
		int i = bitwid - __builtin_ffsl(~che);

		if (var1 != -2) {
			int v1 = var1 + i;
			if (var2 != -2) {
				if (s->assigns[v1] == l_True) {
					assert(s->assigns[v1] == l_True);
					veci_push(&lits1, lit_neg(toLit(v1)));

					assert(s->assigns[var2 + i] == l_False);
					veci_push(&lits1, toLit(var2 + i));
				}
				else {
					assert(s->assigns[var1 + i] == l_False);
					veci_push(&lits1, toLit(v1));

					assert(s->assigns[var2 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
			}
			else {
				if (s->assigns[v1] == l_True) {
					veci_push(&lits1, lit_neg(toLit(v1)));
				}
				else {
					assert(s->assigns[v1] == l_False);
					veci_push(&lits1, toLit(v1));
				}

			}
		}
		else {
			if (var2 != -2) {
				int v2 = var2 + i;
				if (s->assigns[v2] == l_True) {
					veci_push(&lits1, lit_neg(toLit(v2)));
				}
				else {
					assert(s->assigns[v2] == l_False);
					veci_push(&lits1, toLit(v2));
				}
			}
		}

		enqueue_bool(s, lit_neg(toLit(var3)), explan_generate(veci_begin(&lits1), veci_size(&lits1)));
		enqueue_prop(s, word_num3);
		veci_delete(&lits1);
		return 0;
	}
	return 0;
}

// propagate x, let x <=y   
int lessthan(solver *s, int var1, int var2, int var3, struct ul *uplw1, struct ul *uplw2, vecp *confl, int bitwid, 
	unsigned long int ax, unsigned long int ay, struct ws_flag* wsf) {	

	int i;
	unsigned long int xlp, xup, ylp, yup;

	unsigned long int mask;
	if (bitwid == 64)
		mask = ~((uint64_t)(-1) << bitwid);
	else
		mask = (uint64_t)(-1);


	int word_num1 = 0, word_num2 = 0;
	lbool* values = s->assigns;

	if (var1 != -2) {
		word_num1 = uplw1->word_num;
		xlp = uplw1->lower;
		xup = uplw1->upper;
	}
	else {
		xlp = ax;
		xup = ax;
	}

	if (var2 != -2) {
		word_num2 = uplw2->word_num;
		ylp = uplw2->lower;
		yup = uplw2->upper;
	}
	else {
		ylp = ay;
		yup = ay;
	}

	if (xlp > yup) {
		unsigned long int z;
		veci lits1;
		veci_new(&lits1);

		z = (xlp & (~yup)) & mask;
		// find the index of xlp 1 yup 0, enqueue all the 1 bit of x, and all the 0 bit of y before this index

		int j = __builtin_clzl(z) - (64 - bitwid);

		if (var1 != -2)
			for (i = 0; i <= j; i++) {
				if (values[var1 + i] == l_True)
					veci_push(&lits1, lit_neg(toLit(var1 + i)));
			}
		if (var2 != -2)
			for (i = 0; i <= j; i++) {
				if (values[var2 + i] == l_False)
					veci_push(&lits1, toLit(var2 + i));
			}

		assert(s->assigns[var3] == l_True);
		veci_push(&lits1, lit_neg(toLit(var3)));  // var3==l_True

		vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
		veci_delete(&lits1);
		return 0;
	}

	//lbool* values=s->assigns; 
	unsigned long int app, lower, upper; int ii, g;

	if (var1 != -2) {
		for (g = var1;g < var1 + bitwid;g++) {
			if (values[g] == l_Undef) {
				ii = bitwid + var1 - 1 - g;
				app = ((uint64_t)1) << ii;
				lower = xlp | app;  // pretend to fix the iith bit of x to 1
				if (lower > yup) {
					unsigned long int znew = lower & (~yup) & mask;
					int j = __builtin_clzl(znew) - (64 - bitwid);
					int gg = g - var1;

					if (j != gg) {
						veci lits1;
						veci_new(&lits1);

						//assert(s->assigns[g] == l_True);	
						veci_push(&lits1, lit_neg(toLit(g)));

						if (var1 != -2)
							for (i = 0; i <= j; i++) {
								if (values[var1 + i] == l_True && i != gg)
									veci_push(&lits1, lit_neg(toLit(var1 + i)));
							}
						if (var2 != -2)
							for (i = 0; i <= j; i++) {
								if (values[var2 + i] == l_False)
									veci_push(&lits1, toLit(var2 + i));
							}

						assert(s->assigns[var3] == l_True);
						veci_push(&lits1, lit_neg(toLit(var3)));
						enqueue_bool(s, lit_neg(toLit(g)), explan_generate(veci_begin(&lits1), veci_size(&lits1)));
						veci_delete(&lits1);
					}
					else {
						enqueue(s, lit_neg(toLit(g)), wsf, 1);
					}

					xup = (xup & (~app)) & mask;
					enqueue_prop(s, word_num1);
				}
				else
					break;
			}
		}
		uplw1->upper = xup;
	}

	if (var2 != -2) {
		for (g = var2;g < var2 + bitwid;g++) {
			if (values[g] == l_Undef) {
				ii = var2 + bitwid - 1 - g;
				app = ((uint64_t)1) << ((uint64_t)ii);
				upper = (yup & (~app))& mask;

				if (xlp > upper) {
					unsigned long int znew = xlp & (~upper) & mask;
					int j = __builtin_clzl(znew) - (64 - bitwid);
					int gg = g - var2;

					if (j != gg) {
						veci lits1;
						veci_new(&lits1);

						//assert(s->assigns[g] == l_False);	
						veci_push(&lits1, toLit(g));

						if (var1 != -2)
							for (i = 0; i <= j; i++) {
								if (values[var1 + i] == l_True)
									veci_push(&lits1, lit_neg(toLit(var1 + i)));
							}
						if (var2 != -2)
							for (i = 0; i <= j; i++) {
								if (values[var2 + i] == l_False && i != gg)
									veci_push(&lits1, toLit(var2 + i));
							}

						assert(s->assigns[var3] == l_True);
						veci_push(&lits1, lit_neg(toLit(var3)));
						enqueue_bool(s, toLit(g), explan_generate(veci_begin(&lits1), veci_size(&lits1)));
						veci_delete(&lits1);
					}
					else {
						enqueue(s, toLit(g), wsf, 2);
					}
					ylp = ylp | app;
					enqueue_prop(s, word_num2);
				}
				else
					break;
			}
		}
		uplw2->lower = ylp;
	}
	return 1;
}

int great_eq(solver *s, int var1, int var2, int var3, struct ul *uplw1, struct ul *uplw2, vecp *confl, int bitwid, 
	unsigned long int ax, unsigned long int ay, struct ws_flag *wsf) {	//x > y   propagate x 
	int i;
	unsigned long int xlp, xup, ylp, yup;

	unsigned long int mask;
	if (bitwid == 64)
		mask = ~((uint64_t)(-1) << bitwid);
	else
		mask = (uint64_t)(-1);

	int word_num1 = 0, word_num2 = 0;
	lbool* values = s->assigns;

	if (var1 != -2) {
		word_num1 = uplw1->word_num;
		xlp = uplw1->lower;
		xup = uplw1->upper;
	}
	else {
		xlp = ax;
		xup = ax;
	}

	if (var2 != -2) {
		word_num2 = uplw2->word_num;
		ylp = uplw2->lower;
		yup = uplw2->upper;
	}
	else {
		ylp = ay;
		yup = ay;
	}

	if (xup <= ylp) {
		veci lits1;
		veci_new(&lits1);

		if (xup == ylp) {
			if (var1 != -2)
				for (i = 0; i <= bitwid - 1; i++) {
					if (values[var1 + i] == l_False)
						veci_push(&lits1, toLit(var1 + i));
				}
			if (var2 != -2)
				for (i = 0; i <= bitwid - 1; i++) {
					if (values[var2 + i] == l_True)
						veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
		}
		else {
			unsigned long int z = ylp & (~xup) & mask;

			int j = __builtin_clzl(z) - (64 - bitwid);

			if (var1 != -2)
				for (i = 0; i <= j; i++) {
					if (values[var1 + i] == l_False)
						veci_push(&lits1, toLit(var1 + i));
				}
			if (var2 != -2)
				for (i = 0; i <= j; i++) {
					if (values[var2 + i] == l_True)
						veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
		}

		assert(s->assigns[var3] == l_False);
		veci_push(&lits1, toLit(var3));

		vecp_push(confl, confl_generate(veci_begin(&lits1), veci_size(&lits1)));
		veci_delete(&lits1);
		return 0;
	}

	//lbool* values=s->assigns; 
	unsigned long int app, upper, lower; int ii, g;

	if (var1 != -2)  //x
	{
		for (g = var1;g < var1 + bitwid;g++) {
			if (values[g] == l_Undef) {
				ii = var1 + bitwid - 1 - g;
				app = ((uint64_t)1) << ii;
				upper = xup & (~app) &mask;
				if (upper <= ylp) {
					xlp = xlp | app;
					if (upper == ylp) {
						veci lits1;
						veci_new(&lits1);

						int gg = g - var1;

						//assert(s->assigns[g] == l_False);	
						veci_push(&lits1, toLit(g));

						if (var1 != -2)
							for (i = 0; i <= bitwid - 1; i++) {
								if (values[var1 + i] == l_False && i != gg)
									veci_push(&lits1, toLit(var1 + i));
							}
						if (var2 != -2)
							for (i = 0; i <= bitwid - 1; i++) {
								if (values[var2 + i] == l_True)
									veci_push(&lits1, lit_neg(toLit(var2 + i)));
							}

						assert(s->assigns[var3] == l_False);
						veci_push(&lits1, toLit(var3));
						enqueue_bool(s, toLit(g), explan_generate(veci_begin(&lits1), veci_size(&lits1)));
						veci_delete(&lits1);
					}
					else {
						int gg = g - var1;
						unsigned long int znew = ylp & (~upper) & mask;
						int j = __builtin_clzl(znew) - (64 - bitwid);

						if (gg != j) {
							veci lits1;
							veci_new(&lits1);

							veci_push(&lits1, toLit(g));

							if (var1 != -2)
								for (i = 0; i <= j; i++) {
									if (values[var1 + i] == l_False && i != gg)
										veci_push(&lits1, toLit(var1 + i));
								}
							if (var2 != -2)
								for (i = 0; i <= j; i++) {
									if (values[var2 + i] == l_True)
										veci_push(&lits1, lit_neg(toLit(var2 + i)));
								}

							assert(s->assigns[var3] == l_False);
							veci_push(&lits1, toLit(var3));
							enqueue_bool(s, toLit(g), explan_generate(veci_begin(&lits1), veci_size(&lits1)));
							veci_delete(&lits1);
						}
						else {
							enqueue(s, toLit(g), wsf, 1);
						}
					}
					enqueue_prop(s, word_num1);
				}
				else
					break;
			}
		}
		uplw1->lower = xlp;
	}

	if (var2 != -2)  //y
	{
		for (g = var2;g < var2 + bitwid;g++) {
			if (values[g] == l_Undef) {
				ii = var2 + bitwid - 1 - g;
				app = ((uint64_t)1) << ii;
				lower = ylp | app;
				if (lower >= xup) {
					yup = yup & (~app) & mask;
					if (lower == xup) {
						veci lits1;
						veci_new(&lits1);

						int gg = g - var2;

						veci_push(&lits1, lit_neg(toLit(g)));

						if (var1 != -2)
							for (i = 0; i <= bitwid - 1; i++) {
								if (values[var1 + i] == l_False)
									veci_push(&lits1, toLit(var1 + i));
							}
						if (var2 != -2)
							for (i = 0; i <= bitwid - 1; i++) {
								if (values[var2 + i] == l_True && i != gg)
									veci_push(&lits1, lit_neg(toLit(var2 + i)));
							}

						assert(s->assigns[var3] == l_False);
						veci_push(&lits1, toLit(var3));
						enqueue_bool(s, lit_neg(toLit(g)), explan_generate(veci_begin(&lits1), veci_size(&lits1)));
						veci_delete(&lits1);
					}
					else {
						int gg = g - var2;
						unsigned long int znew = lower & (~xup) & mask;
						int j = __builtin_clzl(znew) - (64 - bitwid);
						//if(gg!=i)
						if (gg != j) {
							veci lits1;
							veci_new(&lits1);

							//assert(s->assigns[g] == l_True);	
							veci_push(&lits1, lit_neg(toLit(g)));

							if (var1 != -2)
								for (i = 0; i <= j; i++) {
									if (values[var1 + i] == l_False)
										veci_push(&lits1, toLit(var1 + i));
								}
							if (var2 != -2)
								for (i = 0; i <= j; i++) {
									if (values[var2 + i] == l_True && i != gg)
										veci_push(&lits1, lit_neg(toLit(var2 + i)));
								}

							assert(s->assigns[var3] == l_False);
							veci_push(&lits1, toLit(var3));
							enqueue_bool(s, lit_neg(toLit(g)), explan_generate(veci_begin(&lits1), veci_size(&lits1)));
							veci_delete(&lits1);
						}
						else {
							enqueue(s, lit_neg(toLit(g)), wsf, 2);
						}
					}
					enqueue_prop(s, word_num2);
				}
				else
					break;
			}
		}
		uplw2->upper = yup;
	}
	return 1;
}

int less_eq_Undef(solver *s, int var1, int var2, int var3, struct ul *uplw1, struct ul *uplw2, int bitwid, 
	unsigned long int ax, unsigned long int ay) {
	int i;
	lbool* values = s->assigns;
	unsigned long int xlp, xup, ylp, yup;
	unsigned long int z;
	int word_num3;

	word_num3 = get_word_num(solver_read_wlist(s, toLit(var3)));

	if (var1 != -2) {
		xlp = uplw1->lower;
		xup = uplw1->upper;
	}
	else {
		xlp = ax;
		xup = ax;
	}

	if (var2 != -2) {
		ylp = uplw2->lower;
		yup = uplw2->upper;
	}
	else {
		ylp = ay;
		yup = ay;
	}

	if (xlp > yup)  // 1 of x, 0 of y
	{
		veci lits1;
		veci_new(&lits1);

		veci_push(&lits1, lit_neg(toLit(var3)));

		unsigned long int mask;
		if (bitwid == 64)
			mask = ~((uint64_t)(-1) << bitwid);
		else
			mask = (uint64_t)(-1);

		z = xlp & (~yup) & mask;
		int j = __builtin_clzl(z) - (64 - bitwid);

		if (var1 != -2)
			for (i = 0; i <= j; i++) {
				if (values[var1 + i] == l_True)
					veci_push(&lits1, lit_neg(toLit(var1 + i)));
			}
		if (var2 != -2)
			for (i = 0; i <= j; i++) {
				if (values[var2 + i] == l_False)
					veci_push(&lits1, toLit(var2 + i));
			}

		enqueue_bool(s, lit_neg(toLit(var3)), explan_generate(veci_begin(&lits1), veci_size(&lits1)));
		enqueue_prop(s, word_num3);
		veci_delete(&lits1);
		return 3;
	}
	else if (xup <= ylp)  // 0 of x, 1 of y
	{
		veci lits1;
		veci_new(&lits1);

		veci_push(&lits1, toLit(var3));

		if (xup == ylp) {
			if (var1 != -2)
				for (i = 0; i <= bitwid - 1; i++) {
					if (values[var1 + i] == l_False)
						veci_push(&lits1, toLit(var1 + i));
				}
			if (var2 != -2)
				for (i = 0; i <= bitwid - 1; i++) {
					if (values[var2 + i] == l_True)
						veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
		}
		else {
			unsigned long int mask;
			if (bitwid == 64)
				mask = ~((uint64_t)(-1) << bitwid);
			else
				mask = (uint64_t)(-1);

			z = ylp & (~xup)& mask;
			int j = __builtin_clzl(z) - (64 - bitwid);

			if (var1 != -2)
				for (i = 0; i <= j; i++) {
					if (values[var1 + i] == l_False)
						veci_push(&lits1, toLit(var1 + i));
				}
			if (var2 != -2)
				for (i = 0; i <= j; i++) {
					if (values[var2 + i] == l_True)
						veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
		}

		enqueue_bool(s, toLit(var3), explan_generate(veci_begin(&lits1), veci_size(&lits1)));
		enqueue_prop(s, word_num3);
		veci_delete(&lits1);
		return 3;
	}
	else
		return 3;
}


// backward explanation generators

int conjunction_explan(solver *s, int var1, int var2, int var3, int bitwid, int lt, unsigned long int ax, 
	unsigned long int ay, clause** c) {
	int i;
	veci lits1;
	veci_new(&lits1);

	int varorder = s->varorder[lt];

	if (varorder == 1) {
		i = lt - var1;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));

			assert(s->assigns[var3 + i] == l_True);
			veci_push(&lits1, lit_neg(toLit(var3 + i)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));
			if (var2 != -2) {
				assert(s->assigns[var2 + i] == l_True);
				veci_push(&lits1, lit_neg(toLit(var2 + i)));
			}

			assert(s->assigns[var3 + i] == l_False);
			veci_push(&lits1, toLit(var3 + i));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else if (varorder == 2) {
		i = lt - var2;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));

			assert(s->assigns[var3 + i] == l_True);
			veci_push(&lits1, lit_neg(toLit(var3 + i)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));
			if (var1 != -2) {
				assert(s->assigns[var1 + i] == l_True);
				veci_push(&lits1, lit_neg(toLit(var1 + i)));
			}

			assert(s->assigns[var3 + i] == l_False);
			veci_push(&lits1, toLit(var3 + i));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else {
		i = lt - var3;
		lbool* values = s->assigns;
		if (values[lt] == l_True) {
			veci_push(&lits1, toLit(lt));
			if (var2 != -2) {
				assert(s->assigns[var2 + i] == l_True);
				veci_push(&lits1, lit_neg(toLit(var2 + i)));
			}
			if (var1 != -2) {
				assert(s->assigns[var1 + i] == l_True);
				veci_push(&lits1, lit_neg(toLit(var1 + i)));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			int* pos = s->pos;

			if ((var1 == -2 && ((ax >> (bitwid - 1 - i)) & (uint64_t)1) == (uint64_t)0) || 
				(var2 == -2 && ((ay >> (bitwid - 1 - i)) & (uint64_t)1) == (uint64_t)0)) {
				veci_push(&lits1, lit_neg(toLit(lt)));
			}
			else {	// find the literals that first fix the bit as the explanation
				if (var1 != -2) {
					int v1 = var1 + i;
					if (var2 != -2) {
						int v2 = var2 + i;
						if (values[v1] == l_False && pos[v1] < pos[lt]) {
							if (values[v2] == l_False && pos[v2] < pos[lt]) {
								if (pos[v1] < pos[v2]) {
									veci_push(&lits1, lit_neg(toLit(lt)));

									assert(s->assigns[v1] == l_False);
									veci_push(&lits1, toLit(v1));
								}
								else {
									veci_push(&lits1, lit_neg(toLit(lt)));

									assert(s->assigns[v2] == l_False);
									veci_push(&lits1, toLit(v2));
								}
							}
							else {
								veci_push(&lits1, lit_neg(toLit(lt)));

								assert(s->assigns[v1] == l_False);
								veci_push(&lits1, toLit(v1));
							}
						}
						else {
							veci_push(&lits1, lit_neg(toLit(lt)));

							assert(s->assigns[v2] == l_False);
							veci_push(&lits1, toLit(v2));
						}
					}
					else {
						veci_push(&lits1, lit_neg(toLit(lt)));

						assert(s->assigns[v1] == l_False);
						veci_push(&lits1, toLit(v1));
					}
				}
				else {
					veci_push(&lits1, lit_neg(toLit(lt)));

					assert(s->assigns[var2 + i] == l_False);
					veci_push(&lits1, toLit(var2 + i));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	return 1;
}

int conjunction_neg_explan(solver *s, int var1, int var2, int var3, int bitwid, int lt, unsigned long int ax, 
	unsigned long int ay, clause** c) {
	int i;
	veci lits1;
	veci_new(&lits1);

	int varorder = s->varorder[lt];

	if (varorder == 1) {
		i = lt - var1;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));

			assert(s->assigns[var3 + i] == l_False);
			veci_push(&lits1, toLit(var3 + i));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));
			if (var2 != -2) {
				assert(s->assigns[var2 + i] == l_True);
				veci_push(&lits1, lit_neg(toLit(var2 + i)));
			}

			assert(s->assigns[var3 + i] == l_True);
			veci_push(&lits1, lit_neg(toLit(var3 + i)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else if (varorder == 2) {
		i = lt - var2;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));

			assert(s->assigns[var3 + i] == l_False);
			veci_push(&lits1, toLit(var3 + i));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));
			if (var1 != -2) {
				assert(s->assigns[var1 + i] == l_True);
				veci_push(&lits1, lit_neg(toLit(var1 + i)));
			}

			assert(s->assigns[var3 + i] == l_True);
			veci_push(&lits1, lit_neg(toLit(var3 + i)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else {
		i = lt - var3;
		lbool* values = s->assigns;
		if (values[lt] == l_False) {
			veci_push(&lits1, lit_neg(toLit(lt)));
			if (var2 != -2) {
				assert(s->assigns[var2 + i] == l_True);
				veci_push(&lits1, lit_neg(toLit(var2 + i)));
			}
			if (var1 != -2) {
				assert(s->assigns[var1 + i] == l_True);
				veci_push(&lits1, lit_neg(toLit(var1 + i)));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			int* pos = s->pos;

			if ((var1 == -2 && ((ax >> (bitwid - 1 - i)) & (uint64_t)1) == (uint64_t)0) || 
				(var2 == -2 && ((ay >> (bitwid - 1 - i)) & (uint64_t)1) == (uint64_t)0)) {
				veci_push(&lits1, toLit(lt));
			}
			else {
				if (var1 != -2) {
					int v1 = var1 + i;
					if (var2 != -2) {
						int v2 = var2 + i;
						if (values[v1] == l_False && pos[v1] < pos[lt]) {
							if (values[v2] == l_False && pos[v2] < pos[lt]) {
								if (pos[v1] < pos[v2]) {
									veci_push(&lits1, toLit(lt));
									veci_push(&lits1, toLit(v1));
								}
								else {
									veci_push(&lits1, toLit(lt));
									veci_push(&lits1, toLit(v2));
								}
							}
							else {
								veci_push(&lits1, toLit(lt));
								veci_push(&lits1, toLit(v1));
							}
						}
						else {
							veci_push(&lits1, toLit(lt));
							veci_push(&lits1, toLit(v2));
						}
					}
					else {
						veci_push(&lits1, toLit(lt));

						assert(s->assigns[v1] == l_False);
						veci_push(&lits1, toLit(v1));
					}
				}
				else {
					veci_push(&lits1, toLit(lt));

					assert(s->assigns[var2 + i] == l_False);
					veci_push(&lits1, toLit(var2 + i));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	return 1;
}
int exclusiveor_explan(solver *s, int var1, int var2, int var3, int lt, clause** c) {
	int i;
	veci lits1;
	veci_new(&lits1);
	lbool* values = s->assigns;

	int varorder = s->varorder[lt];

	if (varorder == 1) {
		i = lt - var1;
		if (values[lt] == l_True) {
			veci_push(&lits1, toLit(lt));

			int v3 = var3 + i;
			if (values[v3] == l_True) {
				veci_push(&lits1, lit_neg(toLit(v3)));
				if (var2 != -2) {
					assert(s->assigns[var2 + i] == l_False);
					veci_push(&lits1, toLit(var2 + i));
				}
			}
			else {
				veci_push(&lits1, toLit(v3));       	     				          		    					
				if (var2 != -2) {
					assert(s->assigns[var2 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));

			int v3 = var3 + i;
			if (values[v3] == l_True) {
				veci_push(&lits1, lit_neg(toLit(v3)));
				if (var2 != -2) {
					assert(s->assigns[var2 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
			}
			else {
				veci_push(&lits1, toLit(v3));
				if (var2 != -2) {
					assert(s->assigns[var2 + i] == l_False);
					veci_push(&lits1, toLit(var2 + i));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else if (varorder == 2) {
		i = lt - var2;
		if (values[lt] == l_True) {
			int v3 = var3 + i;
			veci_push(&lits1, toLit(lt));

			if (values[v3] == l_True) {
				veci_push(&lits1, lit_neg(toLit(v3)));
				if (var1 != -2) {
					assert(s->assigns[var1 + i] == l_False);
					veci_push(&lits1, toLit(var1 + i));

				}
			}
			else {
				assert(s->assigns[v3] == l_False);
				veci_push(&lits1, toLit(v3));
				if (var1 != -2) {
					assert(s->assigns[var1 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var1 + i)));
				}
			}
			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {

			int v3 = var3 + i;
			veci_push(&lits1, lit_neg(toLit(lt)));

			if (values[v3] == l_True) {
				veci_push(&lits1, lit_neg(toLit(v3)));
				if (var1 != -2) {
					assert(s->assigns[var1 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var1 + i)));
				}
			}
			else {
				assert(s->assigns[v3] == l_False);
				veci_push(&lits1, toLit(v3));
				if (var1 != -2) {
					assert(s->assigns[var1 + i] == l_False);
					veci_push(&lits1, toLit(var1 + i));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else {
		i = lt - var3;
		if (values[lt] == l_True) {
			veci_push(&lits1, toLit(lt));
			if (var1 != -2) {
				int v1 = var1 + i;
				if (values[v1] == l_False)
					veci_push(&lits1, toLit(v1));
				else {
					assert(s->assigns[v1] == l_True);
					veci_push(&lits1, lit_neg(toLit(v1)));
				}
			}
			if (var2 != -2) {
				int v2 = var2 + i;
				if (values[v2] == l_True)
					veci_push(&lits1, lit_neg(toLit(v2)));
				else {
					assert(s->assigns[v2] == l_False);
					veci_push(&lits1, toLit(v2));
				}
			}


			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {

			veci_push(&lits1, lit_neg(toLit(lt)));
			if (var1 != -2) {
				int v1 = var1 + i;
				if (values[v1] == l_False)
					veci_push(&lits1, toLit(v1));

				else {
					assert(s->assigns[v1] == l_True);
					veci_push(&lits1, lit_neg(toLit(v1)));
				}

			}
			if (var2 != -2) {
				int v2 = var2 + i;
				if (values[v2] == l_True)
					veci_push(&lits1, lit_neg(toLit(v2)));
				else {
					assert(s->assigns[v2] == l_False);
					veci_push(&lits1, toLit(v2));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	return 1;
}

int exclusiveor_neg_explan(solver *s, int var1, int var2, int var3, int lt, clause** c) {
	int i;
	veci lits1;
	veci_new(&lits1);
	lbool* values = s->assigns;

	int varorder = s->varorder[lt];

	if (varorder == 1) {
		i = lt - var1;
		if (values[lt] == l_True) {
			veci_push(&lits1, toLit(lt));

			int v3 = var3 + i;
			if (values[v3] == l_True) {
				veci_push(&lits1, lit_neg(toLit(v3)));
				if (var2 != -2) {
					assert(s->assigns[var2 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
			}
			else {
				veci_push(&lits1, toLit(v3));       	     				          		    					
				if (var2 != -2) {
					assert(s->assigns[var2 + i] == l_False);
					veci_push(&lits1, toLit(var2 + i));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));

			int v3 = var3 + i;
			if (values[v3] == l_True) {
				veci_push(&lits1, lit_neg(toLit(v3)));
				if (var2 != -2) {
					assert(s->assigns[var2 + i] == l_False);
					veci_push(&lits1, toLit(var2 + i));
				}
			}
			else {
				veci_push(&lits1, toLit(v3));
				if (var2 != -2) {
					assert(s->assigns[var2 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else if (varorder == 2) {
		i = lt - var2;
		if (values[lt] == l_True) {
			int v3 = var3 + i;
			veci_push(&lits1, toLit(lt));

			if (values[v3] == l_True) {
				veci_push(&lits1, lit_neg(toLit(v3)));
				if (var1 != -2) {
					assert(s->assigns[var1 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var1 + i)));

				}
			}
			else {
				veci_push(&lits1, toLit(v3));
				if (var1 != -2) {
					assert(s->assigns[var1 + i] == l_False);
					veci_push(&lits1, toLit(var1 + i));
				}
			}
			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {

			int v3 = var3 + i;
			veci_push(&lits1, lit_neg(toLit(lt)));

			if (values[v3] == l_True) {
				veci_push(&lits1, lit_neg(toLit(v3)));
				if (var1 != -2) {
					assert(s->assigns[var1 + i] == l_False);
					veci_push(&lits1, toLit(var1 + i));
				}
			}
			else {
				veci_push(&lits1, toLit(v3));
				if (var1 != -2) {
					assert(s->assigns[var1 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var1 + i)));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else {
		i = lt - var3;
		if (values[lt] == l_True) {
			veci_push(&lits1, toLit(lt));
			if (var1 != -2) {
				int v1 = var1 + i;
				if (values[v1] == l_False)
					veci_push(&lits1, toLit(v1));
				else {
					assert(s->assigns[v1] == l_True);
					veci_push(&lits1, lit_neg(toLit(v1)));
				}
			}
			if (var2 != -2) {
				int v2 = var2 + i;
				if (values[v2] == l_True)
					veci_push(&lits1, lit_neg(toLit(v2)));
				else {
					assert(s->assigns[v2] == l_False);
					veci_push(&lits1, toLit(v2));
				}
			}


			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {

			veci_push(&lits1, lit_neg(toLit(lt)));
			if (var1 != -2) {
				int v1 = var1 + i;
				if (values[v1] == l_False)
					veci_push(&lits1, toLit(v1));

				else {
					assert(s->assigns[v1] == l_True);
					veci_push(&lits1, lit_neg(toLit(v1)));
				}

			}
			if (var2 != -2) {
				int v2 = var2 + i;
				if (values[v2] == l_True)
					veci_push(&lits1, lit_neg(toLit(v2)));
				else {
					assert(s->assigns[v2] == l_False);
					veci_push(&lits1, toLit(v2));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	return 1;
}


int exclusiveor_div_explan(solver *s, int var1, int var2, int lt, clause** c) {
	int i;
	veci lits1;
	veci_new(&lits1);
	lbool* values = s->assigns;
	int varorder = s->varorder[lt];

	if (varorder == 1) {
		i = lt - var1;
		if (values[lt] == l_True) {
			int v2 = var2 + i;
			veci_push(&lits1, toLit(lt));

			if (values[v2] == l_True) {
				assert(s->assigns[v2] == l_True);
				veci_push(&lits1, lit_neg(toLit(v2)));
			}
			else {
				assert(s->assigns[v2] == l_False);
				veci_push(&lits1, toLit(v2));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			int v2 = var2 + i;
			veci_push(&lits1, lit_neg(toLit(lt)));
			if (values[v2] == l_True) {
				assert(s->assigns[v2] == l_True);
				veci_push(&lits1, lit_neg(toLit(v2)));
			}
			else {
				assert(s->assigns[v2] == l_False);
				veci_push(&lits1, toLit(v2));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else {
		i = lt - var2;
		if (values[lt] == l_True) {
			int v1 = var1 + i;
			veci_push(&lits1, toLit(lt));
			if (values[v1] == l_True) {
				veci_push(&lits1, lit_neg(toLit(v1)));
			}
			else {
				assert(s->assigns[v1] == l_False);
				veci_push(&lits1, toLit(v1));
			}
			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {

			int v1 = var1 + i;
			veci_push(&lits1, lit_neg(toLit(lt)));

			if (values[v1] == l_True) {
				veci_push(&lits1, lit_neg(toLit(v1)));
			}
			else {
				assert(s->assigns[v1] == l_False);
				veci_push(&lits1, toLit(v1));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	return 1;
}


int disjunction_explan(solver *s, int var1, int var2, int var3, int bitwid, int lt, unsigned long int ax, 
	unsigned long int ay, clause** c) {
	int i;
	veci lits1;
	veci_new(&lits1);

	int varorder = s->varorder[lt];

	if (varorder == 1) {
		i = lt - var1;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));
			if (var2 != -2) {
				assert(s->assigns[var2 + i] == l_False);
				veci_push(&lits1, toLit(var2 + i));
			}
			assert(s->assigns[var3 + i] == l_True);
			veci_push(&lits1, lit_neg(toLit(var3 + i)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));

			assert(s->assigns[var3 + i] == l_False);
			veci_push(&lits1, toLit(var3 + i));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else if (varorder == 2) {
		i = lt - var2;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));
			if (var1 != -2) {
				assert(s->assigns[var1 + i] == l_False);
				veci_push(&lits1, toLit(var1 + i));
			}
			assert(s->assigns[var3 + i] == l_True);
			veci_push(&lits1, lit_neg(toLit(var3 + i)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {

			assert(s->assigns[lt] == l_False);
			veci_push(&lits1, lit_neg(toLit(lt)));

			assert(s->assigns[var3 + i] == l_False);
			veci_push(&lits1, toLit(var3 + i));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else {
		i = lt - var3;
		lbool* values = s->assigns;
		if (values[lt] == l_True) {

			int* pos = s->pos;
			if ((var1 == -2 && ((ax >> (bitwid - 1 - i)) & (uint64_t)1) == (uint64_t)1) || 
				(var2 == -2 && ((ay >> (bitwid - 1 - i)) & (uint64_t)1) == (uint64_t)1)) {
				veci_push(&lits1, toLit(lt));
			}
			else {	// find the literals that first fix the bit as the explanation
				if (var1 != -2) {
					int v1 = var1 + i;
					if (var2 != -2) {
						int v2 = var2 + i;
						if (values[v1] == l_True && pos[v1] < pos[lt]) {
							if (values[v2] == l_True && pos[v2] < pos[lt]) {
								if (pos[v1] < pos[v2]) {
									veci_push(&lits1, toLit(lt));

									assert(s->assigns[v1] == l_True);
									veci_push(&lits1, lit_neg(toLit(v1)));
								}
								else {
									veci_push(&lits1, toLit(lt));

									assert(s->assigns[v2] == l_True);
									veci_push(&lits1, lit_neg(toLit(v2)));
								}
							}
							else {
								veci_push(&lits1, toLit(lt));

								assert(s->assigns[v1] == l_True);
								veci_push(&lits1, lit_neg(toLit(v1)));
							}
						}
						else {
							veci_push(&lits1, toLit(lt));

							assert(s->assigns[v2] == l_True);
							veci_push(&lits1, lit_neg(toLit(v2)));
						}
					}
					else {
						veci_push(&lits1, toLit(lt));

						assert(s->assigns[v1] == l_True);
						veci_push(&lits1, lit_neg(toLit(v1)));
					}
				}
				else {
					veci_push(&lits1, toLit(lt));

					assert(s->assigns[var2 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {

			veci_push(&lits1, lit_neg(toLit(lt)));

			if (var1 != -2) {
				assert(s->assigns[var1 + i] == l_False);
				veci_push(&lits1, toLit(var1 + i));
			}
			if (var2 != -2) {
				assert(s->assigns[var2 + i] == l_False);
				veci_push(&lits1, toLit(var2 + i));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;

		}
	}
	return 1;
}

int disjunction_neg_explan(solver *s, int var1, int var2, int var3, int bitwid, int lt, unsigned long int ax, 
	unsigned long int ay, clause** c) {
	int i;
	veci lits1;
	veci_new(&lits1);

	int varorder = s->varorder[lt];

	if (varorder == 1) {
		i = lt - var1;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));
			if (var2 != -2) {
				assert(s->assigns[var2 + i] == l_False);
				veci_push(&lits1, toLit(var2 + i));
			}
			assert(s->assigns[var3 + i] == l_False);
			veci_push(&lits1, toLit(var3 + i));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));

			assert(s->assigns[var3 + i] == l_True);
			veci_push(&lits1, lit_neg(toLit(var3 + i)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else if (varorder == 2) {
		i = lt - var2;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));
			if (var1 != -2) {
				assert(s->assigns[var1 + i] == l_False);
				veci_push(&lits1, toLit(var1 + i));
			}
			assert(s->assigns[var3 + i] == l_False);
			veci_push(&lits1, toLit(var3 + i));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));

			assert(s->assigns[var3 + i] == l_True);
			veci_push(&lits1, lit_neg(toLit(var3 + i)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else {
		i = lt - var3;
		lbool* values = s->assigns;
		if (values[lt] == l_False) {

			int* pos = s->pos;
			if ((var1 == -2 && ((ax >> (bitwid - 1 - i)) & (uint64_t)1) == (uint64_t)1) || 
				(var2 == -2 && ((ay >> (bitwid - 1 - i)) & (uint64_t)1) == (uint64_t)1)) {
				veci_push(&lits1, lit_neg(toLit(lt)));
			}
			else {
				if (var1 != -2) {
					int v1 = var1 + i;
					if (var2 != -2) {
						int v2 = var2 + i;
						if (values[v1] == l_True && pos[v1] < pos[lt]) {
							if (values[v2] == l_True && pos[v2] < pos[lt]) {
								if (pos[v1] < pos[v2]) {
									veci_push(&lits1, lit_neg(toLit(lt)));

									assert(s->assigns[v1] == l_True);
									veci_push(&lits1, lit_neg(toLit(v1)));
								}
								else {
									veci_push(&lits1, lit_neg(toLit(lt)));

									assert(s->assigns[v2] == l_True);
									veci_push(&lits1, lit_neg(toLit(v2)));
								}
							}
							else {
								veci_push(&lits1, lit_neg(toLit(lt)));

								assert(s->assigns[v1] == l_True);
								veci_push(&lits1, lit_neg(toLit(v1)));
							}
						}
						else {
							veci_push(&lits1, lit_neg(toLit(lt)));

							assert(s->assigns[v2] == l_True);
							veci_push(&lits1, lit_neg(toLit(v2)));
						}
					}
					else {
						veci_push(&lits1, lit_neg(toLit(lt)));

						assert(s->assigns[v1] == l_True);
						veci_push(&lits1, lit_neg(toLit(v1)));
					}
				}
				else {
					veci_push(&lits1, lit_neg(toLit(lt)));

					assert(s->assigns[var2 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {

			veci_push(&lits1, toLit(lt));

			if (var1 != -2) {
				assert(s->assigns[var1 + i] == l_False);
				veci_push(&lits1, toLit(var1 + i));
			}
			if (var2 != -2) {
				assert(s->assigns[var2 + i] == l_False);
				veci_push(&lits1, toLit(var2 + i));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;

		}
	}
	return 1;
}


int ifstatement_explan(solver *s, int var1, int var2, int var3, int var4, int lt, clause** c) {
	int i;
	veci lits1;
	veci_new(&lits1);
	lbool* values = s->assigns;
	int* pos = s->pos;
	int varorder = s->varorder[lt];

	if (varorder == 1) {
		i = lt - var1;
		if (values[lt] == l_True) {
			veci_push(&lits1, toLit(lt));

			if (var3 != -2) {
				int v4 = var4 + i;  int v3 = var3 + i;

				if (values[v4] == l_True) {
					veci_push(&lits1, lit_neg(toLit(v4)));

					assert(s->assigns[v3] == l_False);
					veci_push(&lits1, toLit(v3));
				}
				else {
					veci_push(&lits1, toLit(v4));

					assert(s->assigns[v3] == l_True);
					veci_push(&lits1, lit_neg(toLit(v3)));
				}
			}
			else {
				int v4 = var4 + i;

				if (values[v4] == l_True) {
					veci_push(&lits1, lit_neg(toLit(v4)));
				}
				else {
					assert(s->assigns[v4] == l_False);
					veci_push(&lits1, toLit(v4));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));

			if (var2 != -2) {
				int v4 = var4 + i;  int v2 = var2 + i;

				if (values[v4] == l_True) {
					veci_push(&lits1, lit_neg(toLit(v4)));

					assert(s->assigns[v2] == l_False);
					veci_push(&lits1, toLit(v2));
				}
				else {
					assert(s->assigns[v4] == l_False);
					veci_push(&lits1, toLit(v4));

					assert(s->assigns[v2] == l_True);
					veci_push(&lits1, lit_neg(toLit(v2)));
				}
			}
			else {
				int v4 = var4 + i;

				if (values[v4] == l_True) {
					veci_push(&lits1, lit_neg(toLit(v4)));
				}
				else {
					assert(s->assigns[v4] == l_False);
					veci_push(&lits1, toLit(v4));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else if (varorder == 2) {
		i = lt - var2;
		if (values[lt] == l_True) {
			int v3 = var3 + i; int v1 = var1 + i;

			veci_push(&lits1, toLit(lt));

			assert(s->assigns[var4 + i] == l_True);
			veci_push(&lits1, lit_neg(toLit(var4 + i)));

			if (values[v1] == l_True && pos[v1] < pos[lt]) {
				veci_push(&lits1, lit_neg(toLit(v1)));
			}
			else if (var3 != -2 && values[v3] == l_False && pos[v3] < pos[lt]) {
				veci_push(&lits1, toLit(v3));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			int v3 = var3 + i; int v1 = var1 + i;

			veci_push(&lits1, lit_neg(toLit(lt)));

			assert(s->assigns[var4 + i] == l_False);
			veci_push(&lits1, toLit(var4 + i));

			if (values[v1] == l_True && pos[v1] < pos[lt]) {
				veci_push(&lits1, lit_neg(toLit(v1)));
			}
			else if (var3 != -2 && values[v3] == l_True && pos[v3] < pos[lt]) {
				veci_push(&lits1, lit_neg(toLit(v3)));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else if (varorder == 3) {
		i = lt - var3;
		if (values[lt] == l_True) {
			int v2 = var2 + i; int v1 = var1 + i;

			veci_push(&lits1, toLit(lt));

			assert(s->assigns[var4 + i] == l_True);
			veci_push(&lits1, lit_neg(toLit(var4 + i)));

			if (values[v1] == l_False && pos[v1] < pos[lt]) {
				veci_push(&lits1, toLit(v1));
			}
			else if (var2 != -2 && values[v2] == l_False && pos[v2] < pos[lt]) {
				veci_push(&lits1, toLit(v2));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			int v2 = var2 + i;  int v1 = var1 + i;

			veci_push(&lits1, lit_neg(toLit(lt)));

			assert(s->assigns[var4 + i] == l_False);
			veci_push(&lits1, toLit(var4 + i));

			if (values[v1] == l_False && pos[v1] < pos[lt]) {
				veci_push(&lits1, toLit(v1));
			}
			else if (var2 != -2 && values[v2] == l_True && pos[v2] < pos[lt]) {
				veci_push(&lits1, lit_neg(toLit(v2)));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else {
		i = lt - var4;
		if (values[lt] == l_True) {
			int v1 = var1 + i;   lbool x = values[v1];
			veci_push(&lits1, toLit(lt));

			if (x == l_True && pos[v1] < pos[lt]) {
				veci_push(&lits1, lit_neg(toLit(v1)));
				if (var2 != -2) {
					assert(s->assigns[var2 + i] == l_True);

					veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
			}
			else if (x == l_False && pos[v1] < pos[lt]) {
				veci_push(&lits1, toLit(v1));
				if (var3 != -2) {
					assert(s->assigns[var3 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var3 + i)));
				}
			}
			else {
				if (var2 != -2) {
					assert(s->assigns[var2 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
				if (var3 != -2) {
					assert(s->assigns[var3 + i] == l_True);
					veci_push(&lits1, lit_neg(toLit(var3 + i)));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			int v1 = var1 + i; lbool x = values[v1];
			veci_push(&lits1, lit_neg(toLit(lt)));

			if (x == l_True && pos[v1] < pos[lt]) {
				veci_push(&lits1, lit_neg(toLit(v1)));
				if (var2 != -2) {
					assert(s->assigns[var2 + i] == l_False);
					veci_push(&lits1, toLit(var2 + i));
				}

			}
			else if (x == l_False && pos[v1] < pos[lt]) {
				veci_push(&lits1, toLit(v1));
				if (var3 != -2) {
					assert(s->assigns[var3 + i] == l_False);
					veci_push(&lits1, toLit(var3 + i));
				}

			}
			else {
				if (var2 != -2) {
					assert(s->assigns[var2 + i] == l_False);
					veci_push(&lits1, toLit(var2 + i));
				}
				if (var3 != -2) {
					assert(s->assigns[var3 + i] == l_False);
					veci_push(&lits1, toLit(var3 + i));
				}

			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
}

int negation_explan(solver *s, int var1, int var2, int lt, clause** c) {
	int i;
	veci lits1;
	veci_new(&lits1);
	int varorder = s->varorder[lt];

	if (varorder == 1) {
		i = lt - var1;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));

			assert(s->assigns[var2 + i] == l_False);
			veci_push(&lits1, toLit(var2 + i));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));

			assert(s->assigns[var2 + i] == l_True);
			veci_push(&lits1, lit_neg(toLit(var2 + i)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else {
		i = lt - var2;
		if (s->assigns[lt] == l_True) {

			veci_push(&lits1, toLit(lt));
			if (var1 != -2) {
				assert(s->assigns[var1 + i] == l_False);
				veci_push(&lits1, toLit(var1 + i));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {

			veci_push(&lits1, lit_neg(toLit(lt)));
			if (var1 != -2) {
				assert(s->assigns[var1 + i] == l_True);
				veci_push(&lits1, lit_neg(toLit(var1 + i)));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	return 1;
}

int leftshift_explan(solver *s, int var1, int var2, int shiftbits, int bitwid, int lt, clause** c) {
	int i;
	veci lits1;
	veci_new(&lits1);
	int varorder = s->varorder[lt];

	if (varorder == 1) {
		i = lt - var1;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));

			assert(s->assigns[var2 + i - shiftbits] == l_True);
			veci_push(&lits1, lit_neg(toLit(var2 + i - shiftbits)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));

			assert(s->assigns[var2 + i - shiftbits] == l_False);
			veci_push(&lits1, toLit(var2 + i - shiftbits));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else {
		i = lt - var2;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));
			if (var1 != -2) {
				assert(s->assigns[var1 + i + shiftbits] == l_True);
				veci_push(&lits1, lit_neg(toLit(var1 + i + shiftbits)));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));
			if (i < bitwid - shiftbits) {
				if (var1 != -2) {
					assert(s->assigns[var1 + i + shiftbits] == l_False);
					veci_push(&lits1, toLit(var1 + i + shiftbits));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	return 1;
}
int rightshift_explan(solver *s, int var1, int var2, int shiftbits, int lt, clause** c) {
	int i;
	veci lits1;
	veci_new(&lits1);
	int varorder = s->varorder[lt];

	if (varorder == 1) {
		i = lt - var1;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));

			assert(s->assigns[var2 + i + shiftbits] == l_True);
			veci_push(&lits1, lit_neg(toLit(var2 + i + shiftbits)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));

			assert(s->assigns[var2 + i + shiftbits] == l_False);
			veci_push(&lits1, toLit(var2 + i + shiftbits));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else {
		i = lt - var2;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));
			if (var1 != -2) {
				assert(s->assigns[var1 + i - shiftbits] == l_True);
				veci_push(&lits1, lit_neg(toLit(var1 + i - shiftbits)));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			if (i < shiftbits) {
				veci_push(&lits1, lit_neg(toLit(lt)));
			}
			else {
				veci_push(&lits1, lit_neg(toLit(lt)));
				if (var1 != -2) {
					assert(s->assigns[var1 + i - shiftbits] == l_False);
					veci_push(&lits1, toLit(var1 + i - shiftbits));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	return 1;
}

int bvsrshift_explan(solver *s, int var1, int var2, int shiftbits, int lt, clause** c) {
	int i;
	veci lits1;
	veci_new(&lits1);
	int varorder = s->varorder[lt];

	if (varorder == 1) {
		i = lt - var1;
		if (i == 0) {
			if (s->assigns[lt] == l_True) {
				veci_push(&lits1, toLit(lt));

				int v2; int *pos = s->pos; int min_pos = pos[lt]; lbool *values = s->assigns;
				for (i = 0; i <= shiftbits; i++) {
					v2 = var2 + i;
					if (pos[v2] < min_pos && values[v2] == l_True) // choose the smallest level
					{
						min_pos = pos[v2];

						veci_resize(&lits1, 1);

						assert(s->assigns[v2] == l_True);
						veci_push(&lits1, lit_neg(toLit(v2)));
					}
				}

				*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
				veci_delete(&lits1);
				return 0;
			}
			else {
				veci_push(&lits1, lit_neg(toLit(lt)));

				int v2; int *pos = s->pos; int min_pos = pos[lt]; lbool *values = s->assigns;
				for (i = 0; i <= shiftbits; i++) {
					v2 = var2 + i;
					if (pos[v2] < min_pos && values[v2] == l_False) // choose the smallest level
					{
						min_pos = pos[v2];

						veci_resize(&lits1, 1);

						assert(s->assigns[v2] == l_False);
						veci_push(&lits1, toLit(v2));
					}
				}

				*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
				veci_delete(&lits1);
				return 0;
			}
		}
		else// if(i<bitwid && i>0)
		{
			if (s->assigns[lt] == l_True) {
				veci_push(&lits1, toLit(lt));

				assert(s->assigns[var2 + i + shiftbits] == l_True);
				veci_push(&lits1, lit_neg(toLit(var2 + i + shiftbits)));

				*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
				veci_delete(&lits1);
				return 0;
			}
			else {
				veci_push(&lits1, lit_neg(toLit(lt)));

				assert(s->assigns[var2 + i + shiftbits] == l_False);
				veci_push(&lits1, toLit(var2 + i + shiftbits));

				*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
				veci_delete(&lits1);
				return 0;
			}
		}
	}
	else {
		i = lt - var2;
		if (s->assigns[lt] == l_True) {
			if (i < shiftbits) {
				veci_push(&lits1, toLit(lt));
				if (var1 != -2) {
					assert(s->assigns[var1] == l_True);
					veci_push(&lits1, lit_neg(toLit(var1)));
				}
			}
			else {
				veci_push(&lits1, toLit(lt));
				if (var1 != -2) {
					assert(s->assigns[var1 + i - shiftbits] == l_True);
					veci_push(&lits1, lit_neg(toLit(var1 + i - shiftbits)));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			if (i < shiftbits) {
				veci_push(&lits1, lit_neg(toLit(lt)));
				if (var1 != -2) {
					assert(s->assigns[var1] == l_False);
					veci_push(&lits1, toLit(var1));
				}
			}
			else {
				veci_push(&lits1, lit_neg(toLit(lt)));
				if (var1 != -2) {
					assert(s->assigns[var1 + i - shiftbits] == l_False);
					veci_push(&lits1, toLit(var1 + i - shiftbits));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	return 1;
}


int zero_extend_explan(solver *s, int var1, int var2, int addbits, int lt, clause** c) {
	int i;
	veci lits1;
	veci_new(&lits1);

	int varorder = s->varorder[lt];

	if (varorder == 1) {
		i = lt - var1;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));

			assert(s->assigns[var2 + i + addbits] == l_True);
			veci_push(&lits1, lit_neg(toLit(var2 + i + addbits)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));

			assert(s->assigns[var2 + i + addbits] == l_False);
			veci_push(&lits1, toLit(var2 + i + addbits));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else {
		i = lt - var2;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));
			if (var1 != -2) {
				assert(s->assigns[var1 + i - addbits] == l_True);
				veci_push(&lits1, lit_neg(toLit(var1 + i - addbits)));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));
			if (i >= addbits) {
				if (var1 != -2) {
					assert(s->assigns[var1 + i - addbits] == l_False);
					veci_push(&lits1, toLit(var1 + i - addbits));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	return 1;
}

int sign_extend_explan(solver *s, int var1, int var2, int addbits, int lt, clause** c) {
	int i;
	veci lits1;
	veci_new(&lits1);
	int varorder = s->varorder[lt];

	if (varorder == 1) {
		i = lt - var1;
		if (i == 0) // x_0
		{
			if (s->assigns[lt] == l_True) {
				veci_push(&lits1, toLit(lt));

				int v2; int *pos = s->pos; int min_pos = pos[lt]; lbool *values = s->assigns;
				for (i = 0; i <= addbits; i++) {
					v2 = var2 + i;
					if (pos[v2] < min_pos && values[v2] == l_True) // choose the smallest level
					{
						min_pos = pos[v2];

						veci_resize(&lits1, 1);
						assert(s->assigns[v2] == l_True);
						veci_push(&lits1, lit_neg(toLit(v2)));
					}
				}

				*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
				veci_delete(&lits1);
				return 0;
			}
			else {
				veci_push(&lits1, lit_neg(toLit(lt)));

				int v2; int *pos = s->pos; int min_pos = pos[lt]; lbool *values = s->assigns;
				for (i = 0; i <= addbits; i++) {
					v2 = var2 + i;
					if (pos[v2] < min_pos && values[v2] == l_False) // choose the smallest level
					{
						min_pos = pos[v2];

						veci_resize(&lits1, 1);

						assert(s->assigns[v2] == l_False);
						veci_push(&lits1, toLit(v2));
					}
				}

				*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
				veci_delete(&lits1);
				return 0;
			}
		}
		else //if(i < orgbits && i>0)
		{
			if (s->assigns[lt] == l_True) {
				veci_push(&lits1, toLit(lt));

				assert(s->assigns[var2 + i + addbits] == l_True);
				veci_push(&lits1, lit_neg(toLit(var2 + i + addbits)));

				*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
				veci_delete(&lits1);
				return 0;
			}
			else {
				veci_push(&lits1, lit_neg(toLit(lt)));

				assert(s->assigns[var2 + i + addbits] == l_False);
				veci_push(&lits1, toLit(var2 + i + addbits));

				*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
				veci_delete(&lits1);
				return 0;
			}
		}
	}
	else {
		i = lt - var2;
		if (s->assigns[lt] == l_True) {
			if (i >= addbits) {
				veci_push(&lits1, toLit(lt));
				if (var1 != -2) {
					assert(s->assigns[var1 + i - addbits] == l_True);
					veci_push(&lits1, lit_neg(toLit(var1 + i - addbits)));
				}
			}
			else {
				veci_push(&lits1, toLit(lt));
				if (var1 != -2) {
					assert(s->assigns[var1] == l_True);
					veci_push(&lits1, lit_neg(toLit(var1)));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			if (i >= addbits) {
				veci_push(&lits1, lit_neg(toLit(lt)));
				if (var1 != -2) {
					assert(s->assigns[var1 + i - addbits] == l_False);
					veci_push(&lits1, toLit(var1 + i - addbits));
				}
			}
			else {
				veci_push(&lits1, lit_neg(toLit(lt)));
				if (var1 != -2) {
					assert(s->assigns[var1] == l_False);
					veci_push(&lits1, toLit(var1));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	return 1;
}
int bvconcat_explan(solver *s, int var1, int var2, int var3, int subwid1, int lt, clause** c) {
	//printf("bitwid %d subwid1 %d subwid2 %d\n",bitwid, subwid1, subwid2);
	int i;
	veci lits1;
	veci_new(&lits1);
	int varorder = s->varorder[lt];

	if (varorder == 1) {
		i = lt - var1;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));

			assert(s->assigns[var3 + i] == l_True);
			veci_push(&lits1, lit_neg(toLit(var3 + i)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));

			if (s->assigns[var3 + i] != l_False)
				//printf("s->assigns[var3+i] == %d var3 %d subwid1 %d, subwid2 %d bitwid %d i %d lt %d var1 %d s->assigns[lt] %d\n",s->assigns[var3+i], var3, subwid1, subwid2, bitwid, i, lt, var1, s->assigns[lt]);

				assert(s->assigns[var3 + i] == l_False);
			veci_push(&lits1, toLit(var3 + i));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else if (varorder == 2) {
		i = lt - var2;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));

			assert(s->assigns[var3 + i + subwid1] == l_True);
			veci_push(&lits1, lit_neg(toLit(var3 + i + subwid1)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));

			assert(s->assigns[var3 + i + subwid1] == l_False);
			veci_push(&lits1, toLit(var3 + i + subwid1));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else {
		i = lt - var3;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));
			if (i < subwid1 && var1 != -2) {
				assert(s->assigns[var1 + i] == l_True);
				veci_push(&lits1, lit_neg(toLit(var1 + i)));
			}
			if (i >= subwid1 && var2 != -2) {
				assert(s->assigns[var2 + i - subwid1] == l_True);
				veci_push(&lits1, lit_neg(toLit(var2 + i - subwid1)));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));
			if (i < subwid1 && var1 != -2) {
				assert(s->assigns[var1 + i] == l_False);
				veci_push(&lits1, toLit(var1 + i));
			}
			if (i >= subwid1 && var2 != -2) {
				assert(s->assigns[var2 + i - subwid1] == l_False);
				veci_push(&lits1, toLit(var2 + i - subwid1));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	return 1;
}

int extract_explan(solver *s, int var1, int var2, int bitwid, int subwid1, int lt, clause** c) {
	int i;
	veci lits1;
	veci_new(&lits1);
	int varorder = s->varorder[lt];

	if (varorder == 1)   // the index difference between var1 and var2 is (bitwid-1-subwid1)
	{
		i = lt - var1;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));

			assert(s->assigns[var2 + i - bitwid + subwid1 + 1] == l_True);
			veci_push(&lits1, lit_neg(toLit(var2 + i - bitwid + subwid1 + 1)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));

			assert(s->assigns[var2 + i - bitwid + subwid1 + 1] == l_False);
			veci_push(&lits1, toLit(var2 + i - bitwid + subwid1 + 1));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else {
		i = lt - var2;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));
			if (var1 != -2) {
				assert(s->assigns[var1 + i + bitwid - subwid1 - 1] == l_True);
				veci_push(&lits1, lit_neg(toLit(var1 + i + bitwid - subwid1 - 1)));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));
			if (var1 != -2) {
				assert(s->assigns[var1 + i + bitwid - subwid1 - 1] == l_False);
				veci_push(&lits1, toLit(var1 + i + bitwid - subwid1 - 1));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	return 1;
}

int inequall_explan(solver *s, int var1, int var2, int var3, int bitwid, unsigned long int ax, struct ul *uplw, int lt, 
	clause** c) {
	int i, j;
	lbool* values = s->assigns;
	veci lits1;
	veci_new(&lits1);
	int varorder = s->varorder[lt];

	unsigned long int xlp;

	if (var1 != -2) {
		xlp = uplw->lower;
	}
	else {
		xlp = ax;
	}

	if (varorder == 1) {
		j = lt - var1;
		if (values[lt] == l_False) {
			veci_push(&lits1, lit_neg(toLit(lt)));

			if (var2 != -2) {
				assert(s->assigns[var2 + j] == l_True);
				veci_push(&lits1, lit_neg(toLit(var2 + j)));
				for (i = bitwid - 1; i >= 0; xlp >>= 1, i--) {
					if ((xlp &(uint64_t)1)) {
						assert(s->assigns[var1 + i] == l_True);
						veci_push(&lits1, lit_neg(toLit(var1 + i)));

						assert(s->assigns[var2 + i] == l_True);
						veci_push(&lits1, lit_neg(toLit(var2 + i)));
					}
					else if (i != j) {
						assert(s->assigns[var1 + i] == l_False);
						veci_push(&lits1, toLit(var1 + i));

						assert(s->assigns[var2 + i] == l_False);
						veci_push(&lits1, toLit(var2 + i));
					}
				}
			}
			else {
				for (i = bitwid - 1; i >= 0; xlp >>= 1, i--) {
					if ((xlp &(uint64_t)1)) {
						assert(s->assigns[var1 + i] == l_True);
						veci_push(&lits1, lit_neg(toLit(var1 + i)));
					}
					else if (i != j) {
						assert(s->assigns[var1 + i] == l_False);
						veci_push(&lits1, toLit(var1 + i));
					}
				}
			}

			assert(s->assigns[var3] == l_False);
			veci_push(&lits1, toLit(var3));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else  //values[lt]==l_True
		{
			veci_push(&lits1, toLit(lt));

			if (var2 != -2) {
				assert(s->assigns[var2 + j] == l_False);
				veci_push(&lits1, toLit(var2 + j));
				for (i = bitwid - 1; i >= 0; xlp >>= 1, i--) {
					if ((xlp &(uint64_t)1)) {
						if (i != j) {
							assert(s->assigns[var1 + i] == l_True);
							veci_push(&lits1, lit_neg(toLit(var1 + i)));

							assert(s->assigns[var2 + i] == l_True);
							veci_push(&lits1, lit_neg(toLit(var2 + i)));
						}
					}
					else {
						assert(s->assigns[var1 + i] == l_False);
						veci_push(&lits1, toLit(var1 + i));

						assert(s->assigns[var2 + i] == l_False);
						veci_push(&lits1, toLit(var2 + i));
					}

				}
			}
			else {
				for (i = bitwid - 1; i >= 0; xlp >>= 1, i--) {
					if ((xlp &(uint64_t)1)) {
						if (i != j) {
							assert(s->assigns[var1 + i] == l_True);
							veci_push(&lits1, lit_neg(toLit(var1 + i)));

						}
					}
					else {
						assert(s->assigns[var1 + i] == l_False);
						veci_push(&lits1, toLit(var1 + i));
					}
				}
			}

			assert(s->assigns[var3] == l_False);
			veci_push(&lits1, toLit(var3));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else //if(varorder ==2)
	{
		j = lt - var2;
		if (values[lt] == l_False) {
			veci_push(&lits1, lit_neg(toLit(lt)));

			if (var1 != -2) {
				assert(s->assigns[var1 + j] == l_True);
				veci_push(&lits1, lit_neg(toLit(var1 + j)));
				for (i = bitwid - 1; i >= 0; xlp >>= 1, i--) {
					if ((xlp &(uint64_t)1)) {
						if (i != j) {
							assert(s->assigns[var1 + i] == l_True);
							veci_push(&lits1, lit_neg(toLit(var1 + i)));

							assert(s->assigns[var2 + i] == l_True);
							veci_push(&lits1, lit_neg(toLit(var2 + i)));
						}
					}
					else {
						assert(s->assigns[var1 + i] == l_False);
						veci_push(&lits1, toLit(var1 + i));

						assert(s->assigns[var2 + i] == l_False);
						veci_push(&lits1, toLit(var2 + i));
					}

				}
			}
			else {
				for (i = bitwid - 1; i >= 0; xlp >>= 1, i--) {
					if ((xlp &(uint64_t)1)) {
						if (i != j) {
							assert(s->assigns[var2 + i] == l_True);
							veci_push(&lits1, lit_neg(toLit(var2 + i)));

						}
					}
					else {
						assert(s->assigns[var2 + i] == l_False);
						veci_push(&lits1, toLit(var2 + i));
					}
				}
			}

			assert(s->assigns[var3] == l_False);
			veci_push(&lits1, toLit(var3));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else  //values[lt]==l_True
		{
			veci_push(&lits1, toLit(lt));

			if (var1 != -2) {
				assert(s->assigns[var1 + j] == l_False);
				veci_push(&lits1, toLit(var1 + j));

				for (i = bitwid - 1;i >= 0; xlp >>= 1, i--) {
					if ((xlp &(uint64_t)1)) {
						assert(s->assigns[var1 + i] == l_True);
						veci_push(&lits1, lit_neg(toLit(var1 + i)));

						assert(s->assigns[var2 + i] == l_True);
						veci_push(&lits1, lit_neg(toLit(var2 + i)));
					}
					else {
						if (i != j) {
							assert(s->assigns[var1 + i] == l_False);
							veci_push(&lits1, toLit(var1 + i));

							assert(s->assigns[var2 + i] == l_False);
							veci_push(&lits1, toLit(var2 + i));
						}
					}

				}
			}
			else {
				for (i = bitwid - 1; i >= 0; xlp >>= 1, i--) {
					if ((xlp &(uint64_t)1)) {
						assert(s->assigns[var2 + i] == l_True);
						veci_push(&lits1, lit_neg(toLit(var2 + i)));
					}
					else {
						if (i != j) {
							assert(s->assigns[var2 + i] == l_False);
							veci_push(&lits1, toLit(var2 + i));
						}
					}
				}
			}

			assert(s->assigns[var3] == l_False);
			veci_push(&lits1, toLit(var3));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	return 0;
}

int equall_explan(solver *s, int var1, int var2, int var3, int lt, clause** c) {
	int i;
	veci lits1;
	veci_new(&lits1);
	int varorder = s->varorder[lt];

	if (varorder == 1) {
		i = lt - var1;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));
			if (var2 != -2) {
				assert(s->assigns[var2 + i] == l_True);
				veci_push(&lits1, lit_neg(toLit(var2 + i)));
			}

			assert(s->assigns[var3] == l_True);
			veci_push(&lits1, lit_neg(toLit(var3)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));
			if (var2 != -2) {
				assert(s->assigns[var2 + i] == l_False);
				veci_push(&lits1, toLit(var2 + i));
			}

			assert(s->assigns[var3] == l_True);
			veci_push(&lits1, lit_neg(toLit(var3)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else //if(varorder ==2)
	{
		i = lt - var2;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));
			if (var1 != -2) {
				assert(s->assigns[var1 + i] == l_True);
				veci_push(&lits1, lit_neg(toLit(var1 + i)));
			}

			assert(s->assigns[var3] == l_True);
			veci_push(&lits1, lit_neg(toLit(var3)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));
			if (var1 != -2) {
				assert(s->assigns[var1 + i] == l_False);
				veci_push(&lits1, toLit(var1 + i));
			}

			assert(s->assigns[var3] == l_True);
			veci_push(&lits1, lit_neg(toLit(var3)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	return 0;
}

int bvequall_explan(solver *s, int var1, int var2, int lt, clause** c) // var2 never constant
{
	int i;
	veci lits1;
	veci_new(&lits1);
	int varorder = s->varorder[lt];

	if (varorder == 1) {
		i = lt - var1;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));
			assert(s->assigns[var2 + i] == l_True);
			veci_push(&lits1, lit_neg(toLit(var2 + i)));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));
			assert(s->assigns[var2 + i] == l_False);
			veci_push(&lits1, toLit(var2 + i));

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else //if(varorder ==2)
	{
		i = lt - var2;
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));
			if (var1 != -2) {
				assert(s->assigns[var1 + i] == l_True);
				veci_push(&lits1, lit_neg(toLit(var1 + i)));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));
			if (var1 != -2) {
				assert(s->assigns[var1 + i] == l_False);
				veci_push(&lits1, toLit(var1 + i));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	return 0;
}


int undef_equall_explan(int var1, int var2, int bitwid, unsigned long int ax, struct ul *uplw, int lt, clause** c) {
	veci lits1;
	veci_new(&lits1);

	int i;

	unsigned long int xlp;

	if (var1 != -2) {
		xlp = uplw->lower;
	}
	else {
		xlp = ax;
	}


	veci_push(&lits1, toLit(lt));
	if (var1 != -2) {
		if (var2 != -2)
			for (i = bitwid - 1; i >= 0; xlp >>= 1, i--) {
				if ((xlp &(uint64_t)1)) {
					veci_push(&lits1, lit_neg(toLit(var1 + i)));
					veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
				else {
					veci_push(&lits1, toLit(var1 + i));
					veci_push(&lits1, toLit(var2 + i));
				}

			}
		else
			for (i = bitwid - 1; i >= 0; xlp >>= 1, i--) {
				if ((xlp &(uint64_t)1)) {
					veci_push(&lits1, lit_neg(toLit(var1 + i)));
				}
				else {
					veci_push(&lits1, toLit(var1 + i));
				}

			}
	}
	else {
		if (var2 != -2)
			for (i = bitwid - 1; i >= 0; xlp >>= 1, i--) {
				if ((xlp &(uint64_t)1)) {
					veci_push(&lits1, lit_neg(toLit(var2 + i)));
				}
				else {
					veci_push(&lits1, toLit(var2 + i));
				}

			}
	}

	*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
	veci_delete(&lits1);
	return 0;
}

// propagate x, let x <=y  , fix x to 0
int lessthan1_explan(solver *s, int var1, int var2, int var3, struct ul *uplw1, struct ul *uplw2, int bitwid, 
	unsigned long int ax, unsigned long int ay, int lt, clause**c) {   

	int ii, gg, i;
	veci lits1;
	veci_new(&lits1);
	unsigned long int xlp, yup, lower;
	unsigned long int znew, app;

	unsigned long int mask;
	if (bitwid == 64)
		mask = ~((uint64_t)(-1) << bitwid);
	else
		mask = (uint64_t)(-1);


	lbool*  values = s->assigns;


	if (var1 != -2) {
		xlp = uplw1->lower;
	}
	else {
		xlp = ax;
	}

	if (var2 != -2) {
		yup = uplw2->upper;
	}
	else {
		yup = ay;
	}

	ii = bitwid + var1 - 1 - lt;   gg = lt - var1;
	app = ((uint64_t)1) << ii;
	lower = xlp | app;

	veci_push(&lits1, lit_neg(toLit(lt)));  // 1 bit of x, 0 bit of y, neg of x, pos of y

	znew = (lower & (~yup)) & mask;
	int j = __builtin_clzl(znew) - (64 - bitwid);

	if (var1 != -2)
		for (i = 0; i <= j; i++) {
			if (values[var1 + i] == l_True && i != gg) {
				veci_push(&lits1, lit_neg(toLit(var1 + i)));
			}
		}
	if (var2 != -2)
		for (i = 0; i <= j; i++) {
			if (values[var2 + i] == l_False) {
				veci_push(&lits1, toLit(var2 + i));
			}
		}

	assert(s->assigns[var3] == l_True);
	veci_push(&lits1, lit_neg(toLit(var3)));
	*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
	veci_delete(&lits1);
	return 3;

}

//fix y to 1 
int lessthan2_explan(solver *s, int var1, int var2, int var3, struct ul *uplw1, struct ul *uplw2, int bitwid, 
	unsigned long int ax, unsigned long int ay, int lt, clause **c) {	 

	int ii, gg, i;
	veci lits1;
	veci_new(&lits1);

	unsigned long int xlp, yup, upper;
	unsigned long int znew, app;

	unsigned long int mask;
	if (bitwid == 64)
		mask = ~((uint64_t)(-1) << bitwid);
	else
		mask = (uint64_t)(-1);

	lbool*  values = s->assigns;

	if (var1 != -2) {
		xlp = uplw1->lower;
	}
	else {
		xlp = ax;
	}

	if (var2 != -2) {
		yup = uplw2->upper;
	}
	else {
		yup = ay;
	}

	ii = bitwid + var2 - 1 - lt;  gg = lt - var2;
	app = ((uint64_t)1) << ii;
	upper = yup & (~app) & mask;

	znew = xlp & (~upper) & mask;
	int j = __builtin_clzl(znew) - (64 - bitwid);

	veci_push(&lits1, toLit(lt));   // 1 bit of x, 0 bit of y, neg of x, pos of y

	if (var1 != -2)
		for (i = 0; i <= j; i++) {
			if (values[var1 + i] == l_True) {
				veci_push(&lits1, lit_neg(toLit(var1 + i)));
			}
		}
	if (var2 != -2)
		for (i = 0; i <= j; i++) {
			if (values[var2 + i] == l_False && i != gg) {
				veci_push(&lits1, toLit(var2 + i));
			}
		}

	assert(s->assigns[var3] == l_True);
	veci_push(&lits1, lit_neg(toLit(var3)));
	*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
	veci_delete(&lits1);
	return 3;
}

// x > y, propagate x , fix x to 1
int great_eq1_explan(solver *s, int var1, int var2, int var3, struct ul *uplw1, struct ul *uplw2, int bitwid, 
	unsigned long int ax, unsigned long int ay, int lt, clause** c) {
	
	int ii, gg, i;
	veci lits1;
	veci_new(&lits1);

	unsigned long int xup, ylp, upper;
	unsigned long int znew, app;
	unsigned long int mask;
	if (bitwid == 64)
		mask = ~((uint64_t)(-1) << bitwid);
	else
		mask = (uint64_t)(-1);

	lbool*  values = s->assigns;

	if (var1 != -2) {
		xup = uplw1->upper;
	}
	else {
		xup = ax;
	}

	if (var2 != -2) {
		ylp = uplw2->lower;
	}
	else {
		ylp = ay;
	}


	ii = bitwid + var1 - 1 - lt; gg = lt - var1;
	app = ((uint64_t)1) << ii;
	upper = xup & (~app) & mask;

	veci_push(&lits1, toLit(lt));  //fix x to 1 ;  0 of x, 1 of y, pos of x, neg of y

	znew = ylp & (~upper) & mask;
	int j = __builtin_clzl(znew) - (64 - bitwid);

	if (var1 != -2)
		for (i = 0; i <= j; i++) {
			if (values[var1 + i] == l_False  && i != gg) {
				veci_push(&lits1, toLit(var1 + i));
			}
		}
	if (var2 != -2)
		for (i = 0; i <= j; i++) {
			if (values[var2 + i] == l_True) {
				veci_push(&lits1, lit_neg(toLit(var2 + i)));
			}
		}

	assert(s->assigns[var3] == l_False);
	veci_push(&lits1, toLit(var3));

	*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
	veci_delete(&lits1);
	return 3;
}
// x > y propagate y, fix y to 0
int great_eq2_explan(solver *s, int var1, int var2, int var3, struct ul *uplw1, struct ul *uplw2, int bitwid, 
	unsigned long int ax, unsigned long int ay, int lt, clause** c) { 
	int ii, gg, i;
	veci lits1;
	veci_new(&lits1);

	unsigned long int xup, ylp, lower;
	unsigned long int znew;
	unsigned long int mask;
	if (bitwid == 64)
		mask = ~((uint64_t)(-1) << bitwid);
	else
		mask = (uint64_t)(-1);

	unsigned long int app;
	lbool*  values = s->assigns;

	if (var1 != -2) {
		xup = uplw1->upper;
	}
	else {
		xup = ax;
	}

	if (var2 != -2) {
		ylp = uplw2->lower;
	}
	else {
		ylp = ay;
	}

	ii = bitwid + var2 - 1 - lt; gg = lt - var2;
	app = ((uint64_t)1) << ii;
	lower = ylp | app;

	veci_push(&lits1, lit_neg(toLit(lt)));  // fix y to 0, pos of x, neg of y; 0 of x, 1 of y

	// xup < lower
	znew = lower & (~xup) & mask;
	int j = __builtin_clzl(znew) - (64 - bitwid);

	if (var1 != -2)
		for (i = 0; i <= j; i++) {
			if (values[var1 + i] == l_False) {
				veci_push(&lits1, toLit(var1 + i));
			}
		}
	if (var2 != -2)
		for (i = 0; i <= j; i++) {
			if (values[var2 + i] == l_True && i != gg) {
				veci_push(&lits1, lit_neg(toLit(var2 + i)));
			}
		}

	assert(s->assigns[var3] == l_False);
	veci_push(&lits1, toLit(var3));
	*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
	veci_delete(&lits1);
	return 0;
}

int bit_toword_explan(solver *s, int var, int var_word, int bitwid, int lt, clause** c) {
	veci lits1;
	veci_new(&lits1);

	if (var == lt) {
		assert(var > 0);
		int i;  lbool *values = s->assigns;
		if (values[lt] == l_True) {
			veci_push(&lits1, toLit(lt));

			int word; int *pos = s->pos; int min_pos = pos[lt];
			for (i = 0; i < bitwid; i++) {
				word = var_word + i;
				if (values[word] == l_True && pos[word] < min_pos) // choose the smallest level
				{
					min_pos = pos[word];

					veci_resize(&lits1, 1);
					veci_push(&lits1, lit_neg(toLit(word)));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));

			int word; int *pos = s->pos; int min_pos = pos[lt];
			for (i = 0; i < bitwid; i++) {
				word = var_word + i;
				if (values[word] == l_False && pos[word] < min_pos) // choose the smallest level
				{
					min_pos = pos[word];

					veci_resize(&lits1, 1);
					veci_push(&lits1, toLit(word));
				}
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	else // var_word
	{
		if (s->assigns[lt] == l_True) {
			veci_push(&lits1, toLit(lt));
			if (var > 0) {
				assert(s->assigns[var] == l_True);
				veci_push(&lits1, lit_neg(toLit(var)));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
		else {
			veci_push(&lits1, lit_neg(toLit(lt)));
			if (var > 0) {
				assert(s->assigns[var] == l_False);
				veci_push(&lits1, toLit(var));
			}

			*c = explan_generate(veci_begin(&lits1), veci_size(&lits1));
			veci_delete(&lits1);
			return 0;
		}
	}
	return 1;
}


void explanation_generator(solver* s, lit v, struct ws_flag* i, clause** c) //explanation generator
{
	lbool*  values = s->assigns;

	int oper = i->oper;
	int* arnum = i->arnum;

	assert(i != NULL);

	switch (oper) {
	case P_BVAND://conjunction
	{
		unsigned long int* bound = i->bound;
		conjunction_explan(s, arnum[0], arnum[1], arnum[2], i->bitwids[0], v, bound[0], bound[1], c);
	}
	break;

	case P_BVNAND://conjunction
	{

		unsigned long int* bound = i->bound;
		conjunction_neg_explan(s, arnum[0], arnum[1], arnum[2], i->bitwids[0], v, bound[0], bound[1], c);
	}
	break;

	case P_BVNEG://negatioin
	{

		negation_explan(s, arnum[0], arnum[1], v, c);
	}
	break;

	case P_BVOR://disjunction
	{

		unsigned long int* bound = i->bound;

		disjunction_explan(s, arnum[0], arnum[1], arnum[2], i->bitwids[0], v, bound[0], bound[1], c);

	}
	break;

	case P_BVNOR://disjunction
	{

		unsigned long int* bound = i->bound;

		disjunction_neg_explan(s, arnum[0], arnum[1], arnum[2], i->bitwids[0], v, bound[0], bound[1], c);

	}
	break;

	case P_BVXOR://exclusiveor
	{

		exclusiveor_explan(s, arnum[0], arnum[1], arnum[2], v, c);
	}
	break;

	case P_BVXNOR://exclusiveor
	{

		exclusiveor_neg_explan(s, arnum[0], arnum[1], arnum[2], v, c);
	}
	break;

	case P_BVXOR_DIV://exclusiveor
	{

		exclusiveor_div_explan(s, arnum[0], arnum[1], v, c);
	}
	break;

	case P_ITE://ifstatement
	{
		ifstatement_explan(s, arnum[0], arnum[1], arnum[2], arnum[3], v, c);
	}
	break;

	case P_BVLEFTSHIFT://leftshift
	{
		int* bitwids = i->bitwids;
		leftshift_explan(s, arnum[0], arnum[1], bitwids[1], bitwids[0], v, c);

	}
	break;

	case P_BVRIGHTSHIFT://rightshift
	{

		int* bitwids = i->bitwids;
		rightshift_explan(s, arnum[0], arnum[1], bitwids[1], v, c);
	}
	break;

	case P_BVSRSHIFT://BVSRSHIFT
	{
		int* bitwids = i->bitwids;
		bvsrshift_explan(s, arnum[0], arnum[1], bitwids[1], v, c);

	}
	break;

	case P_BVCONCAT://bvconcat
	{

		int *bitwids = i->bitwids;
		bvconcat_explan(s, arnum[0], arnum[1], arnum[2], bitwids[1], v, c);
	}
	break;

	case P_BVEXTRACT://extract
	{
		int *bitwids = i->bitwids;
		extract_explan(s, arnum[0], arnum[1], bitwids[0], bitwids[1], v, c);

	}
	break;

	case P_BVZX://ZERO_EXTEND
	{

		int *bitwids = i->bitwids;
		zero_extend_explan(s, arnum[0], arnum[1], bitwids[0], v, c);
	}
	break;

	case P_BVSX://SIGN_EXTEND
	{
		int *bitwids = i->bitwids;
		sign_extend_explan(s, arnum[0], arnum[1], bitwids[0], v, c);

	}
	break;
	case P_BVEQ_C://SIGN_EXTEND
	{
		int var3 = arnum[2];

		if (v == var3) {
			undef_equall_explan(arnum[0], arnum[1], i->bitwids[0], i->bound[0], i->argu[0], v, c);
		}
		else {
			if (values[var3] == l_True) {
				equall_explan(s, arnum[0], arnum[1], var3, v, c);
			}
			else {

				inequall_explan(s, arnum[0], arnum[1], var3, i->bitwids[0], i->bound[0], i->argu[0], v, c);
			}
		}

	}
	break;
	case P_BVLE_C://lessthan or equal
	{
		int var1 = arnum[0]; int var2 = arnum[1]; int var3 = arnum[2];   unsigned long int* bounds = i->bound;
		struct ul **argu = i->argu;	 int* bitwids = i->bitwids;

		if (var1 != -2) {
			int ii = v - var1;
			if (ii >= 0 && ii < bitwids[0]) {
				if (values[v] == l_True) {
					great_eq1_explan(s, var1, var2, var3, argu[0], argu[1], bitwids[0], bounds[0], bounds[1], v, c);
				}
				else {
					lessthan1_explan(s, var1, var2, var3, argu[0], argu[1], bitwids[0], bounds[0], bounds[1], v, c);
				}
			}
		}
		if (var2 != -2) {
			int ii = v - var2;
			if (ii >= 0 && ii < bitwids[0]) {
				if (values[v] == l_True) {
					lessthan2_explan(s, var1, var2, var3, argu[0], argu[1], bitwids[0], bounds[0], bounds[1], v, c);
				}
				else {
					great_eq2_explan(s, var1, var2, var3, argu[0], argu[1], bitwids[0], bounds[0], bounds[1], v, c);
				}
			}
		}
	}
	break;
	case P_BTOW:
	{
		bit_toword_explan(s, arnum[0], arnum[1], i->bitwids[0], v, c);
	}
	break;
	case P_BVEQUALL:
	{
		bvequall_explan(s, arnum[0], arnum[1], v, c);
	}
	break;
	}
}

// dequeue the propagator from the propagator queue, until there is a conflic or the propagator queue is empty
void propagator_solving(solver *s, vecp* confl_vecp) {
	lbool*  values = s->assigns;

	while (vecp_size(confl_vecp) == 0 && s->propt != s->proph) {
		s->stats.propagations++;
		s->stats.inspects++;
		struct ws_flag* prop = s->prop_que[s->proph]; //get the propagator from the propagator queue
		s->proph = (s->proph + 1) % prop_num;  // change the hearder of the propagator queue	

		struct ul** argus;  unsigned long int* bound; int* bitwids; int* arnum;


		bound = prop->bound;
		bitwids = prop->bitwids;
		argus = prop->argu;
		arnum = prop->arnum;

		switch (prop->oper) {
		case P_BVAND://conjunction
		{

			conjunction(s, arnum[0], arnum[1], arnum[2], argus[0], argus[1], argus[2], confl_vecp, bitwids[0], bound[0],
				bound[1], prop);

		}
		break;

		case P_BVNAND://negation of conjunction
		{

			conjunction_neg(s, arnum[0], arnum[1], arnum[2], argus[0], argus[1], argus[2], confl_vecp, bitwids[0], 
				bound[0], bound[1], prop);

		}
		break;

		case P_BVNEG://negatioin
		{
			negation(s, arnum[0], arnum[1], argus[0], argus[1], confl_vecp, bitwids[0], bound[0], prop);
		}
		break;

		case P_BVOR://disjunction
		{
			disjunction(s, arnum[0], arnum[1], arnum[2], argus[0], argus[1], argus[2], confl_vecp, bitwids[0], bound[0], 
				bound[1], prop);
		}
		break;

		case P_BVNOR://negation of disjunction
		{
			disjunction_neg(s, arnum[0], arnum[1], arnum[2], argus[0], argus[1], argus[2], confl_vecp, bitwids[0], 
				bound[0], bound[1], prop);
		}
		break;

		case P_BVXOR://exclusiveor
		{
			exclusiveor(s, arnum[0], arnum[1], arnum[2], argus[0], argus[1], argus[2], confl_vecp, bitwids[0], bound[0], 
				bound[1], prop);

		}
		break;

		case P_BVXNOR://negation of exclusiveor
		{
			exclusiveor_neg(s, arnum[0], arnum[1], arnum[2], argus[0], argus[1], argus[2], confl_vecp, bitwids[0], 
				bound[0], bound[1], prop);

		}
		break;

		case P_BVXOR_DIV://exclusiveor
		{
			exclusiveor_div(s, arnum[0], arnum[1], argus[0], argus[1], confl_vecp, bitwids[0], bound[0], prop);

		}
		break;
		case P_ITE://ifstatement
		{

			ifstatement(s, arnum[0], arnum[1], arnum[2], arnum[3], argus[0], argus[1], argus[2], argus[3], confl_vecp, 
				bitwids[0], bound[0], bound[1], prop);
		}
		break;

		case P_BVLEFTSHIFT://leftshift
		{
			leftshift(s, arnum[0], arnum[1], argus[0], argus[1], bitwids[1], confl_vecp, bitwids[0], bound[0], prop);

		}
		break;

		case P_BVRIGHTSHIFT://rightshift
		{
			rightshift(s, arnum[0], arnum[1], argus[0], argus[1], bitwids[1], confl_vecp, bitwids[0], bound[0], prop);

		}
		break;

		case P_BVSRSHIFT://arithmetic right shift
		{

			bvsrshift(s, arnum[0], arnum[1], argus[0], argus[1], bitwids[1], confl_vecp, bitwids[0], bound[0], prop);

		}
		break;

		case P_BVCONCAT:// concatenation
		{
			bvconcat(s, arnum[0], arnum[1], arnum[2], argus[0], argus[1], argus[2], confl_vecp, bitwids[0], bitwids[1], 
				bitwids[2], bound[0], bound[1], prop);

		}
		break;
		case P_BVEXTRACT://extraction
		{

			extract(s, arnum[0], arnum[1], argus[0], argus[1], confl_vecp, bitwids[0], bitwids[1], bitwids[2], bound[0], prop);

		}
		break;

		case P_BVZX://ZERO_EXTEND
		{
			zero_extend(s, arnum[0], arnum[1], argus[0], argus[1], confl_vecp, bitwids[0], bitwids[1], bound[0], prop);

		}
		break;
		case P_BVSX://SIGN_EXTEND
		{
			sign_extend(s, arnum[0], arnum[1], argus[0], argus[1], confl_vecp, bitwids[0], bitwids[1], bound[0], prop);
		}
		break;
		case P_BVEQ_C:// composed bveq
		{
			int var3 = arnum[2];

			if (values[var3] == l_True) // propagate x = y
			{
				equall(s, arnum[0], arnum[1], var3, argus[0], argus[1], confl_vecp, bitwids[0], bound[0], bound[1], prop);
			}
			else if (values[var3] == l_False) // propagate x != y
			{
				inequall(s, arnum[0], arnum[1], var3, argus[0], argus[1], confl_vecp, bitwids[0], bound[0], bound[1], prop);
			}
			else {
				undef_equall(s, arnum[0], arnum[1], var3, argus[0], argus[1], bitwids[0], bound[0], bound[1], prop);
			}
		}
		break;
		case P_BVLE_C: // composed bvle
		{
			int var3 = arnum[2];

			if (values[var3] == l_True)  // propagate x<=y, fix x to 0, y to 1
			{
				lessthan(s, arnum[0], arnum[1], var3, argus[0], argus[1], confl_vecp, bitwids[0], bound[0], bound[1], prop);
			}
			else if (values[var3] == l_False)// propagate x>y, fix x to 1, y to 0
			{
				great_eq(s, arnum[0], arnum[1], var3, argus[0], argus[1], confl_vecp, bitwids[0], bound[0], bound[1], prop);
			}
			else {
				less_eq_Undef(s, arnum[0], arnum[1], var3, argus[0], argus[1], bitwids[0], bound[0], bound[1]);
			}
		}
		break;
		case P_BTOW: // bitword = bitx bitx bitx....bitx;
		{
			bit_toword(s, arnum[0], arnum[1], argus[0], confl_vecp, bitwids[0], prop);
		}
		break;
		case P_BVEQUALL:
		{
			bvequall(s, arnum[0], arnum[1], argus[0], argus[1], confl_vecp, bitwids[0], bound[0], bound[1], prop);
		}
		}

		prop->inqueue_flag = -1;    //dequeue the propagator
	}
}

