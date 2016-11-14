/********************************************************************
 * AUTHORS: David L. Dill, Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 Permission is hereby granted, free of charge, to any person obtaining a copy
 of this software and associated documentation files (the "Software"), to deal
 in the Software without restriction, including without limitation the rights
 to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in
 all copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 THE SOFTWARE.
 ********************************************************************/
#include <cmath>
#include <cassert>
#include "stp/ToSat/BitBlaster.h"
#include "stp/ToSat/AIG/BBNodeManagerAIG.h"
#include "stp/ToSat/ASTNode/BBNodeManagerASTNode.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include "stp/Simplifier/constantBitP/NodeToFixedBitsMap.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Sat/solver.h" 

#ifdef _MSC_VER
#include <compdep.h>
#endif

namespace stp {

	/********************************************************************
	 * BitBlast
	 *
	 * Convert bitvector terms and formulas to boolean formulas.  A term
	 * is something that can represent a multi-bit bitvector, such as
	 * BVPLUS or BVXOR (or a BV variable or constant).  A formula (form)
	 * represents a boolean value, such as EQ or BVLE.  Bit blasting a
	 * term representing an n-bit bitvector with BBTerm yields a vector
	 * of n boolean formulas (returning BBNodeVec).  Bit blasting a formula
	 * returns a single boolean formula (type BBNode).  A bitblasted
	 * term is a vector of BBNodes for formulas.  The 0th element of
	 * the vector corresponds to bit 0 -- the low-order bit.
	 ********************************************************************/

	using simplifier::constantBitP::FixedBits;
	using simplifier::constantBitP::NodeToFixedBitsMap;
	using std::make_pair;

#define BBNodeVec vector<BBNode>
#define BBNodeVecMap std::map<ASTNode, vector<BBNode>>
#define BBNodeSet std::set<BBNode>

	vector<BBNodeAIG> _empty_BBNodeAIGVec;

	// Bit blast a bitvector term.  The term must have a kind for a
	// bitvector term.  Result is a ref to a vector of formula nodes
	// representing the boolean formula.

	// This prints out each constant expression that the bitblaster
	// discovers. I use this to check that the expressions that are
	// reaching the bitblaster don't have obvious simplifications
	// that should have already been applied.
	const bool debug_do_check = false;
	const bool debug_bitblaster = false;

	const bool conjoin_to_top = true;

	int my_wwform(solver *s, const ASTNode& form);
	int my_wwterm(solver *s, const ASTNode& term);
	int my_wwform_check(const ASTNode& form);
	int my_wwterm_check(const ASTNode& term);
	void bitwise2_general(solver *s, int xkind, unsigned long int xnum, int ykind, unsigned long int ynum, int left_num, 
		int expkind, int num_bits);
	void iteterm_generate(solver *s, int xkind, int xnum, int ykind, unsigned long int ynum, int zkind, 
		unsigned long int znum, int left_num, int num_bits);
	void TranstoClause_signxor(solver *s, const ASTNode& x, const ASTNode& y, int left_num, int bitwid);
	void TranstoClause_signcompare(solver *s, const ASTNode& x, const ASTNode& y, int m2, int left_num);
	void set_right_onebit(int *right, int xkind, unsigned long int xnum, int index);
	void set_rightmost(int *right, const ASTNode& x, int bitwid, int index);
	void bvequall_generate(solver *s, unsigned long int x, unsigned long int y, int bitwid, int kindx);
	void bvle_div_generate(solver *s, unsigned long int x, unsigned long int y, int bitwid, int kindx, int kindy); // y <= m1 <-> false
	void bvle_generate(solver *s, unsigned long int x, unsigned long int y, int b, int bitwid, int kindx, int kindy);
	void bveq_generate(solver *s, unsigned long int x, unsigned long int y, int b, int bitwid, int kindx, int kindy);
	void bvumod_generate(solver *s, unsigned long int xnum, unsigned long int ynum, int znum, int kindx, int kindy, int num_bits);
	void bvudiv_generate(solver *s, unsigned long int xnum, unsigned long int ynum, int znum, int kindx, int kindy, int num_bits);
	void bvmult_generate(solver *s, int kindx, int kindy, int k, unsigned long int xnum, unsigned long int ynum, int left_num);
	void leftshiftx(solver *s, int xnum, int bitwid, int shiftbits, int left_num);
	void leftshiftx_noverflow(solver *s, int xnum, int bitwid, int shiftbits, int left_num, int ynum);
	int leftshift_mult(solver *s, int bitwid, int bit_num, int xnum);
	int leftshift_mult_noverflow(solver *s, int bitwid, int bit_num, int xnum);
	void bvsub_generate(solver *s, unsigned long int x, unsigned long int y, int z, int bitwid, int kindx, int kindy);
	void bvuminus_generate(solver *s, unsigned long int x, int z, int bitwid, int kindx);
	void bvplus_divmod_generate(solver *s, int x, int y, unsigned long int z, int bitwid, int kindz);
	int bvplus_generate(solver *s, unsigned long int x, unsigned long int y, int z, int bitwid, int kindx, int kindy);
	void check_iteconst(int kindx, int* right, unsigned long int* param, int i, unsigned long int num);
	void check_const(int kindx, int* right, unsigned long int* param, int i, unsigned long int num);
	void bit_toword_generate(solver *s, int bitwid, int xbit, int xword);
	void iteparse_generate(solver *s, int bitwid, int* right, int left, unsigned long int* param, int x_begin); //ite
	void shift_generate(solver *s, int kind, int bitwid, int* right, int left, unsigned long int* param);
	void extend_generate(solver *s, int kind, int bitwid, int* right, int left, unsigned long int* param);
	void extract_generate(solver *s, int bitwid, int* right, int left, unsigned long int* param, int subwid1, int subwid2);
	void concate_generate(solver *s, int bitwid, int* right, int left, unsigned long int* param, int subwid1, int subwid2);
	void bvxor_div_generate(solver *s, int bitwid, int* right, unsigned long int left);
	void bitwise1_generate(solver *s, int bitwid, int* right, int left, unsigned long int* param);
	void bitwise2_generate(solver *s, int kind, int bitwid, int* right, int left, unsigned long int* param);
	void compose_generate(solver *s, int kind, int bitwid, int* right, int left, unsigned long int* param);
	void TranstoClause_wite(solver *s, int xkind, unsigned long int xnum, int ykind, unsigned long int ynum, int zkind, 
		unsigned long int znum, int left_num);
	void TranstoClause_bitwise_onebit(solver *s, int xkind, unsigned long int xnum, int ykind, unsigned long int ynum, 
		int left_num, int expkind);
	void TranstoClause_wnot(solver *s, int xkind, unsigned long int xnum, unsigned long int left_num);
	void TranstoClause_wiff(solver *s, int xkind, unsigned long int xnum, int ykind, unsigned long int ynum, int left_num);
	int TranstoClause_bvor(solver *s, int right1_kind, int right1_num, int right2_kind, int right2_num, int left_num);
	void TranstoClause_bvand_val(solver *s, int right1_num, int right2_num, int left_num);
	int TranstoClause_bvand(solver *s, int right1_kind, int right1_num, int right2_kind, int right2_num, int left_num);
	int TranstoClause_Boolex(solver *s, const ASTNode& form, int index, int left_num);
	int TranstoClause_Bite(solver *s, int b_kind, int b_num, int x_kind, int x_num, int y_kind, int y_num, int left_num);
	int TranstoClause_Biff(solver *s, int right1_kind, int right1_num, int right2_kind, int right2_num, int left_num);
	int TranstoClause_Bxor_sym(solver *s, int right1_num, int right2_num, int left_num);
	int TranstoClause_Bxor(solver *s, int right1_kind, int right1_num, int right2_kind, int right2_num, int left_num);
	int TranstoClause_implies(solver *s, int right1_kind, int right1_num, int right2_kind, int right2_num, int left_num);
	int TranstoClause_Bnot_val(solver *s, int right_num, int left_num);
	int TranstoClause_Bnot(solver *s, int right_kind, int right_num, int left_num);
	void creat_clause1(solver *s, int l);
	void creat_clause2(solver *s, int l1, int l2);
	void creat_clause3(solver *s, int l1, int l2, int l3);
	void creat_clausen(solver *s, lit* begin, lit* end);
	struct ul* add_worduplo(solver* s, int v1, int bitwid);
	void realloc_wordinfo(solver *s, int num);
	void realloc_prop(solver *s, int num);

	ASTNodeSet ASTMemo;
	ASTNodeSet ASTMemo_check;


	template <class BBNode> class BBVecHasher {
	public:
		size_t operator()(const vector<BBNode>& n) const {
			int hash = 0;
			for (size_t i = 0; i < std::min(n.size(), (size_t)6); i++) {
				hash += n[i].GetNodeNum();
			}
			return hash;
		}
	};

	template <class BBNode> class BBVecEquals {
	public:
		bool operator()(const vector<BBNode>& n0, const vector<BBNode>& n1) const {
			if (n0.size() != n1.size())
				return false;

			for (size_t i = 0; i < n0.size(); i++) {
				if (!(n0[i] == n1[i]))
					return false;
			}
			return true;
		}
	};

	// Look through the maps to see what the bitblaster has discovered (if anything)
	// is constant.
	// then looks through for AIGS that are mapped to from different ASTNodes.
	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::getConsts(const ASTNode& form,
		ASTNodeMap& fromTo,
		ASTNodeMap& equivs) {
		assert(form.GetType() == BOOLEAN_TYPE);

		BBNodeSet support;
		BBForm(form, support);

		assert(support.size() == 0);

		{
			typename std::map<ASTNode, BBNode>::iterator it;
			for (it = BBFormMemo.begin(); it != BBFormMemo.end(); it++) {
				const ASTNode& n = it->first;
				const BBNode& x = it->second;
				if (n.isConstant())
					continue;

				if (x != BBTrue && x != BBFalse)
					continue;

				assert(n.GetType() == BOOLEAN_TYPE);

				ASTNode result;
				if (x == BBTrue)
					result = n.GetSTPMgr()->ASTTrue;
				else
					result = n.GetSTPMgr()->ASTFalse;

				if (n.GetKind() != SYMBOL)
					fromTo.insert(std::make_pair(n, result));
				else
					simp->UpdateSubstitutionMap(n, result);
			}
		}

		typename BBNodeVecMap::iterator it;
		for (it = BBTermMemo.begin(); it != BBTermMemo.end(); it++) {
			const ASTNode& n = it->first;
			assert(n.GetType() == BITVECTOR_TYPE);

			if (n.isConstant())
				continue;

			vector<BBNode>& x = it->second;
			assert(x.size() == n.GetValueWidth());

			bool constNode = true;
			for (int i = 0; i < (int)x.size(); i++) {
				if (x[i] != BBTrue && x[i] != BBFalse) {
					constNode = false;
					break;
				}
			}
			if (!constNode)
				continue;

			CBV val = CONSTANTBV::BitVector_Create(n.GetValueWidth(), true);
			for (int i = 0; i < (int)x.size(); i++) {
				if (x[i] == BBTrue)
					CONSTANTBV::BitVector_Bit_On(val, i);
			}

			ASTNode r = n.GetSTPMgr()->CreateBVConst(val, n.GetValueWidth());
			if (n.GetKind() == SYMBOL)
				simp->UpdateSubstitutionMap(n, r);
			else
				fromTo.insert(std::make_pair(n, r));
		}

		if (form.GetSTPMgr()->UserFlags.isSet("bb-equiv", "1")) {
			hash_map<intptr_t, ASTNode> nodeToFn;
			typename std::map<ASTNode, BBNode>::iterator it;
			for (it = BBFormMemo.begin(); it != BBFormMemo.end(); it++) {
				const ASTNode& n = it->first;
				if (n.isConstant())
					continue;

				const BBNode& x = it->second;
				if (x == BBTrue || x == BBFalse)
					continue;

				if (nodeToFn.find(x.GetNodeNum()) == nodeToFn.end()) {
					nodeToFn.insert(make_pair(x.GetNodeNum(), n));
				}
				else {
					const ASTNode other = (nodeToFn.find(x.GetNodeNum()))->second;
					std::pair<ASTNode, ASTNode> p;
					if (other.GetNodeNum() > n.GetNodeNum())
						p = make_pair(other, n);
					else
						p = make_pair(n, other);

					equivs.insert(p);
					// std::cerr << "from" << p.first << " to" << p.second;
					// ASTNode equals =
					// ASTNF->CreateNode(NOT,ASTNF->CreateNode(EQ,p.first,p.second));
					// printer::SMTLIB2_PrintBack(std::cerr,p.second);
				}
			}
		}

		typedef hash_map<vector<BBNode>, ASTNode, BBVecHasher<BBNode>,
			BBVecEquals<BBNode>> M;
		if (form.GetSTPMgr()->UserFlags.isSet("bb-equiv", "1")) {
			M lookup;
			typename std::map<ASTNode, vector<BBNode>>::iterator it;
			for (it = BBTermMemo.begin(); it != BBTermMemo.end(); it++) {
				const ASTNode& n = it->first;
				if (n.isConstant())
					continue;

				const vector<BBNode>& x = it->second;

				bool constNode = true;
				for (int i = 0; i < (int)x.size(); i++) {
					if (x[i] != BBTrue && x[i] != BBFalse) {
						constNode = false;
						break;
					}
				}
				if (!constNode)
					continue;

				if (lookup.find(x) == lookup.end()) {
					lookup.insert(make_pair(x, n));
				}
				else {
					const ASTNode other = (lookup.find(x))->second;
					std::pair<ASTNode, ASTNode> p;
					if (other.GetNodeNum() > n.GetNodeNum())
						p = make_pair(other, n);
					else
						p = make_pair(n, other);

					// cerr << "EQUIV";
					equivs.insert(p);
				}
			}
		}
	}

	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::commonCheck(const ASTNode& n) {
		cerr << "Non constant is constant:";
		cerr << n << endl;

		if (cb == NULL)
			return;
		if (cb->fixedMap->map->find(n) != cb->fixedMap->map->end()) {
			FixedBits* b = cb->fixedMap->map->find(n)->second;
			cerr << "fixed bits are:" << *b << endl;
		}
	}

	// If x isn't a constant, and the bit-blasted version is. Print out the
	// AST nodes and the fixed bits.
	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::check(const BBNode& x,
		const ASTNode& n) {
		if (n.isConstant())
			return;

		if (x != BBTrue && x != BBFalse)
			return;

		commonCheck(n);
	}

	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::check(const vector<BBNode>& x,
		const ASTNode& n) {
		if (n.isConstant())
			return;

		for (int i = 0; i < (int)x.size(); i++) {
			if (x[i] != BBTrue && x[i] != BBFalse)
				return;
		}

		commonCheck(n);
	}

	template <class BBNode, class BBNodeManagerT>
	bool BitBlaster<BBNode, BBNodeManagerT>::update(
		const ASTNode& n, const int i, simplifier::constantBitP::FixedBits* b,
		BBNode& bb, BBNodeSet& support) {
		if (b->isFixed(i) && (!(bb == BBTrue || bb == BBFalse))) {
			// We have a fixed bit, but the bitblasted values aren't constant true or
			// false.
			if (conjoin_to_top && (fixedFromBottom.find(n) == fixedFromBottom.end())) {
				if (b->getValue(i))
					support.insert(bb);
				else
					support.insert(nf->CreateNode(NOT, bb));
			}

			bb = b->getValue(i) ? BBTrue : BBFalse;
		}
		else if (!b->isFixed(i) && (bb == BBTrue || bb == BBFalse)) {
			b->setFixed(i, true);
			b->setValue(i, bb == BBTrue ? true : false);
			return true; // Need to propagate.
		}

		return false;
	}

	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::updateForm(const ASTNode& n,
		BBNode& bb,
		BBNodeSet& support) {
		if (cb == NULL || n.isConstant())
			return;

		BBNodeVec v(1, bb);
		updateTerm(n, v, support);
		bb = v[0];
	}

	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::updateTerm(const ASTNode& n,
		BBNodeVec& bb,
		BBNodeSet& support) {

		if (cb == NULL)
			return;

		if (cb->isUnsatisfiable())
			return;

		if (n.isConstant()) {
			// This doesn't hold any longer because we convert BVSDIV and friends to
			// ASTNodes.
#if 0
			simplifier::constantBitP::NodeToFixedBitsMap::NodeToFixedBitsMapType::const_iterator it;
			it = cb->fixedMap->map->find(n);
			if (it == cb->fixedMap->map->end()) {
				cerr << n;
				assert(it != cb->fixedMap->map->end());
			}assert(it->second->isTotallyFixed());
#endif
			return;
		}

		bool bbFixed = false;
		for (int i = 0; i < (int)bb.size(); i++) {
			if (bb[i] == BBTrue || bb[i] == BBFalse) {
				bbFixed = true;
				break;
			}
		}

		FixedBits* b = NULL;

		simplifier::constantBitP::NodeToFixedBitsMap::NodeToFixedBitsMapType::
			const_iterator it;
		if ((it = cb->fixedMap->map->find(n)) == cb->fixedMap->map->end()) {
			if (bbFixed) {
				b = new FixedBits(n.GetType() == BOOLEAN_TYPE ? 1 : n.GetValueWidth(),
					n.GetType() == BOOLEAN_TYPE);
				cb->fixedMap->map->insert(std::pair<ASTNode, FixedBits*>(n, b));
				if (debug_bitblaster)
					cerr << "inserting" << n.GetNodeNum() << endl;
			}
			else
				return; // nothing to update.
		}
		else
			b = it->second;

		assert(b != NULL);
		FixedBits old(*b);

		bool changed = false;
		for (int i = 0; i < (int)bb.size(); i++)
			if (update(n, i, b, bb[i], support))
				changed = true; // don't break, we want to run update(..) on each bit.
		if (changed) {
			cb->scheduleNode(n);
			cb->scheduleUp(n);
			cb->propagate();
		}

		// If it's changed, the propagation may have caused new bits to be fixed.
		if (changed && !FixedBits::equals(*b, old)) {
			updateTerm(n, bb, support);
			return;
		}

		// There may be a conflict between the AIGs and the constant bits (if the
		// problem is unsatisfiable).
		// So we can't ensure that if one is fixed to true (say), that the other
		// should be true also.

		if (!cb->isUnsatisfiable())
			for (int i = 0; i < (int)bb.size(); i++) {
				if (b->isFixed(i))
					assert(bb[i] == BBTrue || bb[i] == BBFalse);

				if (bb[i] == BBFalse || bb[i] == BBTrue)
					assert(b->isFixed(i));
			}
	}

	template <class BBNode, class BBNodeManagerT>
	bool BitBlaster<BBNode, BBNodeManagerT>::isConstant(const BBNodeVec& v) {
		for (int i = 0; i < v.size(); i++) {
			if (v[i] != nf->getTrue() && v[i] != nf->getFalse())
				return false;
		}

		return true;
	}

	template <class BBNode, class BBNodeManagerT>
	ASTNode BitBlaster<BBNode, BBNodeManagerT>::getConstant(const BBNodeVec& v,
		const ASTNode& n) {
		if (n.GetType() == BOOLEAN_TYPE) {
			if (v[0] == nf->getTrue())
				return ASTNF->getTrue();
			else
				return ASTNF->getFalse();
		}

		CBV bv = CONSTANTBV::BitVector_Create(v.size(), true);

		for (int i = 0; i < v.size(); i++)
			if (v[i] == nf->getTrue())
				CONSTANTBV::BitVector_Bit_On(bv, i);

		return ASTNF->CreateConstant(bv, v.size());
	}

	template <class BBNode, class BBNodeManagerT>
	const BBNodeVec BitBlaster<BBNode, BBNodeManagerT>::BBTerm(const ASTNode& _term,
		BBNodeSet& support) {
		ASTNode term = _term; // mutable local copy.

		typename BBNodeVecMap::iterator it = BBTermMemo.find(term);
		if (it != BBTermMemo.end()) {
			// Constant bit propagation may have updated something.
			updateTerm(term, it->second, support);
			return it->second;
		}

		// This block checks if the bitblasting/fixed bits have discovered
		// any new constants. If they've discovered a new constant, then
		// the simplification function is called on a new term with the constant
		// value replacing what used to be a variable child. For instance, if
		// the term is ite(x,y,z), and we now know that x is true. Then we will
		// call SimplifyTerm on ite(true,y,z), which will do the expected
		// simplification.
		// Then the term that we bitblast will by "y".

		if (uf != NULL && uf->optimize_flag && uf->simplify_during_BB_flag) {
			const int numberOfChildren = term.Degree();
			vector<BBNodeVec> ch;
			ch.reserve(numberOfChildren);

			for (int i = 0; i < numberOfChildren; i++) {
				if (term[i].GetType() == BITVECTOR_TYPE) {
					ch.push_back(BBTerm(term[i], support));
				}
				else if (term[i].GetType() == BOOLEAN_TYPE) {
					BBNodeVec t;
					t.push_back(BBForm(term[i], support));
					ch.push_back(t);
				}
				else
					throw "sdfssfa";
			}

			bool newConst = false;
			for (int i = 0; i < numberOfChildren; i++) {
				if (term[i].isConstant())
					continue;

				if (isConstant(ch[i])) {
					// it's only interesting if the child isn't a constant,
					// but the bitblasted version is.
					newConst = true;
					break;
				}
			}

			// Something is now constant that didn't used to be.
			if (newConst) {
				ASTVec new_ch;
				new_ch.reserve(numberOfChildren);
				for (int i = 0; i < numberOfChildren; i++) {
					if (!term[i].isConstant() && isConstant(ch[i]))
						new_ch.push_back(getConstant(ch[i], term[i]));
					else
						new_ch.push_back(term[i]);
				}

				ASTNode n_term = simp->SimplifyTerm(
					ASTNF->CreateTerm(term.GetKind(), term.GetValueWidth(), new_ch));
				assert(BVTypeCheck(n_term));
				// n_term is the potentially simplified version of term.

				if (cb != NULL) {
					// Add all the nodes to the worklist that have a constant as a child.
					cb->initWorkList(n_term);

					simplifier::constantBitP::NodeToFixedBitsMap::NodeToFixedBitsMapType::
						iterator it;
					it = cb->fixedMap->map->find(n_term);
					FixedBits* nBits;
					if (it == cb->fixedMap->map->end()) {
						nBits = new FixedBits(std::max((unsigned)1, n_term.GetValueWidth()),
							term.GetType() == BOOLEAN_TYPE);
						cb->fixedMap->map->insert(
							std::pair<ASTNode, FixedBits*>(n_term, nBits));
					}
					else
						nBits = it->second;

					if (n_term.isConstant()) {
						// It's assumed elsewhere that constants map to themselves in the
						// fixed map.
						// That doesn't happen here unless it's added explicitly.
						*nBits = FixedBits::concreteToAbstract(n_term);
					}

					it = cb->fixedMap->map->find(term);
					if (it != cb->fixedMap->map->end()) {
						// Copy over to the (potentially) new node. Everything we know about
						// the old node.
						nBits->mergeIn(*(it->second));
					}

					cb->scheduleUp(n_term);
					cb->scheduleNode(n_term);
					cb->propagate();

					if (it != cb->fixedMap->map->end()) {
						// Copy to the old node, all we know about the new node. This means
						// that
						// all the parents of the old node get the (potentially) updated
						// fixings.
						it->second->mergeIn(*nBits);
					}
					// Propagate through all the parents of term.
					cb->scheduleUp(term);
					cb->scheduleNode(term);
					cb->propagate();
					// Now we've propagated.
				}
				term = n_term;

				// check if we've already done the simplified one.
				it = BBTermMemo.find(term);
				if (it != BBTermMemo.end()) {
					// Constant bit propagation may have updated something.
					updateTerm(term, it->second, support);
					return it->second;
				}
			}
		}

		BBNodeVec result;

		const Kind k = term.GetKind();
		if (!is_Term_kind(k))
			FatalError("BBTerm: Illegal kind to BBTerm", term);

		const ASTVec::const_iterator kids_end = term.end();
		const unsigned int num_bits = term.GetValueWidth();
		switch (k) {
		case BVNEG:
		{
			// bitwise complement
			const BBNodeVec& bbkids = BBTerm(term[0], support);
			result = BBNeg(bbkids);
			break;
		}

		case BVRIGHTSHIFT:
		case BVSRSHIFT:
		case BVLEFTSHIFT:
		{
			// Barrel shifter
			const BBNodeVec& bbarg1 = BBTerm(term[0], support);
			const BBNodeVec& bbarg2 = BBTerm(term[1], support);

			// Signed right shift, need to copy the sign bit.
			BBNode toFill;
			if (BVSRSHIFT == k)
				toFill = bbarg1.back();
			else
				toFill = nf->getFalse();

			BBNodeVec temp_result(bbarg1);
			// if any bit is set in bbarg2 higher than log2Width, then we know that
			// the result is zero.
			// Add one to make allowance for rounding down. For example, given 300
			// bits, the log2 is about
			// 8.2 so round up to 9.

			const unsigned width = bbarg1.size();
			const unsigned log2Width = (unsigned)log2(width) + 1;

			if (k == BVSRSHIFT || k == BVRIGHTSHIFT)
				for (unsigned int i = 0; i < log2Width; i++) {
					if (bbarg2[i] == nf->getFalse())
						continue; // Not shifting by anything.

					unsigned int shift_amount = 1 << i;

					for (unsigned int j = 0; j < width; j++) {
						if (j + shift_amount >= width)
							temp_result[j] =
							nf->CreateNode(ITE, bbarg2[i], toFill, temp_result[j]);
						else
							temp_result[j] =
							nf->CreateNode(ITE, bbarg2[i], temp_result[j + shift_amount],
								temp_result[j]);
					}
				}
			else
				for (unsigned int i = 0; i < log2Width; i++) {
					if (bbarg2[i] == nf->getFalse())
						continue; // Not shifting by anything.

					int shift_amount = 1 << i;

					for (signed int j = width - 1; j >= 0; j--) {
						if (j < shift_amount)
							temp_result[j] =
							nf->CreateNode(ITE, bbarg2[i], toFill, temp_result[j]);
						else
							temp_result[j] =
							nf->CreateNode(ITE, bbarg2[i], temp_result[j - shift_amount],
								temp_result[j]);
					}
				}

			// If any of the remainder are true. Then the whole thing gets the fill
			// value.
			BBNode remainder = nf->getFalse();
			for (unsigned int i = log2Width; i < width; i++) {
				remainder = nf->CreateNode(OR, remainder, bbarg2[i]);
			}

			for (unsigned int i = 0; i < width; i++) {
				temp_result[i] = nf->CreateNode(ITE, remainder, toFill, temp_result[i]);
			}

			result = temp_result;
		}
		break;

		case ITE:
		{
			// Term version of ITE.
			const BBNode& cond = BBForm(term[0], support);
			const BBNodeVec& thn = BBTerm(term[1], support);
			const BBNodeVec& els = BBTerm(term[2], support);
			result = BBITE(cond, thn, els);
			break;
		}

		case BVSX:
		case BVZX:
		{
			// Replicate high-order bit as many times as necessary.
			// Arg 0 is expression to be sign extended.
			const ASTNode& arg = term[0];
			const unsigned long result_width = term.GetValueWidth();
			const unsigned long arg_width = arg.GetValueWidth();
			const BBNodeVec& bbarg = BBTerm(arg, support);

			if (result_width == arg_width) {
				// nothing to sign extend
				result = bbarg;
				break;
			}
			else {
				// we need to sign extend
				const BBNode& msb = (k == BVSX) ? bbarg.back() : BBFalse;

				BBNodeVec tmp_res(result_width);

				typename BBNodeVec::const_iterator bb_it = bbarg.begin();
				typename BBNodeVec::iterator res_it = tmp_res.begin();
				typename BBNodeVec::iterator res_ext =
					res_it + arg_width; // first bit of extended part
				typename BBNodeVec::iterator res_end = tmp_res.end();

				// copy LSBs directly from bbvec
				for (; res_it < res_ext; (res_it++, bb_it++)) {
					*res_it = *bb_it;
				}
				// repeat MSB to fill up rest of result.
				for (; res_it < res_end; (res_it++)) {
					*res_it = msb;
				}

				result = tmp_res;
				break;
			}
		}

		case BVEXTRACT:
		{
			// bitblast the child, then extract the relevant bits.
			// Note: This could be optimized by not bitblasting the bits
			// that aren't fetched.  But that would be tricky, especially
			// with memo-ization.

			const BBNodeVec& bbkids = BBTerm(term[0], support);
			const unsigned int high = term[1].GetUnsignedConst();
			const unsigned int low = term[2].GetUnsignedConst();

			typename BBNodeVec::const_iterator bbkfit = bbkids.begin();
			// I should have used pointers to BBNodeVec, to avoid this crock

			result = BBNodeVec(bbkfit + low, bbkfit + high + 1);
			break;
		}
		case BVCONCAT:
		{
			const BBNodeVec& vec1 = BBTerm(term[0], support);
			const BBNodeVec& vec2 = BBTerm(term[1], support);

			BBNodeVec tmp_res(vec2);
			tmp_res.insert(tmp_res.end(), vec1.begin(), vec1.end());
			result = tmp_res;
			break;
		}
		case BVPLUS:
		{
			assert(term.Degree() >= 1);
			if (bvplus_variant) {
				// Add children pairwise and accumulate in BBsum

				ASTVec::const_iterator it = term.begin();
				BBNodeVec tmp_res = BBTerm(*it, support);
				for (++it; it < kids_end; it++) {
					const BBNodeVec& tmp = BBTerm(*it, support);
					assert(tmp.size() == num_bits);
					BBPlus2(tmp_res, tmp, nf->getFalse());
				}

				result = tmp_res;
			}
			else {
				// Add all the children up using an addition network.
				vector<BBNodeVec> results;
				for (int i = 0; i < term.Degree(); i++)
					results.push_back(BBTerm(term[i], support));

				const int bitWidth = term[0].GetValueWidth();
				vector<list<BBNode>> products(bitWidth + 1);
				for (int i = 0; i < bitWidth; i++) {
					for (int j = 0; j < results.size(); j++)
						products[i].push_back(results[j][i]);
				}

				result = buildAdditionNetworkResult(products, support, term);
			}
			break;
		}
		case BVUMINUS:
		{
			const BBNodeVec& bbkid = BBTerm(term[0], support);
			result = BBUminus(bbkid);
			break;
		}
		case BVSUB:
		{
			// complement of subtrahend
			// copy, since BBSub writes into it.

			BBNodeVec tmp_res = BBTerm(term[0], support);

			const BBNodeVec& bbkid1 = BBTerm(term[1], support);
			BBSub(tmp_res, bbkid1, support);
			result = tmp_res;
			break;
		}
		case BVMULT:
		{
			assert(BVTypeCheck(term));
			assert(term.Degree() == 2);

			BBNodeVec mpcd1 = BBTerm(term[0], support);
			const BBNodeVec& mpcd2 = BBTerm(term[1], support);
			updateTerm(term[0], mpcd1, support);

			assert(mpcd1.size() == mpcd2.size());
			result = BBMult(mpcd1, mpcd2, support, term);
			break;
		}
		case SBVREM:
		case SBVMOD:
		case SBVDIV:
		{
			ASTNode p = ArrayTransformer::TranslateSignedDivModRem(term, ASTNF,
				term.GetSTPMgr());
			result = BBTerm(p, support);
			break;
		}

		case BVDIV:
		case BVMOD:
		{
			const BBNodeVec& dvdd = BBTerm(term[0], support);
			const BBNodeVec& dvsr = BBTerm(term[1], support);
			assert(dvdd.size() == num_bits);
			assert(dvsr.size() == num_bits);
			BBNodeVec q(num_bits);
			BBNodeVec r(num_bits);
			BBDivMod(dvdd, dvsr, q, r, num_bits, support);
			if (k == BVDIV) {
				if (uf->division_by_zero_returns_one_flag) {
					BBNodeVec zero(term.GetValueWidth(), BBFalse);

					BBNode eq = BBEQ(zero, dvsr);
					BBNodeVec one(term.GetValueWidth(), BBFalse);
					one[0] = BBTrue;

					result = BBITE(eq, one, q);
				}
				else {
					result = q;
				}
			}
			else
				result = r;
			break;
		}
		//  n-ary bitwise operators.
		case BVXOR:
		case BVXNOR:
		case BVAND:
		case BVOR:
		case BVNOR:
		case BVNAND:
		{
			// Add children pairwise and accumulate in BBsum
			ASTVec::const_iterator it = term.begin();
			Kind bk = UNDEFINED; // Kind of individual bit op.
			switch (k) {
			case BVXOR:
				bk = XOR;
				break;
			case BVXNOR:
				bk = IFF;
				break;
			case BVAND:
				bk = AND;
				break;
			case BVOR:
				bk = OR;
				break;
			case BVNOR:
				bk = NOR;
				break;
			case BVNAND:
				bk = NAND;
				break;
			default:
				FatalError("BBTerm: Illegal kind to BBTerm", term);
				break;
			}

			// Sum is destructively modified in the loop, so make a copy of value
			// returned by BBTerm.
			BBNodeVec temp = BBTerm(*it, support);
			BBNodeVec sum(temp); // First operand.

			// Iterate over remaining bitvector term operands
			for (++it; it < kids_end; it++) {
				// FIXME FIXME FIXME: Why does using a temp. var change the behavior?
				temp = BBTerm(*it, support);
				const BBNodeVec& y = temp;

				assert(y.size() == num_bits);
				for (unsigned i = 0; i < num_bits; i++) {
					sum[i] = nf->CreateNode(bk, sum[i], y[i]);
				}
			}
			result = sum;
			break;
		}
		case SYMBOL:
		{
			assert(num_bits > 0);

			BBNodeVec bbvec;
			bbvec.reserve(num_bits);

			for (unsigned int i = 0; i < num_bits; i++) {
				BBNode bit_node = nf->CreateSymbol(term, i);
				bbvec.push_back(bit_node);
			}
			result = bbvec;
			break;
		}
		case BVCONST:
		{
			BBNodeVec tmp_res(num_bits);
			CBV bv = term.GetBVConst();
			for (unsigned int i = 0; i < num_bits; i++) {
				tmp_res[i] = CONSTANTBV::BitVector_bit_test(bv, i) ? nf->getTrue()
					: nf->getFalse();
			}
			result = tmp_res;
			break;
		}
		default:
			FatalError("BBTerm: Illegal kind to BBTerm", term);
		}

		assert(result.size() == term.GetValueWidth());

		if (debug_do_check)
			check(result, term);

		updateTerm(term, result, support);
		return (BBTermMemo[term] = result);
	}

	template <class BBNode, class BBNodeManagerT>
	const BBNode BitBlaster<BBNode, BBNodeManagerT>::BBForm(const ASTNode& form) {

		if (conjoin_to_top && cb != NULL) {
			ASTNodeMap n = cb->getAllFixed();
			for (ASTNodeMap::const_iterator it = n.begin(); it != n.end(); it++)
				fixedFromBottom.insert(it->first);

			// Mark the top node as true.
			cb->setNodeToTrue(form);
			cb->propagate();
		}

		BBNodeSet support;
		BBNode r = BBForm(form, support);

		vector<BBNode> v;
		v.insert(v.end(), support.begin(), support.end());
		v.push_back(r);

		if (!conjoin_to_top) {
			assert(support.size() == 0);
		}

		if (cb != NULL && !cb->isUnsatisfiable()) {
			ASTNodeSet visited;
			assert(cb->checkAtFixedPoint(form, visited));
		}
		if (v.size() == 1)
			return v[0];
		else
			return nf->CreateNode(AND, v);
	}

	// bit blast a formula (boolean term).  Result is one bit wide,
	template <class BBNode, class BBNodeManagerT>
	const BBNode BitBlaster<BBNode, BBNodeManagerT>::BBForm(const ASTNode& form,
		BBNodeSet& support) {
		typename std::map<ASTNode, BBNode>::iterator it = BBFormMemo.find(form);
		if (it != BBFormMemo.end()) {
			// already there.  Just return it.
			return it->second;
		}

		BBNode result;

		const Kind k = form.GetKind();
		if (!is_Form_kind(k)) {
			FatalError("BBForm: Illegal kind: ", form);
		}

		//  Not returning until end, and memoizing everything, makes it easier
		// to trace coherently.

		// Various special cases
		switch (k) {

		case TRUE:
		{
			result = nf->getTrue();
			break;
		}

		case FALSE:
		{
			result = nf->getFalse();
			break;
		}

		case SYMBOL:
			assert(form.GetType() == BOOLEAN_TYPE);

			result = nf->CreateSymbol(form, 0); // 1 bit symbol.
			break;

		case BOOLEXTRACT:
		{
			// exactly two children
			const BBNodeVec bbchild = BBTerm(form[0], support);
			unsigned int index = form[1].GetUnsignedConst();
			result = bbchild[index];
			break;
		}

		case NOT:
			result = nf->CreateNode(NOT, BBForm(form[0], support));
			break;

		case ITE:
			result =
				nf->CreateNode(ITE, BBForm(form[0], support),
					BBForm(form[1], support), BBForm(form[2], support));
			break;

		case AND:
		case OR:
		case NAND:
		case NOR:
		case IFF:
		case XOR:
		case IMPLIES:
		{
			BBNodeVec bbkids; // bit-blasted children (formulas)

			ASTVec::const_iterator kids_end = form.end();
			for (ASTVec::const_iterator it = form.begin(); it != kids_end; it++) {
				bbkids.push_back(BBForm(*it, support));
			}
			result = nf->CreateNode(k, bbkids);
			break;
		}

		case EQ:
		{
			const BBNodeVec left = BBTerm(form[0], support);
			const BBNodeVec right = BBTerm(form[1], support);
			assert(left.size() == right.size());

			result = BBEQ(left, right);
			break;
		}

		case BVLE:
		case BVGE:
		case BVGT:
		case BVLT:
		case BVSLE:
		case BVSGE:
		case BVSGT:
		case BVSLT:
		{
			result = BBcompare(form, support);
			break;
		}
		default:
			FatalError("BBForm: Illegal kind: ", form);
			break;
		}

		assert(!result.IsNull());

		if (debug_do_check)
			check(result, form);

		updateForm(form, result, support);

		return (BBFormMemo[form] = result);
	}

	// Bit blast a sum of two equal length BVs.
	// Update sum vector destructively with new sum.
	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::BBPlus2(BBNodeVec& sum,
		const BBNodeVec& y, BBNode cin) {

		const int bitWidth = sum.size();
		assert(y.size() == (unsigned)bitWidth);
		// Revision 320 avoided creating the nextcin, at I suspect unjustified cost.
		for (int i = 0; i < bitWidth; i++) {
			BBNode nextcin = Majority(sum[i], y[i], cin);
			sum[i] = nf->CreateNode(XOR, sum[i], y[i], cin);
			cin = nextcin;
		}
	}

	// Stores result - x in result, destructively
	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::BBSub(BBNodeVec& result,
		const BBNodeVec& y,
		BBNodeSet& /*support*/) {
		BBNodeVec compsubtrahend = BBNeg(y);
		BBPlus2(result, compsubtrahend, nf->getTrue());
	}

	// Add one bit
	template <class BBNode, class BBNodeManagerT>
	BBNodeVec BitBlaster<BBNode, BBNodeManagerT>::BBAddOneBit(const BBNodeVec& x,
		BBNode cin) {
		BBNodeVec result;
		result.reserve(x.size());
		const typename BBNodeVec::const_iterator itend = x.end();
		for (typename BBNodeVec::const_iterator it = x.begin(); it < itend; it++) {
			BBNode nextcin = nf->CreateNode(AND, *it, cin);
			result.push_back(nf->CreateNode(XOR, *it, cin));
			cin = nextcin;
		}
		return result;
	}

	// Increment bit-blasted vector and return result.
	template <class BBNode, class BBNodeManagerT>
	BBNodeVec BitBlaster<BBNode, BBNodeManagerT>::BBInc(const BBNodeVec& x) {
		return BBAddOneBit(x, nf->getTrue());
	}

	// Return formula for majority function of three bits.
	// Pass arguments by reference to reduce refcounting.
	template <class BBNode, class BBNodeManagerT>
	BBNode BitBlaster<BBNode, BBNodeManagerT>::Majority(const BBNode& a,
		const BBNode& b,
		const BBNode& c) {
		// Checking explicitly for constant a, b and c could
		// be more efficient, because they are repeated in the logic.
		if (nf->getTrue() == a) {
			return nf->CreateNode(OR, b, c);
		}
		else if (nf->getFalse() == a) {
			return nf->CreateNode(AND, b, c);
		}
		else if (nf->getTrue() == b) {
			return nf->CreateNode(OR, a, c);
		}
		else if (nf->getFalse() == b) {
			return nf->CreateNode(AND, a, c);
		}
		else if (nf->getTrue() == c) {
			return nf->CreateNode(OR, a, b);
		}
		else if (nf->getFalse() == c) {
			return nf->CreateNode(AND, a, b);
		}
		// there are lots more simplifications, but I'm not sure they're
		// worth doing explicitly (e.g., a = b, a = ~b, etc.)
		else {
			return nf->CreateNode(OR, nf->CreateNode(AND, a, b),
				nf->CreateNode(AND, b, c), nf->CreateNode(AND, a, c));
		}
	}

	// Bitwise complement
	template <class BBNode, class BBNodeManagerT>
	BBNodeVec BitBlaster<BBNode, BBNodeManagerT>::BBNeg(const BBNodeVec& x) {
		BBNodeVec result;
		result.reserve(x.size());
		// Negate each bit.
		const typename BBNodeVec::const_iterator& xend = x.end();
		for (typename BBNodeVec::const_iterator it = x.begin(); it < xend; it++) {
			result.push_back(nf->CreateNode(NOT, *it));
		}
		return result;
	}

	// Compute unary minus
	template <class BBNode, class BBNodeManagerT>
	BBNodeVec BitBlaster<BBNode, BBNodeManagerT>::BBUminus(const BBNodeVec& x) {
		BBNodeVec xneg = BBNeg(x);
		return BBInc(xneg);
	}

	// AND each bit of vector y with single bit b and return the result.
	template <class BBNode, class BBNodeManagerT>
	BBNodeVec BitBlaster<BBNode, BBNodeManagerT>::BBAndBit(const BBNodeVec& y,
		BBNode b) {
		if (nf->getTrue() == b) {
			return y;
		}

		BBNodeVec result;
		result.reserve(y.size());

		const typename BBNodeVec::const_iterator yend = y.end();
		for (typename BBNodeVec::const_iterator yit = y.begin(); yit < yend; yit++) {
			result.push_back(nf->CreateNode(AND, *yit, b));
		}
		return result;
	}

	typedef enum {
		SYMBOL_MT,
		ZERO_MT,
		ONE_MT,
		MINUS_ONE_MT
	} mult_type;

	void printP(mult_type* m, int width) {
		for (int i = width - 1; i >= 0; i--) {
			if (m[i] == SYMBOL_MT)
				cerr << "s";
			else if (m[i] == ZERO_MT)
				cerr << "0";
			else if (m[i] == ONE_MT)
				cerr << "1";
			else if (m[i] == MINUS_ONE_MT)
				cerr << "-1";
		}
	}

	template <class BBNode, class BBNodeManagerT>
	void convert(const BBNodeVec& v, BBNodeManagerT* nf, mult_type* result) {
		const BBNode& BBTrue = nf->getTrue();
		const BBNode& BBFalse = nf->getFalse();

		for (int i = 0; i < v.size(); i++) {
			if (v[i] == BBTrue)
				result[i] = ONE_MT;
			else if (v[i] == BBFalse)
				result[i] = ZERO_MT;
			else
				result[i] = SYMBOL_MT;
		}

		// find runs of ones.
		int lastOne = -1;
		for (int i = 0; i < v.size(); i++) {
			assert(result[i] != MINUS_ONE_MT);

			if (result[i] == ONE_MT && lastOne == -1)
				lastOne = i;

			if (result[i] != ONE_MT && lastOne != -1 && (i - lastOne >= 3)) {
				result[lastOne] = MINUS_ONE_MT;
				for (int j = lastOne + 1; j < i; j++)
					result[j] = ZERO_MT;
				// Should this be lastOne = i?
				lastOne = i;
				result[i] = ONE_MT;
			}
			else if (result[i] != ONE_MT)
				lastOne = -1;
		}

		// finished with a one.
		if (lastOne != -1 && (v.size() - lastOne > 1)) {
			result[lastOne] = MINUS_ONE_MT;
			for (int j = lastOne + 1; j < v.size(); j++)
				result[j] = ZERO_MT;
		}
	}

	// Multiply "multiplier" by y[start ... bitWidth].
	template <class BBNode, class BBNodeManagerT>
	void pushP(vector<vector<BBNode>>& products, const int start,
		const BBNodeVec& y, const BBNode& multiplier, BBNodeManagerT* nf) {
		const int bitWidth = y.size();

		int c = 0;
		for (int i = start; i < bitWidth; i++) {
			BBNode n = nf->CreateNode(AND, y[c], multiplier);
			if (n != nf->getFalse())
				products[i].push_back(n);
			c++;
		}
	}

	const bool debug_multiply = false;

	/* Cryptominisat2. 5641x5693.smt.   SAT Solving time only!
	 * adder_variant1 = true.    Solving: 12.3s, 12.1s
	 * adder_variant1 = false.   Solving: 26.5s, 26.0s
	 *
	 * Cryptominisat2. mult63bit.smt2.
	 * adder_variant1 = true.    Solving: 8.1s, 8.2s
	 * adder_variant1 = false.   Solving: 11.1s, 11.0s
	 *
	 * Cryptominisat2. conscram2.smt2.
	 * adder_variant1 = true.   Solving:115s, 103s, 303s
	 * adder_variant1 = false.  Solving:181s, 471s, 215s
	 * */

	template <class BBNode, class BBNodeManagerT>
	BBNodeVec BitBlaster<BBNode, BBNodeManagerT>::buildAdditionNetworkResult(
		vector<list<BBNode>>& products, set<BBNode>& support, const ASTNode& n) {
		const int bitWidth = n.GetValueWidth();

		// If we have details of the partial products which can be true,
		int ignore = -1;
		simplifier::constantBitP::MultiplicationStats* ms = getMS(n, ignore);
		if (!upper_multiplication_bound)
			ms = NULL;

		BBNodeVec results;
		for (int i = 0; i < bitWidth; i++) {

			buildAdditionNetworkResult(products[i], products[i + 1], support,
				(i + 1 == bitWidth),
				(ms != NULL && (ms->sumH[i] == 0)));

			assert(products[i].size() == 1);
			results.push_back(products[i].back());
		}

		assert(products[bitWidth].size() ==
			0); // products[bitwidth] is defined but should never be used.
		assert(results.size() == ((unsigned)bitWidth));
		return results;
	}

	// Use full adders to create an addition network that adds together each of the
	// partial products. Puts the carries into the "to" list.

	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::buildAdditionNetworkResult(
		list<BBNode>& from, list<BBNode>& to, set<BBNode>& support,
		const bool at_end, const bool all_false) {

		while (from.size() >= 2) {
			BBNode c;

			if (from.size() == 2)
				c = nf->getFalse();
			else {
				c = from.back();
				from.pop_back();
			}

			const BBNode a = from.back();
			from.pop_back();
			const BBNode b = from.back();
			from.pop_back();

			// Nothing can be true. All must be false.
			if (conjoin_to_top && all_false) {
				if (BBFalse != a)
					support.insert(nf->CreateNode(NOT, a));
				if (BBFalse != b)
					support.insert(nf->CreateNode(NOT, b));
				if (BBFalse != c)
					support.insert(nf->CreateNode(NOT, c));
				continue;
			}

			BBNode carry, sum;

			if (adder_variant) {
				carry = Majority(a, b, c);
				sum = nf->CreateNode(XOR, a, b, c);
			}
			else {
				carry =
					nf->CreateNode(OR, nf->CreateNode(AND, a, b),
						nf->CreateNode(AND, b, c), nf->CreateNode(AND, a, c));
				sum = nf->CreateNode(XOR, nf->CreateNode(XOR, c, b), a);
			}

			if (debug_multiply) {
				cerr << "a" << a;
				cerr << "b" << b;
				cerr << "c" << c;
				cerr << "Carry" << carry;
				cerr << "Sum" << sum;
			}

			from.push_back(sum);

			if (!at_end && carry != BBFalse)
				to.push_back(carry);
		}
		if (0 == from.size())
			from.push_back(BBFalse);

		assert(1 == from.size());
	}

	const bool debug_bounds = false;

	template <class BBNode, class BBNodeManagerT>
	bool BitBlaster<BBNode, BBNodeManagerT>::statsFound(const ASTNode& n) {
		if (NULL == cb)
			return false;

		if (NULL == cb->msm)
			return false;

		if (booth_recoded.find(n) !=
			booth_recoded.end()) // Sums are wrong for recoded.
			return false;

		simplifier::constantBitP::MultiplicationStatsMap::NodeToStats::const_iterator
			it;
		it = cb->msm->map.find(n);
		return (it != cb->msm->map.end());
	}

	// Make sure x and y are the parameters in the correct order. THIS ISNT
	// COMMUTATIVE.
	template <class BBNode, class BBNodeManagerT>
	BBNodeVec BitBlaster<BBNode, BBNodeManagerT>::multWithBounds(
		const ASTNode& n, vector<list<BBNode>>& products, BBNodeSet& toConjoinToTop) {
		const int bitWidth = n.GetValueWidth();

		int ignored = 0;
		assert(upper_multiplication_bound);
		simplifier::constantBitP::MultiplicationStats& ms = *getMS(n, ignored);

		// If all of the partial products in the column must be zero, then replace
		for (int i = 0; i < bitWidth; i++) {
			if (conjoin_to_top && ms.columnH[i] == 0) {
				while (products[i].size() > 0) {
					BBNode c = products[i].back(); // DONT take a reference of the back().
					products[i].pop_back();
					toConjoinToTop.insert(nf->CreateNode(NOT, c));
				}
				products[i].push_back(nf->getFalse());
			}
		}

		BBNodeVec result;

		if (debug_bounds) {
			ms.print();
		}

		vector<BBNode> prior;
		for (int i = 0; i < bitWidth; i++) {
			if (debug_bounds) {
				cerr << "  " << products[i].size();
				cerr << "[" << ms.columnL[i] << ":" << ms.columnH[i] << "][" << ms.sumL[i]
					<< ":" << ms.sumH[i] << "]";
			}

			vector<BBNode> output;

			mult_BubbleSorterWithBounds(toConjoinToTop, products[i], output, prior,
				ms.sumL[i], ms.sumH[i]);
			prior = output;

			assert(products[i].size() == 1);
			result.push_back(products[i].back());
		}

		if (debug_bitblaster)
			cerr << endl << endl;

		assert(result.size() == ((unsigned)bitWidth));
		return result;
	}

	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::mult_Booth(
		const BBNodeVec& x_i, const BBNodeVec& y_i, BBNodeSet& support,
		const ASTNode& xN, const ASTNode& yN, vector<list<BBNode>>& products,
		const ASTNode& n) {
		const int bitWidth = x_i.size();
		assert(x_i.size() == y_i.size());

		const BBNodeVec& x = x_i;
		const BBNodeVec& y = y_i;

		const BBNode& BBTrue = nf->getTrue();
		const BBNode& BBFalse = nf->getFalse();

		for (int i = 0; i < bitWidth; i++) {
			assert(products[i].size() == 0);
		}

		BBNodeVec notY;
		for (int i = 0; i < y.size(); i++) {
			notY.push_back(nf->CreateNode(NOT, y[i]));
		}

		mult_type* xt = (mult_type*)alloca(sizeof(mult_type) * x.size());
		convert(x, nf, xt);

		if (debug_multiply) {
			cerr << "--------" << endl;
			cerr << "x:";
			printP(xt, x.size());
			cerr << xN << endl;
		}

		mult_type* yt = (mult_type*)alloca(sizeof(mult_type) * x.size());
		convert(y, nf, yt);

		if (debug_multiply) {
			cerr << "y:";
			printP(yt, y.size());
			cerr << yN << endl;
		}

		// We store them into here before sorting them.
		vector<vector<BBNode>> t_products(bitWidth);

		for (int i = 0; i < bitWidth; i++) {
			if (x[i] != BBTrue && x[i] != BBFalse) {
				pushP(t_products, i, y, x[i], nf);
			}

			// A bit can not be true or false, as well as one of these two.
			if (xt[i] == MINUS_ONE_MT) {
				pushP(t_products, i, notY, BBTrue, nf);
				t_products[i].push_back(BBTrue);
				booth_recoded.insert(n);
			}

			else if (xt[i] == ONE_MT) {
				pushP(t_products, i, y, BBTrue, nf);
			}

			if (t_products[i].size() == 0)
				t_products[i].push_back(BBFalse);

			sort(t_products[i].begin(), t_products[i].end());
			for (int j = 0; j < t_products[i].size(); j++)
				products[i].push_back(t_products[i][j]);
		}
	}

	// Uses addition networks explicitly.
	// I've copied this in from my the "trevor" branch r482.
	// I've not measured if this is better than the current variant.
	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::mult_allPairs(
		const BBNodeVec& x, const BBNodeVec& y, BBNodeSet& support,
		vector<list<BBNode>>& products) {
		// Make a table of partial products.
		const int bitWidth = x.size();
		assert(x.size() == y.size());
		assert(bitWidth > 0);

		for (int i = 0; i < bitWidth; i++) {
			assert(!x[i].IsNull());
			assert(!y[i].IsNull());
		}

		for (int i = 0; i < bitWidth; i++) {
			for (int j = 0; j <= i; j++) {
				BBNode n = nf->CreateNode(AND, x[i - j], y[j]);

				if (n != nf->getFalse())
					products[i].push_back(n);
			}

			if (0 == products[i].size())
				products[i].push_back(nf->getFalse());
		}
	}

	template <class BBNode, class BBNodeManagerT>
	MultiplicationStats* BitBlaster<BBNode, BBNodeManagerT>::getMS(const ASTNode& n,
		int& highestZero) {
		MultiplicationStats* ms = NULL;
		highestZero = -1;

		if (statsFound(n)) {
			simplifier::constantBitP::MultiplicationStatsMap::NodeToStats::iterator it;
			it = cb->msm->map.find(n);
			if (it != cb->msm->map.end()) {
				ms = &(it->second);

				assert(ms->x.getWidth() == ms->y.getWidth());
				assert(ms->r.getWidth() == ms->y.getWidth());
				assert(ms->r.getWidth() == (int)ms->bitWidth);
			}

			for (int i = 0; i < n.GetValueWidth(); i++)
				if (ms->sumH[i] == 0)
					highestZero = i;

			return ms;
		}

		return NULL;
	}

	// Each bit of 'x' is taken in turn and multiplied by a shifted y.
	template <class BBNode, class BBNodeManagerT>
	BBNodeVec BitBlaster<BBNode, BBNodeManagerT>::mult_normal(const BBNodeVec& x,
		const BBNodeVec& y,
		BBNodeSet& support,
		const ASTNode& n) {
		const int bitWidth = n.GetValueWidth();

		// If we have details of the partial products which can be true,
		int highestZero = -1;
		const simplifier::constantBitP::MultiplicationStats* ms =
			getMS(n, highestZero);
		if (!upper_multiplication_bound)
			ms = NULL;

		BBNodeVec ycopy(y);

		BBNodeVec prod = BBNodeVec(
			BBAndBit(y, *x.begin())); // start prod with first partial product.

		for (int i = 1; i < bitWidth; i++) // start loop at next bit.
		{
			const BBNode& xit = x[i];

			// shift first
			BBLShift(ycopy, 1);

			if (nf->getFalse() == xit) {
				// If this bit is zero, the partial product will
				// be zero.  No reason to add that in.
				continue;
			}

			BBNodeVec pprod = BBAndBit(ycopy, xit);

			// Iterate through from the current location upwards, setting anything to
			// zero that can be..
			if (ms != NULL && highestZero >= i) {
				for (int column = i; column <= highestZero; column++) {
					if (ms->sumH[column] == 0 && (nf->getFalse() != prod[column])) {
						support.insert(nf->CreateNode(NOT, prod[column]));
						prod[column] = BBFalse;
					}
				}
			}

			BBPlus2(prod, pprod, nf->getFalse());
		}
		return prod;
	}

	// assumes the prior column is sorted.
	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::mult_BubbleSorterWithBounds(
		BBNodeSet& support, list<BBNode>& current, vector<BBNode>& currentSorted,
		vector<BBNode>& priorSorted, const int minTrue, const int maxTrue) {

		// Add the carry from the prior column. i.e. each second sorted formula.
		for (int k = 1; k < priorSorted.size(); k += 2) {
			current.push_back(priorSorted[k]);
		}

		const int height = current.size();

		// Set the current sorted to all false.
		currentSorted.clear();
		{
			vector<BBNode> temp(height, nf->getFalse());
			currentSorted = temp;
		}

		// n^2 sorting network.
		for (int l = 0; l < height; l++) {
			vector<BBNode> oldSorted(currentSorted);
			BBNode c = current.back();
			current.pop_back();
			currentSorted[0] = nf->CreateNode(OR, oldSorted[0], c);

			for (int j = 1; j <= l; j++) {
				currentSorted[j] = nf->CreateNode(
					OR, nf->CreateNode(AND, oldSorted[j - 1], c), oldSorted[j]);
			}
		}

		assert(current.size() == 0);

		for (int k = 0; k < height; k++)
			assert(!currentSorted[k].IsNull());

		if (conjoin_to_top) {
			for (int j = 0; j < minTrue; j++) {
				support.insert(currentSorted[j]);
				currentSorted[j] = BBTrue;
			}

			for (int j = height - 1; j >= maxTrue; j--) {
				support.insert(nf->CreateNode(NOT, currentSorted[j]));
				currentSorted[j] = BBFalse;
			}
		}

		BBNode resultNode = nf->getFalse();

		// Constrain to equal the result
		for (int k = 1; k < height; k += 2) {
			BBNode part = nf->CreateNode(AND, nf->CreateNode(NOT, currentSorted[k]),
				currentSorted[k - 1]);
			resultNode = nf->CreateNode(OR, resultNode, part);
		}

		// constraint the all '1's case.
		if (height % 2 == 1)
			resultNode = nf->CreateNode(OR, resultNode, currentSorted.at(height - 1));

		current.push_back(resultNode);
	}

	// If a bit has a fixed value, then it should equal BBTrue or BBFalse in the
	// input vectors.
	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::checkFixed(const BBNodeVec& v,
		const ASTNode& n) {
		if (cb == NULL) {
			return;
		}

		if (cb->isUnsatisfiable()) {
			return;
		}

		if (cb->fixedMap->map->find(n) != cb->fixedMap->map->end()) {
			FixedBits* b = cb->fixedMap->map->find(n)->second;
			for (int i = 0; i < b->getWidth(); i++) {
				if (b->isFixed(i)) {
					if (b->getValue(i)) {
						assert(v[i] == BBTrue);
					}
					else {
						if (v[i] != BBFalse) {
							cerr << *b;
							cerr << i << endl;
							cerr << n;
							cerr << (v[i] == BBTrue) << endl;
						}

						assert(v[i] == BBFalse);
					}
				}
			}
		}
	}

	// If it's not booth encoded, and the column sum is zero,
	// then set that all the partial products must be zero.
	// For this to do anything constant bit propagation must be
	// turned on, and upper_multiplication_bound must be set.
	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::setColumnsToZero(
		vector<list<BBNode>>& products, set<BBNode>& support, const ASTNode& n) {
		const int bitWidth = n.GetValueWidth();

		// If we have details of the partial products which can be true,
		int highestZero = -1;
		simplifier::constantBitP::MultiplicationStats* ms = getMS(n, highestZero);
		if (!upper_multiplication_bound)
			ms = NULL;

		if (ms == NULL)
			return;

		for (int i = 0; i < bitWidth; i++) {
			if (ms->sumH[i] == 0) {
				while (products[i].size() > 0) {
					BBNode curr = products[i].back();
					products[i].pop_back();

					if (BBFalse == curr)
						continue;

					support.insert(nf->CreateNode(NOT, curr));
				}
				products[i].push_back(BBFalse);
			}
		}
	}

	// Multiply two bitblasted numbers
	template <class BBNode, class BBNodeManagerT>
	BBNodeVec BitBlaster<BBNode, BBNodeManagerT>::BBMult(const BBNodeVec& _x,
		const BBNodeVec& _y,
		BBNodeSet& support,
		const ASTNode& n) {

		if (uf->isSet("print_on_mult", "0"))
			cerr << "--mult--";

		BBNodeVec x = _x;
		BBNodeVec y = _y;

		if ((BVCONST != n[0].GetKind()) && (BVCONST == n[1].GetKind())) {
			x = _y;
			y = _x;
		}

		const int bitWidth = n.GetValueWidth();
		assert(x.size() == bitWidth);
		assert(y.size() == bitWidth);

		vector<list<BBNode>> products(
			bitWidth + 1); // Create one extra to avoid special cases.

		if (multiplication_variant == "1") {
			return mult_normal(x, y, support, n);
		}
		// else if (multiplication_variant == "2")
		// V2 used to be V3 with normal rather than booth recoding.
		// To recreate V2, use V3 and turn off Booth recoding.
		else if (multiplication_variant == "3") {
			mult_Booth(_x, _y, support, n[0], n[1], products, n);
			setColumnsToZero(products, support, n);
			return buildAdditionNetworkResult(products, support, n);
		}
		else if (multiplication_variant == "4") {
			// cerr << "v4";
			mult_Booth(_x, _y, support, n[0], n[1], products, n);
			vector<BBNode> prior;

			for (int i = 0; i < bitWidth; i++) {
				vector<BBNode> output;
				mult_BubbleSorterWithBounds(support, products[i], output, prior);
				prior = output;
				assert(products[i].size() == 1);
			}
			return buildAdditionNetworkResult(products, support, n);
		}
		else if (multiplication_variant == "5") {
			if (!statsFound(n) || !upper_multiplication_bound) {
				mult_Booth(_x, _y, support, n[0], n[1], products, n);
				setColumnsToZero(products, support, n);
				return buildAdditionNetworkResult(products, support, n);
			}

			mult_allPairs(x, y, support, products);
			setColumnsToZero(products, support, n);
			return multWithBounds(n, products, support);
		}
		else if (multiplication_variant == "6") {
			mult_Booth(_x, _y, support, n[0], n[1], products, n);
			setColumnsToZero(products, support, n);
			return v6(products, support, n);
		}
		else if (multiplication_variant == "7") {
			mult_Booth(_x, _y, support, n[0], n[1], products, n);
			setColumnsToZero(products, support, n);
			return v7(products, support, n);
		}
		else if (multiplication_variant == "8") {
			mult_Booth(_x, _y, support, n[0], n[1], products, n);
			setColumnsToZero(products, support, n);
			return v8(products, support, n);
		}
		else if (multiplication_variant == "9") {
			mult_Booth(_x, _y, support, n[0], n[1], products, n);
			setColumnsToZero(products, support, n);
			return v9(products, support, n);
		}
		else if (multiplication_variant == "13") {
			mult_Booth(_x, _y, support, n[0], n[1], products, n);
			setColumnsToZero(products, support, n);
			return v13(products, support, n);
		}
		else {
			cerr << "Unk variant" << multiplication_variant;
			FatalError("sda44f");
		}
	}

	// Takes an unsorted array, and returns a sorted array.
	template <class BBNode, class BBNodeManagerT>
	BBNodeVec BitBlaster<BBNode, BBNodeManagerT>::batcher(const vector<BBNode>& in) {
		assert(in.size() != 0);

		if (in.size() == 1)
			return in;

		vector<BBNode> a;
		vector<BBNode> b;

		// half way rounded up.
		const int halfWay = (((in.size() % 2) == 0 ? 0 : 1) + (in.size() / 2));
		for (int i = 0; i < halfWay; i++)
			a.push_back(in[i]);

		for (int i = halfWay; i < in.size(); i++)
			b.push_back(in[i]);

		assert(a.size() >= b.size());
		assert(a.size() + b.size() == in.size());
		vector<BBNode> result = mergeSorted(batcher(a), batcher(b));

		for (int k = 0; k < result.size(); k++)
			assert(!result[k].IsNull());

		assert(result.size() == in.size());
		return result;
	}

	// assumes that the prior column is sorted.
	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::sortingNetworkAdd(
		BBNodeSet& support, list<BBNode>& current, vector<BBNode>& currentSorted,
		vector<BBNode>& priorSorted) {

		vector<BBNode> toSort;

		// convert the list to a vector.
		while (current.size() != 0) {
			BBNode currentN = current.front();
			assert(!currentN.IsNull());
			toSort.push_back(currentN);
			current.pop_front();
		}

		vector<BBNode> sorted = batcher(toSort);

		assert(sorted.size() == toSort.size());

		vector<BBNode> sortedCarryIn;
		for (int k = 1; k < priorSorted.size(); k += 2) {
			sortedCarryIn.push_back(priorSorted[k]);
		}

		if (sorted.size() >= sortedCarryIn.size())
			currentSorted = mergeSorted(sorted, sortedCarryIn);
		else
			currentSorted = mergeSorted(sortedCarryIn, sorted);

		assert(currentSorted.size() == sortedCarryIn.size() + toSort.size());
		int height = currentSorted.size();

		assert(current.size() == 0);

		for (int k = 0; k < height; k++)
			assert(!currentSorted[k].IsNull());

		BBNode resultNode = nf->getFalse();

		// Constrain to equal the result
		for (int k = 1; k < height; k += 2) {
			BBNode part = nf->CreateNode(AND, nf->CreateNode(NOT, currentSorted[k]),
				currentSorted[k - 1]);
			resultNode = nf->CreateNode(OR, resultNode, part);
		}

		// constraint the all '1's case.
		if (height % 2 == 1)
			resultNode = nf->CreateNode(OR, resultNode, currentSorted.at(height - 1));

		current.push_back(resultNode);
	}

	template <class BBNode, class BBNodeManagerT>
	BBNodeVec BitBlaster<BBNode, BBNodeManagerT>::v6(vector<list<BBNode>>& products,
		set<BBNode>& support,
		const ASTNode& n) {
		const int bitWidth = n.GetValueWidth();

		vector<BBNode> prior;

		for (int i = 0; i < bitWidth; i++) {
			vector<BBNode> output;
			sortingNetworkAdd(support, products[i], output, prior);
			prior = output;
			assert(products[i].size() == 1);
		}

		// This converts the array of lists to a vector.
		return buildAdditionNetworkResult(products, support, n);
	}

	template <class BBNode, class BBNodeManagerT>
	BBNodeVec
		BitBlaster<BBNode, BBNodeManagerT>::v13(vector<list<BBNode>>& products,
			set<BBNode>& support, const ASTNode& n) {
		const int bitWidth = n.GetValueWidth();

		int ignore = -1;
		simplifier::constantBitP::MultiplicationStats* ms = getMS(n, ignore);
		if (!upper_multiplication_bound)
			ms = NULL;

		bool done = false;

		vector<BBNode> a(bitWidth);
		vector<BBNode> b(bitWidth);

		while (!done) {
			done = true;

			for (int i = 0; i < bitWidth; i++) {
				if (products[i].size() > 2)
					done = false;
				if (products[i].size() > 0) {
					a[i] = products[i].back();
					products[i].pop_back();
				}
				else
					a[i] = BBFalse;

				if (products[i].size() > 0) {
					b[i] = products[i].back();
					products[i].pop_back();
				}
				else
					b[i] = BBFalse;

				if (ms != NULL && ms->sumH[i] == 0) {
					if (a[i] != BBFalse) {
						support.insert(nf->CreateNode(NOT, a[i]));
						a[i] = BBFalse;
					}

					if (b[i] != BBFalse) {
						support.insert(nf->CreateNode(NOT, b[i]));
						b[i] = BBFalse;
					}
				}
				assert(!a[i].IsNull());
				assert(!b[i].IsNull());
			}
			BBPlus2(a, b, BBFalse);
			for (int i = 0; i < bitWidth; i++)
				products[i].push_back(a[i]);
		}

		BBNodeVec results;
		for (int i = 0; i < bitWidth; i++) {
			assert(products[i].size() == 1);
			results.push_back(products[i].back());
		}

		assert(results.size() == ((unsigned)bitWidth));
		return results;
	}

	// Sorting network that delivers carries directly to the correct column.
	// For instance, if there are 6 true in a column, then a carry will flow to
	// column+1, and column+2.
	template <class BBNode, class BBNodeManagerT>
	BBNodeVec BitBlaster<BBNode, BBNodeManagerT>::v9(vector<list<BBNode>>& products,
		set<BBNode>& support,
		const ASTNode& n) {
		const int bitWidth = n.GetValueWidth();

		vector<vector<BBNode>> toAdd(bitWidth);

		for (int column = 0; column < bitWidth; column++) {
			vector<BBNode> sorted; // The current column (sorted) gets put into here.
			vector<BBNode> prior;  // Prior is always empty in this..

			const int size = products[column].size();
			sortingNetworkAdd(support, products[column], sorted, prior);

			assert(products[column].size() == 1);
			assert(sorted.size() == size);

			for (int k = 2; k <= sorted.size(); k++) {
				BBNode part;
				if (k == sorted.size())
					part = sorted[k - 1];
				else {
					// We expect the 1's to be sorted first.
					assert((sorted[k - 1] != BBFalse) || (sorted[k] != BBTrue));
					part =
						nf->CreateNode(AND, nf->CreateNode(NOT, sorted[k]), sorted[k - 1]);

					if (part == BBFalse)
						continue; // shortcut.
				}

				int position = k;
				int increment = 1;
				while (position != 0) {
					if (column + increment >= bitWidth)
						break;

					position >>= 1;
					if ((position & 1) != 0) // bit is set.
						toAdd[column + increment].push_back(part);

					increment++;
				}
			}

			for (int carry_column = column + 1; carry_column < bitWidth; carry_column++) {
				if (toAdd[carry_column].size() == 0)
					continue;
				BBNode disjunct = BBFalse;
				for (int l = 0; l < toAdd[carry_column].size(); l++) {
					disjunct = nf->CreateNode(OR, disjunct, toAdd[carry_column][l]);
				}

				if (disjunct != BBFalse)
					products[carry_column].push_back(disjunct);
				toAdd[carry_column].clear();
			}
		}
		for (int i = 0; i < bitWidth; i++) {
			assert(toAdd[i].size() == 0);
		}

		// This converts the array of lists to a vector.
		return buildAdditionNetworkResult(products, support, n);
	}

	template <class BBNode, class BBNodeManagerT>
	BBNodeVec BitBlaster<BBNode, BBNodeManagerT>::v7(vector<list<BBNode>>& products,
		set<BBNode>& support,
		const ASTNode& n) {
		const int bitWidth = n.GetValueWidth();

		// If we have details of the partial products which can be true,
		int ignore = -1;
		simplifier::constantBitP::MultiplicationStats* ms = getMS(n, ignore);
		if (!upper_multiplication_bound)
			ms = NULL;

		vector<list<BBNode>> later(bitWidth + 1);
		vector<list<BBNode>> next(bitWidth + 1);

		for (int i = 0; i < bitWidth; i++) {
			next[i + 1].clear();
			buildAdditionNetworkResult(products[i], next[i + 1], support,
				bitWidth == i + 1,
				(ms != NULL && (ms->sumH[i] == 0)));

			// Calculate the carries of carries.
			for (int j = i + 1; j < bitWidth; j++) {
				if (next[j].size() == 0)
					break;

				next[j + 1].clear();
				buildAdditionNetworkResult(next[j], next[j + 1], support,
					bitWidth == j + 1, false);
			}

			// Put the carries of the carries away until later.
			for (int j = i + 1; j < bitWidth; j++) {
				if (next[j].size() == 0)
					break;

				assert(next[j].size() <= 1);
				later[j].push_back(next[j].back());
			}
		}

		for (int i = 0; i < bitWidth; i++) {
			// Copy all the laters into products
			while (later[i].size() > 0) {
				products[i].push_front(later[i].front());
				later[i].pop_front();
			}
		}

		BBNodeVec results;
		for (int i = 0; i < bitWidth; i++) {

			buildAdditionNetworkResult((products[i]), (products[i + 1]), support,
				bitWidth == i + 1, false);

			results.push_back(products[i].back());
			products[i].pop_back();
		}

		assert(results.size() == ((unsigned)bitWidth));
		return results;
	}

	template <class BBNode, class BBNodeManagerT>
	BBNodeVec BitBlaster<BBNode, BBNodeManagerT>::v8(vector<list<BBNode>>& products,
		set<BBNode>& support,
		const ASTNode& n) {
		const int bitWidth = n.GetValueWidth();

		// If we have details of the partial products which can be true,
		int ignore = -1;
		simplifier::constantBitP::MultiplicationStats* ms = getMS(n, ignore);
		if (!upper_multiplication_bound)
			ms = NULL;

		vector<list<BBNode>> later(bitWidth + 1); // +1 then ignore the topmost.
		vector<list<BBNode>> next(bitWidth + 1);

		for (int i = 0; i < bitWidth; i++) {
			// Put all the products into next.
			next[i + 1].clear();
			buildAdditionNetworkResult((products[i]), (next[i + 1]), support,
				i + 1 == bitWidth,
				(ms != NULL && (ms->sumH[i] == 0)));

			// Calculate the carries of carries.
			for (int j = i + 1; j < bitWidth; j++) {
				if (next[j].size() == 0)
					break;

				next[j + 1].clear();
				buildAdditionNetworkResult(next[j], next[j + 1], support,
					j + 1 == bitWidth, false);
			}

			// Put the carries of the carries away until later.
			for (int j = i + 1; j < bitWidth; j++) {
				if (next[j].size() == 0)
					break;

				assert(next[j].size() <= 1);
				later[j].push_back(next[j].back());
			}
		}

		for (int i = 0; i < bitWidth; i++) {
			// Copy all the laters into products
			while (later[i].size() > 0) {
				products[i].push_back(later[i].back());
				later[i].pop_back();
			}
		}

		BBNodeVec results;
		for (int i = 0; i < bitWidth; i++) {
			buildAdditionNetworkResult(products[i], products[i + 1], support,
				i + 1 == bitWidth, false);
			results.push_back(products[i].back());
			products[i].pop_back();
		}

		assert(results.size() == ((unsigned)bitWidth));
		return results;
	}

	// compare element 1 with 2, 3 with 4, and so on.
	template <class BBNode, class BBNodeManagerT>
	vector<BBNode>
		BitBlaster<BBNode, BBNodeManagerT>::compareOddEven(const vector<BBNode>& in) {
		vector<BBNode> result(in);

		for (int i = 2; i < in.size(); i = i + 2) {
			BBNode a = in[i - 1];
			BBNode b = in[i];
			// comparators++;
			result[i - 1] = nf->CreateNode(OR, a, b);
			result[i] = nf->CreateNode(AND, a, b);
		}
		return result;
	}

	template <class BBNode, class BBNodeManagerT>
	vector<BBNode>
		BitBlaster<BBNode, BBNodeManagerT>::mergeSorted(const vector<BBNode>& in1,
			const vector<BBNode>& in2) {

		assert(in1.size() >= in2.size());
		assert(in1.size() > 0);

		vector<BBNode> result;

		if (in2.size() == 0) {
			result = in1;
		}
		else if (in1.size() == 1 && in2.size() == 1) {
			// comparators++;
			result.push_back(nf->CreateNode(OR, in1[0], in2[0]));
			result.push_back(nf->CreateNode(AND, in1[0], in2[0]));
		}
		else {
			vector<BBNode> evenL;
			vector<BBNode> oddL;
			for (int i = 0; i < in1.size(); i++) {
				if (i % 2 == 0)
					evenL.push_back(in1[i]);
				else
					oddL.push_back(in1[i]);
			}

			vector<BBNode> evenR; // Take the even of each.
			vector<BBNode> oddR;  // Take the odd of each
			for (int i = 0; i < in2.size(); i++) {
				if (i % 2 == 0)
					evenR.push_back(in2[i]);
				else
					oddR.push_back(in2[i]);
			}

			vector<BBNode> even = evenL.size() < evenR.size()
				? mergeSorted(evenR, evenL)
				: mergeSorted(evenL, evenR);
			vector<BBNode> odd = oddL.size() < oddR.size() ? mergeSorted(oddR, oddL)
				: mergeSorted(oddL, oddR);

			for (int i = 0; i < std::max(even.size(), odd.size()); i++) {
				if (even.size() > i)
					result.push_back(even[i]);

				if (odd.size() > i)
					result.push_back(odd[i]);
			}
			result = compareOddEven(result);
		}

		assert(result.size() == in1.size() + in2.size());
		return result;
	}

	// All combinations of division_variant_1, _2, _3
	/* on factoring12bitsx12.cvc with MINISAT2.
  000:    0m2.764s
  001:    0m4.060s
  010:    0m2.750s
  011:    0m4.173s
  100:    0m3.064s
  101:    0m3.217s
  110:    0m3.064s
  111:    0m3.230s
	 */

	 // This implements a variant of binary long division.
	 // q and r are "out" parameters.  rwidth puts a bound on the
	 // recursion depth.
	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::BBDivMod(const BBNodeVec& y,
		const BBNodeVec& x,
		BBNodeVec& q, BBNodeVec& r,
		unsigned int rwidth,
		BBNodeSet& support) {
		const unsigned int width = y.size();
		const BBNodeVec zero = BBfill(width, nf->getFalse());
		BBNodeVec one = zero;
		one[0] = nf->getTrue();

		// check if y is already zero.
		bool isZero = true;
		for (int i = 0; i < rwidth; i++)
			if (y[i] != nf->getFalse()) {
				isZero = false;
				break;
			}

		if (isZero || rwidth == 0) {
			// When we have shifted the entire width, y is guaranteed to be 0.
			q = zero;
			r = zero;
		}
		else {
			BBNodeVec q1, r1;
			BBNodeVec yrshift1(y);
			BBRShift(yrshift1, 1);

			// recursively divide y/2 by x.
			BBDivMod(yrshift1, x, q1, r1, rwidth - 1, support);

			BBNodeVec q1lshift1(q1);
			BBLShift(q1lshift1, 1);

			BBNodeVec r1lshift1(r1);
			BBLShift(r1lshift1, 1);

			BBNodeVec r1lshift1plusyodd(r1lshift1);
			r1lshift1plusyodd[0] = y[0];

			// By extending rminusx by one bit, we can use that top-bit
			// to check whether r>=x. We need to compute rminusx anyway,
			// so this saves having a separate compare circut.
			BBNodeVec rminusx(r1lshift1plusyodd);
			rminusx.push_back(nf->getFalse());
			BBNodeVec xCopy(x);
			xCopy.push_back(nf->getFalse());
			BBSub(rminusx, xCopy, support);
			BBNode sign = rminusx[width];
			rminusx.pop_back();

			// Adjusted q, r values when when r is too large.
			// q1lshift1 has zero in the least significant digit.
			// BBNodeVec ygtrxqval = BBITE(sign, q1lshift1, BBInc(q1lshift1));
			q1lshift1[0] = nf->CreateNode(NOT, sign);
			BBNodeVec ygtrxrval = BBITE(sign, r1lshift1plusyodd, rminusx);

			BBNodeVec notylessxqval;
			BBNodeVec notylessxrval;

			/* variant_1 removes the equality check of (x=y). When we get to here I
			   think
			   that r and q already have the proper values.
			   Let x =y, so we are solving y/y.
			   As a first step solve (y/2)/y.
			   If y != 0, then y/2 < y. (strictly less than).
			   By the last rule in this block, that will return q=0, r=(y/2)
			   On return, that will be rightshifted, and the parity bit added back,
			   giving q = 0, r=y.
			   By the immediately preceeding rule, 0 <= 0 is true, so q becomes 1,
			   and r becomes 0.
			   So q and r are already set correctly when we get here.

			   If y=0 & x=0, then (y/2)/0 will return q=0, r=0.
			   By the preceeding rule  0 <= 0 is true, so q =1, r=0.
			   So q and r are already set correctly when we get here.
			 */

			if (division_variant_1) {
				notylessxqval = q1lshift1;
				notylessxrval = ygtrxrval;
			}
			else {
				// q & r values when y >= x
				BBNode yeqx = BBEQ(y, x);
				// *** Problem: the bbfill for qval is wrong.  Should be 1, not -1.
				notylessxqval = BBITE(yeqx, one, q1lshift1);
				notylessxrval = BBITE(yeqx, zero, ygtrxrval);
			}

			/****************/
			BBNode ylessx;
			if (division_variant_2) {
				ylessx = BBBVLE(y, x, false, true);
			}
			else {
				// y < x <=> not x >= y.
				ylessx = nf->CreateNode(NOT, BBBVLE(x, y, false));
			}

			if (division_variant_3) {
				q = notylessxqval;
				r = notylessxrval;
			}
			else {
				// This variant often helps somehow. I don't know why.
				// Even though it uses more memory..
				q = BBITE(ylessx, zero, notylessxqval);
				r = BBITE(ylessx, y, notylessxrval);
			}
		}
	}

	// build ITE's (ITE cond then[i] else[i]) for each i.
	template <class BBNode, class BBNodeManagerT>
	BBNodeVec BitBlaster<BBNode, BBNodeManagerT>::BBITE(const BBNode& cond,
		const BBNodeVec& thn,
		const BBNodeVec& els) {
		// Fast exits.
		if (cond == nf->getTrue()) {
			return thn;
		}
		else if (cond == nf->getFalse()) {
			return els;
		}

		BBNodeVec result;
		result.reserve(els.size());
		const typename BBNodeVec::const_iterator th_it_end = thn.end();
		typename BBNodeVec::const_iterator el_it = els.begin();
		for (typename BBNodeVec::const_iterator th_it = thn.begin();
			th_it < th_it_end; th_it++, el_it++) {
			result.push_back(nf->CreateNode(ITE, cond, *th_it, *el_it));
		}
		return result;
	}

	//  smt-test/transitive400.smt2
	// Minisat 2:  bbbvle_variant = true. 8 ms
	// Minisat 2:  bbbvle_variant = false. 577 ms

	// Workhorse for comparison routines.  This does a signed BVLE if is_signed
	// is true, else it's unsigned.  All other comparison operators can be reduced
	// to this by swapping args or complementing the result bit.
	template <class BBNode, class BBNodeManagerT>
	BBNode BitBlaster<BBNode, BBNodeManagerT>::BBBVLE(const BBNodeVec& left,
		const BBNodeVec& right,
		bool is_signed, bool is_bvlt) {
		if (bbbvle_variant)
			return BBBVLE_variant1(left, right, is_signed, is_bvlt);
		else
			return BBBVLE_variant2(left, right, is_signed, is_bvlt);
	}

	template <class BBNode, class BBNodeManagerT>
	BBNode BitBlaster<BBNode, BBNodeManagerT>::BBBVLE_variant1(
		const BBNodeVec& left_, const BBNodeVec& right_, bool is_signed,
		bool is_bvlt) {
		const BBNodeVec& left = !is_bvlt ? left_ : right_;
		const BBNodeVec& right = !is_bvlt ? right_ : left_;

		// "thisbit" represents BVLE of the suffixes of the BVs
		// from that position .  if R < L, return TRUE, else if L < R
		// return FALSE, else return BVLE of lower-order bits.  MSB is
		// treated separately, because signed comparison is done by
		// complementing the MSB of each BV, then doing an unsigned
		// comparison.
		typename BBNodeVec::const_iterator lit = left.begin();
		typename BBNodeVec::const_iterator litend = left.end();
		typename BBNodeVec::const_iterator rit = right.begin();
		BBNode prevbit = nf->getTrue();
		for (; lit < litend - 1; lit++, rit++) {
			BBNode thisbit =
				nf->CreateNode(ITE, nf->CreateNode(IFF, *rit, *lit), prevbit, *rit);
			prevbit = thisbit;
		}

		// Handle MSB -- negate MSBs if signed comparison
		BBNode lmsb = *lit;
		BBNode rmsb = *rit;
		if (is_signed) {
			lmsb = nf->CreateNode(NOT, *lit);
			rmsb = nf->CreateNode(NOT, *rit);
		}

		BBNode msb =
			nf->CreateNode(ITE, nf->CreateNode(IFF, rmsb, lmsb), prevbit, rmsb);

		if (is_bvlt) {
			msb = nf->CreateNode(NOT, msb);
		}
		return msb;
	}

	template <class BBNode, class BBNodeManagerT>
	BBNode BitBlaster<BBNode, BBNodeManagerT>::BBBVLE_variant2(
		const BBNodeVec& left, const BBNodeVec& right, bool is_signed, bool is_bvlt) {
		typename BBNodeVec::const_reverse_iterator lit = left.rbegin();
		const typename BBNodeVec::const_reverse_iterator litend = left.rend();
		typename BBNodeVec::const_reverse_iterator rit = right.rbegin();

		BBNode this_compare_bit =
			is_signed ? nf->CreateNode(AND, *lit, nf->CreateNode(NOT, *rit))
			: nf->CreateNode(AND, nf->CreateNode(NOT, *lit), *rit);

		BBNodeVec bit_comparisons;
		bit_comparisons.reserve(left.size() + 1);

		bit_comparisons.push_back(this_compare_bit);

		//(lit IFF rit) is the same as (NOT(lit) XOR rit)
		BBNode prev_eq_bit = nf->CreateNode(XOR, nf->CreateNode(NOT, *lit), *rit);
		for (lit++, rit++; lit < litend; lit++, rit++) {
			this_compare_bit = nf->CreateNode(AND, nf->CreateNode(NOT, *lit), *rit);

			BBNode thisbit_output = nf->CreateNode(AND, this_compare_bit, prev_eq_bit);
			bit_comparisons.push_back(thisbit_output);

			BBNode this_eq_bit = nf->CreateNode(
				AND, nf->CreateNode(XOR, nf->CreateNode(NOT, *lit), *rit), prev_eq_bit);
			prev_eq_bit = this_eq_bit;
		}

		if (!is_bvlt) {
			bit_comparisons.push_back(prev_eq_bit);
		}

		// Either zero or one of the nodes in bit_comparisons can be true.

		BBNode output;
		output = nf->CreateNode(OR, bit_comparisons);
		return output;
	}

	// Left shift  within fixed field inserting zeros at LSB.
	// Writes result into first argument.
	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::BBLShift(BBNodeVec& x,
		unsigned int shift) {
		// left shift x (destructively) within width.
		// loop backwards so that copy to self works correctly. (DON'T use STL
		// insert!)
		for (int i = ((int)x.size()) - 1; i >= 0; i--) {
			if (i - (int)shift >= 0)
				x[i] = x[i - (int)shift];
			else
				x[i] = nf->getFalse(); // new LSB is zero.
		}
	}

	// Right shift within fixed field inserting zeros at MSB.
	// Writes result into first argument.
	template <class BBNode, class BBNodeManagerT>
	void BitBlaster<BBNode, BBNodeManagerT>::BBRShift(BBNodeVec& x,
		unsigned int shift) {
		// right shift x (destructively) within width.
		const typename BBNodeVec::iterator xend = x.end();
		typename BBNodeVec::iterator xit = x.begin();
		for (; xit < xend; xit++) {
			if (xit + shift < xend)
				*xit = *(xit + shift);
			else
				*xit = nf->getFalse(); // new MSB is zero.
		}
	}

	// Return bit-blasted form for BVLE, BVGE, BVGT, SBLE, etc.
	template <class BBNode, class BBNodeManagerT>
	BBNode BitBlaster<BBNode, BBNodeManagerT>::BBcompare(const ASTNode& form,
		BBNodeSet& support) {
		const BBNodeVec& left = BBTerm(form[0], support);
		const BBNodeVec& right = BBTerm(form[1], support);

		const Kind k = form.GetKind();
		switch (k) {
		case BVLE:
		{
			return BBBVLE(left, right, false);
			break;
		}
		case BVGE:
		{
			return BBBVLE(right, left, false);
			break;
		}
		case BVGT:
		{
			return BBBVLE(right, left, false, true);
			break;
		}
		case BVLT:
		{
			return BBBVLE(left, right, false, true);
			break;
		}
		case BVSLE:
		{
			return BBBVLE(left, right, true);
			break;
		}
		case BVSGE:
		{
			return BBBVLE(right, left, true);
			break;
		}
		case BVSGT:
		{
			return nf->CreateNode(NOT, BBBVLE(left, right, true));
			break;
		}
		case BVSLT:
		{
			return nf->CreateNode(NOT, BBBVLE(right, left, true));
			break;
		}
		default:
			cerr << "BBCompare: Illegal kind" << form << endl;
			FatalError("", form);
			exit(-1);
		}
	}

	// return a vector with n copies of fillval
	template <class BBNode, class BBNodeManagerT>
	BBNodeVec BitBlaster<BBNode, BBNodeManagerT>::BBfill(unsigned int width,
		BBNode fillval) {
		BBNodeVec zvec(width, fillval);
		return zvec;
	}

	template <class BBNode, class BBNodeManagerT>
	BBNode BitBlaster<BBNode, BBNodeManagerT>::BBEQ(const BBNodeVec& left,
		const BBNodeVec& right) {
		BBNodeVec andvec;
		andvec.reserve(left.size());
		typename BBNodeVec::const_iterator lit = left.begin();
		const typename BBNodeVec::const_iterator litend = left.end();
		typename BBNodeVec::const_iterator rit = right.begin();

		if (left.size() > 1) {
			for (; lit != litend; lit++, rit++) {
				BBNode biteq = nf->CreateNode(IFF, *lit, *rit);
				// fast path exit
				if (biteq == nf->getFalse()) {
					return nf->getFalse();
				}
				else {
					andvec.push_back(biteq);
				}
			}
			BBNode n = nf->CreateNode(AND, andvec);
			return n;
		}
		else
			return nf->CreateNode(IFF, *lit, *rit);
	}

	std::ostream& operator<<(std::ostream& output, const BBNodeAIG& /*h*/) {
		FatalError("This isn't implemented  yet sorry;");
		return output;
	}

	// This creates all the specialisations of the class that are ever needed.
	template class BitBlaster<ASTNode, BBNodeManagerASTNode>;
	template class BitBlaster<BBNodeAIG, BBNodeManagerAIG>;

#undef BBNodeVec
#undef BBNodeVecMap
#undef BBNodeSet

	void print_check(int st) {
		if (st == 0) {
			if (input_status == TO_BE_SATISFIABLE)
				std::cout << ",1\n"; // WRONG
			else if (input_status == TO_BE_UNSATISFIABLE)
				std::cout << ",0\n";
			else if (input_status == TO_BE_UNKNOWN)
				std::cout << ",2\n";
		}
		else // 1
		{
			if (input_status == TO_BE_UNSATISFIABLE)
				std::cout << ",1\n"; // WRONG
			else if (input_status == TO_BE_SATISFIABLE)
				std::cout << ",0\n";
			else if (input_status == TO_BE_UNKNOWN)
				std::cout << ",2\n";
		}
	}

	/*
	   <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
	   word-level solver part
	   <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
	 */

	 //traverse AST tree of the input formula, and decide which solving method to use 
	 //(bit-blasting, composed/decomposed word-level solving)
	int BBForm_check_wenxi(const ASTNode& form) {
		// features for the decision tree model
		whole_num = 0;
		ite_num = 0;
		bitwise_num = 0;
		sign_num = 0;
		extcon_num = 0;
		extend_num = 0;
		shift_con_num = 0;
		shift_noncon_num = 0;
		eq_num = 0;
		ineq_num = 0;
		mult_num = 0;
		bvplus_num = 0;
		udiv_num = 0;
		div_num = 0;
		mult_con_num = 0;
		logic_num = 0;
		arith_num = 0;
		form_num = 1;
		const_num = 0;
		symbool_num = 0;
		symvec_num = 0;
		uminus_num = 0;
		bvsub_num = 0;

		whole_bitwid = 0;
		logic_bitwid = 0;
		arith_bitwid = 0;

		my_wwform_check(form); // traverse the AST tree of input formula to get all the value of the features

		logic_num = ite_num + bitwise_num + extend_num + shift_con_num + shift_noncon_num + extcon_num;
		arith_num = eq_num + ineq_num + bvplus_num + uminus_num + bvsub_num + mult_num + mult_con_num;

		int logic_org, arith_org;
		logic_org = logic_bitwid; arith_org = arith_bitwid;
		if (logic_num != 0)
			logic_bitwid = logic_bitwid / logic_num;
		if (arith_num != 0)
			arith_bitwid = arith_bitwid / arith_num;
		if (logic_num + arith_num != 0)
			whole_bitwid = (logic_org + arith_org) / (logic_num + arith_num);

		int whole_form; // the ratio of bit-vector operations and the boolean operations
		whole_form = whole_num / form_num;

		int logic_arith; // the ratio of logic operations and arithmetic operations	
		if (arith_num)
			logic_arith = logic_num / arith_num;
		else if (logic_num == 0)
			logic_arith = 0;
		else
			logic_arith = 200000;

		// dicide =0 -> bit-blasting solving; decide =1 -> word-level composed solving; decide =2 -> word-level decomposed solving	
		int decide;
		// decision tree
		if (arith_bitwid <= 37)
			if (const_num <= 0)
				if (whole_num > 3088) decide = 2;
				else
					if (arith_bitwid > 27) decide = 2;
					else
						if (whole_form <= 5.19718)
							if (arith_bitwid <= 13) decide = 1;
							else
								if (logic_arith <= 2.0219) decide = 1;
								else
									if (whole_form <= 4.38912) decide = 1;
									else decide = 2;
						else
							if (whole_bitwid > 6) decide = 2;
							else
								if (whole_form <= 6.59207) decide = 1;
								else decide = 2;
			else
				if (mult_con_num <= 54)
					if (whole_form <= 1.07692)
						if (ineq_num <= 1)
							if (logic_arith <= 0.985163) decide = 0;
							else
								if (whole_bitwid <= 18) decide = 1;
								else decide = 0;
						else
							if (const_num > 32) decide = 1;
							else
								if (ite_num > 4) decide = 0;
								else
									if (symvec_num <= 195) decide = 1;
									else
										if (whole_bitwid <= 6)
											if (ineq_num <= 153) decide = 0;
											else
												if (whole_bitwid > 5) decide = 1;
												else
													if (ineq_num <= 243) decide = 1;
													else
														if (const_num <= 5) decide = 0;
														else
															if (const_num <= 8)
																if (bvplus_num <= 6108) decide = 1;
																else decide = 0;
															else
																if (whole_num <= 14432) decide = 1;
																else decide = 0;
										else
											if (ineq_num <= 494) decide = 1;
											else decide = 0;
					else
						if (whole_num <= 612)
							if (mult_num <= 0)
								if (sign_num <= 0)
									if (mult_con_num > 8) decide = 0;
									else
										if (extend_num <= 21) decide = 0;
										else
											if (bvplus_num <= 64) decide = 1;
											else decide = 0;
								else
									if (bitwise_num <= 18) decide = 0;
									else decide = 1;
							else
								if (bitwise_num > 38) decide = 0;
								else
									if (form_num > 8) decide = 1;
									else
										if (form_num <= 5)
											if (mult_con_num <= 0) decide = 1;
											else decide = 2;
										else
											if (symvec_num <= 1) decide = 1;
											else decide = 0;
						else
							if (arith_bitwid <= 4) decide = 0;
							else
								if (whole_bitwid <= 11)
									if (mult_con_num <= 1) decide = 1;
									else decide = 0;
								else
									if (bitwise_num > 33) decide = 0;
									else
										if (logic_arith > 0.184057) decide = 1;
										else
											if (eq_num <= 100) decide = 0;
											else
												if (whole_num <= 3872) decide = 1;
												else decide = 0;
				else
					if (eq_num <= 47)
						if (logic_arith > 0.579418) decide = 1;
						else
							if (extcon_num > 21) decide = 1;
							else
								if (logic_num <= 257) decide = 1;
								else
									if (const_num > 164) decide = 1;
									else
										if (mult_con_num <= 100) decide = 0;
										else decide = 1;
					else
						if (ineq_num <= 213) decide = 1;
						else decide = 0;
		else
			if (ineq_num <= 6) decide = 0;
			else
				if (extcon_num <= 102)
					if (const_num <= 29) decide = 1;
					else
						if (whole_bitwid <= 47)
							if (eq_num <= 64) decide = 0;
							else
								if (eq_num <= 65) decide = 1;
								else decide = 0;
						else
							if (form_num > 129) decide = 1;
							else
								if (mult_num <= 8) decide = 1;
								else decide = 0;
				else
					if (const_num > 22) decide = 0;
					else
						if (arith_bitwid <= 42)
							if (logic_bitwid <= 38) decide = 1;
							else
								if (mult_num <= 5) decide = 0;
								else
									if (logic_arith <= 3.55502) decide = 1;
									else decide = 0;
						else
							if (whole_bitwid > 39) decide = 1;
							else
								if (whole_num <= 4956) decide = 0;
								else decide = 1;

								return decide;
	}


	// word-level solving for the input formula
	bool BBForm_wenxi(const ASTNode& form, int decide) {

		solver *s = solver_new(); // create a word-level solver
		varnum = 0;   // number of literals (including boolean variables, the bits in the bit-vector, and intermediate variables)
		prop_num = 1; // number of propagators            
		composed_flag = decide; // flag to indicate composed method or decomposed method
		word_num = 0; // number of the bit-vectors
		st = true;  // status indicates the formula SAT or UNSAT
		If_Bwlistprop = 0; // indicate if there are propagators in the boolean watch list

		// traverse the AST tree of the input formula
		// and split the formula into basic bit-vector and boolean operations by adding intermediate variables
		my_wwform(s, form);

		creat_clause1(s, toLit(form.Getvarnum())); // set the root of the AST tree to true

		if (st != false) {
			if (solver_simplify(s) == false) {
				st = false;
			}
			else {
				s->verbosity = 1;
				st = solver_solve(s, 0, 0);
			}

			solver_delete(s);
		}
		else {	// st = false
			solver_delete(s);
		}

		return st;
	}

	/* adding intermediate varaibles functions */
	int add_boolean(solver *s) // used for adding intermediate boolean variables
	{
		++varnum;
		solver_setnvars(s, varnum + 1);
		return varnum;
	}

	int add_bitvector(solver *s, int bitwid) // used for adding intermediate bit-vector variables
	{
		int termnum = varnum + 1;
		varnum = bitwid + varnum;
		solver_setnvars(s, varnum + 1);
		// add the bit-vector information (word_num, lower and upper bound) to the "word-info" array
		add_worduplo(s, termnum, bitwid); 

		return termnum;
	}

	/*clauses generation functions*/
	void creat_clause1(solver *s, int l) // unit clause
	{
		int a[1];
		a[0] = l;
		if (!solver_addclause(s, a, a + 1)) {
			st = false;
		}
	}

	void creat_clause2(solver *s, int l1, int l2) // two-lit clause
	{
		int a[2];
		a[0] = l1; a[1] = l2;
		if (!solver_addclause(s, a, a + 2)) {
			st = false;
		}
	}

	void creat_clause3(solver *s, int l1, int l2, int l3) // three-lit clause
	{
		int a[3];
		a[0] = l1; a[1] = l2; a[2] = l3;
		if (!solver_addclause(s, a, a + 3)) {
			st = false;
		}
	}

	void creat_clausen(solver *s, lit* begin, lit* end) // n-lit clause
	{
		if (!solver_addclause(s, begin, end)) {
			st = false;
		}
	}



	/*transfer the boolean operations to clauses */
	int TranstoClause_Bnot(solver *s, int right_kind, int right_num, int left_num) {
		if (right_kind == FALSE) {
			creat_clause1(s, toLit(left_num));
			return 0;
		}
		else if (right_kind == TRUE) {
			creat_clause1(s, lit_neg(toLit(left_num)));
			return 0;
		}
		else {
			creat_clause2(s, toLit(left_num), toLit(right_num));
			creat_clause2(s, lit_neg(toLit(left_num)), lit_neg(toLit(right_num)));
			return 0;
		}
	}

	int TranstoClause_Bnot_val(solver *s, int right_num, int left_num) // when the right_num is not constant variable for sure
	{
		creat_clause2(s, toLit(left_num), toLit(right_num));
		creat_clause2(s, lit_neg(toLit(left_num)), lit_neg(toLit(right_num)));
		return 0;
	}

	int TranstoClause_implies(solver *s, int right1_kind, int right1_num, int right2_kind, int right2_num, int left_num) {
		if (right1_kind == TRUE) {
			if (right2_kind == TRUE) {
				creat_clause1(s, toLit(left_num));
				return 0;
			}
			else if (right2_kind == FALSE) {
				creat_clause1(s, lit_neg(toLit(left_num)));
				return 0;
			}
			else {
				creat_clause2(s, toLit(left_num), lit_neg(toLit(right2_num)));
				creat_clause2(s, lit_neg(toLit(left_num)), toLit(right2_num));
				return 0;
			}
		}
		else if (right1_kind == FALSE) {
			creat_clause1(s, toLit(left_num));
			return 0;
		}
		else {
			if (right2_kind == TRUE) {
				creat_clause1(s, toLit(left_num));
				return 0;
			}
			else if (right2_kind == FALSE) {
				creat_clause2(s, toLit(left_num), toLit(right1_num));
				creat_clause2(s, lit_neg(toLit(left_num)), lit_neg(toLit(right1_num)));
				return 0;
			}
			else {
				creat_clause2(s, toLit(left_num), toLit(right1_num));
				creat_clause2(s, toLit(left_num), lit_neg(toLit(right2_num)));
				creat_clause3(s, lit_neg(toLit(left_num)), lit_neg(toLit(right1_num)), toLit(right2_num));
				return 0;
			}
		}
	}
	int TranstoClause_Bxor(solver *s, int right1_kind, int right1_num, int right2_kind, int right2_num, int left_num) {
		if (right1_kind == TRUE) {
			if (right2_kind == TRUE) {
				creat_clause1(s, lit_neg(toLit(left_num)));
				return 0;
			}
			else if (right2_kind == FALSE) {
				creat_clause1(s, toLit(left_num));
				return 0;
			}
			else {
				creat_clause2(s, toLit(left_num), toLit(right2_num));
				creat_clause2(s, lit_neg(toLit(left_num)), lit_neg(toLit(right2_num)));
				return 0;
			}
		}
		else if (right1_kind == FALSE) {
			if (right2_kind == TRUE) {
				creat_clause1(s, toLit(left_num));
				return 0;
			}
			else if (right2_kind == FALSE) {
				creat_clause1(s, lit_neg(toLit(left_num)));
				return 0;
			}
			else {
				creat_clause2(s, toLit(left_num), lit_neg(toLit(right2_num)));
				creat_clause2(s, lit_neg(toLit(left_num)), toLit(right2_num));
				return 0;
			}
		}
		else {
			if (right2_kind == TRUE) {
				creat_clause2(s, toLit(left_num), toLit(right1_num));
				creat_clause2(s, lit_neg(toLit(left_num)), lit_neg(toLit(right1_num)));
				return 0;
			}
			else if (right2_kind == FALSE) {
				creat_clause2(s, toLit(left_num), lit_neg(toLit(right1_num)));
				creat_clause2(s, lit_neg(toLit(left_num)), toLit(right1_num));
				return 0;
			}
			else {
				creat_clause3(s, toLit(left_num), toLit(right1_num), lit_neg(toLit(right2_num)));
				creat_clause3(s, toLit(left_num), lit_neg(toLit(right1_num)), toLit(right2_num));
				creat_clause3(s, lit_neg(toLit(left_num)), toLit(right1_num), toLit(right2_num));
				creat_clause3(s, lit_neg(toLit(left_num)), lit_neg(toLit(right1_num)), lit_neg(toLit(right2_num)));
				return 0;
			}
		}
	}
	// when both right1 and right2 is not constant for sure
	int TranstoClause_Bxor_sym(solver *s, int right1_num, int right2_num, int left_num) 
	{
		creat_clause3(s, toLit(left_num), toLit(right1_num), lit_neg(toLit(right2_num)));
		creat_clause3(s, toLit(left_num), lit_neg(toLit(right1_num)), toLit(right2_num));
		creat_clause3(s, lit_neg(toLit(left_num)), toLit(right1_num), toLit(right2_num));
		creat_clause3(s, lit_neg(toLit(left_num)), lit_neg(toLit(right1_num)), lit_neg(toLit(right2_num)));
		return 0;
	}
	int TranstoClause_Biff(solver *s, int right1_kind, int right1_num, int right2_kind, int right2_num, int left_num) {
		if (right1_kind == TRUE) {
			if (right2_kind == TRUE) {
				creat_clause1(s, toLit(left_num));
				return 0;
			}
			else if (right2_kind == FALSE) {
				creat_clause1(s, lit_neg(toLit(left_num)));
				return 0;
			}
			else {
				creat_clause2(s, toLit(left_num), lit_neg(toLit(right2_num)));
				creat_clause2(s, lit_neg(toLit(left_num)), toLit(right2_num));
				return 0;
			}
		}
		else if (right1_kind == FALSE) {
			if (right2_kind == TRUE) {
				creat_clause1(s, lit_neg(toLit(left_num)));
				return 0;
			}
			else if (right2_kind == FALSE) {
				creat_clause1(s, toLit(left_num));
				return 0;
			}
			else {
				creat_clause2(s, toLit(left_num), toLit(right2_num));
				creat_clause2(s, lit_neg(toLit(left_num)), lit_neg(toLit(right2_num)));
				return 0;
			}
		}
		else {
			if (right2_kind == TRUE) {
				creat_clause2(s, toLit(left_num), lit_neg(toLit(right1_num)));
				creat_clause2(s, lit_neg(toLit(left_num)), toLit(right1_num));
				return 0;
			}
			else if (right2_kind == FALSE) {
				creat_clause2(s, toLit(left_num), toLit(right1_num));
				creat_clause2(s, lit_neg(toLit(left_num)), lit_neg(toLit(right1_num)));
				return 0;
			}
			else {
				creat_clause3(s, lit_neg(toLit(left_num)), lit_neg(toLit(right1_num)), toLit(right2_num));
				creat_clause3(s, toLit(left_num), lit_neg(toLit(right1_num)), lit_neg(toLit(right2_num)));
				creat_clause3(s, lit_neg(toLit(left_num)), toLit(right1_num), lit_neg(toLit(right2_num)));
				creat_clause3(s, toLit(left_num), toLit(right1_num), toLit(right2_num));
				return 0;
			}
		}
	}

	int TranstoClause_Bite(solver *s, int b_kind, int b_num, int x_kind, int x_num, int y_kind, int y_num, int left_num) {
		if (b_kind == TRUE) {
			if (x_kind == TRUE) {
				creat_clause1(s, toLit(left_num));
				return 0;
			}
			else if (x_kind == FALSE) {
				creat_clause1(s, lit_neg(toLit(left_num)));
				return 0;
			}
			else {
				creat_clause2(s, toLit(left_num), lit_neg(toLit(x_num)));
				creat_clause2(s, lit_neg(toLit(left_num)), toLit(x_num));
				return 0;
			}
		}
		else if (b_kind == FALSE) {
			if (y_kind == TRUE) {
				creat_clause1(s, toLit(left_num));
				return 0;
			}
			else if (y_kind == FALSE) {
				creat_clause1(s, lit_neg(toLit(left_num)));
				return 0;
			}
			else {
				creat_clause2(s, toLit(left_num), lit_neg(toLit(y_num)));
				creat_clause2(s, lit_neg(toLit(left_num)), toLit(y_num));
				return 0;
			}
		}
		else {
			if (x_kind == TRUE) {
				if (y_kind == TRUE) {
					creat_clause1(s, toLit(left_num));
					return 0;
				}
				else if (y_kind == FALSE) {
					creat_clause2(s, toLit(left_num), lit_neg(toLit(b_num)));
					creat_clause2(s, lit_neg(toLit(left_num)), toLit(b_num));
					return 0;
				}
				else {
					creat_clause2(s, toLit(left_num), lit_neg(toLit(b_num)));
					creat_clause3(s, lit_neg(toLit(left_num)), toLit(b_num), toLit(y_num));
					creat_clause2(s, toLit(left_num), lit_neg(toLit(y_num)));
					return 0;
				}
			}
			else if (x_kind == FALSE) {
				if (y_kind == TRUE) {
					creat_clause2(s, toLit(left_num), toLit(b_num));
					creat_clause2(s, lit_neg(toLit(left_num)), lit_neg(toLit(b_num)));
					return 0;
				}
				else if (y_kind == FALSE) {
					creat_clause1(s, lit_neg(toLit(left_num)));
					return 0;
				}
				else {
					creat_clause2(s, lit_neg(toLit(left_num)), lit_neg(toLit(b_num)));
					creat_clause3(s, toLit(left_num), toLit(b_num), lit_neg(toLit(y_num)));
					creat_clause2(s, lit_neg(toLit(left_num)), toLit(y_num));
					return 0;
				}
			}
			else {
				if (y_kind == TRUE) {
					creat_clause2(s, toLit(left_num), toLit(b_num));
					creat_clause3(s, lit_neg(toLit(left_num)), lit_neg(toLit(b_num)), toLit(x_num));
					creat_clause2(s, toLit(left_num), lit_neg(toLit(x_num)));
					return 0;
				}
				else if (y_kind == FALSE) {
					creat_clause2(s, lit_neg(toLit(left_num)), toLit(b_num));
					creat_clause3(s, toLit(left_num), lit_neg(toLit(b_num)), lit_neg(toLit(x_num)));
					creat_clause2(s, lit_neg(toLit(left_num)), toLit(x_num));
					return 0;
				}
				else {
					creat_clause3(s, lit_neg(toLit(b_num)), lit_neg(toLit(x_num)), toLit(left_num));
					creat_clause3(s, lit_neg(toLit(b_num)), toLit(x_num), lit_neg(toLit(left_num)));
					creat_clause3(s, toLit(b_num), lit_neg(toLit(y_num)), toLit(left_num));
					creat_clause3(s, toLit(b_num), toLit(y_num), lit_neg(toLit(left_num)));
					creat_clause3(s, lit_neg(toLit(x_num)), lit_neg(toLit(y_num)), toLit(left_num));
					creat_clause3(s, toLit(x_num), toLit(y_num), lit_neg(toLit(left_num)));
					return 0;
				}
			}
		}
	}
	int TranstoClause_Boolex(solver *s, const ASTNode& form, int index, int left_num) {
		if (form.GetKind() == BVCONST) {
			unsigned long int mask = (uint64_t)1 << index;
			if (mask & form.Getvarnum()) {
				creat_clause1(s, toLit(left_num));
				return 0;
			}
			else {
				creat_clause1(s, lit_neg(toLit(left_num)));
				return 0;
			}
		}
		else {

			int num = form.Getvarnum() + form.GetValueWidth() - index - 1;
			creat_clause2(s, toLit(left_num), lit_neg(toLit(num)));
			creat_clause2(s, lit_neg(toLit(left_num)), toLit(num));
			return 0;
		}
	}
	int TranstoClause_bvand(solver *s, int right1_kind, int right1_num, int right2_kind, int right2_num, int left_num) {
		if (right1_kind == TRUE) // 1 True
		{
			if (right2_kind == TRUE) // 2 True
			{
				creat_clause1(s, toLit(left_num));
				return 0;
			}
			else if (right2_kind == FALSE) // 2 FALSE
			{
				creat_clause1(s, lit_neg(toLit(left_num)));
				return 0;
			}
			else {
				creat_clause2(s, toLit(left_num), lit_neg(toLit(right2_num)));
				creat_clause2(s, lit_neg(toLit(left_num)), toLit(right2_num));
				return 0;
			}
		}
		else if (right1_kind == FALSE) // 1 false
		{
			creat_clause1(s, lit_neg(toLit(left_num)));
			return 0;
		}
		else {
			if (right2_kind == TRUE) {
				creat_clause2(s, toLit(left_num), lit_neg(toLit(right1_num)));
				creat_clause2(s, lit_neg(toLit(left_num)), toLit(right1_num));
				return 0;
			}
			else if (right2_kind == FALSE) {
				creat_clause1(s, lit_neg(toLit(left_num)));
				return 0;
			}
			else {
				creat_clause2(s, lit_neg(toLit(left_num)), toLit(right1_num));
				creat_clause2(s, lit_neg(toLit(left_num)), toLit(right2_num));
				creat_clause3(s, lit_neg(toLit(right1_num)), lit_neg(toLit(right2_num)), toLit(left_num));
				return 0;
			}
		}
	}
	// when right1 and right2 is not constant for sure
	void TranstoClause_bvand_val(solver *s, int right1_num, int right2_num, int left_num) 
	{
		creat_clause2(s, lit_neg(toLit(left_num)), toLit(right1_num));
		creat_clause2(s, lit_neg(toLit(left_num)), toLit(right2_num));
		creat_clause3(s, lit_neg(toLit(right1_num)), lit_neg(toLit(right2_num)), toLit(left_num));
	}

	int TranstoClause_bvor(solver *s, int right1_kind, int right1_num, int right2_kind, int right2_num, int left_num) {
		if (right1_kind == TRUE) // 1 True
		{
			creat_clause1(s, toLit(left_num));
			return 0;
		}
		else if (right1_kind == FALSE) // 1 false
		{
			if (right2_kind == TRUE) // 2 True
			{
				creat_clause1(s, toLit(left_num));
				return 0;
			}
			else if (right2_kind == FALSE) // 2 FALSE
			{
				creat_clause1(s, lit_neg(toLit(left_num)));
				return 0;
			}
			else {
				creat_clause2(s, toLit(left_num), lit_neg(toLit(right2_num)));
				creat_clause2(s, lit_neg(toLit(left_num)), toLit(right2_num));
				return 0;
			}
		}
		else {
			if (right2_kind == TRUE) {
				creat_clause1(s, toLit(left_num));
				return 0;
			}
			else if (right2_kind == FALSE) {
				creat_clause2(s, toLit(left_num), lit_neg(toLit(right1_num)));
				creat_clause2(s, lit_neg(toLit(left_num)), toLit(right1_num));
				return 0;
			}
			else {
				creat_clause2(s, toLit(left_num), lit_neg(toLit(right1_num)));
				creat_clause2(s, toLit(left_num), lit_neg(toLit(right2_num)));
				creat_clause3(s, toLit(right1_num), toLit(right2_num), lit_neg(toLit(left_num)));
				return 0;
			}
		}
	}

	/* generate the 'kind' of the bit in the right-hand side operand, to use the transtoclause functions */
	void set_right_onebit(int *rightkind, int xkind, unsigned long int xnum, int index) // set the kind of the bit in one-bit word
	{
		if (xkind == BVCONST) {
			if (xnum) {
				rightkind[index] = TRUE;
			}
			else {
				rightkind[index] = FALSE;
			}
		}
		else {
			rightkind[index] = SYMBOL;
		}
	}

	// set the kind of the most significant bit in word x
	void set_rightmost(int *rightkind, const ASTNode& x, int bitwid, int index) 
	{
		if (x.GetKind() == BVCONST) {
			if ((x.Getvarnum() >> (bitwid - 1))) {
				rightkind[index] = TRUE;
			}
			else {
				rightkind[index] = FALSE;
			}
		}
		else {
			rightkind[index] = SYMBOL;
		}
	}

	// for the signed bit of the comparison operations (bvsge, bvsgt, bvsle, bvslt)
	void TranstoClause_signcompare(solver *s, const ASTNode& x, const ASTNode& y, int m2, int left_num) {
		int rightkind[2]; int bitwid = x.GetValueWidth();

		set_rightmost(rightkind, x, bitwid, 0);
		set_rightmost(rightkind, y, bitwid, 1);

		int m1 = add_boolean(s);
		TranstoClause_Bxor(s, rightkind[0], x.Getvarnum(), rightkind[1], y.Getvarnum(), m1); // x^y= m1
		TranstoClause_Bxor_sym(s, m1, m2, left_num); // m1^m2 = left_num
	}

	// generate xor clause for two signed bits in x and y
	void TranstoClause_signxor(solver *s, const ASTNode& x, const ASTNode& y, int left_num, int bitwid) {
		int rightkind[2];

		set_rightmost(rightkind, x, bitwid, 0);
		set_rightmost(rightkind, y, bitwid, 1);

		TranstoClause_Bxor(s, rightkind[0], x.Getvarnum(), rightkind[1], y.Getvarnum(), left_num);
	}

	// for one-bit iff bit-vector operation, treat as boolean operation
	void TranstoClause_wiff(solver *s, int xkind, unsigned long int xnum, int ykind, unsigned long int ynum, int left_num) {
		int rightkind[2];

		set_right_onebit(rightkind, xkind, xnum, 0);
		set_right_onebit(rightkind, ykind, ynum, 1);

		TranstoClause_Biff(s, rightkind[0], xnum, rightkind[1], ynum, left_num);
	}
	// for one-bit bvnot bit-vector operation, treat as boolean operation
	void TranstoClause_wnot(solver *s, int xkind, unsigned long int xnum, unsigned long int left_num) {
		int rightkind[1];

		set_right_onebit(rightkind, xkind, xnum, 0);

		TranstoClause_Bnot(s, rightkind[0], xnum, left_num);
	}

	// for one-bit bvand, bvor, bvxor bit-vector operations, treat as boolean operation
	void TranstoClause_bitwise_onebit(solver *s, int xkind, unsigned long int xnum, int ykind, unsigned long int ynum, 
		int left_num, int expkind) {
		int rightkind[2];

		set_right_onebit(rightkind, xkind, xnum, 0);
		set_right_onebit(rightkind, ykind, ynum, 1);

		switch (expkind) {
		case BVXOR:
			TranstoClause_Bxor(s, rightkind[0], xnum, rightkind[1], ynum, left_num);
			break;
		case BVOR:
			TranstoClause_bvor(s, rightkind[0], xnum, rightkind[1], ynum, left_num);
			break;
		case BVAND:

			TranstoClause_bvand(s, rightkind[0], xnum, rightkind[1], ynum, left_num);
			break;
		case BVXNOR:
		{
			int m1 = add_boolean(s);
			TranstoClause_Bxor(s, rightkind[0], xnum, rightkind[1], ynum, m1);
			TranstoClause_Bnot_val(s, m1, left_num);
			break;
		}
		case BVNOR:
		{
			int m1 = add_boolean(s);
			TranstoClause_bvor(s, rightkind[0], xnum, rightkind[1], ynum, m1);
			TranstoClause_Bnot_val(s, m1, left_num);
			break;
		}
		case BVNAND:
		{
			int m1 = add_boolean(s);
			TranstoClause_bvand(s, rightkind[0], xnum, rightkind[1], ynum, m1);
			TranstoClause_Bnot_val(s, m1, left_num);
			break;
		}
		}
	}

	// for one-bit bvand, bvor, bvxor bit-vector operations, treat as boolean operation
	void TranstoClause_wite(solver *s, int xkind, unsigned long int xnum, int ykind, unsigned long int ynum, int zkind, 
		unsigned long int znum, int left_num) {
		int rightkind[2];
		set_right_onebit(rightkind, ykind, ynum, 0);
		set_right_onebit(rightkind, zkind, znum, 1);

		TranstoClause_Bite(s, xkind, xnum, rightkind[0], ynum, rightkind[1], znum, left_num);
	}





	/* functions for set the parameters (operands of the bit-vector operations) of propagator
	   since the right-hand side operands might be constant number in which case we need to capture;
	   when the operand i is constant, right[i] is -2, param[i] is the constant number (64 bit width);
	   when it is variable right[i] is the variable number (we assume the variable number is within 32 bit width), param[i] is -2;
	 */
	void check_const(int kindx, int* right, unsigned long int* param, int i, unsigned long int num) {
		if (kindx == BVCONST) {
			right[i] = -2;
			param[i] = num;
		}
		else {
			right[i] = num;
			param[i] = (uint64_t)(-2);
		}
	}

	// for the operand of ite propagator
	void check_iteconst(int kindx, int* right, unsigned long int* param, int i, unsigned long int num) 
	{
		if (kindx == BVCONST) {
			right[i] = -2;
			param[i - 1] = num;
		}
		else {
			right[i] = num;
			param[i - 1] = (uint64_t)(-2);
		}
	}

	/*generate the lower and upper bound for each argument in the propagator*/
	struct ul* get_argu(solver *s, int v1) {
		struct ul* argu0;  vecp *wl1;
		if (v1 != -2) {
			wl1 = solver_read_wlist(s, toLit(v1));
			argu0 = (struct ul*)(vecp_begin(&s->word_info[get_word_num(wl1)])[0]);
		}
		else
			argu0 = NULL;

		return argu0;
	}

	// for the arugment which is not constant variable for sure
	struct ul* get_argu_set(solver *s, int v1) {
		struct ul* argu0; vecp *wl1;

		wl1 = solver_read_wlist(s, toLit(v1));
		argu0 = (struct ul*)(vecp_begin(&s->word_info[get_word_num(wl1)])[0]);

		return argu0;
	}



	/* push the initial upper and lower bound into vecp "word_info" for each newly added bit-vector */
	struct ul* add_worduplo(solver* s, int v1, int bitwid) {
		realloc_wordinfo(s, word_num + 1);
		vecp* words = &s->word_info[word_num];
		vecp_new(words);

		int* indexs = s->index;
		vecp *wl1, *wl2; int i; struct ul* vval;

		vval = (struct ul*)malloc(sizeof(struct ul));
		vval->word_num = word_num;
		vval->lower = 0;
		if (bitwid == 64) {
			vval->upper = (uint64_t)(-1);
		}
		else {
			vval->upper = ~((uint64_t)(-1) << bitwid);
		}

		for (i = bitwid - 1;i >= 0;i--) {
			wl1 = solver_read_wlist(s, toLit(v1)); wl2 = solver_read_wlist(s, lit_neg(toLit(v1)));
			set_word_num(wl1, word_num);
			set_word_num(wl2, word_num);
			indexs[v1] = i;
			v1++;
		}

		vecp_push(words, vval);

		word_num++;
		return vval;
	}

	// push "fake" upper and lower bound for bool var into vecp "word_info"
	void add_booluplo(solver* s, int v1) {
		realloc_wordinfo(s, word_num + 1);
		vecp_new(&s->word_info[word_num]);

		struct ul* vval = (struct ul*)1;

		set_word_num(solver_read_wlist(s, toLit(v1)), word_num);
		set_word_num(solver_read_wlist(s, lit_neg(toLit(v1))), word_num);
		vecp_push(&s->word_info[word_num], vval);

		word_num++;
	}

	void realloc_wordinfo(solver *s, int num) {
		if (s->wordcap < num) {
			while (s->wordcap < num)
				s->wordcap = s->wordcap * 2 + 1;
			s->word_info = (vecp*)realloc(s->word_info, sizeof(vecp)* s->wordcap);
		}
	}

	// push the propagators into "word_info" array for the corresponding bit-vector; 
	void add_wordprop(solver* s, int num, struct ws_flag* wat) {
		vecp* words = &s->word_info[num];
		vecp_push(words, wat);
	}

	/*create the propagator and push the propagator into the propgator queue*/
	void enque_initp(solver* s, struct ws_flag* wat) {
		prop_num++;
		vecp_push(&s->prop_stock, wat);
		realloc_prop(s, prop_num + 1);
		s->prop_que[s->propt] = wat;	// enqueue the fresh propagator to the propagator queue	
		s->propt = s->propt + 1; // at the beginning 
	}

	void realloc_prop(solver *s, int num) {
		if (s->propcap < num) {
			while (s->propcap < num)
				s->propcap = s->propcap * 2 + 1;
			s->prop_que = (struct ws_flag**)realloc(s->prop_que, sizeof(struct ws_flag*)* s->propcap);
		}
	}

	/* word-level propagator generation functions*/
	// BVAND, BVOR, BVXOR
	void bitwise2_generate(solver *s, int kind, int bitwid, int* right, int left, unsigned long int* param) 
	{
		int v1 = right[0]; int v2 = right[1];
		struct ws_flag* wat;

		wat = (struct ws_flag*)malloc(sizeof(struct ws_flag));
		wat->oper = kind;
		wat->inqueue_flag = 1;
		wat->bitwids = (int*)malloc(sizeof(int));
		wat->bitwids[0] = bitwid;
		wat->arnum = (int*)malloc(sizeof(int) * 3);
		wat->arnum[0] = v1;
		wat->arnum[1] = v2;
		wat->arnum[2] = left;
		wat->argu = (struct ul**)malloc(sizeof(struct ul*) * 3);
		wat->bound = (unsigned long int*)malloc(sizeof(unsigned long int) * 2);
		wat->bound[0] = param[0]; wat->bound[1] = param[1];

		struct ul* argu0 = get_argu(s, v1);
		struct ul* argu1 = get_argu(s, v2);
		struct ul* argu2 = get_argu_set(s, left);

		wat->argu[0] = argu0; wat->argu[1] = argu1; wat->argu[2] = argu2;

		if (argu0 != NULL)
			add_wordprop(s, argu0->word_num, wat);
		if (argu1 != NULL)
			add_wordprop(s, argu1->word_num, wat);
		add_wordprop(s, argu2->word_num, wat);

		enque_initp(s, wat);
	}


	void bitwise1_generate(solver *s, int bitwid, int* right, int left, unsigned long int* param) // BVNEG
	{
		int v1 = right[0];
		struct ws_flag* wat;

		wat = (struct ws_flag*)malloc(sizeof(struct ws_flag));
		wat->oper = BVNEG;
		wat->inqueue_flag = 1;
		wat->bitwids = (int*)malloc(sizeof(int));
		wat->bitwids[0] = bitwid;
		wat->arnum = (int*)malloc(sizeof(int) * 2);
		wat->arnum[0] = v1;
		wat->arnum[1] = left;
		wat->argu = (struct ul**)malloc(sizeof(struct ul*) * 2);
		wat->bound = (unsigned long int*)malloc(sizeof(unsigned long int) * 1);
		wat->bound[0] = param[0];

		struct ul* argu0 = get_argu(s, v1);
		struct ul* argu1 = get_argu_set(s, left);

		wat->argu[0] = argu0; wat->argu[1] = argu1;

		if (argu0 != NULL)
			add_wordprop(s, argu0->word_num, wat);
		add_wordprop(s, argu1->word_num, wat);

		enque_initp(s, wat);
	}

	// for composed BVEQ, BVLE
	void compose_generate(solver *s, int kind, int bitwid, int* right, int left, unsigned long int* param) 
	{
		int v1 = right[0]; int v2 = right[1];

		struct ws_flag* wat;
		wat = (struct ws_flag*)malloc(sizeof(struct ws_flag));
		wat->oper = kind;
		wat->inqueue_flag = 1;
		wat->bitwids = (int*)malloc(sizeof(int));
		wat->bitwids[0] = bitwid;
		wat->arnum = (int*)malloc(sizeof(int) * 3);
		wat->arnum[0] = v1;
		wat->arnum[1] = v2;
		wat->arnum[2] = left;
		wat->argu = (struct ul**)malloc(sizeof(struct ul*) * 2);
		wat->bound = (unsigned long int*)malloc(sizeof(unsigned long int) * 2);
		wat->bound[0] = param[0];
		wat->bound[1] = param[1];

		struct ul* argu0 = get_argu(s, v1);
		struct ul* argu1 = get_argu(s, v2);

		vecp* wl1 = solver_read_wlist(s, toLit(left));
		int word_num1 = get_word_num(wl1);
		if (word_num1 == -1) {
			word_num1 = word_num;
			add_booluplo(s, left);
		}

		wat->argu[0] = argu0; wat->argu[1] = argu1;

		if (argu0 != NULL)
			add_wordprop(s, argu0->word_num, wat);
		if (argu1 != NULL)
			add_wordprop(s, argu1->word_num, wat);
		add_wordprop(s, word_num1, wat);


		enque_initp(s, wat);
	}

	void bvxor_div_generate(solver *s, int bitwid, int* right, unsigned long int left) // BVAND, BVOR, BVXOR, BVNOT
	{
		int v1 = right[0]; int v2 = right[1]; //v3=var[3];	 // dont need v3	     

		struct ws_flag* wat;
		wat = (struct ws_flag*)malloc(sizeof(struct ws_flag));
		wat->oper = BVXOR_DIV;
		wat->inqueue_flag = 1;
		wat->bitwids = (int*)malloc(sizeof(int));
		wat->bitwids[0] = bitwid;
		wat->arnum = (int*)malloc(sizeof(int) * 2);
		wat->arnum[0] = v1;
		wat->arnum[1] = v2;
		//wat->arnum[2] = v3;
		wat->argu = (struct ul**)malloc(sizeof(struct ul*) * 2);
		wat->bound = (unsigned long int*)malloc(sizeof(unsigned long int) * 1);
		wat->bound[0] = left;

		struct ul *argu0 = get_argu_set(s, v1);
		struct ul *argu1 = get_argu_set(s, v2);
		//argu2 = get_argu(s, v3);

		wat->argu[0] = argu0; wat->argu[1] = argu1; //wat->argu[2]= argu2; 

		//if(argu0!=NULL)
		add_wordprop(s, argu0->word_num, wat);
		//if(argu1!=NULL)	
		add_wordprop(s, argu1->word_num, wat);
		//add_wordprop(s, argu2->word_num, wat);	

		enque_initp(s, wat);
	}

	// concatenation
	void concate_generate(solver *s, int bitwid, int* right, int left, unsigned long int* param, int subwid1, int subwid2) 
	{
		int v1 = right[0]; int v2 = right[1];

		struct ws_flag* wat;
		wat = (struct ws_flag*)malloc(sizeof(struct ws_flag));
		wat->oper = BVCONCAT;
		wat->inqueue_flag = 1;
		wat->bitwids = (int*)malloc(sizeof(int) * 3);
		wat->bitwids[0] = bitwid;
		wat->bitwids[1] = subwid1;
		wat->bitwids[2] = subwid2;
		wat->arnum = (int*)malloc(sizeof(int) * 3);
		wat->arnum[0] = v1;
		wat->arnum[1] = v2;
		wat->arnum[2] = left;
		wat->argu = (struct ul**)malloc(sizeof(struct ul*) * 3);
		wat->bound = (unsigned long int*)malloc(sizeof(unsigned long int) * 2);
		wat->bound[0] = param[0];
		wat->bound[1] = param[1];

		struct ul *argu0 = get_argu(s, v1);
		struct ul *argu1 = get_argu(s, v2);
		struct ul *argu2 = get_argu_set(s, left);

		wat->argu[0] = argu0; wat->argu[1] = argu1; wat->argu[2] = argu2;

		if (argu0 != NULL)
			add_wordprop(s, argu0->word_num, wat);
		if (argu1 != NULL)
			add_wordprop(s, argu1->word_num, wat);
		add_wordprop(s, argu2->word_num, wat);


		enque_initp(s, wat);
	}

	// extraction
	void extract_generate(solver *s, int bitwid, int* right, int left, unsigned long int* param, int subwid1, int subwid2) 
	{
		int v1 = right[0];

		struct ws_flag* wat;
		wat = (struct ws_flag*)malloc(sizeof(struct ws_flag));
		wat->oper = BVEXTRACT;
		wat->inqueue_flag = 1;
		wat->bitwids = (int*)malloc(sizeof(int) * 3);
		wat->bitwids[0] = bitwid; // org bitwid
		wat->bitwids[1] = subwid1;
		wat->bitwids[2] = subwid2;
		wat->arnum = (int*)malloc(sizeof(int) * 2);
		wat->arnum[0] = v1;
		wat->arnum[1] = left;
		wat->argu = (struct ul**)malloc(sizeof(struct ul*) * 2);
		wat->bound = (unsigned long int*)malloc(sizeof(unsigned long int) * 1);
		wat->bound[0] = param[0];

		struct ul *argu0 = get_argu(s, v1);
		struct ul *argu1 = get_argu_set(s, left);

		wat->argu[0] = argu0; wat->argu[1] = argu1;
		if (argu0 != NULL)
			add_wordprop(s, argu0->word_num, wat);
		add_wordprop(s, argu1->word_num, wat);


		enque_initp(s, wat);
	}

	//leftshift, (a_)rightshift
	void shift_generate(solver *s, int kind, int bitwid, int* right, int left, unsigned long int* param)  
	{
		int v1 = right[0]; int shiftbits = right[1];

		struct ws_flag* wat;
		wat = (struct ws_flag*)malloc(sizeof(struct ws_flag));
		wat->oper = kind;
		wat->inqueue_flag = 1;
		wat->bitwids = (int*)malloc(sizeof(int) * 2);
		wat->bitwids[0] = bitwid;
		wat->bitwids[1] = shiftbits; //shiftbits
		wat->arnum = (int*)malloc(sizeof(int) * 2);
		wat->arnum[0] = v1;
		wat->arnum[1] = left;
		wat->argu = (struct ul**)malloc(sizeof(struct ul*) * 2);
		wat->bound = (unsigned long int*)malloc(sizeof(unsigned long int) * 1);
		wat->bound[0] = param[0];

		struct ul *argu0 = get_argu(s, v1);
		struct ul *argu1 = get_argu_set(s, left);

		wat->argu[0] = argu0; wat->argu[1] = argu1;

		if (argu0 != NULL)
			add_wordprop(s, argu0->word_num, wat);
		add_wordprop(s, argu1->word_num, wat);


		enque_initp(s, wat);
	}

	//zero_extend, sign_extend
	void extend_generate(solver *s, int kind, int bitwid, int* right, int left, unsigned long int* param)  
	{
		int v1 = right[0]; int orgbits = right[1];

		struct ws_flag* wat;
		wat = (struct ws_flag*)malloc(sizeof(struct ws_flag));
		wat->oper = kind;
		wat->inqueue_flag = 1;
		wat->bitwids = (int*)malloc(sizeof(int) * 2);
		wat->bitwids[0] = bitwid; // addbits
		wat->bitwids[1] = orgbits; // orgbits
		wat->arnum = (int*)malloc(sizeof(int) * 2);
		wat->arnum[0] = v1;
		wat->arnum[1] = left;
		wat->argu = (struct ul**)malloc(sizeof(struct ul*) * 2);
		wat->bound = (unsigned long int*)malloc(sizeof(unsigned long int) * 1);
		wat->bound[0] = param[0];

		struct ul *argu0 = get_argu(s, v1);
		struct ul *argu1 = get_argu_set(s, left);

		wat->argu[0] = argu0; wat->argu[1] = argu1;

		if (argu0 != NULL)
			add_wordprop(s, argu0->word_num, wat);
		add_wordprop(s, argu1->word_num, wat);


		enque_initp(s, wat);
	}

	void iteparse_generate(solver *s, int bitwid, int* right, int left, unsigned long int* param) //if-then-else statement
	{
		int v1 = right[0]; int v2 = right[1]; int v3 = right[2];

		struct ws_flag* wat;
		wat = (struct ws_flag*)malloc(sizeof(struct ws_flag));
		wat->oper = ITE;
		wat->inqueue_flag = 1;
		wat->bitwids = (int*)malloc(sizeof(int));
		wat->bitwids[0] = bitwid;
		wat->arnum = (int*)malloc(sizeof(int) * 4);
		wat->arnum[0] = v1;
		wat->arnum[1] = v2;
		wat->arnum[2] = v3;
		wat->arnum[3] = left;
		wat->argu = (struct ul**)malloc(sizeof(struct ul*) * 4);
		wat->bound = (unsigned long int*)malloc(sizeof(unsigned long int) * 2);
		wat->bound[0] = param[0];
		wat->bound[1] = param[1];

		struct ul* argu0 = get_argu_set(s, v1);
		struct ul* argu1 = get_argu(s, v2);
		struct ul* argu2 = get_argu(s, v3);
		struct ul* argu3 = get_argu_set(s, left);

		wat->argu[0] = argu0; wat->argu[1] = argu1; wat->argu[2] = argu2; wat->argu[3] = argu3;

		add_wordprop(s, argu0->word_num, wat);
		if (argu1 != NULL)
			add_wordprop(s, argu1->word_num, wat);
		if (argu2 != NULL)
			add_wordprop(s, argu2->word_num, wat);
		add_wordprop(s, argu3->word_num, wat);

		enque_initp(s, wat);
	}

	// xbit xbit xbit ... -> xword (every bit in xword is xbit)
	void bit_toword_generate(solver *s, int bitwid, int xbit, int xword) 
	{
		struct ws_flag* wat;
		wat = (struct ws_flag*)malloc(sizeof(struct ws_flag));
		wat->oper = BTOW;
		wat->inqueue_flag = 1;
		wat->bitwids = (int*)malloc(sizeof(int));
		wat->bitwids[0] = bitwid;
		wat->arnum = (int*)malloc(sizeof(int) * 2);
		wat->arnum[0] = xbit;
		wat->arnum[1] = xword;
		wat->argu = (struct ul**)malloc(sizeof(struct ul*));
		wat->bound = NULL;
		// flag_inword 0 indicates not in word, not 0 means bool var or const				

		struct ul* argu1 = get_argu_set(s, xword);
		wat->argu[0] = argu1;

		if (xbit > 0) {
			If_Bwlistprop = 1;
			vecp_push_prop(solver_read_wlist(s, toLit(xbit)), wat);
			vecp_push_prop(solver_read_wlist(s, lit_neg(toLit(xbit))), wat);
		}
		add_wordprop(s, argu1->word_num, wat);

		enque_initp(s, wat);
	}


	int bvplus_generate(solver *s, unsigned long int x, unsigned long int y, int z, int bitwid, int kindx, int kindy) {
		int m1 = add_bitvector(s, bitwid);
		int m2 = add_bitvector(s, bitwid);
		int m3 = add_bitvector(s, bitwid);
		int co = add_bitvector(s, bitwid); //carry out 
		int c = add_bitvector(s, bitwid);  //carry in

		int right[2]; unsigned long int param[2];

		check_const(kindx, right, param, 0, x);
		check_const(kindy, right, param, 1, y);
		bitwise2_generate(s, BVXOR, bitwid, right, m1, param); // x ^ y = m1

		right[0] = m1;
		right[1] = c;
		bitwise2_generate(s, BVXOR, bitwid, right, z, param); // m1 ^ c = z

		right[0] = m1;
		right[1] = c;
		bitwise2_generate(s, BVAND, bitwid, right, m2, param); // m1 & c = m2

		check_const(kindx, right, param, 0, x);
		check_const(kindy, right, param, 1, y);
		bitwise2_generate(s, BVAND, bitwid, right, m3, param); // x & y = m3

		right[0] = m2;
		right[1] = m3;
		bitwise2_generate(s, BVOR, bitwid, right, co, param); // m2 | m3 = co

		right[0] = co;
		right[1] = 1;
		shift_generate(s, BVLEFTSHIFT, bitwid, right, c, param); // co << 1 = c

		return co;
	}

	void bvplus_nonoverflow_generate(solver *s, unsigned long int x, unsigned long int y, int z, int bitwid, int kindx, int kindy) {
		int co = bvplus_generate(s, x, y, z, bitwid, kindx, kindy);

		creat_clause1(s, lit_neg(toLit(co))); // make sure the carry out bit of the addition is zero (non-overflow addtion)
	}

	// x and y is not constant variable for sure, and non-overflow
	void bvplus_divmod_generate(solver *s, int x, int y, unsigned long int z, int bitwid, int kindz) {
		int m1 = add_bitvector(s, bitwid);
		int m2 = add_bitvector(s, bitwid);
		int m3 = add_bitvector(s, bitwid);
		int co = add_bitvector(s, bitwid); //carry out
		int c = add_bitvector(s, bitwid);  //carry in

		int right[2]; unsigned long int param[2];

		right[0] = x;
		right[1] = y;
		bitwise2_generate(s, BVXOR, bitwid, right, m1, param); // x ^ y = m1

		if (kindz != BVCONST) {
			right[0] = m1;
			right[1] = c;
			bitwise2_generate(s, BVXOR, bitwid, right, z, param); // m1 ^ c = z
		}
		else {
			right[0] = m1;
			right[1] = c;
			bvxor_div_generate(s, bitwid, right, z); // m1 ^ c = z	
		}

		right[0] = m1;
		right[1] = c;
		bitwise2_generate(s, BVAND, bitwid, right, m2, param); // m1 & c = m2

		right[0] = x;
		right[1] = y;
		bitwise2_generate(s, BVAND, bitwid, right, m3, param); // x & y = m3

		right[0] = m2;
		right[1] = m3;
		bitwise2_generate(s, BVOR, bitwid, right, co, param); // m2 | m3 = co

		right[0] = co;
		right[1] = 1;
		shift_generate(s, BVLEFTSHIFT, bitwid, right, c, param); // co << 1 = c

		creat_clause1(s, lit_neg(toLit(co))); // make sure the carry out bit of the addition is zero (non-overflow addtion)
	}


	void bvuminus_generate(solver *s, unsigned long int x, int z, int bitwid, int kindx) {
		int m1 = add_bitvector(s, bitwid);
		unsigned long int m2 = (uint64_t)1;

		int right[1]; unsigned long int param[1];

		check_const(kindx, right, param, 0, x);
		bitwise1_generate(s, bitwid, right, m1, param); // ~x = m1

		bvplus_generate(s, m1, m2, z, bitwid, SYMBOL, BVCONST); // m1 + m2 = z
	}

	void bvsub_generate(solver *s, unsigned long int x, unsigned long int y, int z, int bitwid, int kindx, int kindy) {
		int m1 = add_bitvector(s, bitwid);

		bvuminus_generate(s, y, m1, bitwid, kindy);  // -y = m1
		bvplus_generate(s, x, m1, z, bitwid, kindx, SYMBOL); // x + m1 = z
	}

	/* bvmult and bvmult_non_overflow generation */
	void bvmult_generate(solver *s, int kindx, int kindy, int k, unsigned long int xnum, unsigned long int ynum, int left_num) {
		if (kindx == BVCONST && kindy == BVCONST) {
			unsigned long int z = xnum*ynum;  int i;
			for (i = 0; i < k; i++) // Z = 0
			{
				if (((z >> (k - 1 - i))&(uint64_t)1)) {
					creat_clause1(s, toLit(left_num + i));
				}
				else {
					creat_clause1(s, lit_neg(toLit(left_num + i)));
				}
			}
		}
		else if (kindx == BVCONST) {
			if (xnum == (uint64_t)0) {
				// Z = 0;
				bvequall_generate(s, (uint64_t)0, left_num, k, BVCONST);
			}
			else if (__builtin_popcountl(xnum) == 1) {
				int right[2]; unsigned long int param[1];
				right[0] = ynum; // y is not const for sure
				right[1] = __builtin_ffsl(xnum) - 1;

				shift_generate(s, BVLEFTSHIFT, k, right, left_num, param);
			}
			else // j>=2
			{
				int i;  int j = 0;
				int* vector = (int*)malloc(sizeof(int)*k); //vector[k]		
				if ((xnum & (uint64_t)1)) {
					vector[j] = ynum;
					j++;

					xnum &= (xnum - (uint64_t)1);
				}
				while (xnum) {
					i = __builtin_ffsl(xnum) - 1;
					vector[j] = leftshift_mult(s, k, i, ynum);
					j++;

					xnum &= (xnum - (uint64_t)1);
				}

				int m1 = 0; int m2 = 0;
				for (i = 1; i < j - 1; i++) {
					m2 = m1; // the former one
					m1 = add_bitvector(s, k);
					if (m2 == 0) {
						bvplus_generate(s, vector[0], vector[1], m1, k, SYMBOL, SYMBOL);

					}
					else {
						bvplus_generate(s, vector[i], m2, m1, k, SYMBOL, SYMBOL);
					}
				}
				if (m1 == 0) {
					bvplus_generate(s, vector[0], vector[i], left_num, k, SYMBOL, SYMBOL);
				}
				else {
					bvplus_generate(s, vector[i], m1, left_num, k, SYMBOL, SYMBOL);
				}

				free(vector);
			}
		}
		else if (kindy == BVCONST) {
			if (ynum == (uint64_t)0) {
				// left_num = 0;
				bvequall_generate(s, (uint64_t)0, left_num, k, BVCONST);
			}
			else if (__builtin_popcountl(ynum) == 1) {
				int right[2]; unsigned long int param[1];
				right[0] = xnum; // x is not const for sure
				right[1] = __builtin_ffsl(ynum) - 1;

				shift_generate(s, BVLEFTSHIFT, k, right, left_num, param);
			}
			else {
				int i; int j = 0;
				int* vector = (int*)malloc(sizeof(int)*k); //vector[k]	 

				if ((ynum & (uint64_t)1)) {
					vector[j] = xnum;
					j++;

					ynum &= (ynum - (uint64_t)1);

				}
				while (ynum) {
					i = __builtin_ffsl(ynum) - 1;
					vector[j] = leftshift_mult(s, k, i, xnum);
					j++;

					ynum &= (ynum - (uint64_t)1);
				}

				int m1 = 0; int m2 = 0;
				for (i = 1; i < j - 1; i++) {
					m2 = m1; // the former one
					m1 = add_bitvector(s, k);

					if (m2 == 0) {
						bvplus_generate(s, vector[0], vector[1], m1, k, SYMBOL, SYMBOL);
					}
					else {
						bvplus_generate(s, vector[i], m2, m1, k, SYMBOL, SYMBOL);
					}
				}
				if (m1 == 0) {
					bvplus_generate(s, vector[0], vector[i], left_num, k, SYMBOL, SYMBOL);
				}
				else {
					bvplus_generate(s, vector[i], m1, left_num, k, SYMBOL, SYMBOL);
				}

				free(vector);
			}
		}
		else {
			if (k == 1) {
				TranstoClause_Bite(s, kindy, ynum, kindx, xnum, FALSE, 0, left_num);
			}
			else {
				int ite_num; int shift_xnum;

				shift_xnum = add_bitvector(s, k);

				leftshiftx(s, xnum, k, k - 1, shift_xnum);

				int ite_first = add_bitvector(s, k);

				iteterm_generate(s, SYMBOL, ynum, SYMBOL, shift_xnum, BVCONST, (int64_t)0, ite_first, k);

				int m1 = 0; int m2 = 0;
				int i = 1;

				for (; i < k - 1; i++) {
					shift_xnum = add_bitvector(s, k);
					leftshiftx(s, xnum, k, k - 1 - i, shift_xnum);

					ite_num = add_bitvector(s, k);
					iteterm_generate(s, SYMBOL, ynum + i, SYMBOL, shift_xnum, BVCONST, (int64_t)0, ite_num, k);

					m2 = m1; // the former result for plus
					m1 = add_bitvector(s, k); // the result for the current plus

					if (m2 == 0) {
						bvplus_generate(s, ite_first, ite_num, m1, k, SYMBOL, SYMBOL);
					}
					else {
						bvplus_generate(s, ite_num, m2, m1, k, SYMBOL, SYMBOL);
					}
				}

				// no shift for x
				ite_num = add_bitvector(s, k);
				iteterm_generate(s, SYMBOL, ynum + i, SYMBOL, xnum, BVCONST, (int64_t)0, ite_num, k);

				if (m1 == 0) {
					bvplus_generate(s, ite_first, ite_num, left_num, k, SYMBOL, SYMBOL);
				}
				else {
					bvplus_generate(s, m1, ite_num, left_num, k, SYMBOL, SYMBOL);
				}
			}
		}
	}

	void bvmult_noverflow_generate(solver *s, int kindx, int kindy, int k, unsigned long int xnum, unsigned long int ynum, int left_num) {
		if (kindy == BVCONST) {
			if (ynum == (uint64_t)0) {
				bvequall_generate(s, (uint64_t)0, left_num, k, BVCONST);
			}
			else if (__builtin_popcountl(ynum) == 1) {
				int right[2]; unsigned long int param[1];
				right[0] = xnum; // x is not const for sure
				right[1] = __builtin_ffsl(ynum) - 1;

				int i;   // non-overflow
				for (i = 0; i < right[1]; i++) {
					creat_clause1(s, lit_neg(toLit(xnum + i)));
				}

				shift_generate(s, BVLEFTSHIFT, k, right, left_num, param);
			}
			else {
				int i; int j = 0;
				int* vector = (int*)malloc(sizeof(int)*k); //vector[k]			
				if ((ynum & (uint64_t)1)) {
					vector[j] = xnum;
					j++;

					ynum &= (ynum - (uint64_t)1);

				}
				while (ynum) {
					i = __builtin_ffsl(ynum) - 1;
					vector[j] = leftshift_mult_noverflow(s, k, i, xnum);
					j++;

					ynum &= (ynum - (uint64_t)1);
				}

				int m1 = 0; int m2 = 0;
				for (i = 1; i < j - 1; i++) {
					m2 = m1; // the former one
					m1 = add_bitvector(s, k);

					if (m2 == 0) {
						bvplus_nonoverflow_generate(s, vector[0], vector[1], m1, k, SYMBOL, SYMBOL);
					}
					else {
						bvplus_nonoverflow_generate(s, vector[i], m2, m1, k, SYMBOL, SYMBOL);
					}
				}
				if (m1 == 0) {
					bvplus_nonoverflow_generate(s, vector[0], vector[i], left_num, k, SYMBOL, SYMBOL);
				}
				else {
					bvplus_nonoverflow_generate(s, vector[i], m1, left_num, k, SYMBOL, SYMBOL);
				}

				free(vector);
			}
		}
		else {
			if (k == 1) {
				TranstoClause_Bite(s, kindy, ynum, kindx, xnum, FALSE, 0, left_num);
			}
			else {
				int ite_num; int shift_xnum;

				shift_xnum = add_bitvector(s, k);

				leftshiftx_noverflow(s, xnum, k, k - 1, shift_xnum, ynum);

				int ite_first = add_bitvector(s, k);
				iteterm_generate(s, SYMBOL, ynum, SYMBOL, shift_xnum, BVCONST, (int64_t)0, ite_first, k);

				int m1 = 0; int m2 = 0;
				int i = 1;

				for (; i < k - 1; i++) {
					shift_xnum = add_bitvector(s, k);
					leftshiftx_noverflow(s, xnum, k, k - 1 - i, shift_xnum, ynum);

					ite_num = add_bitvector(s, k);
					iteterm_generate(s, SYMBOL, ynum + i, SYMBOL, shift_xnum, BVCONST, (int64_t)0, ite_num, k);

					m2 = m1; // the former result for plus
					m1 = add_bitvector(s, k); // the result for the current plus

					if (m2 == 0) {
						bvplus_nonoverflow_generate(s, ite_first, ite_num, m1, k, SYMBOL, SYMBOL);
					}
					else {
						bvplus_nonoverflow_generate(s, ite_num, m2, m1, k, SYMBOL, SYMBOL);
					}
				}

				// no shift for x
				ite_num = add_bitvector(s, k);
				iteterm_generate(s, SYMBOL, ynum + i, SYMBOL, xnum, BVCONST, (int64_t)0, ite_num, k);

				if (m1 == 0) {
					bvplus_nonoverflow_generate(s, ite_first, ite_num, left_num, k, SYMBOL, SYMBOL);
				}
				else {
					bvplus_nonoverflow_generate(s, m1, ite_num, left_num, k, SYMBOL, SYMBOL);
				}
			}
		}
	}

	int leftshift_mult(solver *s, int bitwid, int bit_num, int xnum) {
		int m_shift = add_bitvector(s, bitwid);

		int right[2]; unsigned long int param[1];
		right[0] = xnum;
		right[1] = bit_num;

		shift_generate(s, BVLEFTSHIFT, bitwid, right, m_shift, param);

		return m_shift;
	}

	int leftshift_mult_noverflow(solver *s, int bitwid, int bit_num, int xnum) {
		int m_shift = add_bitvector(s, bitwid);

		int right[2]; unsigned long int param[1];
		right[0] = xnum;
		right[1] = bit_num;

		int i;
		for (i = 0; i < bit_num; i++) {
			creat_clause1(s, lit_neg(toLit(xnum + i)));
		}

		shift_generate(s, BVLEFTSHIFT, bitwid, right, m_shift, param);

		return m_shift;
	}

	void leftshiftx(solver *s, int xnum, int bitwid, int shiftbits, int left_num) {
		int right[2]; unsigned long int param[1];
		right[0] = xnum;
		right[1] = shiftbits;
		shift_generate(s, BVLEFTSHIFT, bitwid, right, left_num, param);
	}

	void leftshiftx_noverflow(solver *s, int xnum, int bitwid, int shiftbits, int left_num, int ynum) {
		int right[2]; unsigned long int param[1];
		right[0] = xnum;
		right[1] = shiftbits;

		int i;
		for (i = 0; i < shiftbits; i++) // ynum+bit_num -> !(xnum+i)
		{
			creat_clause2(s, lit_neg(toLit(ynum + bitwid - 1 - shiftbits)), lit_neg(toLit(xnum + i)));
		}

		shift_generate(s, BVLEFTSHIFT, bitwid, right, left_num, param);
	}

	// unsigned divison
	void bvudiv_generate(solver *s, unsigned long int xnum, unsigned long int ynum, int znum, int kindx, int kindy, int num_bits) {
		int m1 = add_bitvector(s, num_bits); // R
		int m2 = add_bitvector(s, num_bits);

		bvmult_noverflow_generate(s, SYMBOL, kindy, num_bits, znum, ynum, m2);  // z * y = m2
		bvplus_divmod_generate(s, m2, m1, xnum, num_bits, kindx);   // m2 + m1 = x			
		bvle_div_generate(s, ynum, m1, num_bits, kindy, SYMBOL); // y <= m1 <-> false
	}

	// unsigned modulo
	void bvumod_generate(solver *s, unsigned long int xnum, unsigned long int ynum, int znum, int kindx, int kindy, int num_bits) {
		int m1 = add_bitvector(s, num_bits);  //Q
		int m2 = add_bitvector(s, num_bits);

		bvmult_noverflow_generate(s, SYMBOL, kindy, num_bits, m1, ynum, m2);  // m1 * y = m2
		bvplus_divmod_generate(s, m2, znum, xnum, num_bits, kindx);   // m2 + z = x			
		bvle_div_generate(s, ynum, znum, num_bits, kindy, SYMBOL); // y <= z <-> false
	}

	void bveq_generate(solver *s, unsigned long int x, unsigned long int y, int b, int bitwid, int kindx, int kindy) // x=y <-> b
	{
		if (composed_flag == 1) {
			int right[2]; unsigned long int param[2];
			check_const(kindx, right, param, 0, x);
			check_const(kindy, right, param, 1, y);

			compose_generate(s, BVEQ_C, bitwid, right, b, param);
		}
		else {
			int m1 = add_bitvector(s, bitwid);
			int m2 = add_bitvector(s, bitwid);
			int m3 = add_bitvector(s, bitwid);
			int m4 = add_bitvector(s, bitwid);

			int right[2]; unsigned long int param[2];

			bvsub_generate(s, x, y, m1, bitwid, kindx, kindy); // x-y = m1
			bvuminus_generate(s, m1, m2, bitwid, SYMBOL); // -m1 =m2

			right[0] = m1;
			right[1] = m2;
			bitwise2_generate(s, BVOR, bitwid, right, m3, param); // m1 | m2 = m3

			right[0] = m3;
			bitwise1_generate(s, bitwid, right, m4, param); // ~m3 = m4 BVNEG

			creat_clause2(s, lit_neg(toLit(m4)), toLit(b));
			creat_clause2(s, toLit(m4), lit_neg(toLit(b)));
		}
	}
	void bvequall_generate(solver *s, unsigned long int x, unsigned long int y, int bitwid, int kindx) // x = y
	{
		int right[1]; unsigned long int param[1];
		check_const(kindx, right, param, 0, x);

		struct ws_flag* wat;
		wat = (struct ws_flag*)malloc(sizeof(struct ws_flag));
		wat->oper = BVEQUALL;
		wat->inqueue_flag = 1;
		wat->bitwids = (int*)malloc(sizeof(int));
		wat->bitwids[0] = bitwid;
		wat->arnum = (int*)malloc(sizeof(int) * 2);
		wat->arnum[0] = right[0]; // xnum
		wat->arnum[1] = y;
		wat->argu = (struct ul**)malloc(sizeof(struct ul*) * 2);
		wat->bound = (unsigned long int*)malloc(sizeof(unsigned long int));
		wat->bound[0] = param[0];  // const_x

		struct ul* argu0 = get_argu(s, right[0]); // x
		struct ul* argu1 = get_argu(s, y); // y

		wat->argu[0] = argu0; wat->argu[1] = argu1;

		if (argu0 != NULL)
			add_wordprop(s, argu0->word_num, wat);
		add_wordprop(s, argu1->word_num, wat);

		enque_initp(s, wat);
	}

	// b <-> x <= y 
	void bvle_generate(solver *s, unsigned long int x, unsigned long int y, int b, int bitwid, int kindx, int kindy) 
	{
		if (composed_flag == 1) {
			int right[2]; unsigned long int param[2];
			check_const(kindx, right, param, 0, x);
			check_const(kindy, right, param, 1, y);

			compose_generate(s, BVLE_C, bitwid, right, b, param);
		}
		else {
			int m0 = add_bitvector(s, bitwid);
			int m1 = add_bitvector(s, bitwid);
			int m2 = add_bitvector(s, bitwid);
			int m3 = add_bitvector(s, bitwid);
			int m4 = add_bitvector(s, bitwid);
			int m5 = add_bitvector(s, bitwid);
			int m6 = add_bitvector(s, bitwid);

			int right[2]; unsigned long int param[2];

			creat_clause2(s, lit_neg(toLit(m6)), toLit(b));
			creat_clause2(s, toLit(m6), lit_neg(toLit(b)));

			check_const(kindx, right, param, 0, x);
			bitwise1_generate(s, bitwid, right, m0, param); // ~x = m0, BVNEG

			right[0] = m0;
			check_const(kindy, right, param, 1, y);
			bitwise2_generate(s, BVOR, bitwid, right, m1, param);  // m0 | y = m1

			check_const(kindx, right, param, 0, x);
			check_const(kindy, right, param, 1, y);
			bitwise2_generate(s, BVXOR, bitwid, right, m2, param); // x ^ y = m2

			bvsub_generate(s, y, x, m3, bitwid, kindy, kindx); // y - x = m3

			right[0] = m3;
			bitwise1_generate(s, bitwid, right, m4, param); // ~m3 = m4 BVNEG

			right[0] = m2;
			right[1] = m4;
			bitwise2_generate(s, BVOR, bitwid, right, m5, param); // m2 | m4 = m5

			right[0] = m1;
			right[1] = m5;
			bitwise2_generate(s, BVAND, bitwid, right, m6, param); // m1 & m5 = m6 
		}
	}

	// x <= y <-> false
	void bvle_div_generate(solver *s, unsigned long int x, unsigned long int y, int bitwid, int kindx, int kindy) 
	{
		if (composed_flag == 1) {
			int right[2]; unsigned long int param[2];
			check_const(kindx, right, param, 0, x);
			check_const(kindy, right, param, 1, y);

			int b = add_boolean(s);
			compose_generate(s, BVLE_C, bitwid, right, b, param);
			creat_clause1(s, lit_neg(toLit(b)));
		}
		else {
			int m0 = add_bitvector(s, bitwid);
			int m1 = add_bitvector(s, bitwid);
			int m2 = add_bitvector(s, bitwid);
			int m3 = add_bitvector(s, bitwid);
			int m4 = add_bitvector(s, bitwid);
			int m5 = add_bitvector(s, bitwid);
			int m6 = add_bitvector(s, bitwid);

			int right[2]; unsigned long int param[2];

			creat_clause1(s, lit_neg(toLit(m6))); // -m6

			check_const(kindx, right, param, 0, x);
			bitwise1_generate(s, bitwid, right, m0, param); // ~x = m0 BVNEG

			right[0] = m0;
			check_const(kindy, right, param, 1, y);
			bitwise2_generate(s, BVOR, bitwid, right, m1, param);  // m0 | y = m1

			check_const(kindx, right, param, 0, x);
			check_const(kindy, right, param, 1, y);
			bitwise2_generate(s, BVXOR, bitwid, right, m2, param); // x ^ y = m2

			bvsub_generate(s, y, x, m3, bitwid, kindy, kindx); // y - x = m3

			right[0] = m3;
			bitwise1_generate(s, bitwid, right, m4, param); // ~m3 = m4 BVNEG

			right[0] = m2;
			right[1] = m4;
			bitwise2_generate(s, BVOR, bitwid, right, m5, param); // m2 | m4 = m5

			right[0] = m1;
			right[1] = m5;
			bitwise2_generate(s, BVAND, bitwid, right, m6, param); // m1 & m5 = m6 
		}
	}


	void iteterm_generate(solver *s, int xkind, int xnum, int ykind, unsigned long int ynum, int zkind, 
		unsigned long int znum, int left_num, int num_bits) {
		if (num_bits == 1) {
			TranstoClause_wite(s, xkind, xnum, ykind, ynum, zkind, znum, left_num);
		}
		else {
			int xbit;
			int xword = add_bitvector(s, num_bits);
			if (xkind == BVCONST) // for sdiv, srem	
			{
				if ((xnum >> (num_bits - 1)))
					xbit = -1; // TRUE
				else
					xbit = -2; // FALSE		
			}
			else if (xkind == FALSE) {
				xbit = -2;
			}
			else if (xkind == TRUE) {
				xbit = -1;
			}
			else {
				xbit = xnum;
			}

			bit_toword_generate(s, num_bits, xbit, xword);

			int right[3]; unsigned long int param[2];
			right[0] = xword;
			check_iteconst(ykind, right, param, 1, ynum);
			check_iteconst(zkind, right, param, 2, znum);
			iteparse_generate(s, num_bits, right, left_num, param);
		}
	}

	void bitwise2_general(solver *s, int xkind, unsigned long int xnum, int ykind, unsigned long int ynum, int left_num, 
		int expkind, int num_bits) {
		int right[2]; unsigned long int param[2];
		check_const(xkind, right, param, 0, xnum);
		check_const(ykind, right, param, 1, ynum);

		bitwise2_generate(s, expkind, num_bits, right, left_num, param);
	}

	/* traverse the AST tree, transfer it into basic bit-vector operations, and generate the corresponding bit-vector propagators*/
	int my_wwform(solver* s, const ASTNode& form) {
		ASTNodeSet::iterator it = ASTMemo.find(form);
		if (it != ASTMemo.end()) {
			form.Setvarnum_const(it->Getvarnum());
			return 1;
		}

		const Kind k = form.GetKind();

		switch (k) {
		case TRUE:
		{

		}
		break;
		case FALSE:
		{

		}
		break;
		case SYMBOL:
		{
			form.Setvarnum(add_boolean(s));
		}
		break;
		case BOOLEXTRACT:
		{
			form.Setvarnum(add_boolean(s));

			my_wwterm(s, form[0]);
			unsigned int index = form[1].GetUnsignedConst();
			TranstoClause_Boolex(s, form[0], index, form.Getvarnum());
		}
		break;
		case NOT:
		{
			form.Setvarnum(add_boolean(s));
			my_wwform(s, form[0]);
			TranstoClause_Bnot(s, form[0].GetKind(), form[0].Getvarnum(), form.Getvarnum());
		}
		break;
		case ITE:
		{
			form.Setvarnum(add_boolean(s));
			my_wwform(s, form[0]);
			my_wwform(s, form[1]);
			my_wwform(s, form[2]);
			TranstoClause_Bite(s, form[0].GetKind(), form[0].Getvarnum(), form[1].GetKind(), form[1].Getvarnum(), 
				form[2].GetKind(), form[2].Getvarnum(), form.Getvarnum());
		}
		break;
		case AND:
		{
			form.Setvarnum(add_boolean(s));

			ASTVec::const_iterator kids_end = form.end(); int counter = 1; int found = 0;
			int left = form.Getvarnum();
			for (ASTVec::const_iterator it = form.begin(); it != kids_end; it++) {
				my_wwform(s, *it);
				if ((*it).GetKind() == FALSE) {
					found = 1;
				}
				counter++;
			}


			if (found) // have false
			{
				creat_clause1(s, lit_neg(toLit(left)));
			}
			else // no false
			{
				int i = 0; int a;
				int *num = (int*)malloc(sizeof(int)*counter); // num[counter]

				for (ASTVec::const_iterator it = form.begin(); it != kids_end; it++) {
					if (it->GetKind() != TRUE) {
						a = it->Getvarnum();
						creat_clause2(s, toLit(a), lit_neg(toLit(left)));

						num[i] = lit_neg(toLit(a)); // for the next long clause
						i++;
					}
				}
				num[i] = toLit(left);
				i++; // number of the literals				  	
				creat_clausen(s, num, num + i);

				free(num);
			}
		}
		break;
		case OR:
		{
			form.Setvarnum(add_boolean(s));

			ASTVec::const_iterator kids_end = form.end();int counter = 1; int found = 0;
			int left = form.Getvarnum();
			for (ASTVec::const_iterator it = form.begin(); it != kids_end; it++) {
				my_wwform(s, *it);
				if ((*it).GetKind() == TRUE) {
					found = 1;
				}
				counter++;
			}


			if (found) // have true
			{
				creat_clause1(s, toLit(left));
			}
			else // no true
			{
				int i = 0; int a;
				int *num = (int*)malloc(sizeof(int)*counter); // num[counter]

				for (ASTVec::const_iterator it = form.begin(); it != kids_end; it++) {
					if ((*it).GetKind() != FALSE) {
						a = (*it).Getvarnum();
						creat_clause2(s, lit_neg(toLit(a)), toLit(left));

						num[i] = toLit(a); // for the next long clause					
						i++;
					}
				}
				num[i] = lit_neg(toLit(left));
				i++; // number of literals for the long clause

				creat_clausen(s, num, num + i);

				free(num);
			}
		}
		break;
		case IFF:
		{
			form.Setvarnum(add_boolean(s));
			assert(form.Degree() == 2);

			my_wwform(s, form[0]);
			my_wwform(s, form[1]);
			TranstoClause_Biff(s, form[0].GetKind(), form[0].Getvarnum(), form[1].GetKind(), form[1].Getvarnum(), 
				form.Getvarnum());
		}
		break;
		case XOR:
		{
			form.Setvarnum(add_boolean(s));
			assert(form.Degree() == 2);

			my_wwform(s, form[0]);
			my_wwform(s, form[1]);
			TranstoClause_Bxor(s, form[0].GetKind(), form[0].Getvarnum(), form[1].GetKind(), form[1].Getvarnum(), 
				form.Getvarnum());
		}
		break;
		case IMPLIES:
		{
			form.Setvarnum(add_boolean(s));
			assert(form.Degree() == 2);

			my_wwform(s, form[0]);
			my_wwform(s, form[1]);
			TranstoClause_implies(s, form[0].GetKind(), form[0].Getvarnum(), form[1].GetKind(), form[1].Getvarnum(), 
				form.Getvarnum());
		}
		break;
		case NAND:
		{
			form.Setvarnum(add_boolean(s));
			assert(form.Degree() == 2);

			my_wwform(s, form[0]);
			my_wwform(s, form[1]);

			int m1 = add_boolean(s);
			TranstoClause_bvand(s, form[0].GetKind(), form[0].Getvarnum(), form[1].GetKind(), form[1].Getvarnum(), m1);
			TranstoClause_Bnot_val(s, m1, form.Getvarnum());
		}
		break;
		case NOR:
		{
			form.Setvarnum(add_boolean(s));
			assert(form.Degree() == 2);

			my_wwform(s, form[0]);
			my_wwform(s, form[1]);

			int m1 = add_boolean(s);
			TranstoClause_bvor(s, form[0].GetKind(), form[0].Getvarnum(), form[1].GetKind(), form[1].Getvarnum(), m1);
			TranstoClause_Bnot_val(s, m1, form.Getvarnum());
		}
		break;
		case EQ:
		{
			form.Setvarnum(add_boolean(s));

			my_wwterm(s, form[0]);
			my_wwterm(s, form[1]);

			int num_bits = form[0].GetValueWidth();

			if (num_bits > 64) {
				printf("bitwid > 64! cannot solve!\n"); exit(0);
			}

			if (num_bits == 1) {
				TranstoClause_wiff(s, form[0].GetKind(), form[0].Getvarnum(), form[1].GetKind(), form[1].Getvarnum(), 
					form.Getvarnum());
			}
			else {
				//eq_num++; 
				bveq_generate(s, form[0].Getvarnum(), form[1].Getvarnum(), form.Getvarnum(), form[0].GetValueWidth(), 
					form[0].GetKind(), form[1].GetKind());
			}
		}
		break;
		// comparison operations
		case BVLE:
		{
			int num_bits = form[0].GetValueWidth();

			if (num_bits > 64) {
				printf("bitwid > 64! cannot solve!\n"); exit(0);
			}

			form.Setvarnum(add_boolean(s));

			my_wwterm(s, form[0]);
			my_wwterm(s, form[1]);

			bvle_generate(s, form[0].Getvarnum(), form[1].Getvarnum(), form.Getvarnum(), form[0].GetValueWidth(), 
				form[0].GetKind(), form[1].GetKind());
		}
		break;
		case BVGE:
		{
			int num_bits = form[0].GetValueWidth();

			if (num_bits > 64) {
				printf("bitwid > 64! cannot solve!\n"); exit(0);
			}

			form.Setvarnum(add_boolean(s));

			my_wwterm(s, form[0]);
			my_wwterm(s, form[1]);

			bvle_generate(s, form[1].Getvarnum(), form[0].Getvarnum(), form.Getvarnum(), form[0].GetValueWidth(), 
				form[1].GetKind(), form[0].GetKind());
		}
		break;
		case BVGT:
		{
			int num_bits = form[0].GetValueWidth();

			if (num_bits > 64) {
				printf("bitwid > 64! cannot solve!\n"); exit(0);
			}

			form.Setvarnum(add_boolean(s));

			my_wwterm(s, form[0]);
			my_wwterm(s, form[1]);

			int m1 = add_boolean(s);
			TranstoClause_Bnot_val(s, m1, form.Getvarnum());

			bvle_generate(s, form[0].Getvarnum(), form[1].Getvarnum(), m1, form[0].GetValueWidth(), form[0].GetKind(), 
				form[1].GetKind());
		}
		break;
		case BVLT:
		{
			int num_bits = form[0].GetValueWidth();

			if (num_bits > 64) {
				printf("bitwid > 64! cannot solve!\n"); exit(0);
			}

			form.Setvarnum(add_boolean(s));

			my_wwterm(s, form[0]);
			my_wwterm(s, form[1]);

			int m1 = add_boolean(s);
			TranstoClause_Bnot_val(s, m1, form.Getvarnum());

			bvle_generate(s, form[1].Getvarnum(), form[0].Getvarnum(), m1, form[0].GetValueWidth(), form[1].GetKind(), 
				form[0].GetKind());
		}
		break;
		case BVSLE:
		{
			int num_bits = form[0].GetValueWidth();

			if (num_bits > 64) {
				printf("bitwid > 64! cannot solve!\n"); exit(0);
			}

			form.Setvarnum(add_boolean(s));

			my_wwterm(s, form[0]);
			my_wwterm(s, form[1]);

			int m1 = add_boolean(s);

			bvle_generate(s, form[0].Getvarnum(), form[1].Getvarnum(), m1, form[0].GetValueWidth(), form[0].GetKind(), 
				form[1].GetKind());

			TranstoClause_signcompare(s, form[0], form[1], m1, form.Getvarnum());
		}
		break;
		case BVSGE:
		{
			int num_bits = form[0].GetValueWidth();

			if (num_bits > 64) {
				printf("bitwid > 64! cannot solve!\n"); exit(0);
			}

			form.Setvarnum(add_boolean(s));

			my_wwterm(s, form[0]);
			my_wwterm(s, form[1]);

			int m1 = add_boolean(s);

			bvle_generate(s, form[1].Getvarnum(), form[0].Getvarnum(), m1, form[0].GetValueWidth(), form[1].GetKind(), 
				form[0].GetKind());

			TranstoClause_signcompare(s, form[0], form[1], m1, form.Getvarnum());
		}
		break;
		case BVSGT:
		{
			int num_bits = form[0].GetValueWidth();

			if (num_bits > 64) {
				printf("bitwid > 64! cannot solve!\n"); exit(0);
			}

			form.Setvarnum(add_boolean(s));

			my_wwterm(s, form[0]);
			my_wwterm(s, form[1]);

			int m1 = add_boolean(s); int m2 = add_boolean(s);
			TranstoClause_Bnot_val(s, m1, m2);

			bvle_generate(s, form[0].Getvarnum(), form[1].Getvarnum(), m1, form[0].GetValueWidth(), form[0].GetKind(), 
				form[1].GetKind());

			TranstoClause_signcompare(s, form[0], form[1], m2, form.Getvarnum());
		}
		break;
		case BVSLT:
		{

			int num_bits = form[0].GetValueWidth();

			if (num_bits > 64) {
				printf("bitwid > 64! cannot solve!\n"); exit(0);
			}

			form.Setvarnum(add_boolean(s));

			my_wwterm(s, form[0]);
			my_wwterm(s, form[1]);

			int m1 = add_boolean(s); int m2 = add_boolean(s);
			TranstoClause_Bnot_val(s, m1, m2);

			bvle_generate(s, form[1].Getvarnum(), form[0].Getvarnum(), m1, form[0].GetValueWidth(), form[1].GetKind(), 
				form[0].GetKind());

			TranstoClause_signcompare(s, form[0], form[1], m2, form.Getvarnum());
		}
		break;
		default:
			FatalError("BBForm: Illegal kind: ", form);
			break;
		}

		ASTMemo.insert(form);
		return 0;
	}


	int my_wwterm(solver *s, const ASTNode& term) {
		ASTNodeSet::iterator it = ASTMemo.find(term);
		if (it != ASTMemo.end()) {
			term.Setvarnum_const((it->Getvarnum()));
			return 1;
		}

		const Kind k = term.GetKind();
		const int num_bits = term.GetValueWidth();

		switch (k) {
		case BVNEG: // bitwise not
		{
			term.Setvarnum(add_bitvector(s, num_bits));

			my_wwterm(s, term[0]);
			if (num_bits == 1) {
				TranstoClause_wnot(s, term[0].GetKind(), term[0].Getvarnum(), term.Getvarnum());
			}
			else {
				int right[1]; unsigned long int param[1];
				check_const(term[0].GetKind(), right, param, 0, term[0].Getvarnum());
				bitwise1_generate(s, num_bits, right, term.Getvarnum(), param); // BVNEG
			}
		}
		break;
		case BVLEFTSHIFT:
		case BVRIGHTSHIFT:
		{
			term.Setvarnum(add_bitvector(s, num_bits));

			my_wwterm(s, term[0]);
			my_wwterm(s, term[1]);

			assert(term[1].GetValueWidth() == num_bits);

			int kindz = term[1].GetKind(); int left_num = term.Getvarnum();
			if (num_bits == 1)	 // x = y << z
			{
				int znum = term[1].Getvarnum();
				if (kindz == BVCONST) {
					if (znum)
						kindz = TRUE;
					else
						kindz = FALSE;
				}
				TranstoClause_wite(s, kindz, znum, BVCONST, (uint64_t)0, term[0].GetKind(), term[0].Getvarnum(), left_num);
			}
			else {
				if (kindz == BVCONST) {
					int left_num = term.Getvarnum();
					int shift_amount = term[1].GetUnsignedConst();
					if (shift_amount == 0) {
						// left_num = x;
						bvequall_generate(s, term[0].Getvarnum(), left_num, num_bits, term[0].GetKind());
					}
					else if (shift_amount >= num_bits) {
						// left_num = 0;
						bvequall_generate(s, (uint64_t)0, left_num, num_bits, BVCONST);
					}
					else {
						int right[2]; unsigned long int param[1];

						check_const(term[0].GetKind(), right, param, 0, term[0].Getvarnum());
						right[1] = shift_amount;
						shift_generate(s, k, num_bits, right, left_num, param);
					}
				}
				else // x = y << z
				{
					int i;
					int care_zbits = (unsigned)log2(num_bits) + 1; int znum = term[1].Getvarnum(); int z_i;
					int previous_x = term[0].Getvarnum();  int kindy = term[0].GetKind(); int current_x;
					int right[2]; unsigned long int param[1];
					int shift_x; int shift_amount;

					//i = 0;
					shift_amount = 1; shift_x = add_bitvector(s, num_bits);

					check_const(term[0].GetKind(), right, param, 0, previous_x);
					right[1] = shift_amount;
					shift_generate(s, k, num_bits, right, shift_x, param);

					current_x = add_bitvector(s, num_bits);
					z_i = znum + num_bits - 1;
					iteterm_generate(s, SYMBOL, z_i, SYMBOL, shift_x, kindy, previous_x, current_x, num_bits);
					previous_x = current_x;

					for (i = 1; i < care_zbits; i++) {
						shift_amount = 1 << i;

						if (shift_amount < num_bits) {
							shift_x = add_bitvector(s, num_bits);
							right[0] = previous_x;
							right[1] = shift_amount;
							shift_generate(s, k, num_bits, right, shift_x, param);

							current_x = add_bitvector(s, num_bits);
							z_i = znum + num_bits - 1 - i;

							iteterm_generate(s, SYMBOL, z_i, SYMBOL, shift_x, SYMBOL, previous_x, current_x, num_bits);
							previous_x = current_x;
						}
						else {
							care_zbits = i; // reset care_zbits;
							break;
						}
					}

					int or_z = add_boolean(s); int count = num_bits - care_zbits;
					int* num = (int*)malloc(sizeof(int)*(count + 1)); // num[count+1]

					for (i = 0; i < count; i++) {
						creat_clause2(s, lit_neg(toLit(znum + i)), toLit(or_z));

						num[i] = toLit(znum + i);
					}
					num[i] = lit_neg(toLit(or_z));
					i++; // number of the next clause
					creat_clausen(s, num, num + i);

					iteterm_generate(s, SYMBOL, or_z, BVCONST, (uint64_t)0, SYMBOL, current_x, left_num, num_bits);

					free(num);
				}
			}
		}
		break;
		case BVSRSHIFT:
		{
			term.Setvarnum(add_bitvector(s, num_bits));

			my_wwterm(s, term[0]);
			my_wwterm(s, term[1]);

			assert(term[1].GetValueWidth() == num_bits);

			int kindz = term[1].GetKind(); unsigned long int znum = term[1].Getvarnum();
			int kindy = term[0].GetKind(); unsigned long int ynum = term[0].Getvarnum();
			int left_num = term.Getvarnum();
			if (num_bits == 1)	 // left_x = y >> z
			{
				if (kindy == BVCONST) {
					if (ynum)
						creat_clause1(s, toLit(left_num));
					else
						creat_clause1(s, lit_neg(toLit(left_num)));

				}
				else {
					creat_clause2(s, toLit(left_num), lit_neg(toLit(ynum)));
					creat_clause2(s, lit_neg(toLit(left_num)), toLit(ynum));
				}
			}
			else {
				if (kindz == BVCONST) // x = y << z;
				{
					int left_num = term.Getvarnum();
					int shift_amount = term[1].GetUnsignedConst();
					if (shift_amount == 0) {
						// left_num = y;
						bvequall_generate(s, term[0].Getvarnum(), left_num, num_bits, term[0].GetKind());
					}
					else if (shift_amount >= num_bits) {
						// left_num = y_begin_word;
						int ybit; int kindy = term[0].GetKind(); unsigned long int ynum = term[0].Getvarnum();
						if (kindy == BVCONST) {
							if ((ynum >> (num_bits - 1)))
								ybit = -1;
							else
								ybit = -2;
						}
						else {
							ybit = ynum;
						}

						if (ybit > 0)	// y is not const			
							bit_toword_generate(s, num_bits, ybit, left_num);
						else
							bit_toword_generate(s, num_bits, ybit, left_num);
					}
					else {
						int right[2]; unsigned long int param[1];

						check_const(term[0].GetKind(), right, param, 0, term[0].Getvarnum());
						right[1] = shift_amount;
						shift_generate(s, k, num_bits, right, left_num, param);
					}
				}
				else // x = y << z
				{
					int i;
					int care_zbits = (unsigned)log2(num_bits) + 1;  int z_i;
					int current_x; int previous_x;
					int right[2]; unsigned long int param[1];
					int shift_x; int shift_amount;

					//i = 0;
					shift_amount = 1; shift_x = add_bitvector(s, num_bits);
					check_const(kindy, right, param, 0, ynum);
					right[1] = shift_amount;
					shift_generate(s, k, num_bits, right, shift_x, param);
					current_x = add_bitvector(s, num_bits);
					z_i = znum + num_bits - 1;
					iteterm_generate(s, SYMBOL, z_i, SYMBOL, shift_x, kindy, ynum, current_x, num_bits);
					previous_x = current_x;

					for (i = 1; i < care_zbits; i++) {
						shift_amount = 1 << i;

						if (shift_amount < num_bits) {
							shift_x = add_bitvector(s, num_bits);
							right[0] = previous_x;
							right[1] = shift_amount;
							shift_generate(s, k, num_bits, right, shift_x, param);

							current_x = add_bitvector(s, num_bits);
							z_i = znum + num_bits - 1 - i;

							iteterm_generate(s, SYMBOL, z_i, SYMBOL, shift_x, SYMBOL, previous_x, current_x, num_bits);
							previous_x = current_x;
						}
						else {
							care_zbits = i; // reset care_zbits;
							break;
						}
					}

					int or_z = add_boolean(s); int count = num_bits - care_zbits;
					int* num = (int*)malloc(sizeof(int)*(count + 1)); // num[counter+1]

					for (i = 0; i < count; i++) {
						creat_clause2(s, lit_neg(toLit(znum + i)), toLit(or_z));

						num[i] = toLit(znum + i);
					}
					num[i] = lit_neg(toLit(or_z));
					i++; // number of the next clause
					creat_clausen(s, num, num + i);

					int ybit;
					if (kindy == BVCONST) {
						if ((ynum >> (num_bits - 1)))
							ybit = -1;
						else
							ybit = -2;
					}
					else {
						ybit = ynum;
					}

					int yword = add_bitvector(s, num_bits);
					if (ybit > 0)
						bit_toword_generate(s, num_bits, ybit, yword);
					else
						bit_toword_generate(s, num_bits, ybit, yword);

					iteterm_generate(s, SYMBOL, or_z, SYMBOL, yword, SYMBOL, current_x, left_num, num_bits);

					free(num);
				}
			}
		}
		break;
		case ITE:
		{
			term.Setvarnum(add_bitvector(s, num_bits));

			my_wwform(s, term[0]);
			my_wwterm(s, term[1]);
			my_wwterm(s, term[2]);

			iteterm_generate(s, term[0].GetKind(), term[0].Getvarnum(), term[1].GetKind(), term[1].Getvarnum(), 
				term[2].GetKind(), term[2].Getvarnum(), term.Getvarnum(), num_bits);

		}
		break;

		case BVZX:
		case BVSX:
		{
			term.Setvarnum(add_bitvector(s, num_bits));

			my_wwterm(s, term[0]);
			int right[2]; unsigned long int param[1];
			check_const(term[0].GetKind(), right, param, 0, term[0].Getvarnum());
			right[1] = term[0].GetValueWidth(); // orgbits

			extend_generate(s, k, num_bits - right[1], right, term.Getvarnum(), param); // num_bits-right[1] is addbits
		}
		break;
		case BVEXTRACT:
		{
			term.Setvarnum(add_bitvector(s, num_bits));

			my_wwterm(s, term[0]);

			int high = term[1].GetUnsignedConst(); int low = term[2].GetUnsignedConst();


			if (high == low) {
				TranstoClause_Boolex(s, term[0], low, term.Getvarnum());
			}
			else {
				int right[1]; unsigned long int param[1];
				check_const(term[0].GetKind(), right, param, 0, term[0].Getvarnum());
				extract_generate(s, term[0].GetValueWidth(), right, term.Getvarnum(), param, high, low);
			}
		}
		break;
		case BVCONCAT:
		{
			term.Setvarnum(add_bitvector(s, num_bits));

			my_wwterm(s, term[0]);
			my_wwterm(s, term[1]);
			int right[2]; unsigned long int param[2];
			check_const(term[0].GetKind(), right, param, 0, term[0].Getvarnum());
			check_const(term[1].GetKind(), right, param, 1, term[1].Getvarnum());
			concate_generate(s, num_bits, right, term.Getvarnum(), param, term[0].GetValueWidth(), term[1].GetValueWidth());
		}
		break;
		case BVPLUS:
		{
			term.Setvarnum(add_bitvector(s, num_bits));

			int i; int m1 = 0; int m2 = 0; int term_num = term.Degree();

			my_wwterm(s, term[0]);

			for (i = 1; i < term_num - 1; i++) {
				my_wwterm(s, term[i]);
				m2 = m1; // the former one
				m1 = add_bitvector(s, num_bits);
				if (m2 == 0)

					bvplus_generate(s, term[i - 1].Getvarnum(), term[i].Getvarnum(), m1, num_bits, term[i - 1].GetKind(), 
						term[i].GetKind());
				else
					bvplus_generate(s, term[i].Getvarnum(), m2, m1, num_bits, term[i].GetKind(), SYMBOL);
			}
			my_wwterm(s, term[i]);
			if (m1 == 0) {
				bvplus_generate(s, term[i - 1].Getvarnum(), term[i].Getvarnum(), term.Getvarnum(), num_bits, 
					term[i - 1].GetKind(), term[i].GetKind());
			}
			else
				bvplus_generate(s, term[i].Getvarnum(), m1, term.Getvarnum(), num_bits, term[i].GetKind(), SYMBOL);

		}
		break;
		case BVUMINUS: //bvneg, bvnot +1
		{
			term.Setvarnum(add_bitvector(s, num_bits));

			my_wwterm(s, term[0]);
			bvuminus_generate(s, term[0].Getvarnum(), term.Getvarnum(), num_bits, term[0].GetKind());

		}
		break;
		case BVSUB:
		{
			term.Setvarnum(add_bitvector(s, num_bits));

			my_wwterm(s, term[0]);
			my_wwterm(s, term[1]);
			bvsub_generate(s, term[0].Getvarnum(), term[1].Getvarnum(), term.Getvarnum(), num_bits, term[0].GetKind(), 
				term[1].GetKind());
		}
		break;
		case BVMULT:
		{
			term.Setvarnum(add_bitvector(s, num_bits));

			my_wwterm(s, term[0]);
			my_wwterm(s, term[1]);

			bvmult_generate(s, term[0].GetKind(), term[1].GetKind(), num_bits, term[0].Getvarnum(), term[1].Getvarnum(), term.Getvarnum());
		}
		break;
		case SBVDIV: // n = a bvsdiv b;
		{
			term.Setvarnum(add_bitvector(s, num_bits));

			my_wwterm(s, term[0]);
			my_wwterm(s, term[1]);

			unsigned long int a = term[0].Getvarnum(); int kinda = term[0].GetKind();
			unsigned long int b = term[1].Getvarnum(); int kindb = term[1].GetKind();
			unsigned long int n = term.Getvarnum();

			int neg_a = add_bitvector(s, num_bits);
			int neg_b = add_bitvector(s, num_bits);

			int abs_a = add_bitvector(s, num_bits);
			int abs_b = add_bitvector(s, num_bits);


			bvuminus_generate(s, a, neg_a, num_bits, kinda);  // neg_a = -a
			bvuminus_generate(s, b, neg_b, num_bits, kindb);  // neg_b = -b

			iteterm_generate(s, kinda, a, SYMBOL, neg_a, kinda, a, abs_a, num_bits); // |a| = ite(sign_a, -a, a)	
			iteterm_generate(s, kindb, b, SYMBOL, neg_b, kindb, b, abs_b, num_bits); // |b| = ite(sign_b, -b, b)

			int result_u = add_bitvector(s, num_bits);
			int result_neg = add_bitvector(s, num_bits);

			bvudiv_generate(s, abs_a, abs_b, result_u, SYMBOL, SYMBOL, num_bits);	 // result_u = |a| / |b|	
			bvuminus_generate(s, result_u, result_neg, num_bits, SYMBOL); // result_neg = -result_u

			int condition = add_boolean(s);
			TranstoClause_signxor(s, term[0], term[1], condition, num_bits); // condition = sign_b ^ sign_a;

			iteterm_generate(s, SYMBOL, condition, SYMBOL, result_neg, SYMBOL, result_u, n, num_bits); // ite(condi, -UR, UR);
		}
		break;
		case SBVMOD:
		{
			term.Setvarnum(add_bitvector(s, num_bits));

			my_wwterm(s, term[0]);
			my_wwterm(s, term[1]);

			unsigned long int a = term[0].Getvarnum(); int kinda = term[0].GetKind();
			unsigned long int b = term[1].Getvarnum(); int kindb = term[1].GetKind();
			unsigned long int n = term.Getvarnum();

			int neg_a = add_bitvector(s, num_bits);
			int neg_b = add_bitvector(s, num_bits);

			int abs_a = add_bitvector(s, num_bits);
			int abs_b = add_bitvector(s, num_bits);

			bvuminus_generate(s, a, neg_a, num_bits, kinda);  // neg_a = -a
			bvuminus_generate(s, b, neg_b, num_bits, kindb);  // neg_b = -b

			iteterm_generate(s, kinda, a, SYMBOL, neg_a, kinda, a, abs_a, num_bits); // |a| = ite(a< 0, -a, a)	
			iteterm_generate(s, kindb, b, SYMBOL, neg_b, kindb, b, abs_b, num_bits); // |b| = ite(b< 0, -b, b)

			int urem = add_bitvector(s, num_bits);
			int urem_neg = add_bitvector(s, num_bits);
			int srem = add_bitvector(s, num_bits);

			bvumod_generate(s, abs_a, abs_b, urem, SYMBOL, SYMBOL, num_bits);	 // urem = |a| umod |b|	
			bvuminus_generate(s, urem, urem_neg, num_bits, SYMBOL); // result_neg = -urem			
			iteterm_generate(s, kinda, a, SYMBOL, urem_neg, SYMBOL, urem, srem, num_bits);

			int xor_node = add_boolean(s);
			TranstoClause_signxor(s, term[0], term[1], xor_node, num_bits); // xor_node = sign_b ^ sign_a;
			int nez = add_boolean(s);
			int eqz = add_boolean(s);

			bveq_generate(s, srem, (uint64_t)0, eqz, num_bits, SYMBOL, BVCONST);

			TranstoClause_Bnot_val(s, eqz, nez);

			int condition = add_boolean(s);
			TranstoClause_bvand_val(s, xor_node, nez, condition);

			int srem_plus = add_bitvector(s, num_bits);

			bvplus_generate(s, srem, b, srem_plus, num_bits, SYMBOL, kindb);
			iteterm_generate(s, SYMBOL, condition, SYMBOL, srem_plus, SYMBOL, srem, n, num_bits);

		}
		break;
		case SBVREM: // n = a bvsrem b
		{
			term.Setvarnum(add_bitvector(s, num_bits));

			my_wwterm(s, term[0]);
			my_wwterm(s, term[1]);

			unsigned long int a = term[0].Getvarnum(); int kinda = term[0].GetKind();
			unsigned long int b = term[1].Getvarnum(); int kindb = term[1].GetKind();
			unsigned long int n = term.Getvarnum();

			int neg_a = add_bitvector(s, num_bits);
			int neg_b = add_bitvector(s, num_bits);

			int abs_a = add_bitvector(s, num_bits);
			int abs_b = add_bitvector(s, num_bits);

			bvuminus_generate(s, a, neg_a, num_bits, kinda);  // neg_a = -a
			bvuminus_generate(s, b, neg_b, num_bits, kindb);  // neg_b = -b

			iteterm_generate(s, kinda, a, SYMBOL, neg_a, kinda, a, abs_a, num_bits); // |a| = ite(a< 0, -a, a)	
			iteterm_generate(s, kindb, b, SYMBOL, neg_b, kindb, b, abs_b, num_bits); // |b| = ite(b< 0, -b, b)

			int result_u = add_bitvector(s, num_bits);
			int result_neg = add_bitvector(s, num_bits);

			bvumod_generate(s, abs_a, abs_b, result_u, SYMBOL, SYMBOL, num_bits);	 // result_u = |a| umod |b|	
			bvuminus_generate(s, result_u, result_neg, num_bits, SYMBOL); // result_neg = -result_u

			iteterm_generate(s, kinda, a, SYMBOL, result_neg, SYMBOL, result_u, n, num_bits);
			// n = ite(les_zero_a, -UR, UR);

		}
		break;
		case BVDIV: // z = x bvudiv y
		{
			term.Setvarnum(add_bitvector(s, num_bits));

			my_wwterm(s, term[0]);
			my_wwterm(s, term[1]);

			unsigned long int xnum = term[0].Getvarnum(); int kindx = term[0].GetKind();
			unsigned long int ynum = term[1].Getvarnum(); int kindy = term[1].GetKind();
			unsigned long int znum = term.Getvarnum();

			bvudiv_generate(s, xnum, ynum, znum, kindx, kindy, num_bits);
		}
		break;
		case BVMOD: // z = x bvumod y
		{
			term.Setvarnum(add_bitvector(s, num_bits));

			my_wwterm(s, term[0]);
			my_wwterm(s, term[1]);

			unsigned long int xnum = term[0].Getvarnum(); int kindx = term[0].GetKind();
			unsigned long int ynum = term[1].Getvarnum(); int kindy = term[1].GetKind();
			unsigned long int znum = term.Getvarnum();

			bvumod_generate(s, xnum, ynum, znum, kindx, kindy, num_bits);
		}
		break;
		//bitwise operations
		case BVXOR:
		case BVAND:
		case BVOR:
		case BVXNOR:
		case BVNOR:
		case BVNAND:
		{
			term.Setvarnum(add_bitvector(s, num_bits));

			if (num_bits == 1) {
				int i; int m1 = 0; int m2 = 0; int term_num = term.Degree();

				my_wwterm(s, term[0]);
				for (i = 1; i < term_num - 1; i++) {
					my_wwterm(s, term[i]);
					m2 = m1; // the former one
					m1 = add_boolean(s);
					if (m2 == 0)
						TranstoClause_bitwise_onebit(s, term[i - 1].GetKind(), term[i - 1].Getvarnum(), term[i].GetKind(), 
							term[i].Getvarnum(), m1, k);
					else
						TranstoClause_bitwise_onebit(s, term[i].GetKind(), term[i].Getvarnum(), SYMBOL, m2, m1, k);
				}
				my_wwterm(s, term[i]);
				if (m1 == 0) {

					TranstoClause_bitwise_onebit(s, term[i - 1].GetKind(), term[i - 1].Getvarnum(), term[i].GetKind(), 
						term[i].Getvarnum(), term.Getvarnum(), k);

				}
				else
					TranstoClause_bitwise_onebit(s, term[i].GetKind(), term[i].Getvarnum(), SYMBOL, m1, term.Getvarnum(), k);
			}
			else {
				int i; int m1 = 0; int m2 = 0; int term_num = term.Degree();

				my_wwterm(s, term[0]);
				for (i = 1; i < term_num - 1; i++) {
					my_wwterm(s, term[i]);
					m2 = m1; // the former one
					m1 = add_bitvector(s, num_bits);

					if (m2 == 0) {
						bitwise2_general(s, term[i - 1].GetKind(), term[i - 1].Getvarnum(), term[i].GetKind(), 
							term[i].Getvarnum(), m1, k, num_bits);
					}
					else {
						bitwise2_general(s, term[i].GetKind(), term[i].Getvarnum(), SYMBOL, m2, m1, k, num_bits);
					}
				}
				my_wwterm(s, term[i]);
				if (m1 == 0) {
					bitwise2_general(s, term[i - 1].GetKind(), term[i - 1].Getvarnum(), term[i].GetKind(), term[i].Getvarnum(), term.Getvarnum(), k, num_bits);
				}
				else
					bitwise2_general(s, term[i].GetKind(), term[i].Getvarnum(), SYMBOL, m1, term.Getvarnum(), k, num_bits);
			}
		}
		break;
		case SYMBOL:
		{
			term.Setvarnum(add_bitvector(s, num_bits));
		}
		break;
		case BVCONST:
		{
			if (num_bits <= 32) {
				term.Setvarnum_const(term.GetUnsignedConst());
			}
			else {
				CBV bv = term.GetBVConst(); unsigned long int constnum = (uint64_t)0;
				for (unsigned int i = 0; i < num_bits; i++) {
					if ((CONSTANTBV::BitVector_bit_test(bv, i))) {
						constnum = ((uint64_t)1 << i) | constnum;
					}
				}
				term.Setvarnum_const(constnum);
			}
		}
		break;
		default:
			FatalError("BBTerm: Illegal kind to BBTerm", term);
		}

		ASTMemo.insert(term);
		return 0;
	}

	// traverse the AST tree, and get the value for each features
	int  my_wwform_check(const ASTNode& form) {
		ASTNodeSet::iterator it = ASTMemo_check.find(form);
		if (it != ASTMemo_check.end()) {
			return 1;
		}

		const Kind k = form.GetKind();

		switch (k) {
		case TRUE:
		case FALSE:
		{
			break;
		}
		case SYMBOL:
		{
			symbool_num++;
			break;
		}
		case BOOLEXTRACT:
		{
			form_num++;

			my_wwterm_check(form[0]);
			break;
		}
		case NOT:
		{
			form_num++;

			my_wwform_check(form[0]);
			break;
		}
		case ITE:
		{
			form_num++;

			my_wwform_check(form[0]);
			my_wwform_check(form[1]);
			my_wwform_check(form[2]);
			break;
		}
		case AND:
		case OR:
		case NAND:
		case NOR:
		case IFF:
		case XOR:
		case IMPLIES:
		{
			form_num++;

			ASTVec::const_iterator kids_end = form.end();
			for (ASTVec::const_iterator it = form.begin(); it != kids_end; it++) {
				my_wwform_check(*it);
			}
			break;
		}
		case EQ:
		{
			int num_bits = form[0].GetValueWidth();

			if (num_bits > 64) {
				printf("bitwid > 64! cannot solve! \n"); exit(0);
			}

			if (num_bits == 1) {
				form_num++;
			}
			else {
				whole_num++;
				eq_num++;
				arith_bitwid = arith_bitwid + num_bits;
			}

			my_wwterm_check(form[0]);
			my_wwterm_check(form[1]);
			break;
		}
		case BVLE:
		case BVGE:
		case BVGT:
		case BVLT:
		case BVSLE:
		case BVSGE:
		case BVSGT:
		case BVSLT:
		{
			int num_bits = form[0].GetValueWidth();

			if (num_bits > 64) {
				printf("bitwid > 64! cannot solve!\n"); exit(0);
			}

			if (num_bits == 1) {
				form_num++;
			}
			else {
				whole_num++;
				ineq_num++;
				arith_bitwid = arith_bitwid + num_bits;
			}

			my_wwterm_check(form[0]);
			my_wwterm_check(form[1]);
			break;
		}
		default:
			FatalError("BBForm: Illegal kind: ", form);
			break;
		}

		ASTMemo_check.insert(form);
		return 0;
	}

	int  my_wwterm_check(const ASTNode& term) {
		ASTNodeSet::iterator it = ASTMemo_check.find(term);
		if (it != ASTMemo_check.end()) {
			return 1;
		}

		const Kind k = term.GetKind();

		if (!is_Term_kind(k))
			FatalError("BBTerm: Illegal kind to BBTerm", term);

		const unsigned int num_bits = term.GetValueWidth();

		if (num_bits > 64) {
			printf("bitwid > 64! cannot solve!\n"); exit(0);
		}

		switch (k) {
		case BVNEG: // bitwise not
		{
			if (num_bits == 1) {
				form_num++;
			}
			else {
				bitwise_num++;
				whole_num++;
				logic_bitwid = logic_bitwid + num_bits;
			}
			my_wwterm_check(term[0]);
		}
		break;

		case BVLEFTSHIFT:
		case BVRIGHTSHIFT:
		{
			int kindz = term[1].GetKind();
			if (num_bits == 1) {
				form_num++;
			}
			else {
				whole_num++;
				logic_bitwid = logic_bitwid + num_bits;

				if (kindz == BVCONST) {
					shift_con_num++;
				}
				else {
					shift_noncon_num++;
				}
			}

			my_wwterm_check(term[0]);
			my_wwterm_check(term[1]);
		}
		break;

		case BVSRSHIFT:
		{
			int kindz = term[1].GetKind();

			if (num_bits == 1) {
				form_num++;
			}
			else {
				whole_num++;
				sign_num++;
				logic_bitwid = logic_bitwid + num_bits;

				if (kindz == BVCONST) {
					shift_con_num++;
				}
				else {
					shift_noncon_num++;
				}
			}

			my_wwterm_check(term[0]);
			my_wwterm_check(term[1]);
		}
		break;

		case ITE:
		{
			if (num_bits == 1) {
				form_num++;
			}
			else {
				whole_num++;
				ite_num++;
				logic_bitwid = logic_bitwid + num_bits;
			}

			my_wwform_check(term[0]);
			my_wwterm_check(term[1]);
			my_wwterm_check(term[2]);
		}
		break;

		case BVZX:
		{
			whole_num++;
			extend_num++;
			logic_bitwid = logic_bitwid + num_bits;

			my_wwterm_check(term[0]);
		}
		break;
		case BVSX:
		{
			whole_num++;
			extend_num++;
			sign_num++;
			logic_bitwid = logic_bitwid + num_bits;

			my_wwterm_check(term[0]);
		}
		break;
		case BVEXTRACT:
		{
			int high = term[1].GetUnsignedConst(); int low = term[2].GetUnsignedConst();

			if (high == low) {
				form_num++;
			}
			else {
				whole_num++;
				extcon_num++;
				logic_bitwid = logic_bitwid + num_bits;
			}

			my_wwterm_check(term[0]);
		}
		break;
		case BVCONCAT:
		{
			whole_num++;
			extcon_num++;
			logic_bitwid = logic_bitwid + num_bits;

			my_wwterm_check(term[0]);
			my_wwterm_check(term[1]);
		}
		break;
		case BVPLUS:
		{
			ASTVec::const_iterator it = term.begin();
			ASTVec::const_iterator kids_end = term.end();
			my_wwterm_check(*it);
			for (++it; it < kids_end; it++) {
				whole_num++;
				bvplus_num++;
				arith_bitwid = arith_bitwid + num_bits;

				my_wwterm_check(*it);
			}

		}
		break;
		case BVUMINUS: //bvneg, bvnot +1
		{
			whole_num++;
			uminus_num++;
			arith_bitwid = arith_bitwid + num_bits;

			my_wwterm_check(term[0]);
		}
		break;
		case BVSUB:
		{
			whole_num++;
			bvsub_num++;
			arith_bitwid = arith_bitwid + num_bits;

			my_wwterm_check(term[0]);
			my_wwterm_check(term[1]);
		}
		break;
		case BVMULT:
		{
			whole_num++;
			arith_bitwid = arith_bitwid + num_bits;

			int kindx = term[0].GetKind(); int kindy = term[1].GetKind();
			if (kindx == BVCONST && kindy != BVCONST) {
				mult_con_num++;
			}
			else if (kindy == BVCONST && kindx != BVCONST) {
				mult_con_num++;
			}
			else {
				mult_num++;
			}

			my_wwterm_check(term[0]);
			my_wwterm_check(term[1]);
		}
		break;
		case SBVDIV: // n = a bvsdiv b;
		{
			whole_num++;
			div_num++;
			arith_bitwid = arith_bitwid + num_bits;

			mult_num++;

			my_wwterm_check(term[0]);
			my_wwterm_check(term[1]);
		}
		break;
		case SBVMOD:
		{
			whole_num++;
			div_num++;
			arith_bitwid = arith_bitwid + num_bits;

			mult_num++;

			my_wwterm_check(term[0]);
			my_wwterm_check(term[1]);
		}
		break;
		case SBVREM: // n = a bvsrem b
		{
			whole_num++;
			div_num++;
			arith_bitwid = arith_bitwid + num_bits;

			mult_num++;

			my_wwterm_check(term[0]);
			my_wwterm_check(term[1]);
		}
		break;
		case BVDIV: // z = x bvudiv y
		{
			whole_num++;
			udiv_num++;
			arith_bitwid = arith_bitwid + num_bits;

			int kindy = term[1].GetKind();
			if (kindy == BVCONST) {
				mult_con_num++;
			}
			else {
				mult_num++;
			}

			my_wwterm_check(term[0]);
			my_wwterm_check(term[1]);
		}
		break;
		case BVMOD: // z = x bvumod y
		{
			whole_num++;
			udiv_num++;
			arith_bitwid = arith_bitwid + num_bits;

			int kindy = term[1].GetKind();
			if (kindy == BVCONST) {
				mult_con_num++;
			}
			else {
				mult_num++;
			}

			my_wwterm_check(term[0]);
			my_wwterm_check(term[1]);
		}
		break;
		//bitwise operations
		case BVXOR:
		case BVAND:
		case BVOR:
		case BVXNOR:
		case BVNOR:
		case BVNAND:
		{
			if (num_bits == 1) {
				ASTVec::const_iterator it = term.begin();
				ASTVec::const_iterator kids_end = term.end();
				my_wwterm_check(*it);
				for (++it; it < kids_end; it++) {
					form_num++;
					my_wwterm_check(*it);
				}
			}
			else {
				ASTVec::const_iterator it = term.begin();
				ASTVec::const_iterator kids_end = term.end();
				my_wwterm_check(*it);
				for (++it; it < kids_end; it++) {
					whole_num++;
					bitwise_num++;
					logic_bitwid = logic_bitwid + num_bits;

					my_wwterm_check(*it);
				}
			}
		}
		break;
		case SYMBOL:
		{
			symvec_num++;
		}
		break;
		case BVCONST:
		{
			const_num++;
		}
		break;
		default:
			FatalError("BBTerm: Illegal kind to BBTerm", term);
		}

		ASTMemo_check.insert(term);
		return 0;
	}


} // stp namespace
