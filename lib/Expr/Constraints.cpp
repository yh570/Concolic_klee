//===-- Constraints.cpp ---------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Constraints.h"

#include "klee/util/ExprPPrinter.h"
#include "klee/util/ExprVisitor.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Expr.h"

#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"

#include <map>
#include <queue>

using namespace klee;

namespace {
  llvm::cl::opt<bool>
  RewriteEqualities("rewrite-equalities",
		    llvm::cl::init(true),
		    llvm::cl::desc("Rewrite existing constraints when an equality with a constant is added (default=on)"));
}


class ExprReplaceVisitor : public ExprVisitor {
private:
  ref<Expr> src, dst;

public:
  ExprReplaceVisitor(ref<Expr> _src, ref<Expr> _dst) : src(_src), dst(_dst) {}

  Action visitExpr(const Expr &e) {
    if (e == *src.get()) {
      return Action::changeTo(dst);
    } else {
      return Action::doChildren();
    }
  }

  Action visitExprPost(const Expr &e) {
    if (e == *src.get()) {
      return Action::changeTo(dst);
    } else {
      return Action::doChildren();
    }
  }
};

class ExprReplaceVisitor2 : public ExprVisitor {
private:
  const std::map< ref<Expr>, ref<Expr> > &replacements;

public:
  ExprReplaceVisitor2(const std::map< ref<Expr>, ref<Expr> > &_replacements) 
    : ExprVisitor(true),
      replacements(_replacements) {}

  Action visitExprPost(const Expr &e) {
    std::map< ref<Expr>, ref<Expr> >::const_iterator it =
      replacements.find(ref<Expr>(const_cast<Expr*>(&e)));
    if (it!=replacements.end()) {
      return Action::changeTo(it->second);
    } else {
      return Action::doChildren();
    }
  }
};

bool ConstraintManager::rewriteConstraints(ExprVisitor &visitor) {
  ConstraintManager::constraints_ty old;
  bool changed = false;

  constraints.swap(old);
  for (ConstraintManager::constraints_ty::iterator 
         it = old.begin(), ie = old.end(); it != ie; ++it) {
    ref<Expr> &ce = *it;
    ref<Expr> e = visitor.visit(ce);

    if (e!=ce) {
      addConstraintInternal(e); // enable further reductions
      changed = true;
    } else {
      constraints.push_back(ce);
    }
  }

  return changed;
}

void ConstraintManager::simplifyForValidConstraint(ref<Expr> e) {
  // XXX 
}

ref<Expr> ConstraintManager::simplifyAddressExpr(ref<Expr> e) {
  if (isa<ConstantExpr>(e))
    return e;
  if (constraints.size() < 1)
    return e;
  std::map< ref<Expr>, ref<Expr> > equalities;
  ref<Expr> constraint = constraints[constraints.size() - 1];
  if (const EqExpr *ee = dyn_cast<EqExpr>(constraint)) {
    if (isa<ConstantExpr>(ee->left)) {
      equalities.insert(std::make_pair(ee->right, ee->left));
    } else {
      equalities.insert(std::make_pair(constraint, ConstantExpr::alloc(1, Expr::Bool)));
    }
  } else if (const UltExpr *ue = dyn_cast<UltExpr> (constraint)) {
    if (isa<ConstantExpr>(ue->right)) {
      if (ue->right->isOne()) {
        equalities.insert(std::make_pair(ue->left, ConstantExpr::create(0, 64)));  
      } 
      else {
        std::queue<ref<Expr>> search_queue;
        search_queue.push(ue->left);
        unsigned int count = 0;
        while (!search_queue.empty()) {
          ref<Expr> cur = search_queue.front();
          search_queue.pop();
          /*std::string Str;
          llvm::raw_string_ostream info(Str);
          info << cur;
          printf("Searching node:\n%s\n", info.str().c_str());*/
          if (const ConstantExpr *ce = dyn_cast<ConstantExpr>(cur.get())) {
            continue;
          }
          else if (const ReadExpr *re = dyn_cast<ReadExpr>(cur.get())) {
            continue;
          }
          else if (const ZExtExpr *ue = dyn_cast<ZExtExpr>(cur.get())) {
            search_queue.push(ue->getKid(0));
          }
          else if (const MulExpr *me = dyn_cast<MulExpr>(cur.get())) {
          //std::string Str;
          //llvm::raw_string_ostream info(Str);
          //info << cur ;
          //printf("Mul searching:\n%s\n", info.str().c_str());
          //Str = "";
            if (const ZExtExpr *zee = dyn_cast<ZExtExpr>(me->right)) {
              //info << *zee;
              //printf("Mul(ZExt()) searching:\n%s\n", info.str().c_str());
              //Str = "";
              if (const EqExpr *eqe = dyn_cast<EqExpr>(zee->getKid(0))){
                //info << *eqe;
                //printf("Mul(ZExt(Eq())) searching:\n%s\n", info.str().c_str());
                if (me->left == eqe->right) {
                  // lava: should add something to make this always true
                  equalities.insert(std::make_pair((cur.get()), ConstantExpr::create(0, 32)));
                  //printf("Equality inserted\n");
                  constraints.pop_back();
                  constraints.push_back(EqExpr::create(ConstantExpr::create(0, cur->getWidth()), cur));
                  break;
                }
              }
            }
            search_queue.push(me->left);
            search_queue.push(me->right);
          }
          else if (const BinaryExpr *be = dyn_cast<BinaryExpr>(cur.get())) {
            search_queue.push(be->left);
            search_queue.push(be->right);
          } else {
            //std::string Str;
            //llvm::raw_string_ostream info(Str);
            //info << cur ;
            //printf("searching:\n%s\n", info.str().c_str());
            //Str = "";
            //printf("Unhandle case: %d\n", ++count);
          }
        }
      }
    }
  }
  return ExprReplaceVisitor2(equalities).visit(e);
}

ref<Expr> ConstraintManager::simplifyExpr(ref<Expr> e) const {
  if (isa<ConstantExpr>(e))
    return e;

  std::map< ref<Expr>, ref<Expr> > equalities;
  
  for (ConstraintManager::constraints_ty::const_iterator 
         it = constraints.begin(), ie = constraints.end(); it != ie; ++it) {
    if (const EqExpr *ee = dyn_cast<EqExpr>(*it)) {
      if (isa<ConstantExpr>(ee->left)) {
        equalities.insert(std::make_pair(ee->right,
                                         ee->left));
      } else {
        equalities.insert(std::make_pair(*it,
                                         ConstantExpr::alloc(1, Expr::Bool)));
      }  
    } else {
      equalities.insert(std::make_pair(*it,
                                         ConstantExpr::alloc(1, Expr::Bool)));
    }
  }

  return ExprReplaceVisitor2(equalities).visit(e);
}

void ConstraintManager::addConstraintInternal(ref<Expr> e) {
  // rewrite any known equalities and split Ands into different conjuncts

  switch (e->getKind()) {
  case Expr::Constant:
    assert(cast<ConstantExpr>(e)->isTrue() && 
           "attempt to add invalid (false) constraint");
    break;
    
    // split to enable finer grained independence and other optimizations
  case Expr::And: {
    BinaryExpr *be = cast<BinaryExpr>(e);
    addConstraintInternal(be->left);
    addConstraintInternal(be->right);
    break;
  }

  case Expr::Eq: {
    if (RewriteEqualities) {
      // XXX: should profile the effects of this and the overhead.
      // traversing the constraints looking for equalities is hardly the
      // slowest thing we do, but it is probably nicer to have a
      // ConstraintSet ADT which efficiently remembers obvious patterns
      // (byte-constant comparison).
      BinaryExpr *be = cast<BinaryExpr>(e);
      if (isa<ConstantExpr>(be->left)) {
	ExprReplaceVisitor visitor(be->right, be->left);
	rewriteConstraints(visitor);
      }
    }
    constraints.push_back(e);
    break;
  }
    
  default:
    constraints.push_back(e);
    break;
  }
}

void ConstraintManager::addConstraint(ref<Expr> e) {
  e = simplifyExpr(e);
  addConstraintInternal(e);
}
