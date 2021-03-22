package miniscala

import miniscala.{SymbolicCMScalaTreeModule => S}
import miniscala.{SymbolicCPSTreeModule => C}

object CMScalaToCPSTranslator extends (S.Tree => C.Tree) {
  def apply(tree: S.Tree): C.Tree = {
    nonTail(tree){_ =>
      val z = Symbol.fresh("c0")
      C.LetL(z, IntLit(0), C.Halt(z))
    }(Set.empty)
  }

  private def nonTail(tree: S.Tree)(ctx: Symbol=>C.Tree)(implicit mut: Set[Symbol]): C.Tree = {
    // @unchecked to avoid bogus compiler warnings

    (tree: @unchecked) match {
      case S.Let(name, _, value, body) =>
        nonTail(value)(v =>
            C.LetP(name, MiniScalaId, Seq(v), nonTail(body)(ctx)))

      // TODO: complete the following cases and add the missing ones.

      // Reference of an immutable variable
      case S.Ref(name) if !mut(name) => //???
        ctx(name)

      // Reference of an mutable variable
      case S.Ref(name) => // if mut(name) => //???

        val z = Symbol.fresh("z_ref_n")
        val v = Symbol.fresh("v_ref_n")
        C.LetL(z, IntLit(0), C.LetP(v, MiniScalaBlockGet, Seq(name, z), ctx(v)))

      case S.Lit(x) =>

        val n = Symbol.fresh("n_lit_n")
        C.LetL(n, x, ctx(n))

      case S.VarDec(name, _, rhs, body) =>
        val s = Symbol.fresh("s_vd_n")
        val z = Symbol.fresh("z_vd_n")
        val d = Symbol.fresh("d_vd_n")
        C.LetL(s, IntLit(1), C.LetP(name, MiniScalaBlockAlloc(242), Seq(s),
          C.LetL(z, IntLit(0),
            nonTail(rhs)(v => C.LetP(d, MiniScalaBlockSet, Seq(name, z, v), nonTail(body)(ctx)))(mut + name))
        ))


      case S.VarAssign(name, rhs) =>
        val z = Symbol.fresh("z_va_n")
        val d = Symbol.fresh("d_va_n")
        C.LetL(z, IntLit(0), nonTail(rhs)(v => C.LetP(d, MiniScalaBlockSet, Seq(name, z, v), ctx(v))))

      case S.LetRec(funs, body) =>
        //val c = Symbol.fresh("c")
        val fseq : Seq[C.FunDef] = funs map{
          case S.FunDef(name, _, args, _, fbody) =>
            val c = Symbol.fresh("c_lr_n")
            //C.FunDef(name, c ,args map { arg => arg.name},nonTail(fbody)(v => C.AppC(c, Seq(v))))
            C.FunDef(name, c, args map { arg => arg.name}, tail(fbody, c))
        }
        C.LetF(fseq, nonTail(body)(ctx))

      case S.App(f, _, args) =>

        val r = Symbol.fresh("r_app_n")
        tempLetC("c", Seq(r), ctx(r))(v2 => nonTail(f)(v => nonTail_*(args)(ast => C.AppF(v,v2,ast))))


        // below need to fix

      case S.If(condi, tBranch, eBranch) =>
        /*
        val r = Symbol.fresh("r")
        tempLetC("c",Seq(r), ctx(r))(condE =>
          tempLetC("ct", Seq(), nonTail(tBranch)(v2 => C.AppC(condE, Seq(v2))))(trueC =>
            tempLetC("cf", Seq(), nonTail(eBranch)(v3 => C.AppC(condE, Seq(v3))))(falseC =>
              cond(condi,trueC,falseC)
            )
          )
        )
        */

        val r = Symbol.fresh("r_if_n")
        tempLetC("c_if_n",Seq(r), ctx(r))(condE =>
          tempLetC("ct_if_n", Seq(), tail(tBranch, condE))(trueC =>
            tempLetC("cf_if_n", Seq(), tail(eBranch, condE))(falseC =>
              cond(condi,trueC,falseC) //not sure
            )
          )
        )

      case S.While(condi, lbody, body) =>
        /*
        val loop = Symbol.fresh("loop")
        val tempbody = tempLetC("c", Seq(), nonTail(body)(ctx))(c =>
          tempLetC("ct", Seq(), nonTail(lbody)(_ => C.AppC(loop, Seq())))(ct =>
            cond(condi, ct, c)
          )
        )
        C.LetC(Seq(C.CntDef(loop, Seq(),tempbody)),C.AppC(loop, Seq()))
        */

        val d = Symbol.fresh("d_wh_n")
        val loop = Symbol.fresh("loop_n")
        val tempbody = tempLetC("c_wh_n", Seq(), nonTail(body)(ctx))(c =>
          tempLetC("ct", Seq(), tail(lbody, loop))(ct =>
            cond(condi, ct, c)
          )
        )
        val sLoop = Seq(C.CntDef(loop, Seq(d),tempbody))
        val dLoop = Symbol.fresh("dLoop_n")
        //C.LetL(dLoop, UnitLit, ctx(dLoop))
        //C.LetC(Seq(C.CntDef(loop, Seq(dd),tempbody)),C.AppC(loop, Seq(dLoop)))
        //C.LetC(sLoop, nonTail(S.Lit(UnitLit))(_ => C.LetL(dLoop, UnitLit, C.AppC(loop, Seq(dLoop)))))
        C.LetC(sLoop, C.LetL(dLoop, UnitLit, C.AppC(loop, Seq(dLoop))))


      case prim@S.Prim(op : MiniScalaTestPrimitive, args) =>
        nonTail(S.If(prim, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))))(ctx)

      case S.Prim(op : MiniScalaValuePrimitive, args) =>
        val pri = Symbol.fresh("pri_n")
        nonTail_*(args)(ast => C.LetP(pri, op, ast, ctx(pri)))
    }
  }

  private def nonTail_*(trees: Seq[S.Tree])(ctx: Seq[Symbol]=>C.Tree)(implicit mut: Set[Symbol]): C.Tree =
    trees match {
      case Seq() =>
        ctx(Seq())
      case t +: ts =>
        nonTail(t)(tSym => nonTail_*(ts)(tSyms => ctx(tSym +: tSyms)))
    }

  private def tail(tree: S.Tree, c: Symbol)(implicit mut: Set[Symbol]): C.Tree = {
    // @unchecked to avoid bogus compiler warnings
    (tree: @unchecked) match {
      case S.Let(name, _, value, body) =>
        nonTail(value)(v =>
          C.LetP(name, MiniScalaId, Seq(v), tail(body, c)))

      // TODO: add the missing cases.
      case S.Ref(name) if !mut(name) =>
        C.AppC(c, Seq(name))

      // Reference of an mutable variable
      case S.Ref(name) => // if mut(name) =>
        val z = Symbol.fresh("z_ref_t")
        val v = Symbol.fresh("v_ref_t")
        C.LetL(z, IntLit(0), C.LetP(v, MiniScalaBlockGet, Seq(name, z), C.AppC(c, Seq(v))))

      case S.Lit(x) =>
        val n = Symbol.fresh("n_lit_t")
        C.LetL(n, x, C.AppC(c, Seq(n)))

      case S.VarDec(name, _, rhs, body) =>
        val s = Symbol.fresh("s_vd_t")
        val z = Symbol.fresh("z_vd_t")
        val d = Symbol.fresh("d_vd_t")
        C.LetL(s, IntLit(1), C.LetP(name, MiniScalaBlockAlloc(242), Seq(s),
          C.LetL(z, IntLit(0),
            nonTail(rhs)(v => C.LetP(d, MiniScalaBlockSet, Seq(name, z, v), tail(body, c)))(mut + name))))

      case S.VarAssign(name, rhs) =>
        val z = Symbol.fresh("z_va_t")
        val d = Symbol.fresh("d_va_t")
        C.LetL(z, IntLit(0), nonTail(rhs)(v => C.LetP(d, MiniScalaBlockSet, Seq(name, z, v), C.AppC(c, Seq(v)))))

        //unsure from here

      case S.LetRec(funs, body) =>
        //val c = Symbol.fresh("c")
        val fseq : Seq[SymbolicCPSTreeModule.FunDef] = funs map{
          case S.FunDef(name, _, args, _, fbody) =>
            val cc = Symbol.fresh("cc_lr_t")
            //C.FunDef(name,c,args map { arg => arg.name},nonTail(fbody)(v => C.AppC(c, Seq(v))))
            C.FunDef(name,cc,args map { arg => arg.name},tail(fbody, cc))
        }
        C.LetF(fseq, tail(body, c))

      case S.App(f, _, args) =>

        //val r = Symbol.fresh("r")
        //tempLetC(c.name, Seq(r), C.AppC(c, Seq(r)))(v2 => nonTail(f)(v => nonTail_*(args)(ast => C.AppF(v,v2,ast))))
        nonTail(f)(v => nonTail_*(args)(ast => C.AppF(v,c,ast)))

      case S.If(condi, tBranch, eBranch) =>

        tempLetC("ct_if_t", Seq(), tail(tBranch, c))(trueC =>
            tempLetC("cf_if_t", Seq(), tail(eBranch, c))(falseC =>
              cond(condi,trueC,falseC)
            )
        )

      case S.While(condi, lbody, body) =>

        val d = Symbol.fresh("d_wh_t")
        val loop = Symbol.fresh("loop_t")
        val tempbody = tempLetC("cc_wh_t", Seq(), tail(body, c))(cc =>
          tempLetC("ct_wh_t", Seq(), tail(lbody, loop))(ct =>
            cond(condi, ct, cc)
          )
        )
        val sLoop = Seq(C.CntDef(loop, Seq(d),tempbody))
        val dLoop = Symbol.fresh("dLoop_t")
        //C.LetL(dLoop, UnitLit, C.AppC(c, Seq(dLoop)))
        //C.LetC(sLoop, C.AppC(loop, Seq(dLoop)))
        //C.LetC(sLoop, nonTail(S.Lit(UnitLit))(_ => C.LetL(dLoop, UnitLit, C.AppC(loop, Seq(dLoop)))))
        C.LetC(sLoop, C.LetL(dLoop, UnitLit, C.AppC(loop, Seq(dLoop))))

      case prim@S.Prim(op : MiniScalaTestPrimitive, args) =>
        //nonTail(S.If(prim, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))))(ctx))
        tail(S.If(prim, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))),c) //not sure

      case S.Prim(op : MiniScalaValuePrimitive, args) =>
        val pri = Symbol.fresh("pri_t")
        nonTail_*(args)(ast => C.LetP(pri, op, ast, C.AppC(c, Seq(pri))))

    }
  }

  private def cond(tree: S.Tree, trueC: Symbol, falseC: Symbol)(implicit mut: Set[Symbol]): C.Tree = {

    def litToCont(l: CMScalaLiteral): Symbol =
      if (l != BooleanLit(false)) trueC else falseC

    tree match {
      case S.If(condE, S.Lit(tl), S.Lit(fl)) =>
        cond(condE, litToCont(tl), litToCont(fl))

      // TODO add missing cases
      case S.If(condE, tBranch, S.Lit(fl)) =>
        tempLetC("ac_tb",Seq(),cond(tBranch, trueC, falseC))(acf => cond(condE, acf, litToCont(fl)))

      case S.If(condE, S.Lit(tl), eBranch) =>
        tempLetC("ac_eb",Seq(),cond(eBranch, trueC, falseC))(acf => cond(condE, litToCont(tl), acf))

      case S.Prim(p: MiniScalaTestPrimitive, args) =>
        nonTail_*(args)(as => C.If(p, as, trueC, falseC))

      case other =>
        nonTail(other)(o =>
          nonTail(S.Lit(BooleanLit(false)))(n =>
            C.If(MiniScalaNe, Seq(o, n), trueC, falseC)))
    }
  }

  private def tempLetC(cName: String, args: Seq[C.Name], cBody: C.Tree)
                      (body: C.Name=>C.Tree): C.Tree = {
    val cSym = Symbol.fresh(cName)
    C.LetC(Seq(C.CntDef(cSym, args, cBody)), body(cSym))
  }
}
