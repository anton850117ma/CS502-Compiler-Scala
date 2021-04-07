package miniscala

import BitTwiddling.bitsToIntMSBF
import miniscala.CPSValueRepresenter.tempLetP
import miniscala.{SymbolicCPSTreeModule => H}
import miniscala.{SymbolicCPSTreeModuleLow => L}

/**
 * Value-representation phase for the CPS language. Translates a tree
 * with high-level values (blocks, integers, booleans, unit) and
 * corresponding primitives to one with low-level values (blocks
 * and integers only) and corresponding primitives.
 *
 * @author Michel Schinz <Michel.Schinz@epfl.ch>
 */

object CPSValueRepresenter extends (H.Tree => L.Tree) {
  def apply(tree: H.Tree): L.Tree =
    transform(tree)(Map.empty)

  val unitLit = bitsToIntMSBF(0, 0, 1, 0)
  val optimized = false

  private def transform(tree: H.Tree)
                       (implicit worker: Map[Symbol, (Symbol, Seq[Symbol])])
      : L.Tree = tree match {

    // Literals
    case H.LetL(name, IntLit(value), body) =>
      L.LetL(name, (value << 1) | 1, transform(body))
    case H.LetL(name, CharLit(value), body) =>
      L.LetL(name, (value << 3) | bitsToIntMSBF(1, 1, 0), transform(body))

    case H.LetL(name, BooleanLit(value), body) => //true and false
      if (value){L.LetL(name, bitsToIntMSBF(1, 1, 0, 1, 0), transform(body))}
      else{ L.LetL(name, bitsToIntMSBF(0, 1, 0, 1, 0), transform(body))}
    case H.LetL(name, UnitLit, body) => //unit
      L.LetL(name, unitLit, transform(body))

    // TODO: Add missing literals

    // *************** Primitives ***********************
    // Make sure you implement all possible primitives
    // (defined in MiniScalaPrimitives.scala)
    //
    // Integer primitives
    case H.LetP(name, MiniScalaIntAdd, args, body) => //add

      tempLetP(CPSAdd, args) { r =>
        tempLetL(1) { c1 =>
          L.LetP(name, CPSSub, Seq(r, c1), transform(body)) } }

    // TODO: Add missing integer primitives
    case H.LetP(name, MiniScalaIntSub, args, body) => //sub

      tempLetP(CPSSub, args) { r =>
        tempLetL(1) { c1 =>
          L.LetP(name, CPSAdd, Seq(r, c1), transform(body)) } }

    case H.LetP(name, MiniScalaIntMul, Seq(n, m), body) => //times

      tempLetL(1) { c1 =>
        tempLetP(CPSSub, Seq(n,c1)){ n_f =>
         tempLetP(CPSArithShiftR, Seq(m,c1)){ m_f =>
           tempLetP(CPSMul, Seq(n_f,m_f)){ re =>
             L.LetP(name, CPSAdd, Seq(re, c1), transform(body))} } } }

    case H.LetP(name, MiniScalaIntDiv, Seq(n, m), body) => //divide

      tempLetL(1){ c1 =>
        tempLetP(CPSSub, Seq(n,c1)){ n_f =>
          tempLetP(CPSSub, Seq(m,c1)){ m_f =>
            tempLetP(CPSDiv, Seq(n_f,m_f)){ re =>
              tempLetP(CPSArithShiftL, Seq(re, c1)){ end =>
                L.LetP(name, CPSAdd, Seq(end, c1), transform(body))} } } } }

    case H.LetP(name, MiniScalaIntMod, Seq(n, m), body) => //mode

      tempLetL(1){ c1 =>
        tempLetP(CPSSub, Seq(n,c1)){ n_f =>
          tempLetP(CPSSub, Seq(m,c1)){ m_f =>
            tempLetP(CPSMod, Seq(n_f,m_f)){ re =>
                L.LetP(name, CPSAdd, Seq(re, c1), transform(body))} } } }

    case H.LetP(name, MiniScalaIntArithShiftLeft, Seq(n, m), body) => //Leftshift

      tempLetL(1){ c1 =>
        tempLetP(CPSSub, Seq(n,c1)){ n_f => //n-1
          tempLetP(CPSArithShiftR, Seq(m,c1)){ m_f => //m>>1
            tempLetP(CPSArithShiftL, Seq(n_f,m_f)){ re => //n<<m
              L.LetP(name, CPSAdd, Seq(re, c1), transform(body))} } } }

    case H.LetP(name, MiniScalaIntArithShiftRight, Seq(n, m), body) => //Rightshift

      tempLetL(1){ c1 =>
        tempLetP(CPSArithShiftR, Seq(m, c1)){ m_f =>
          tempLetP(CPSArithShiftR, Seq(n, m_f)){ re =>
            L.LetP(name, CPSAdd, Seq(re, c1), transform(body))} } }

    case H.LetP(name, MiniScalaIntBitwiseAnd, Seq(n, m), body) => //and
      L.LetP(name, CPSAnd, Seq(n, m), transform(body))

    case H.LetP(name, MiniScalaIntBitwiseOr, Seq(n, m), body) => //or
      L.LetP(name, CPSOr, Seq(n, m), transform(body))

    case H.LetP(name, MiniScalaIntBitwiseXOr, Seq(n, m), body) => //xor

      tempLetL(1){ c1 =>
        tempLetP(CPSXOr, Seq(n,m)){ re =>
          L.LetP(name, CPSOr, Seq(re, c1), transform(body))} }

    // Block primitives
    // TODO: Add block primitives
    case H.LetP(name, MiniScalaBlockAlloc(k), Seq(n), body)=>

      tempLetL(1){ c1 =>
        tempLetP(CPSArithShiftR, Seq(n,c1)){ re =>
          L.LetP(name, CPSBlockAlloc(k), Seq(re), transform(body))} }

    case H.LetP(name, MiniScalaBlockTag, Seq(n), body)=>

      tempLetL(1){ c1 =>
        tempLetP(CPSBlockTag, Seq(n)){ re =>
          tempLetP(CPSArithShiftL, Seq(re,c1)){ end =>
            L.LetP(name, CPSAdd, Seq(end,c1), transform(body))} } }

      /*========= not sure=========*/
    case H.LetP(name, MiniScalaBlockLength, Seq(n), body)=>

      tempLetL(1){ c1 =>
        tempLetP(CPSBlockLength, Seq(n)){ re =>
          tempLetP(CPSArithShiftL, Seq(re,c1)){ end =>
            L.LetP(name, CPSAdd, Seq(end,c1), transform(body))} } }

    case H.LetP(name, MiniScalaBlockGet, List(env, offset), body)=>

      tempLetL(1){ c1 =>
        tempLetP(CPSArithShiftR, Seq(offset, c1)){ re =>
            L.LetP(name, CPSBlockGet, Seq(env, re), transform(body))} }

    case H.LetP(name, MiniScalaBlockSet, Seq(fun, offset, fv), body)=> //unitlit

      tempLetL(1){ c1 =>
        tempLetP(CPSArithShiftR, Seq(offset, c1)){ re =>
          tempLetP(CPSBlockSet, Seq(fun, re, fv)){ _ =>
            L.LetL(name, unitLit, transform(body))} } }


    // Conversion primitives int->char/char->int
    // TODO
    case H.LetP(name, MiniScalaCharToInt, Seq(n), body)=>

      tempLetL(2){ c2 =>
          L.LetP(name, CPSArithShiftR, Seq(n, c2), transform(body))}

    case H.LetP(name, MiniScalaIntToChar, Seq(n), body)=>

      tempLetL(2){ c2 =>
        tempLetP(CPSArithShiftL, Seq(n,c2)){ re =>
          L.LetP(name, CPSAdd, Seq(re,c2), transform(body))} }
    // IO primitives
    // TODO
    case H.LetP(name, MiniScalaByteRead, _, body)=>

      tempLetL(1){c1 =>
        tempLetP(CPSByteRead, Seq()){ re =>
          tempLetP(CPSArithShiftL, Seq(re,c1)){ end =>
            L.LetP(name, CPSAdd, Seq(end,c1), transform(body))} } }

    case H.LetP(name, MiniScalaByteWrite, Seq(n), body)=> //problem

      tempLetL(1){ c1 =>
        tempLetP(CPSArithShiftR, Seq(n,c1)){ re =>
          tempLetP(CPSByteWrite, Seq(re)){ _ =>
            L.LetL(name, unitLit, transform(body))} } }


    // Other primitives
    // TODO
    case H.LetP(name, MiniScalaId, args, body) =>
      L.LetP(name, CPSId, args, transform(body))
    // Continuations nodes (LetC, AppC)
    // TODO
    case H.LetC(cnts, body) =>
      L.LetC(cnts map {cnt => L.CntDef(cnt.name, cnt.args, transform(cnt.body))}, transform(body))
    case H.AppC(cnt, args) =>
      L.AppC(cnt, args)
    // Functions nodes (LetF, AppF)
    // TODO
    case H.LetF(funs, body) =>

      /*val new_funs = funs map {fun => freeVariables(fun)(Map(Symbol, Set(Symbol))).toSeq}
      val nfuns = (funs zip new_funs) map {
        case (fun, fun_fvs) =>
          val work = Symbol.fresh("w")
          //val fvs = freeVariables(fun)(Map(work, Set(work)))
          //val fun_fvs = freeVariables(fun)(Map.empty).toSeq
          val us = fun_fvs map {_ => Symbol.fresh("u")}
          val sub = Substitution.apply(fun_fvs, us)
          val worker = L.FunDef(work, fun.retC, fun.args ++ us, transform(fun.body).subst(sub))
          val vs = us map { _ => Symbol.fresh("v")}
          val env = Symbol.fresh("env")
          val inner = L.AppF(worker.name,worker.retC, worker.args)
          val nums : Seq[Int] = vs map {v => vs.indexOf(v)}
          val res = wrap(vs zip nums, inner){
            case ((v, num), inner) =>
              tempLetL(num+1){ c => L.LetP(v, CPSBlockGet, Seq(env, c), inner)}
          }
          L.FunDef(Symbol.fresh("s"), inner.retC, Seq(env) ++ inner.args, res)
      }
      val inner1 = transform(body)
      val ss = nfuns map { funss => funss.name}
      val inner2 = wrap((funs zip ss) zip new_funs, inner1){
        case (((fun, s), fv),inner1) =>
          val fv_seq = fv
          tempLetL(0) { c0 =>
            tempLetP(CPSBlockSet, Seq(fun.name, c0, s)){ _ =>
              wrap(fv_seq, inner1){
                case (fv_s, inner1) =>
                  tempLetL(fv_seq.indexOf(fv_s)+1){ fv_i =>
                    tempLetP(CPSBlockSet, Seq(fun.name, fv_i , fv_s)){_ => inner1}
                  }
              }
            }
          }
      }
      val result = wrap(new_funs zip funs, inner2){
        case ((funn, fun), inner2) =>
          tempLetL(funn.size+1) { fun_size =>
            L.LetP(fun.name, CPSBlockAlloc(202), Seq(fun_size), inner2)} }
      L.LetF(nfuns, result)*/

      val new_funs = funs map {fun => freeVariables(fun)(Map.empty)}
      val nfuns = (new_funs zip funs) map {
        case (nf, fun) =>
          val nf_seq = nf.toSeq
          val vs = nf_seq map { _ => Symbol.fresh("v") }
          val env = Symbol.fresh("env")
          val sub = Substitution.apply(fun.name,env) ++ (nf_seq zip vs)
          val inner = transform(fun.body).subst(sub)
          val nums : Seq[Int] = vs map {v => vs.indexOf(v)}
          val res = wrap(vs zip nums, inner){
            case ((v, num), inner) =>
              tempLetL(num+1){ c => L.LetP(v, CPSBlockGet, Seq(env, c), inner)}
          }
          L.FunDef(Symbol.fresh("w"), fun.retC, Seq(env) ++ fun.args, res)
        }
      val inner1 = transform(body)
      val works = nfuns map { funss => funss.name}
      val inner2 = wrap((funs zip works) zip new_funs, inner1){
        case (((fun, work), fv),inner1) =>
          val fv_seq = fv.toSeq
          tempLetL(0) { c0 =>
            tempLetP(CPSBlockSet, Seq(fun.name, c0, work)){ _ =>
              wrap(fv_seq, inner1){
                case (fv_s, inner1) =>
                  tempLetL(fv_seq.indexOf(fv_s)+1){ fv_i =>
                    tempLetP(CPSBlockSet, Seq(fun.name, fv_i , fv_s)){_ => inner1}
                  }
              }
            }
          }
      }
      val result = wrap(new_funs zip funs, inner2){
        case ((funn, fun), inner2) =>
          tempLetL(funn.size+1) { fun_size =>
            L.LetP(fun.name, CPSBlockAlloc(202), Seq(fun_size), inner2)} }
      L.LetF(nfuns, result)

    case H.AppF(fun, retC, args) =>

      tempLetL(0){ c0 =>
        tempLetP(CPSBlockGet, Seq(fun, c0)){ f =>
          L.AppF(f, retC, Seq(fun) ++ args)} }

    // ********************* Conditionnals ***********************
    // Type tests
    case H.If(MiniScalaBlockP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(0, 0), thenC, elseC)
    // TODO: add missing cases

    case H.If(MiniScalaIntP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(1), thenC, elseC)

    case H.If(MiniScalaBoolP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(1,0,1,0), thenC, elseC)

    case H.If(MiniScalaCharP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(1, 1, 0), thenC, elseC)

    case H.If(MiniScalaUnitP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(0, 0, 1, 0), thenC, elseC)

    // Test primitives (<, >, ==, ...)
    // TODO
    case H.If(MiniScalaIntLt, Seq(n,m), thenC, elseC) =>
      L.If(CPSLt, Seq(n,m), thenC, elseC)
    case H.If(MiniScalaIntLe, Seq(n,m), thenC, elseC) =>
      L.If(CPSLe, Seq(n,m), thenC, elseC)
    case H.If(MiniScalaIntGt, Seq(n,m), thenC, elseC) =>
      L.If(CPSGt, Seq(n,m), thenC, elseC)
    case H.If(MiniScalaIntGe, Seq(n,m), thenC, elseC) =>
      L.If(CPSGe, Seq(n,m), thenC, elseC)
    case H.If(MiniScalaEq, Seq(n,m), thenC, elseC) =>
      L.If(CPSEq, Seq(n,m), thenC, elseC)
    case H.If(MiniScalaNe, Seq(n,m), thenC, elseC) =>
      L.If(CPSNe, Seq(n,m), thenC, elseC)
    // Halt case
    // TODO
    case H.Halt(n) =>
      tempLetL(1){c1=>
        tempLetP(CPSArithShiftR, Seq(n, c1)){ re =>
          L.Halt(re)} }
  }

  /*
   * Auxilary function.
   *
   * Example:
   *  // assuming we have a function with symbol f and the return continuation is rc:
   *
   *  val names = Seq("first", "second")
   *  val values = Seq(42, 112)
   *  val inner = L.AppF(f, rc, names)
   *  val res = wrap(names zip values , inner) {
   *    case ((n, v), inner) => L.LetL(n, v, inner)
   *  }
   *
   *  // res is going to be the following L.Tree
   *  L.LetL("first", 42,
   *    L.LetL("second", 112,
   *      L.AppF(f, rc, Seq("first", "second"))
   *    )
   *  )
   */
  private def wrap[T](args: Seq[T], inner: L.Tree)(createLayer: (T, L.Tree) => L.Tree) = {
    def addLayers(args: Seq[T]): L.Tree = args match {
      case h +: t => createLayer(h, addLayers(t))
      case _ => inner
    }
    addLayers(args)
  }

  private def freeVariables(tree: H.Tree)
                           (implicit worker: Map[Symbol, Set[Symbol]])
      : Set[Symbol] = tree match {
    case H.LetL(name, _, body) =>
      freeVariables(body) - name
    case H.LetP(name, _, args, body) =>
      freeVariables(body) - name ++ args
    // TODO: add missing cases

    case H.LetC(cnts, body) =>

      var temp = freeVariables(body)
      cnts foreach(cnt => temp = temp ++ freeVariables(cnt.body) -- cnt.args)
      temp

    case H.LetF(funs, body) =>

      var temp = freeVariables(body)
      funs foreach(fun => temp = temp ++ freeVariables(fun.body) -- fun.args)
      funs foreach(fun => temp = temp - fun.name)
      temp

    case H.AppC(_, args) =>
      args.toSet

    case H.AppF(fun, _, args) =>
      Set(fun) ++ args.toSet

    case H.If(_, args, _, _) =>
      args.toSet

  }

  private def freeVariables(cnt: H.CntDef)
                           (implicit worker: Map[Symbol, Set[Symbol]])
      : Set[Symbol] =
    freeVariables(cnt.body) -- cnt.args

  private def freeVariables(fun: H.FunDef)
                           (implicit worker: Map[Symbol, Set[Symbol]])
      : Set[Symbol] =
    freeVariables(fun.body) - fun.name -- fun.args

  // Tree builders

  /**
   * Call body with a fresh name, and wraps its resulting tree in one
   * that binds the fresh name to the given literal value.
   */
  private def tempLetL(v: Int)(body: L.Name => L.Tree): L.Tree = {
    val tempSym = Symbol.fresh("t")
    L.LetL(tempSym, v, body(tempSym))
  }

  /**
   * Call body with a fresh name, and wraps its resulting tree in one
   * that binds the fresh name to the result of applying the given
   * primitive to the given arguments.
   */
  private def tempLetP(p: L.ValuePrimitive, args: Seq[L.Name])
                      (body: L.Name => L.Tree): L.Tree = {
    val tempSym = Symbol.fresh("t")
    L.LetP(tempSym, p, args, body(tempSym))
  }

  /**
   * Generate an If tree to check whether the least-significant bits
   * of the value bound to the given name are equal to those passed as
   * argument. The generated If tree will apply continuation tC if it
   * is the case, and eC otherwise. The bits should be ordered with
   * the most-significant one first (e.g. the list (1,1,0) represents
   * the decimal value 6).
   */
  private def ifEqLSB(arg: L.Name, bits: Seq[Int], tC: L.Name, eC: L.Name)
      : L.Tree =
    tempLetL(bitsToIntMSBF(bits map { b => 1 } : _*)) { mask =>
      tempLetP(CPSAnd, Seq(arg, mask)) { masked =>
        tempLetL(bitsToIntMSBF(bits : _*)) { value =>
          L.If(CPSEq, Seq(masked, value), tC, eC) } } }
}
