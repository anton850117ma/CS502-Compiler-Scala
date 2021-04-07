package miniscala

import com.sun.javafx.geom.transform.Identity

import scala.collection.mutable.{Map => MutableMap}

abstract class CPSOptimizer[T <: CPSTreeModule { type Name = Symbol }]
  (val treeModule: T) {
  import treeModule._

  def apply(tree: Tree): Tree = {
    val simplifiedTree = fixedPoint(tree)(shrink)
    val maxSize = (size(simplifiedTree) * 1.5).toInt
    fixedPoint(simplifiedTree, 8) { t => inline(t, maxSize) }
  }

  /* Counts how many times a symbol is encountered as an applied function,
   * and how many as a value
   */
  private case class Count(applied: Int = 0, asValue: Int = 0)

  /* Local state of the optimization
   * Note: To update the state, use the with* methods
   */
  private case class State(
    /* How many times a symbol is encountered in the Tree. Note: The
     * census for the whole program gets calculated once in the
     * beginning, and passed to the initial state.
     */
    census: Map[Name, Count],
    // Name substitution that needs to be applied to the current tree
    subst: Substitution[Name] = Substitution.empty,
    // Names that have a constant value
    lEnv: Map[Name, Literal] = Map.empty,
    // The inverse of lEnv
    lInvEnv: Map[Literal, Name] = Map.empty,
    // A known block mapped to its tag and length
    bEnv: Map[Name, (Literal, Name)] = Map.empty,
    // ((p, args) -> n2) is included in eInvEnv iff n2 == p(args)
    // Note: useful for common-subexpression elimination
    eInvEnv: Map[(ValuePrimitive, Seq[Name]), Name] = Map.empty,
    // Continuations that will be inlined
    cEnv: Map[Name, CntDef] = Map.empty,
    // Functions that will be inlined
    fEnv: Map[Name, FunDef] = Map.empty) {

    // Checks whether a symbol is dead in the current state
    def dead(s: Name): Boolean =
      census get s map (_ == Count(applied = 0, asValue = 0)) getOrElse true
    // Checks whether a symbols is applied exactly once as a function
    // in the current State, and never used as a value
    def appliedOnce(s: Name): Boolean =
      census get s map (_ == Count(applied = 1, asValue = 0)) getOrElse false

    // Addas a substitution to the state
    def withSubst(from: Name, to: Name): State =
      copy(subst = subst + (from -> to))
    // Adds a Seq of substitutions to the state
    def withSubst(from: Seq[Name], to: Seq[Name]): State =
      copy(subst = subst ++ (from zip to))

    // Adds a constant to the State
    def withLit(name: Name, value: Literal) =
      copy(lEnv = lEnv + (name -> value), lInvEnv = lInvEnv + (value -> name))
    // Adds a block to the state
    def withBlock(name: Name, tag: Literal, size: Name) =
      copy(bEnv = bEnv + (name -> (tag, size)))
    // Adds a primitive assignment to the state
    def withExp(name: Name, prim: ValuePrimitive, args: Seq[Name]) =
      copy(eInvEnv = eInvEnv + ((prim, args) -> name))
    // Adds an inlinable continuation to the state
    def withCnt(cnt: CntDef) =
      copy(cEnv = cEnv + (cnt.name -> cnt))
    // Adds a Seq of inlinable continuations to the state
    def withCnts(cnts: Seq[CntDef]) =
      (this /: cnts) (_.withCnt(_))
    // Adds an inlinable function to the state
    def withFun(fun: FunDef) =
      copy(fEnv = fEnv + (fun.name -> fun))
    // Adds a Seq of inlinable functions to the state
    def withFuns(funs: Seq[FunDef]) =
      (this /: funs) (_.withFun(_))
    /*
     * The same state, with empty inverse environments.
     * Use this when entering a new FunDef, because assigned Name's may
     * come out of scope during hoisting.
     */
    def withEmptyInvEnvs =
      copy(lInvEnv = Map.empty, eInvEnv = Map.empty)
  }

  // Shrinking optimizations

  private def shrink(tree: Tree): Tree = {
    def shrinkT(tree: Tree)(implicit s: State): Tree = tree match {

      case LetL(name, value, body) =>
        if(s.dead(name))shrinkT(body)
        else if(s.lInvEnv.contains(value)) {
          val new_body = body.subst(Substitution(name, s.lInvEnv(value)))
          shrinkT(new_body)(s.withSubst(name, s.lInvEnv(value)))
        }
        else LetL(name, value, shrinkT(body)(s.withLit(name, value)))

      case LetP(name, prim, args, body) =>

        //dead and not impure
        if(s.dead(name) && !impure(prim)) shrinkT(body)
          //block prims
        else if(impure(prim) || unstable(prim)){
          if(blockAllocTag.isDefinedAt(prim)){
            val value = blockAllocTag(prim)
            LetP(name, prim, args, shrinkT(body)(s.withBlock(name, value, args.head)))
          }
          else LetP(name, prim, args, shrinkT(body)(s.withExp(name, prim, args)))
        }
        else {
          //block prims
          if (prim == blockLength) {
            LetP(name, prim, args, shrinkT(body)(s.withExp(name, prim, args)))
          }
          else if (prim == blockTag) {
            if(s.bEnv.contains(args.head)){
              val value = s.bEnv(args.head)._1
              shrinkT(LetL(name, value, body))
            }
            else LetP(name, prim, args, shrinkT(body)(s.withExp(name, prim, args)))
          }
            //same LetP
          else if (s.eInvEnv.contains((prim, args))){
            val new_body = body.subst(Substitution(name, s.eInvEnv(prim, args)))
            shrinkT(new_body)(s.withSubst(name, s.eInvEnv(prim, args)))
          }
            //deal with Ref
          else if (prim == identity) {
            shrinkT(body.subst(Substitution(name, args.head)))(s.withSubst(name, args.head))
          }
          else {
            // if all args are in lEnv, become LetL
            val foldable = args.forall(arg => s.lEnv.contains(arg))
            if (foldable) {
              val lits = args map { arg => s.lEnv(arg) }
              val result = vEvaluator(prim, lits)
              shrinkT(LetL(name, result, body))
            }
            else {
              if (args.size == 2) {
                if (args.head == args(1) && sameArgReduce.isDefinedAt(prim)) {
                  val value = sameArgReduce(prim)
                  shrinkT(LetL(name, value, body))
                }
                else if (s.lEnv.contains(args.head)) {

                  if (leftNeutral(s.lEnv(args.head), prim)) {
                    shrinkT(body.subst(Substitution(name, args(1))))(s.withSubst(name, args(1)))
                  }
                  else if (leftAbsorbing(s.lEnv(args.head), prim)){
                    shrinkT(body.subst(Substitution(name, args.head)))(s.withSubst(name, args.head))
                  }
                  else LetP(name, prim, args, shrinkT(body)(s.withExp(name, prim, args)))
                }
                else if (s.lEnv.contains(args(1))) {

                  if (rightNeutral(prim, s.lEnv(args(1)))){
                    shrinkT(body.subst(Substitution(name, args.head)))(s.withSubst(name, args.head))
                  }
                  else if (rightAbsorbing(prim, s.lEnv(args(1)))){
                    shrinkT(body.subst(Substitution(name, args(1))))(s.withSubst(name, args(1)))
                  }
                  else LetP(name, prim, args, shrinkT(body)(s.withExp(name, prim, args)))
                }
                else LetP(name, prim, args, shrinkT(body)(s.withExp(name, prim, args)))
              }
              else LetP(name, prim, args, shrinkT(body)(s.withExp(name, prim, args)))
            }
          }
        }

      case If(cond, args, thenC, elseC) =>

//        If(cond, args, thenC, elseC)
        if(args.size == 2 && args.head == args(1)){
          if(sameArgReduceC(cond)) shrinkT(AppC(thenC, Seq()))
          else shrinkT(AppC(elseC, Seq()))
        }
        else {
          val foldable = args.forall(arg => s.lEnv.contains(arg))
          if (foldable) {
            val lits = args map { arg => s.lEnv(arg) }
            val result = cEvaluator(cond, lits)
            if (result) shrinkT(AppC(thenC, Seq()))
            else shrinkT(AppC(elseC, Seq()))
          }
          else If(cond, args, thenC, elseC)
        }

      case LetF(funs, body) =>

        var new_funs = Seq[FunDef]() //DCE
        var inlined = Seq[FunDef]()
        for (fun <- funs){
          if(!s.dead(fun.name) && s.appliedOnce(fun.name))
            inlined = inlined :+ fun
          else if(!s.dead(fun.name) && !s.appliedOnce(fun.name))
            new_funs = new_funs :+ fun
        }
        val nfuns = new_funs map{fun =>
          FunDef(fun.name, fun.retC, fun.args, shrinkT(fun.body)(s.withFuns(inlined).withEmptyInvEnvs))}

        if (nfuns.isEmpty)shrinkT(body)(s.withFuns(inlined))
        else LetF(nfuns, shrinkT(body)(s.withFuns(inlined)))

      case LetC(cnts, body) =>

        var new_cnts = Seq[CntDef]() //DCE
        var inlined = Seq[CntDef]()
        for (cnt <- cnts) {
          if (!s.dead(cnt.name) && s.appliedOnce(cnt.name))
            inlined = inlined :+ cnt
          else if (!s.dead(cnt.name) && !s.appliedOnce(cnt.name))
            new_cnts = new_cnts :+ cnt
        }
        val ncnts = new_cnts map{cnt => CntDef(cnt.name, cnt.args, shrinkT(cnt.body)(s.withCnts(inlined)))}
        if(ncnts.isEmpty) shrinkT(body)(s.withCnts(inlined))
        else LetC(ncnts, shrinkT(body)(s.withCnts(inlined)))

      case AppF(fun, retC, args) =>

        if(s.fEnv.contains(fun)){
          val old_fun = s.fEnv(fun)
          val new_retc = old_fun.body.subst(Substitution(old_fun.retC, retC))
          val new_body = new_retc.subst(Substitution(old_fun.args, args))
          shrinkT(new_body)(s.withSubst(old_fun.retC +: old_fun.args, retC +: args))
        }
        else AppF(fun, retC, args)

      case AppC(cnt, args) =>

        if(s.cEnv.contains(cnt)){
          val old_cnt = s.cEnv(cnt)
          val new_body = old_cnt.body.subst(Substitution(old_cnt.args, args))
          shrinkT(new_body)(s.withSubst(old_cnt.args, args))
        }
        else AppC(cnt, args)

      case _ =>
        // TODO
        tree
    }

    shrinkT(tree)(State(census(tree)))
  }

  // (Non-shrinking) inlining

  private def inline(tree: Tree, maxSize: Int): Tree = {

    val fibonacci = Seq(1, 2, 3, 5, 8, 13)

    val trees = Stream.iterate((0, tree), fibonacci.length) { case (i, tree) =>
      val funLimit = fibonacci(i)
      val cntLimit = i

      def freshAll(tree: Tree)(implicit s: State): Tree = tree match{

        case LetL(name, value, body) =>

          val NewL = Symbol.fresh("NewL")
          LetL(NewL, value, freshAll(body).subst(Substitution(name, NewL)))

        case LetP(name, prim, args, body) =>

          val new_args = args map{ _ => Symbol.fresh("NewArg_P")}
          val NewP = Symbol.fresh("NewP")
//          println("Start")
          val new_body = freshAll(body).subst(Substitution(name , NewP))
//          println("end")
          LetP(NewP, prim, args, new_body)

        case LetF(funs, body) =>

          var all_olds = Seq[Symbol]()
          var all_news = Seq[Symbol]()

          val new_funs = funs map{fun =>
            val new_name = Symbol.fresh("NewFun")
            val new_retc = Symbol.fresh("NewRet")
            val new_args = fun.args map{ _ => Symbol.fresh("NewArg_F")}
            val olds = fun.retC +: fun.args
            val news = new_retc +: new_args
            all_olds = all_olds :+ fun.name
            all_news = all_news :+ new_name
            FunDef(new_name, new_retc, new_args,
              freshAll(fun.body).subst(Substitution(fun.name +: olds, new_name +:news)))
          }
          LetF(new_funs, freshAll(body).subst(Substitution(all_olds, all_news)))

        case LetC(cnts, body) => //not sure

          var all_olds = Seq[Symbol]()
          var all_news = Seq[Symbol]()

          val new_cnts = cnts map{cnt =>
            val new_name = Symbol.fresh("NewCnt")
            val new_args = cnt.args map{ _ => Symbol.fresh("NewArg_C")}
            val olds = cnt.name +: cnt.args
            val news = new_name +: new_args
            all_olds = all_olds :+ cnt.name
            all_news = all_news :+ new_name
            CntDef(new_name, new_args, freshAll(cnt.body).subst(Substitution(olds, news)))
          }
          LetC(new_cnts, freshAll(body).subst(Substitution(all_olds, all_news)))

        case _ =>
          tree
      }

      def inlineT(tree: Tree)(implicit s: State): Tree = tree match {

        case LetL(name, value, body) =>

          LetL(name, value, inlineT(body))

        case LetP(name, prim, args, body) =>

          LetP(name, prim, args, inlineT(body))

        case LetF(funs, body) =>

          var inline = Seq[FunDef]()
          val new_funs = funs map{ fun =>
            val other_funs = funs.filterNot(p => p.name == fun.name)
            val inline_fun = inlineT(fun.body)(s.withFuns(other_funs))
            if(size(inline_fun) < size(fun.body)*funLimit){
              val new_fun = FunDef(fun.name, fun.retC, fun.args, inline_fun)
              inline = inline :+ new_fun
              new_fun
            }
            else fun
          }
          LetF(new_funs, inlineT(body)(s.withFuns(inline)))

        case LetC(cnts, body) =>

          var inline = Seq[CntDef]()
          val new_cnts = cnts map{ cnt =>
            val other_cnts = cnts.filterNot(p => p.name == cnt.name)
            val inline_cnt = inlineT(cnt.body)(s.withCnts(other_cnts))
            if(size(inline_cnt) < size(cnt.body)*cntLimit){
              val new_cnt = CntDef(cnt.name, cnt.args, inline_cnt)
              inline = inline :+ new_cnt
              new_cnt
            }
            else cnt
          }
          LetC(new_cnts, inlineT(body)(s.withCnts(inline)))

        case AppF(fun, retC, args) => //fresh & subst

          if(s.fEnv.contains(fun)){
            val old_fun = s.fEnv(fun)
            var new_body = old_fun.body
            if(old_fun.retC != retC) {
              new_body = new_body.subst(Substitution(old_fun.retC, retC))
            }
            if(args.nonEmpty){
              old_fun.args zip args foreach( tuple =>
                if(tuple._1 != tuple._2) {
                  new_body = new_body.subst(Substitution(tuple._1,tuple._2))
                })
            }
            freshAll(new_body)
          }
          else tree

        case AppC(cnt, args) =>

          if(s.cEnv.contains(cnt)){
            val old_cnt = s.cEnv(cnt)
            var new_body = old_cnt.body
            if(args.nonEmpty){
              old_cnt.args zip args foreach( tuple =>
                if(tuple._1 != tuple._2) new_body = new_body.subst(Substitution(tuple._1,tuple._2)))
            }
            freshAll(new_body)
          }
          else tree

        case _ =>
          // TODO
          tree
      }

      (i + 1, fixedPoint(inlineT(tree)(State(census(tree))))(shrink))
    }

    trees.takeWhile{ case (_, tree) => size(tree) <= maxSize }.last._2
  }

  // Census computation
  private def census(tree: Tree): Map[Name, Count] = {
    val census = MutableMap[Name, Count]()
    val rhs = MutableMap[Name, Tree]()

    def incAppUse(symbol: Name): Unit = {
      val currCount = census.getOrElse(symbol, Count())
      census(symbol) = currCount.copy(applied = currCount.applied + 1)
      rhs remove symbol foreach addToCensus
    }

    def incValUse(symbol: Name): Unit = {
      val currCount = census.getOrElse(symbol, Count())
      census(symbol) = currCount.copy(asValue = currCount.asValue + 1)
      rhs remove symbol foreach addToCensus
    }

    def addToCensus(tree: Tree): Unit = (tree: @unchecked) match {
      case LetL(_, _, body) =>
        addToCensus(body)
      case LetP(_, _, args, body) =>
        args foreach incValUse; addToCensus(body)
      case LetC(cnts, body) =>
        rhs ++= (cnts map { c => (c.name, c.body) }); addToCensus(body)
      case LetF(funs, body) =>
        rhs ++= (funs map { f => (f.name, f.body) }); addToCensus(body)
      case AppC(cnt, args) =>
        incAppUse(cnt); args foreach incValUse
      case AppF(fun, retC, args) =>
        incAppUse(fun); incValUse(retC); args foreach incValUse
      case If(_, args, thenC, elseC) =>
        args foreach incValUse; incValUse(thenC); incValUse(elseC)
      case Halt(arg) =>
        incValUse(arg)
    }

    addToCensus(tree)
    census.toMap
  }

  private def sameLen(formalArgs: Seq[Name], actualArgs: Seq[Name]): Boolean =
    formalArgs.length == actualArgs.length

  private def size(tree: Tree): Int = (tree: @unchecked) match {
    case LetL(_, _, body) => size(body) + 1
    case LetP(_, _, _, body) => size(body) + 1
    case LetC(cs, body) => (cs map { c => size(c.body) }).sum + size(body)
    case LetF(fs, body) => (fs map { f => size(f.body) }).sum + size(body)
    case AppC(_, _) | AppF(_, _, _) | If(_, _, _, _) | Halt(_) => 1
  }

  // Returns whether a ValuePrimitive has side-effects
  protected val impure: ValuePrimitive => Boolean
  // Returns whether different applications of a ValuePrimivite on the
  // same arguments may yield different results
  protected val unstable: ValuePrimitive => Boolean
  // Extracts the tag from a block allocation primitive
  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal]
  // Returns true for the block tag primitive
  protected val blockTag: ValuePrimitive
  // Returns true for the block length primitive
  protected val blockLength: ValuePrimitive
  // Returns true for the identity primitive
  protected val identity: ValuePrimitive

  // ValuePrimitives with their left-neutral elements
  protected val leftNeutral: Set[(Literal, ValuePrimitive)]
  // ValuePrimitives with their right-neutral elements
  protected val rightNeutral: Set[(ValuePrimitive, Literal)]
  // ValuePrimitives with their left-absorbing elements
  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)]
  // ValuePrimitives with their right-absorbing elements
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)]
  // ValuePrimitives with the value equal arguments reduce to
  protected val sameArgReduce: PartialFunction[ValuePrimitive, Literal]
  // TestPrimitives with the (boolean) value equal arguments reduce to
  protected val sameArgReduceC: TestPrimitive => Boolean
  // An evaluator for ValuePrimitives
  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal]
  // An evaluator for TestPrimitives
  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean]
}

object CPSOptimizerHigh extends CPSOptimizer(SymbolicCPSTreeModule)
    with (SymbolicCPSTreeModule.Tree => SymbolicCPSTreeModule.Tree) {
  import treeModule._

  protected val impure: ValuePrimitive => Boolean =
    Set(MiniScalaBlockSet, MiniScalaByteRead, MiniScalaByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    // TODO
    case MiniScalaBlockAlloc(_) | MiniScalaBlockGet | MiniScalaByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case MiniScalaBlockAlloc(tag) => IntLit(tag)
  }
  protected val blockTag: ValuePrimitive = MiniScalaBlockTag
  protected val blockLength: ValuePrimitive = MiniScalaBlockLength

  protected val identity: ValuePrimitive = MiniScalaId

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    // TODO
    Set((IntLit(0), MiniScalaIntAdd),
      (IntLit(1), MiniScalaIntMul),
      (IntLit(~0), MiniScalaIntBitwiseAnd),
      (IntLit(0), MiniScalaIntBitwiseOr),
      (IntLit(0), MiniScalaIntBitwiseXOr))

  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
     // TODO
    Set((MiniScalaIntAdd, IntLit(0)),
      (MiniScalaIntSub, IntLit(0)),
      (MiniScalaIntMul, IntLit(1)),
      (MiniScalaIntDiv, IntLit(1)),
      (MiniScalaIntArithShiftLeft, IntLit(0)),
      (MiniScalaIntArithShiftRight, IntLit(0)),
      (MiniScalaIntBitwiseAnd, IntLit(~0)),
      (MiniScalaIntBitwiseOr, IntLit(0)),
      (MiniScalaIntBitwiseXOr, IntLit(0)))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    // TODO
    Set((IntLit(0), MiniScalaIntMul),
      (IntLit(0),MiniScalaIntBitwiseAnd),
      (IntLit(~0),MiniScalaIntBitwiseOr))

  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    // TODO
    Set((MiniScalaIntMul, IntLit(0)),
      (MiniScalaIntBitwiseAnd, IntLit(0)),
      (MiniScalaIntBitwiseOr, IntLit(~0)))

  protected val sameArgReduce: PartialFunction[ValuePrimitive, Literal] =
    // TODO
    Map(MiniScalaIntSub -> IntLit(0),
      MiniScalaIntDiv -> IntLit(1),
      MiniScalaIntMod -> IntLit(0),
      MiniScalaIntBitwiseXOr -> IntLit(0))

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case MiniScalaIntLe | MiniScalaIntGe | MiniScalaEq => true
    case MiniScalaIntLt | MiniScalaIntGt | MiniScalaNe => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    // TODO
    case (MiniScalaIntAdd, Seq(IntLit(x), IntLit(y))) => IntLit(x + y)
    case (MiniScalaIntSub, Seq(IntLit(x), IntLit(y))) => IntLit(x - y)
    case (MiniScalaIntMul, Seq(IntLit(x), IntLit(y))) => IntLit(x * y)
    case (MiniScalaIntDiv, Seq(IntLit(x), IntLit(y))) => IntLit(x / y)//?
    case (MiniScalaIntMod, Seq(IntLit(x), IntLit(y))) => IntLit(x % y)//?
    case (MiniScalaIntBitwiseAnd, Seq(IntLit(x), IntLit(y))) => IntLit(x & y)
    case (MiniScalaIntBitwiseOr, Seq(IntLit(x), IntLit(y))) => IntLit(x | y)
    case (MiniScalaIntBitwiseXOr, Seq(IntLit(x), IntLit(y))) => IntLit(x ^ y)
    case (MiniScalaIntArithShiftLeft, Seq(IntLit(x), IntLit(y))) => IntLit(x << y)
    case (MiniScalaIntArithShiftRight, Seq(IntLit(x), IntLit(y))) => IntLit(x >> y)
    case (MiniScalaCharToInt, Seq(CharLit(x))) => IntLit(x.toInt)
    case (MiniScalaIntToChar, Seq(IntLit(x))) => CharLit(x.toChar)
    case (MiniScalaIntSub, Seq(IntLit(x))) => IntLit(-x)
    case (MiniScalaIntAdd, Seq(IntLit(x))) => IntLit(x)

  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {

    case (MiniScalaIntP, Seq(IntLit(_))) => true
    // TODO
    case (MiniScalaIntP, Seq(_)) => false
    case (MiniScalaBoolP, Seq(BooleanLit(_))) => true
    case (MiniScalaBoolP, Seq(_)) => false
    case (MiniScalaCharP, Seq(CharLit(_))) => true
    case (MiniScalaCharP, Seq(_)) => false
    case (MiniScalaUnitP, Seq(UnitLit)) => true
    case (MiniScalaUnitP, Seq(_)) => false
    case (MiniScalaBlockP, Seq(_)) => false

    //?
    case (MiniScalaEq, Seq(IntLit(x), IntLit(y))) => if (x == y) true else false
    case (MiniScalaNe, Seq(IntLit(x), IntLit(y))) => if (x != y) true else false
    case (MiniScalaEq, Seq(BooleanLit(x), BooleanLit(y))) => if (x == y) true else false
    case (MiniScalaNe, Seq(BooleanLit(x), BooleanLit(y))) => if (x != y) true else false
    case (MiniScalaEq, Seq(CharLit(x), CharLit(y))) => if (x == y) true else false
    case (MiniScalaNe, Seq(CharLit(x), CharLit(y))) => if (x != y) true else false

    case (MiniScalaIntGe, Seq(IntLit(x), IntLit(y))) => if (x >= y) true else false
    case (MiniScalaIntLe, Seq(IntLit(x), IntLit(y))) => if (x <= y) true else false
    case (MiniScalaIntLt, Seq(IntLit(x), IntLit(y))) => if (x < y) true else false
    case (MiniScalaIntGt, Seq(IntLit(x), IntLit(y))) => if (x > y) true else false

  }
}

object CPSOptimizerLow extends CPSOptimizer(SymbolicCPSTreeModuleLow)
    with (SymbolicCPSTreeModuleLow.Tree => SymbolicCPSTreeModuleLow.Tree) {
  import treeModule._

  protected val impure: ValuePrimitive => Boolean =
    Set(CPSBlockSet, CPSByteRead, CPSByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case CPSBlockAlloc(_) | CPSBlockGet | CPSByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case CPSBlockAlloc(tag) => tag
  }
  protected val blockTag: ValuePrimitive = CPSBlockTag
  protected val blockLength: ValuePrimitive = CPSBlockLength

  protected val identity: ValuePrimitive = CPSId

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, CPSAdd), (1, CPSMul), (~0, CPSAnd), (0, CPSOr), (0, CPSXOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((CPSAdd, 0), (CPSSub, 0), (CPSMul, 1), (CPSDiv, 1),
        (CPSArithShiftL, 0), (CPSArithShiftR, 0),
        (CPSAnd, ~0), (CPSOr, 0), (CPSXOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, CPSMul), (0, CPSAnd), (~0, CPSOr))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((CPSMul, 0), (CPSAnd, 0), (CPSOr, ~0))

  protected val sameArgReduce: Map[ValuePrimitive, Literal] =
    Map(CPSSub -> 0, CPSDiv -> 1, CPSMod -> 0, CPSXOr -> 0)

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case CPSLe | CPSGe | CPSEq => true
    case CPSLt | CPSGt | CPSNe => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    case (CPSAdd, Seq(x, y)) => x + y
    case (CPSSub, Seq(x, y)) => x - y
    case (CPSMul, Seq(x, y)) => x * y
    case (CPSDiv, Seq(x, y)) if (y != 0) => Math.floorDiv(x, y)
    case (CPSMod, Seq(x, y)) if (y != 0) => Math.floorMod(x, y)

    case (CPSArithShiftL, Seq(x, y)) => x << y
    case (CPSArithShiftR, Seq(x, y)) => x >> y
    case (CPSAnd, Seq(x, y)) => x & y
    case (CPSOr, Seq(x, y)) => x | y
    case (CPSXOr, Seq(x, y)) => x ^ y
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {

    case (CPSLt, Seq(x, y)) => x < y
    case (CPSLe, Seq(x, y)) => x <= y
    case (CPSEq, Seq(x, y)) => x == y
    case (CPSNe, Seq(x, y)) => x != y
    case (CPSGe, Seq(x, y)) => x >= y
    case (CPSGt, Seq(x, y)) => x > y
  }
}
