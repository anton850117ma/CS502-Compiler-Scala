package project2

import org.scalatest._

class SemanticAnalyzerTest extends FunSuite {
  import Language._

  def testSemanticAnalyzer(ast: Exp, nWarning: Int, nError: Int) = {
    val fakeParser = new Parser(null) {
      override def error(msg: String, pos: Position) = {}
    }

    val analyzer = new SemanticAnalyzer(fakeParser)

    val (w, e) = analyzer.run(ast)
    assert(w == nWarning, "Incorrect number of Warnings")
    assert(e == nError, "Incorrect number of Errors")
  }

  test("29") {
    testSemanticAnalyzer(Lit(1), 0, 0)
    testSemanticAnalyzer(Prim("+", Lit(1), Lit(2)), 0, 0)
  }
  test("30"){
    testSemanticAnalyzer(Unary("*",Lit(1)),0,1)
  }
  test("31"){
    testSemanticAnalyzer(Prim("%",Lit(1),Lit(5)),0,1)
  }
  test("32"){
    testSemanticAnalyzer(VarDec("x",Lit(1),Let("x",Lit(5),Lit(4))), 0 ,0)
  }
  /*test("3"){
    testSemanticAnalyzer(Prim("%",Lit(1),Lit(5)),0,1)
  }
  test("3134"){
    testSemanticAnalyzer(Prim("%",Lit(1),Lit(5)),0,1)
  }*/

}
