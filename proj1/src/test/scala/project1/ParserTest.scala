package project1

import java.io._
import org.scalatest._

class ParserTest extends FunSuite {

  def reader(src: String) = new BaseReader(src.iterator, '\u0000')
  def runner(src: String, gData: Map[Char,Int] = Map()) = new ASMRunner(src, gData)

  test("SingleDigit") {
    val gen = new SingleDigitParser(reader("4"))
    val ast = gen.parseCode

    assert(ast == Lit(4), "Invalid result")
  }

  // Function Helper for SingleAddOpParser
  def testSingleAdd(op: String, res: Exp) = {
    val gen = new SingleAddOpParser(reader(op))
    val ast = gen.parseCode

    assert(ast == res, "Invalid result")
  }

  test("SingleAddopAdd") {
    testSingleAdd("1+1", Plus(Lit(1),Lit(1)))
  }

  // Function Helper for MultipleAddOpParser
  def testMultipleAdd(op: String, res: Exp) = {
    val gen = new MultipleAddOpParser(reader(op))
    val ast = gen.parseCode

    assert(ast == res, "Invalid result")
  }
  // TODO
  test("MultipleAddop") {
    testMultipleAdd("1", Lit(1))
    testMultipleAdd("1+2", Plus(Lit(1), Lit(2)))
    testMultipleAdd("1+2-3", Minus(Plus(Lit(1), Lit(2)),Lit(3)))
  }

  // Function Helper for ArithOpParser
  def testArith(op: String, res: Exp) = {
    val gen = new ArithOpParser(reader(op))
    val ast = gen.parseCode

    assert(ast == res, "Invalid result")
  }

  // TODO
  test("ArithOp") {
    testArith("1-3*7", Minus(Lit(1), Times(Lit(3), Lit(7))))
    testArith("9/4+8/7", Plus(Div(Lit(9),Lit(4)), Div(Lit(8),Lit(7))))
    testArith("8/2/2", Div(Div(Lit(8),Lit(2)), Lit(2)))
  }
  // Function Helper for ArithParOpParser
  def testArithPar(op: String, res: Exp) = {
    val gen = new ArithParOpParser(reader(op))
    val ast = gen.parseCode

    assert(ast == res, "Invalid result")
  }

  // TODO
  test("ArithParOp") {
    testArithPar("(1-3)*7", Times(Minus(Lit(1), Lit(3)),Lit(7)))
    testArithPar("9/(4-8)/7", Div(Div(Lit(9),Minus(Lit(4),Lit(8))), Lit(7)))
    testArithPar("2*3*4*5", Times(Times(Times(Lit(2),Lit(3)), Lit(4)), Lit(5)))
  }
}
