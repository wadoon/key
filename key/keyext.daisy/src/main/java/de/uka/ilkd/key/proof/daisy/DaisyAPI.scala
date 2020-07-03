package de.uka.ilkd.key.proof.daisy

import java.util

import daisy.analysis.DataflowPhase
import daisy.lang.Identifiers.Identifier
import daisy.lang.Trees.{BooleanLiteral, Expr, Plus, Variable}
import daisy.lang.Types
import daisy.tools.{Interval, Rational}
import de.uka.ilkd.key.logic.Term
import de.uka.ilkd.key.util.Pair


object DaisyAPI {


  def computeRange(preconditions: util.List[Term], floatExpr: Term, lets: util.List[Term]): Pair[java.lang.Float, java.lang.Float] = {

    DataflowPhase.rangeMethod = "interval"

    val range: Interval = DataflowPhase.computeRange(convertPreCondsToInputIntervals(preconditions),
      merge(lets, floatExpr), BooleanLiteral(true)) _1

    new Pair[java.lang.Float, java.lang.Float](range.xlo.toFloat, range.xhi.toFloat)
  }

  def convertPreCondsToInputIntervals(preconditions: util.List[Term]): Map[Identifier, Interval] = ??? //todo Fahia

  def merge(lets: util.List[Term], floatExpr: Term): Expr = ??? //todo Fahia


  def sample: Pair[java.lang.Float, java.lang.Float] = {

    val xId = daisy.lang.Identifiers.FreshIdentifier("x", Types.RealType, true)
    val yId = daisy.lang.Identifiers.FreshIdentifier("y", Types.RealType, true)

    val interval = Interval(Rational.fromReal(1.0), Rational.fromReal(2.0))
    val intervalsMap = Map(xId -> interval, yId -> interval)

    val expr: Expr = Plus(Variable(xId), Variable(yId))

    DataflowPhase.rangeMethod = "interval"

    val range: Interval = DataflowPhase.computeRange(intervalsMap,
      expr, BooleanLiteral(true)) _1

    new Pair[java.lang.Float, java.lang.Float](range.xlo.toFloat, range.xhi.toFloat)
  }

  def main(args: Array[String]): Unit = {
    println(sample)
    return
  }
}



