package de.uka.ilkd.key.proof.daisy

import java.util

import daisy.analysis.DataflowPhase
import daisy.lang.Identifiers.{FreshIdentifier, Identifier}
import daisy.lang.Trees.{BooleanLiteral, Division, Expr, Minus, Plus, RealLiteral, Times, Variable}
import daisy.lang.Types
import daisy.lang.Types.RealType
import daisy.tools.{Interval, Rational}
import de.uka.ilkd.key.java.Services
import de.uka.ilkd.key.java.expression.literal.FloatLiteral
import de.uka.ilkd.key.ldt.FloatLDT
import de.uka.ilkd.key.logic.op.Operator
import de.uka.ilkd.key.logic.{ProgramElementName, Term}
import de.uka.ilkd.key.util.Pair
import org.key_project.util.ExtList
import scala.collection.JavaConverters._


object DaisyAPI {


  def computeRange(preconditions: util.List[Term], floatExpr: Term, lets: util.List[Term], services: Services): Pair[java.lang.Float, java.lang.Float] = {

    DataflowPhase.rangeMethod = "interval"

    val daisyInputValMap = convertPreCondsToInputIntervals(preconditions, services)
    val daisyExpression = merge(lets, floatExpr, daisyInputValMap.keys.toList, services)

    val range: Interval = DataflowPhase.computeRange(daisyInputValMap, daisyExpression, BooleanLiteral(true)) _1

    new Pair[java.lang.Float, java.lang.Float](range.xlo.toFloat, range.xhi.toFloat)
  }

  def convertPreCondsToInputIntervals(preconditions: util.List[Term], services: Services): Map[Identifier, Interval] = {

    var daisyInputValMap = Map[Identifier, Interval]()
    var preConds = Map[String, (Option[Rational], Option[Rational])]()
    val floatLDT = new FloatLDT(services)

    def updatePreCondsMap(key: String, fl: Rational): Unit = {

      if (!preConds.isDefinedAt(key))
        preConds += key -> (Some(fl), None)
      else {
        val intervalBounds = preConds(key)
        if (intervalBounds._1.get < fl)
          preConds += key -> (intervalBounds._1, Some(fl))
        else
          preConds += key -> (Some(fl), intervalBounds._1)
      }
    }

    for (expr <- preconditions.asScala) {

      val termDetails = expr.asInstanceOf[Term].subs()
      val varName = termDetails.asScala.filter(p => !p.asInstanceOf[Term].isRigid).toList.head.asInstanceOf[Term].op().name().asInstanceOf[ProgramElementName].getProgramName
      val literal = termDetails.asScala.filter(p => p.asInstanceOf[Term].isRigid).toList.head.asInstanceOf[Term]

      val fl: Double = floatLDT.translateTerm(literal, new ExtList, services).asInstanceOf[FloatLiteral].getValue.toDouble
      val fr: Rational = Rational.fromDouble(fl)

      updatePreCondsMap(varName, fr)
    }

    for (item <- preConds) {

      val varId = FreshIdentifier(item._1, RealType, false)
      val varLowerBound = item._2._1
      val varUpperBound = item._2._2
      if (varUpperBound isDefined)
        daisyInputValMap += varId -> Interval(varLowerBound.get, varUpperBound.get)
      else throw new Exception("Upper or lower bound not given")

    }

    daisyInputValMap
  }

  //TODO  add support for let expressions
  def merge(lets: util.List[Term], floatExpr: Term, varIds: List[Identifier], services: Services): Expr = {

    val floatLDT = new FloatLDT(services)
    val op: Operator = floatExpr.op()
    val subTerms = floatExpr.subs()

    if (op == floatLDT.getJavaAdd)
      Plus(merge(lets, subTerms.get(0), varIds, services), merge(lets, subTerms.get(1), varIds, services))
    else if (op == floatLDT.getJavaSub)
      Minus(merge(lets, subTerms.get(0), varIds, services), merge(lets, subTerms.get(1), varIds, services))
    else if (op == floatLDT.getJavaMul)
      Times(merge(lets, subTerms.get(0), varIds, services), merge(lets, subTerms.get(1), varIds, services))
    else if (op == floatLDT.getJavaDiv)
      Division(merge(lets, subTerms.get(0), varIds, services), merge(lets, subTerms.get(1), varIds, services))
    // if variable
    else if (!op.isRigid && op.arity() == 0) {
      val varName = op.name().asInstanceOf[ProgramElementName].getProgramName
      Variable(varIds.filter(id => id.name == varName).head)
    }
    // if literal
    else if (op.name().toString == "FP") {
      val fl: Double = floatLDT.translateTerm(floatExpr, new ExtList, services).asInstanceOf[FloatLiteral].getValue.toDouble
      RealLiteral(Rational.fromDouble(fl))
    }
    else throw new Exception("Operation" + op + "not supported")
  }

  def main(args: Array[String]): Unit = {
    println(sample)
    return
  }

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
}



