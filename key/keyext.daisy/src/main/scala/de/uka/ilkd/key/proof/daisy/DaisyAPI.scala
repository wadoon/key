package de.uka.ilkd.key.proof.daisy

import java.util
import daisy.analysis.DataflowPhase
import daisy.lang.Identifiers.{FreshIdentifier, Identifier}
import daisy.lang.Trees._
import daisy.lang.{Trees, Types}
import daisy.lang.Types.RealType
import daisy.tools.{DoubleInterval, FloatInterval}
import de.uka.ilkd.key.java.Services
import de.uka.ilkd.key.java.expression.literal.FloatLiteral
import de.uka.ilkd.key.ldt.{DoubleLDT, FloatLDT}
import de.uka.ilkd.key.logic.op.Operator
import de.uka.ilkd.key.logic.{ProgramElementName, Term}
import de.uka.ilkd.key.util.Pair
import org.key_project.util.ExtList

import scala.language.postfixOps
import scala.collection.JavaConverters._


object DaisyAPI {


  def computeFloatRange(preconditions: util.List[Term], floatExpr: Term, lets: util.List[Term], services: Services): Pair[java.lang.Float, java.lang.Float] = {

    DataflowPhase.rangeMethod = "interval"

    val daisyInputValMap = convertFloatPreCondsToInputIntervals(preconditions, services)
    val daisyExpression = convertToDaisyExpr(lets, floatExpr, daisyInputValMap.keys.toList, services)

    val range: FloatInterval = FloatInterval.floatEvalRange(daisyExpression, daisyInputValMap)

    new Pair[java.lang.Float, java.lang.Float](range.xlo, range.xhi)
  }

  def computeDoubleRange(preconditions: util.List[Term], doubleExpr: Term, lets: util.List[Term], services: Services): Pair[java.lang.Double, java.lang.Double] = {

    DataflowPhase.rangeMethod = "interval"

    val daisyInputValMap = convertDoublePreCondsToInputIntervals(preconditions, services)
    val daisyExpression = convertToDaisyExpr(lets, doubleExpr, daisyInputValMap.keys.toList, services)

    val range: DoubleInterval = DoubleInterval.doubleEvalRange(daisyExpression, daisyInputValMap)

    new Pair[java.lang.Double, java.lang.Double](range.xlo, range.xhi)
  }

  def convertFloatPreCondsToInputIntervals(floatPreconditions: util.List[Term], services: Services): Map[Identifier, FloatInterval] = {

    var daisyInputValMap = Map[Identifier, FloatInterval]()
    var preConds = Map[String, (Option[Float], Option[Float])]()
    val floatLDT = new FloatLDT(services)

    def updatePreCondsMap(key: String, fl: Float): Unit = {

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

    for (expr <- floatPreconditions.asScala) {

      val termDetails = expr.asInstanceOf[Term].subs()
      val varName = termDetails.asScala.filter(p => !p.asInstanceOf[Term].isRigid).toList.head.asInstanceOf[Term].op().name().asInstanceOf[ProgramElementName].getProgramName
      val literal = termDetails.asScala.filter(p => p.asInstanceOf[Term].isRigid).toList.head.asInstanceOf[Term]

      val fl: Float = floatLDT.translateTerm(literal, new ExtList, services).asInstanceOf[FloatLiteral].getValue.toFloat

      updatePreCondsMap(varName, fl)
    }

    for (item <- preConds) {

      val varId = FreshIdentifier(item._1, RealType, false)
      val varLowerBound = item._2._1
      val varUpperBound = item._2._2
      if (varUpperBound isDefined)
        daisyInputValMap += varId -> FloatInterval(varLowerBound.get, varUpperBound.get)
      else throw new IllegalArgumentException("Upper or lower bound not given")

    }

    daisyInputValMap
  }

  def convertDoublePreCondsToInputIntervals(doublePreconditions: util.List[Term], services: Services): Map[Identifier, DoubleInterval] = {

    var daisyInputValMap = Map[Identifier, DoubleInterval]()
    var preConds = Map[String, (Option[Double], Option[Double])]()
    val doubleLTD = new DoubleLDT(services)

    def updatePreCondsMap(key: String, d: Double): Unit = {

      if (!preConds.isDefinedAt(key))
        preConds += key -> (Some(d), None)
      else {
        val intervalBounds = preConds(key)
        if (intervalBounds._1.get < d)
          preConds += key -> (intervalBounds._1, Some(d))
        else
          preConds += key -> (Some(d), intervalBounds._1)
      }
    }

    for (expr <- doublePreconditions.asScala) {

      val termDetails = expr.asInstanceOf[Term].subs()
      val varName = termDetails.asScala.filter(p => !p.asInstanceOf[Term].isRigid).toList.head.asInstanceOf[Term].op().name().asInstanceOf[ProgramElementName].getProgramName
      val literal = termDetails.asScala.filter(p => p.asInstanceOf[Term].isRigid).toList.head.asInstanceOf[Term]

      val d: Double = doubleLTD.translateTerm(literal, new ExtList, services).asInstanceOf[de.uka.ilkd.key.java.expression.literal.DoubleLiteral].getValue.toDouble

      updatePreCondsMap(varName, d)
    }

    for (item <- preConds) {

      val varId = FreshIdentifier(item._1, RealType, false)
      val varLowerBound = item._2._1
      val varUpperBound = item._2._2
      if (varUpperBound isDefined)
        daisyInputValMap += varId -> DoubleInterval(varLowerBound.get, varUpperBound.get)
      else throw new IllegalArgumentException("Upper or lower bound not given")

    }

    daisyInputValMap
  }

  //TODO  add support for let expressions
  def convertToDaisyExpr(lets: util.List[Term], term: Term, varIds: List[Identifier], services: Services): Expr = {

    val floatLDT = new FloatLDT(services)
    val doubleLDT = new DoubleLDT(services)
    val op: Operator = term.op()
    val subTerms = term.subs()

    if (op == floatLDT.getAddIEEE || op == doubleLDT.getAddIEEE)
      Plus(convertToDaisyExpr(lets, subTerms.get(1), varIds, services), convertToDaisyExpr(lets, subTerms.get(2), varIds, services))
    else if (op == floatLDT.getSubIEEE || op == doubleLDT.getSubIEEE)
      Minus(convertToDaisyExpr(lets, subTerms.get(1), varIds, services), convertToDaisyExpr(lets, subTerms.get(2), varIds, services))
    else if (op == floatLDT.getMulIEEE || op == doubleLDT.getMulIEEE)
      Times(convertToDaisyExpr(lets, subTerms.get(1), varIds, services), convertToDaisyExpr(lets, subTerms.get(2), varIds, services))
    else if (op == floatLDT.getDivIEEE || op == doubleLDT.getDivIEEE)
      Division(convertToDaisyExpr(lets, subTerms.get(1), varIds, services), convertToDaisyExpr(lets, subTerms.get(2), varIds, services))
    else if (op == floatLDT.getJavaUnaryMinus || op == doubleLDT.getJavaUnaryMinus)
      UMinus(convertToDaisyExpr(lets, subTerms.get(0), varIds, services))
    // if variable
    else if (!op.isRigid && op.arity() == 0) {
      val varName = op.name().asInstanceOf[ProgramElementName].getProgramName
      Variable(varIds.filter(id => id.name == varName).head)
    }
    // if literal
    else if (op.name().toString == "FP") {
      val fl: Float = floatLDT.translateTerm(term, new ExtList, services).asInstanceOf[FloatLiteral].getValue.toFloat
      Trees.FloatLiteral(fl)
    } else if (op.name().toString == "DFP") {
      val db: Double = doubleLDT.translateTerm(term, new ExtList, services).asInstanceOf[de.uka.ilkd.key.java.expression.literal.DoubleLiteral].getValue.toDouble
      Trees.DoubleLiteral(db)
    }
    else throw new IllegalArgumentException("Operation " + op + " not supported")
  }

  def main(args: Array[String]): Unit = {
    println(sample)
    return
  }

  def sample: Pair[java.lang.Float, java.lang.Float] = {

    val xId = daisy.lang.Identifiers.FreshIdentifier("x", Types.RealType, true)
    val yId = daisy.lang.Identifiers.FreshIdentifier("y", Types.RealType, true)

    val interval = FloatInterval(1.0f, 2.0f)
    val intervalsMap = Map(xId -> interval, yId -> interval)

    val expr: Expr = Plus(Variable(xId), Variable(yId))

    DataflowPhase.rangeMethod = "interval"

    val range: FloatInterval = FloatInterval.floatEvalRange(expr, intervalsMap)

    new Pair[java.lang.Float, java.lang.Float](range.xlo, range.xhi)
  }
}



