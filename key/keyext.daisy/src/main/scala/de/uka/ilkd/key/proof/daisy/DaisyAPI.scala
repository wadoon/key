package de.uka.ilkd.key.proof.daisy

import java.util

import daisy.analysis.DataflowPhase
import daisy.lang.Identifiers.FreshIdentifier.{decode, uniqueCounter}
import daisy.lang.Identifiers.{FreshIdentifier, Identifier}
import daisy.lang.Trees.{BooleanLiteral, Division, Expr, Minus, Plus, RealLiteral, Times, Variable}
import daisy.lang.Types
import daisy.lang.Types.RealType
import daisy.tools.Rational.{double2Fraction, fromReal}
import daisy.tools.{Interval, Rational}
import de.uka.ilkd.key.java.Services
import de.uka.ilkd.key.java.expression.literal.FloatLiteral
import de.uka.ilkd.key.ldt.FloatLDT
import de.uka.ilkd.key.logic.op.Operator
import de.uka.ilkd.key.logic.{Name, ProgramElementName, Term}
import de.uka.ilkd.key.util.Pair
import org.key_project.util.ExtList

import scala.collection.JavaConverters._
import scala.collection.mutable


object DaisyAPI {


  def computeRange(preconditions: util.List[Term], floatExpr: Term, lets: util.List[Term], services: Services): Pair[java.lang.Float, java.lang.Float] = {

    DataflowPhase.rangeMethod = "interval"
    val temp = merge(lets, floatExpr, services)

    val range: Interval = DataflowPhase.computeRange(convertPreCondsToInputIntervals(preconditions, services),
      merge(lets, floatExpr, services), BooleanLiteral(true)) _1

    new Pair[java.lang.Float, java.lang.Float](range.xlo.toFloat, range.xhi.toFloat)
  }

  def convertPreCondsToInputIntervals(preconditions: util.List[Term], services: Services): Map[Identifier, Interval] = {

    var preConds = Map[Identifier, Interval]()
    var preCondsTemp = Map[String, List[Rational]]()

    def updateMap(key: String, fl: Rational): Unit = {

      if (!preCondsTemp.isDefinedAt(key))
        preCondsTemp += key -> List(fl)
      else {
        var item = preCondsTemp(key)
        var newItem = fl :: item
        preCondsTemp += key -> (newItem)
      }
    }

    for (expr <- preconditions.asScala) {

      val termDetails = expr.asInstanceOf[Term].subs()
      val varName = termDetails.asScala.filter(p => !p.asInstanceOf[Term].isRigid).toList.head.asInstanceOf[Term].op().name().asInstanceOf[ProgramElementName].getProgramName
      val literal = termDetails.asScala.filter(p => p.asInstanceOf[Term].isRigid).toList.head.asInstanceOf[Term]

      val floatLDT = new FloatLDT(services)
      val fl: Double = floatLDT.translateTerm(literal, new ExtList, services).asInstanceOf[FloatLiteral].getValue.toDouble
      val fr: Rational = Rational.fromDouble(fl)

      updateMap(varName, fr)
    }
    for (item <- preCondsTemp) {

      val varId = FreshIdentifier(item._1, RealType, true)
      var itemList = preCondsTemp(item._1)
      val sortedList = itemList.sorted
      var varInterval = Interval(sortedList.head, sortedList(1))

      preConds += varId -> varInterval
    }
    preConds
  }

  def merge(lets: util.List[Term], floatExpr: Term, services: Services): Expr = {

    val op: Operator = floatExpr.op()
    val floatLDT = new FloatLDT(services)
    val subterms = floatExpr.subs()

    if (op == floatLDT.getJavaAdd)
      Plus(merge(lets, subterms.get(0), services), merge(lets, subterms.get(1), services))
    else if (op == floatLDT.getJavaSub)
      Minus(merge(lets, subterms.get(0), services), merge(lets, subterms.get(1), services))
    else if (op == floatLDT.getJavaMul)
      Times(merge(lets, subterms.get(0), services), merge(lets, subterms.get(1), services))
    else if (op == floatLDT.getJavaDiv)
      Division(merge(lets, subterms.get(0), services), merge(lets, subterms.get(1), services))
    else if (!op.isRigid && op.arity() == 0) {
      val name = op.name().asInstanceOf[ProgramElementName].getProgramName
      Variable(FreshIdentifier(name, RealType, true))
    }
    else if (op.name().toString == "FP") {
      val fl: Double = floatLDT.translateTerm(floatExpr, new ExtList, services).asInstanceOf[FloatLiteral].getValue.toDouble
      RealLiteral(Rational.fromDouble(fl))
    }
    else
      BooleanLiteral(true)
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



