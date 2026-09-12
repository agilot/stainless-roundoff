/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._

/** One step from a result to something inside it. */
enum ResultStep {
  case Index(at: Int)
  case Field(id: Identifier)

  def name: String = this match {
    case Index(at) => s"_$at"
    case Field(id) => id.name
  }

  /** `e` with this step taken. */
  def select(e: Expr): Expr = this match {
    case Index(at) => TupleSelect(e, at)
    case Field(id) => ADTSelector(e, id)
  }
}

/** Where a floating-point number sits inside a function's result.
  *
  * The error of a pair of numbers is a pair of errors, not a number, so a function whose result
  * holds several of them is answered about one at a time. Every path is analysed over the same
  * guard tree, which is what the result was computed by however it is taken apart.
  */
case class ResultPath(steps: Seq[ResultStep]) {

  /** How the field reads in a report, empty where the result is one number. */
  def label: String = steps.map(_.name).mkString(".")

  /** `e` with every step taken, which for the empty path is `e` itself. */
  def select(e: Expr): Expr = steps.foldLeft(e)((inner, step) => step.select(inner))
}

object ResultPath {

  /** The path to a result that is one floating-point number. */
  val whole: ResultPath = ResultPath(Seq.empty)

  /** Every floating-point number inside `tpe`, in the order the type writes them.
    *
    * Tuples and case classes are taken apart, to any depth; a class with more than one
    * constructor is not, since which fields a value has is then not known from its type. A
    * field that holds neither a number nor more fields — a flag, a name, a list — is passed
    * over rather than refused, so a result that carries one alongside its numbers is still
    * answered about. Empty means there is nothing here to bound.
    */
  def of(tpe: Type)(using symbols: Symbols): Seq[ResultPath] = {
    def rec(tpe: Type, taken: Seq[ResultStep], seen: Set[Identifier]): Seq[ResultPath] =
      tpe match {
        case FPType(_, _) => Seq(ResultPath(taken))

        case TupleType(bases) =>
          bases.zipWithIndex.flatMap { case (base, at) =>
            rec(base, taken :+ ResultStep.Index(at + 1), seen)
          }

        // A type reached through itself would be taken apart forever, and a value of it holds
        // no fixed number of fields anyway.
        case adt: ADTType if !seen(adt.id) =>
          adt.getSort.constructors match {
            case Seq(only) =>
              only.fields.flatMap(field =>
                rec(field.getType, taken :+ ResultStep.Field(field.id), seen + adt.id))
            case _ => Seq.empty
          }

        case _ => Seq.empty
      }

    rec(tpe, Seq.empty, Set.empty)
  }

  /** Whether `tpe` is a result the analysis takes apart rather than one value. */
  def isCompound(tpe: Type): Boolean = tpe match {
    case TupleType(_) => true
    case _: ADTType => true
    case _ => false
  }

  /** Why `tpe` holds nothing to bound, said in terms of what was written. */
  def refusal(tpe: Type)(using Symbols): String = tpe match {
    case adt: ADTType if adt.getSort.constructors.size > 1 =>
      s"the result is a '${adt.id.name}', which has more than one constructor, so which " +
      "fields a value of it has is not known from its type"
    case _ if isCompound(tpe) =>
      "nothing in the result of this function is a floating-point number"
    case _ =>
      "the result of this function is not a floating-point number"
  }
}
